#!/usr/bin/env python3
"""Suggest edits for the sentences Leanify cannot read: a hook proposes, the checker decides.

`leanify check` reports the sentences of an article that have no reading. Most of
them say something the grammar reads in another form (`docs/writing.md`). This
script gives each such sentence to a command of yours (a model, usually), with the
finding, the sentences around it and the guide, and asks for the sentence rewritten.

A suggestion is kept only if the checker then reads every sentence of the rewritten
text and still reads every sentence it read before. So the meaning of the edited
article is fixed by the grammar, as always: the hook never tells Leanify what a
sentence means. Whether the rewritten sentence still says what you meant is for you
to judge: the script prints each suggestion as a diff, with the formal reading of the
new sentence, and changes nothing unless you pass `--apply`.

    python scripts/leanify_suggest.py Note/article.tex --hook CMD [--vocab FIELDS]
        [--proofs] [--jobs 4] [--rounds 2] [--apply] [--leanify EXE] [--guide FILE]

CMD reads one JSON object on its standard input:

    sentence      the sentence as it is in the source
    finding       why Leanify does not read it (may be empty: no reading at all)
    environment   theorem, lemma, proof, text, …
    before, after the sentences around it, in order
    guide         docs/writing.md, the forms the grammar reads
    instructions  what to print
    previous      earlier suggestions for this sentence and why they were not kept

and prints the LaTeX that replaces the sentence (one or more sentences), or nothing.

The targets are the sentences of results without a reading, and every sentence that
failed (an undefined symbol is skipped: its fix is elsewhere); `--proofs` adds the
sentences of proofs, so that results can be derived from their printed proofs.
The exit status is 1 if a target is left without a suggestion.
"""
import argparse
import concurrent.futures
import difflib
import json
import pathlib
import shlex
import shutil
import subprocess
import sys
import tempfile

DISCUSSION = {"remark", "example", "conjecture"}

INSTRUCTIONS = (
    "Rewrite the sentence so that Leanify reads it, in one of the forms of the guide, without changing "
    "what it says. Keep the author's notation and labels. You may split it into several sentences, and you "
    "may put a convention sentence of the guide before it (for example `Throughout, increasing means "
    "non-decreasing.`) when the finding asks for one. Do not add mathematical content, and do not "
    "strengthen or weaken the statement. Print only the LaTeX that replaces the sentence, with no "
    "explanation and no code fences. If the sentence cannot be said in the forms of the guide, print nothing."
)


# --- running the checker ----------------------------------------------------------------

def project_root(start):
    for d in [start, *start.parents]:
        if (d / "lakefile.toml").exists() or (d / "lakefile.lean").exists():
            return d
    return None


def checker(article, given):
    """The command that runs `leanify`: the given executable, the one lake built, lake, or the PATH."""
    if given:
        return shlex.split(given), None
    root = project_root(article.parent)
    if root:
        for rel in (".lake/packages/leanify/.lake/build/bin/leanify", ".lake/build/bin/leanify"):
            for ext in ("", ".exe"):
                exe = root / (rel + ext)
                if exe.exists():
                    return [str(exe)], None
        return ["lake", "exe", "leanify"], root
    if shutil.which("leanify"):
        return ["leanify"], None
    raise SystemExit("leanify not found: run inside a Lean project that requires Leanify, or pass --leanify EXE")


def check(cmd, cwd, article, vocab):
    args = cmd + ["check", str(article), "--json"] + (["--vocab", vocab] if vocab else [])
    p = subprocess.run(args, cwd=cwd, capture_output=True, text=True, encoding="utf-8", errors="replace")
    line = next((l for l in p.stdout.splitlines() if l.startswith("{")), None)
    if line is None:
        raise SystemExit(f"{' '.join(args)}\ngave no report:\n{p.stdout}{p.stderr}")
    return json.loads(line)


# --- the text of the article --------------------------------------------------------------

class Files:
    """The article and the files it inputs, as lists of lines, copied to a working folder."""

    def __init__(self, article, report, work):
        self.dir = article.parent
        self.work = work
        self.names = [article.name] + [pathlib.Path(f).resolve().relative_to(self.dir.resolve()).as_posix()
                                       for f in report.get("inputs", [])]
        self.text, self.crlf = {}, {}
        for n in self.names:
            raw = (self.dir / n).read_bytes().decode("utf-8")
            self.crlf[n] = "\r\n" in raw
            self.text[n] = raw.replace("\r\n", "\n")
        self.original = dict(self.text)
        # the edits made so far: (file, place in the original text, old length, new length)
        self.edits = []
        self.article = work / article.name
        self.flush()

    def key(self, reported):
        """The name of a file of the working folder, as a report of it names the file."""
        try:
            n = pathlib.Path(reported).resolve().relative_to(self.work.resolve()).as_posix()
        except ValueError:
            return None
        return n if n in self.text else None

    def now(self, name, place):
        """Where a place of the original text is now."""
        return place + sum(new - old for (n, at, old, new) in self.edits if n == name and at < place)

    def save(self):
        """Write the edited files back into the article's folder, with their line endings."""
        for n in self.names:
            if self.text[n] != self.original[n]:
                t = self.text[n].replace("\n", "\r\n") if self.crlf[n] else self.text[n]
                (self.dir / n).write_bytes(t.encode("utf-8"))
                print(f"wrote {self.dir / n}")

    def flush(self):
        for n, t in self.text.items():
            f = self.work / n
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_text(t, encoding="utf-8", newline="\n")

    def offset(self, name, line, col):
        lines = self.text[name].split("\n")
        return sum(len(l) + 1 for l in lines[:line - 1]) + col - 1

    def span(self, s):
        """(name, start, stop) of a sentence in its file, if the report's text is there."""
        name, end = self.key(s["file"]), self.key(s["endFile"])
        if name is None or name != end:
            return None
        a = self.offset(name, s["line"], s["column"])
        b = self.offset(name, s["endLine"], s["endColumn"])
        return (name, a, b) if self.text[name][a:b] == s["text"] else None


# --- targets and suggestions ----------------------------------------------------------------

def targets(report, proofs):
    out = []
    for s in report["sentences"]:
        env = s["environment"]
        if s["outcome"] == "compiled" or env in DISCUSSION:
            continue
        message = s.get("message", "")
        if s["outcome"] == "failed":
            # an undefined symbol is fixed where it should have been defined
            if message.endswith("is not defined"):
                continue
            if env == "proof" and not proofs:
                continue
        elif env == "text" or (env == "proof" and not proofs):
            continue
        out.append(s)
    return out


def payload(s, report, guide, previous):
    i = s["index"]
    sents = report["sentences"]
    return {
        "sentence": s["text"], "finding": s.get("message", ""), "environment": s["environment"],
        "label": s.get("label", ""),
        "before": [t["text"] for t in sents[max(0, i - 8):i]],
        "after": [t["text"] for t in sents[i + 1:i + 3]],
        "guide": guide, "instructions": INSTRUCTIONS, "previous": previous,
    }


def ask(hook, data, timeout):
    try:
        p = subprocess.run(shlex.split(hook), input=json.dumps(data, ensure_ascii=False), capture_output=True,
                           text=True, timeout=timeout, encoding="utf-8", errors="replace")
    except subprocess.TimeoutExpired:
        return None
    lines = [l for l in p.stdout.strip().splitlines() if not l.startswith("```")]
    text = "\n".join(lines).strip()
    return text or None


def compiled_texts(report):
    texts = {}
    for s in report["sentences"]:
        if s["outcome"] == "compiled":
            texts[s["text"]] = texts.get(s["text"], 0) + 1
    return texts


def judge(before, after, files, name, start, new):
    """Why a suggestion is not kept (None: it is). `after` is the check of the article with
    `new` at `start` of file `name`."""
    stop = start + len(new)
    inside = []
    for s in after["sentences"]:
        if files.key(s["file"]) != name:
            continue
        a = files.offset(name, s["line"], s["column"])
        if start <= a < stop:
            inside.append(s)
    if not inside:
        return "the checker finds no sentence in the suggestion", []
    bad = [s for s in inside if s["outcome"] != "compiled"]
    if bad:
        why = bad[0].get("message") or "no reading: it matches none of the forms of the guide"
        return f"Leanify does not read `{bad[0]['text']}`: {why}", []
    was, now = compiled_texts(before), compiled_texts(after)
    lost = [t for t, n in was.items() if now.get(t, 0) < n]
    if lost:
        return f"with it, Leanify no longer reads `{lost[0]}`", []
    readings = [c["reading"] for s in inside for k in s.get("claims", []) for c in [after["claims"][k]]]
    defs = [after["definitions"][i]["symbol"] for s in inside for i in s.get("definitions", [])]
    return None, [f"defines {d}" for d in defs] + readings


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("article")
    ap.add_argument("--hook", required=True, help="command that rewrites one sentence (JSON on stdin, LaTeX on stdout)")
    ap.add_argument("--vocab", help="the fields of the article's vocabulary, as for `leanify check`")
    ap.add_argument("--proofs", action="store_true", help="also the sentences of proofs")
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--rounds", type=int, default=2, help="tries of the hook per sentence")
    ap.add_argument("--hook-timeout", type=int, default=600)
    ap.add_argument("--leanify", help="the leanify executable (default: the project's, or the PATH's)")
    ap.add_argument("--guide", help="the guide given to the hook (default: docs/writing.md of Leanify)")
    ap.add_argument("--apply", action="store_true", help="write the kept suggestions into the article")
    a = ap.parse_args(argv)

    article = pathlib.Path(a.article).resolve()
    cmd, cwd = checker(article, a.leanify)
    guide_path = pathlib.Path(a.guide) if a.guide else pathlib.Path(__file__).resolve().parent.parent / "docs" / "writing.md"
    guide = guide_path.read_text(encoding="utf-8") if guide_path.exists() else ""

    first = check(cmd, cwd, article, a.vocab)
    with tempfile.TemporaryDirectory(prefix="leanify-suggest-") as tmp:
        files = Files(article, first, pathlib.Path(tmp))
        report = check(cmd, cwd, files.article, a.vocab)
        report0 = report
        todo = []
        for s in targets(report, a.proofs):
            span = files.span(s)
            if span:
                s["name"], s["place"] = span[0], span[1]
                todo.append(s)
        print(f"{len(todo)} sentence{'s' if len(todo) != 1 else ''} without a reading in {article.name}")
        if not todo:
            return 0
        # the hook sees the article as it is; the suggestions are tried one after the other, each
        # in the article with the suggestions kept before it
        todo.sort(key=lambda s: (files.names.index(s["name"]), s["place"]))
        previous = {s["index"]: [] for s in todo}
        kept, open_ = [], list(todo)
        for _ in range(a.rounds):
            if not open_:
                break
            with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as pool:
                answers = list(pool.map(lambda s: ask(a.hook, payload(s, report0, guide, previous[s["index"]]),
                                                      a.hook_timeout), open_))
            still = []
            for s, new in zip(open_, answers):
                if not new:
                    previous[s["index"]].append({"suggestion": "", "rejected": "no suggestion"})
                    still.append(s)
                    continue
                # the sentence, where it is now
                name = s["name"]
                start = files.now(name, s["place"])
                stop = start + len(s["text"])
                saved = files.text[name]
                files.text[name] = saved[:start] + new + saved[stop:]
                files.flush()
                after = check(cmd, cwd, files.article, a.vocab)
                why, readings = judge(report, after, files, name, start, new)
                if why is None:
                    kept.append((s, new, readings))
                    files.edits.append((name, s["place"], len(s["text"]), len(new)))
                    report = after
                else:
                    files.text[name] = saved
                    files.flush()
                    previous[s["index"]].append({"suggestion": new, "rejected": why})
                    still.append(s)
            open_ = still

        kept.sort(key=lambda k: (files.names.index(k[0]["name"]), k[0]["place"]))
        for s, new, readings in kept:
            print(f"\n{s['name']}:{s['line']}: {s['environment']}")
            for l in s["text"].splitlines():
                print(f"  - {l}")
            for l in new.splitlines():
                print(f"  + {l}")
            for r in readings:
                print(f"    reads as: {r}")
        for s in open_:
            last = previous[s["index"]][-1]["rejected"] if previous[s["index"]] else "no suggestion"
            print(f"\n{s['name']}:{s['line']}: no suggestion kept ({last})")

        diff = []
        for n in files.names:
            if files.text[n] != files.original[n]:
                diff += difflib.unified_diff(files.original[n].splitlines(True), files.text[n].splitlines(True),
                                             fromfile=n, tofile=n)
        print(f"\nkept {len(kept)} of {len(todo)} suggestions; without one: {len(open_)}")
        if diff:
            if a.apply:
                files.save()
            else:
                out = article.with_suffix(".leanify.diff")
                out.write_text("".join(diff), encoding="utf-8", newline="\n")
                print(f"wrote {out}: read it, then apply it (git apply, or run again with --apply)")
        return 0 if not open_ else 1


if __name__ == "__main__":
    sys.exit(main())
