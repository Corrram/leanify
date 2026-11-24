#!/usr/bin/env python3
"""Where an article stands, and what to do next, in the words of its author.

    python scripts/leanify_status.py ARTICLE.tex [--all] [--leanify EXE]

With a certificate (the report `ARTICLE.leanify.json` of the present text), it says
what Leanify reads, how each claim is justified, and lists what is left: a sentence
that is not read, a claim that is false as it is read (with the values at which it
fails), a claim without a proof, a step that is larger than it looks. Each item names
its line, quotes its sentence and says what the author can do about it.

Without a certificate it runs the quick check (`leanify check`, no Lean needed) and
says what a certificate would have to prove.

The exit status is 0 if nothing is left to do, and 1 otherwise.
"""
import argparse
import json
import pathlib
import re
import shutil
import subprocess
import sys
import textwrap

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from leanify_diagnostics import source_pin, failed_message  # noqa: E402

RESULTS = ("text", "proof", "remark", "example", "conjecture")


def plural(n, word, many=None):
    return f"{n} {word if n == 1 else (many or word + 's')}"


def sentence_text(source, s):
    a, b = s["start"], s["stop"]
    while b < len(source) and source[b] not in ".\n":
        b += 1
    return " ".join(source[a:b + 1].split())


def where(s):
    """`Theorem thm:bound`, `the proof at line 53`."""
    env = s["environment"]
    if env == "proof":
        return "Proof"
    if env == "text":
        return "In the text"
    return env.capitalize() + (f" {s['label']}" if s.get("label") else "")


def variables(lean):
    """The variables of a claim in the order of the text (as `leanify_prove.py` counts them)."""
    from leanify_prove import variables as v
    return v(lean)


def counterexample(article, k, claim):
    """`x = 1` from the refutation `refuteK` of the proofs file, if it is by `leanify_counter`."""
    for f in sorted(article.parent.rglob("*.lean")):
        if ".lake" in f.parts:
            continue
        try:
            text = f.read_text(encoding="utf-8")
        except OSError:
            continue
        m = re.search(rf"^theorem refute{k} [^\n]*\n((?:[ \t]+[^\n]*\n?)*)", text, re.M)
        if not m:
            continue
        c = re.search(r"leanify_counter[^\n]*", m.group(1))
        if c:
            from leanify_prove import counter_text
            return counter_text(claim, c.group(0))
        c = re.search(r"--\s*false as it is read: at ([^\n]*)", m.group(1))
        return c.group(1).strip() if c else None
    return None


class Items:
    """What is left, by line."""
    def __init__(self, source, width):
        self.source, self.width, self.items = source, width, []

    def add(self, s, head, advice, quote=True):
        self.items.append((s["line"], head, sentence_text(self.source, s) if quote else "", advice))

    def show(self, limit):
        items = sorted(self.items, key=lambda i: i[0])
        for line, head, quote, advice in items[:limit] if limit else items:
            first = f"  line {line:<5}"
            pad = " " * len(first)
            wrap = lambda t, lead: textwrap.fill(t, self.width, initial_indent=lead, subsequent_indent=pad + " ")
            print(wrap(head, first + " "))
            if quote:
                print(wrap("“" + (quote if len(quote) <= 220 else quote[:217] + "…") + "”", pad + " "))
            print(wrap("→ " + advice, pad + " "))
        if limit and len(items) > limit:
            print(f"  … and {len(items) - limit} more (--all lists them)")
        return len(items)


def certified(article, report, source, a):
    sentences, claims, defs = report["sentences"], report["claims"], report["definitions"]
    ns = report.get("justifications") or ""
    has_cert = ns not in ("", "[anonymous]")
    count = lambda st: sum(c["status"] == st for c in claims)
    out = lambda o: sum(s["outcome"] == o for s in sentences)
    unread = [s for s in sentences if s["outcome"] == "prose" and s["environment"] not in RESULTS]
    print(f"{article.name}: read by Leanify {report.get('leanify', '')}".rstrip()
          + ("" if has_cert else " (statements only: no proofs are checked yet)"))
    print()
    print("What Leanify reads")
    print(f"  {plural(len(sentences), 'sentence')}: {out('compiled')} read as mathematics, "
          f"{out('failed')} with a finding, {out('prose')} running text"
          + (f" ({len(unread)} of them in the statement of a result)" if unread else ""))
    roles = lambda r: sum(c["role"] == r for c in claims)
    print(f"  {plural(len(defs), 'definition')}, {plural(len(claims), 'claim')} "
          f"({plural(roles('statement'), 'statement')} of results, {plural(roles('proof step'), 'step')} of proofs"
          + (f", {roles('text')} in the text" if roles("text") else "") + ")")
    print()
    print("Where the claims stand")
    text = [c for c in claims if c["status"] == "text"]
    standard = sum(c.get("step") == "standard" for c in text)
    if text:
        print(f"  {len(text):>4} proved from exactly the sentences and results they cite "
              f"({standard} by routine steps, {len(text) - standard} by a longer Lean argument)")
    for st, what in (("companion", "proved by a Lean proof that the text does not spell out"),
                     ("quoted", "quoted from the literature and assumed"),
                     ("refuted", "false as read"), ("unverified", "without a proof")):
        if count(st) or st in ("refuted", "unverified"):
            print(f"  {count(st):>4} {what}")
    bad_defs = [d for d in defs if not d.get("justification") and not d.get("undefined")]
    print(f"  {len(defs) - len(bad_defs):>4} of {plural(len(defs), 'definition')} shown to be well defined")
    print()

    items = Items(source, a.width)
    for s in sentences:
        if s["outcome"] == "failed":
            items.add(s, f"{failed_message(s['message'])}: this sentence of {where(s)} is not checked.",
                      "Define the symbol before this sentence, or correct the typo.")
    seen = set()
    for s in unread:
        if s["env"] in seen:
            continue
        seen.add(s["env"])
        n = sum(t["env"] == s["env"] for t in unread)
        items.add(s, f"{where(s)}: Leanify cannot read {'this sentence' if n == 1 else f'{n} of its sentences'}, "
                     "so the result is not checked as you state it.",
                  "Rephrase it with a construction of docs/writing.md "
                  "(`leanify_suggest.py --hook CMD` proposes a wording).")
    for c in claims:
        k, s = c["index"], sentences[c["sentence"]]
        what = "the statement" if c["role"] == "statement" else "this step" if c["role"] == "proof step" else "this claim"
        if c["status"] == "refuted":
            at = counterexample(article, k, c)
            items.add(s, f"{where(s)}: {what} is false as Leanify reads it"
                         + (f": it fails at {at}." if at else f" (claim {k}, refuted by {c.get('justification', '')})."),
                      "Correct the statement (a strict inequality, the end of a range, a missing hypothesis). "
                      f"If you meant something else, compare the reading: `leanify check --claims` shows claim {k}.")
        elif c["status"] == "unverified":
            note = c.get("note") or ""
            if not has_cert:
                continue  # (no proof is checked yet: said once, below)
            elif "rests on" in note:
                first = re.search(r"claim \d+", note)
                advice = (f"Nothing to do here: it uses {first.group(0) if first else 'another claim'}, which is "
                          + ("false as read. Correct that one first." if "refuted" in note
                             else "not proved yet. Prove that one first."))
            else:
                advice = ("`leanify_prove.py` proves a routine step by itself; this one needs a proof by hand or "
                          f"by a model (`--hook CMD`), as `proof{k}` in the proofs file."
                          + (f" ({note})" if note else ""))
            items.add(s, f"{where(s)}: {what} has no proof yet (claim {k}).", advice)
        elif c["status"] in ("text", "companion") and c.get("after"):
            lines = sorted({sentences[t]["line"] for t in c["after"]})
            items.add(s, f"{where(s)}: {what} is proved as it is read, but after a sentence that Leanify does not read "
                         f"(line{'s' if len(lines) > 1 else ''} {', '.join(map(str, lines))}).",
                      "Check that this sentence introduces no hypothesis that the claim needs, or rephrase it so "
                      "that it is read.")
        if c.get("hypotheses") == "open" and c.get("hypothesesOf", k) == k and has_cert:
            items.add(s, f"{where(s)}: its hypotheses are not shown to hold together (claim {k}).",
                      "Give values for the variables (`leanify_prove.py` tries simple ones). If there are none, "
                      "the statement is true for an empty reason: correct its hypotheses.")
    for d in bad_defs:
        s = next((t for t in sentences if d["index"] in (t.get("definitions") or [])), None)
        if s and has_cert:
            items.add(s, f"Definition of {d.get('symbol') or d.get('name')}: not shown to be well defined.",
                      "A term may be used outside its domain (a division by zero, a root of a negative number): "
                      "restrict the range, or prove `defined" + str(d["index"]) + "` with the fact it needs.")
    large = [c for c in text if c.get("step") == "argument"]
    pending = count("unverified") if not has_cert else 0
    print("What is left to do" if items.items or pending
          else "Nothing is left to do: every claim that is read is certified.")
    n = items.show(0 if a.all else a.limit) + pending
    if pending:
        print(textwrap.fill(
            f"None of the {plural(pending, 'claim')} has a proof that Lean has checked yet. `leanify_auto.py "
            f"{article.name}` proves the routine steps by tactics, reports the claims that fail at simple values, "
            "and gives the others to a model if you name one (`--model CMD`).",
            a.width, initial_indent="  ", subsequent_indent="  "))
    if large:
        print()
        lines = sorted({sentences[c["sentence"]]["line"] for c in large})
        shown = lines if a.all else lines[:12]
        print(textwrap.fill(
            f"{plural(len(large), 'step')} of the proofs {'is' if len(large) == 1 else 'are'} verified, but not by a "
            f"routine step: the sentence skips more than a reader checks at a glance (line"
            f"{'s' if len(lines) > 1 else ''} {', '.join(map(str, shown))}{', …' if len(shown) < len(lines) else ''}). "
            "Nothing is wrong there; an intermediate sentence in the printed proof would make such a step routine.",
            a.width))
    return 1 if n else 0


def uncertified(article, check, source, a):
    cov, claims, defs = check["coverage"], check["claims"], check["definitions"]
    roles = lambda r: sum(c["role"] == r for c in claims)
    print(f"{article.name}: no certificate of this text yet (quick check only)")
    print()
    print("What Leanify reads")
    for part, name in (("results", "sentences of results"), ("proofs", "sentences of proofs")):
        c = cov[part]
        total = c["compiled"] + c["failed"] + c["prose"]
        print(f"  {c['compiled']} of {total} {name}" + (f", {c['failed']} with a finding" if c["failed"] else ""))
    print(f"  {plural(len(defs), 'definition')}, {plural(len(claims), 'claim')} "
          f"({plural(roles('statement'), 'statement')} of results, {plural(roles('proof step'), 'step')} of proofs)")
    print()
    print("What a certificate takes")
    print(textwrap.fill(
        f"Lean has to be given a proof of each of the {plural(len(claims), 'claim')}, and that each of the "
        f"{plural(len(defs), 'definition')} is well defined. `leanify certify {article.name}` sets up the Lean project; "
        "`leanify_prove.py` then proves the routine steps by itself and reports the claims that fail at simple "
        "values. What is left needs a proof by hand or by a model (`--hook CMD`); in the research articles "
        "certified so far (probability, analysis) that was most of the steps.",
        a.width, initial_indent="  ", subsequent_indent="  "))
    print()
    findings = [f for f in check.get("findings", []) if f.get("severity") in ("warning", "error")]
    print("What is left to do before that" if findings else "Every sentence of a result is read.")
    for f in findings if a.all else findings[:a.limit]:
        print(textwrap.fill(f["message"], a.width, initial_indent=f"  line {f['line']:<5} ", subsequent_indent=" " * 14))
    if not a.all and len(findings) > a.limit:
        print(f"  … and {len(findings) - a.limit} more (--all lists them)")
    return 1 if findings else 0


def find_exe(article, given):
    if given:
        return [given]
    for d in [article.parent, *article.parents]:
        for name in ("leanify", "leanify.exe"):
            for rel in (pathlib.Path(".lake/build/bin"), pathlib.Path(".lake/packages/leanify/.lake/build/bin"),
                        pathlib.Path("lean/.lake/packages/leanify/.lake/build/bin")):
                if (d / rel / name).exists():
                    return [str(d / rel / name)]
    exe = shutil.which("leanify")
    return [exe] if exe else None


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("article", type=pathlib.Path)
    ap.add_argument("--all", action="store_true", help="list every item")
    ap.add_argument("--limit", type=int, default=20, help="items listed without --all")
    ap.add_argument("--leanify", help="the checker, for an article without a certificate")
    ap.add_argument("--vocab", help="fields for the quick check (as `leanify check --vocab`)")
    ap.add_argument("--width", type=int, default=100)
    a = ap.parse_args(argv)
    article = a.article.resolve()
    raw = article.read_bytes().decode("utf-8")
    source = raw.replace("\r\n", "\n")
    report_path = article.with_suffix(".leanify.json")
    if report_path.exists():
        report = json.loads(report_path.read_text(encoding="utf-8"))
        if report.get("sourceHash") == source_pin(raw):
            return certified(article, report, source, a)
        print(f"({report_path.name} is the report of an earlier text: `leanify certify {article.name}` renews it)\n")
    exe = find_exe(article, a.leanify)
    if not exe:
        raise SystemExit("no certificate of this text, and no `leanify` to check it with: give --leanify EXE "
                         "(https://github.com/Corrram/leanify/releases)")
    cmd = exe + ["check", str(article), "--json"] + (["--vocab", a.vocab] if a.vocab else [])
    p = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", errors="replace")
    try:
        check = json.loads(p.stdout)
    except json.JSONDecodeError:
        raise SystemExit(f"{' '.join(cmd)} did not answer:\n{p.stdout}{p.stderr}")
    return uncertified(article, check, source, a)


if __name__ == "__main__":
    sys.exit(main())
