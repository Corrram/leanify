#!/usr/bin/env python3
"""Prove the open obligations of a compiled article: tactics first, then a hook.

`leanify init` writes a stub for every claim into `Proofs.lean`:

    theorem proof4 : obligation4 := by
      intro_premises
      refine ⟨by unfold meaningful4; definedness [], ?_⟩
      sorry

This script fills in the stubs that still end in `sorry`.

* Tier 0 (no model): a fixed portfolio of tactic scripts is tried on every open
  obligation. The candidates of all obligations go into one Lean file, which Lean
  elaborates once; the first candidate of each obligation that elaborates without
  an error replaces the `sorry`.
* Tier 1 (optional, `--hook CMD`): every obligation still open is given to CMD,
  one at a time and in parallel (`--jobs`), as JSON on its standard input: the
  claim, its formal reading, its Lean statement, its premises, the sentence and
  the proof around it, and the errors of the last attempt. CMD prints a tactic
  block (the body after `:= by`). The blocks are checked the same way, and
  `--rounds` gives CMD the errors of a failed block for another try.

Every proof is checked by Lean before it is written, and `lake build` of the
certificate checks it again, with the citation audit. Proofs that worked are
cached by the statement they prove (in `.lake/leanify-prove/cache.json`), so
after an edit of the article only what changed is proved again.

    python scripts/leanify_prove.py Note/article.tex [--proofs Note/Proofs.lean]
        [--hook CMD] [--jobs 4] [--rounds 2] [--timeout 900] [--dry-run]

It needs the report `Note/article.leanify.json`: build the certificate once
(`lake build Note.Certified`) before the first run; it covers the claims whose
proofs are still `sorry`.
"""
import argparse
import concurrent.futures
import hashlib
import json
import pathlib
import re
import shlex
import subprocess
import sys

STUB_HEAD = re.compile(r"^theorem proof(\d+) : obligation\1 := by\s*$")
MESSAGE = re.compile(r"^(.*?):(\d+):(\d+): (error|warning): (.*)$")


# --- the project, the report and the stubs --------------------------------------------

def project_root(start):
    for d in [start, *start.parents]:
        if (d / "lakefile.toml").exists() or (d / "lakefile.lean").exists():
            return d
    raise SystemExit(f"{start}: no lakefile.toml or lakefile.lean in this folder or above")


def stub_blocks(lines):
    """The claim stubs of Proofs.lean: {k: (first line, end line)} of each `theorem proofK` block
    (the end is exclusive: the next declaration, docstring, blank line or `end`)."""
    blocks = {}
    i = 0
    while i < len(lines):
        m = STUB_HEAD.match(lines[i])
        if m:
            j = i + 1
            while j < len(lines) and lines[j].strip() and not lines[j].startswith(("/--", "theorem ", "end ", "lemma ", "def ")):
                j += 1
            blocks[int(m.group(1))] = (i, j)
            i = j
        else:
            i += 1
    return blocks


def is_open(lines, block):
    a, b = block
    return any(re.search(r"\bsorry\b", l) for l in lines[a:b])


# --- the shape of a claim ---------------------------------------------------------------

def split_top(s, sep):
    """Split at `sep` outside brackets."""
    parts, depth, cur, i = [], 0, "", 0
    while i < len(s):
        c = s[i]
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        if depth == 0 and s.startswith(sep, i):
            parts.append(cur)
            cur = ""
            i += len(sep)
            continue
        cur += c
        i += 1
    parts.append(cur)
    return [p.strip() for p in parts]


def shape(lean):
    """The names to introduce, in order, for `∀ (x : T), H → ∀ (y : U), H' → … → body`:
    binder names and `h_0`, `h_1`, … for the hypotheses."""
    s = " ".join(lean.split())
    seq, nh = [], 0
    while True:
        if s.startswith("∀"):
            m = re.match(r"∀\s*((?:\([^()]*\)\s*)+),\s*", s)
            if m:
                for group in re.findall(r"\(([^()]*)\)", m.group(1)):
                    seq += group.split(":")[0].split()
                s = s[m.end():]
                continue
            m = re.match(r"∀\s*([^,:]+?)\s*(?::[^,]*)?,\s*", s)
            if not m:
                break
            binder = m.group(1)
            if "∈" in binder or any(op in binder for op in ("<", ">", "≤", "≥")):
                # `∀ x ∈ S,` and `∀ x > 0,`: a variable and a hypothesis
                seq += [binder.split()[0], f"h_{nh}"]
                nh += 1
            else:
                seq += binder.split()
            s = s[m.end():]
            continue
        parts = split_top(s, "→")
        if len(parts) < 2:
            break
        seq.append(f"h_{nh}")
        nh += 1
        s = " → ".join(parts[1:])
    return seq


# --- tier 0: candidate scripts ----------------------------------------------------------

def closers(defs, phase):
    """Phase 0: fast tactics; phase 1: the slower ones, for what phase 0 left open."""
    d = ", ".join(defs)
    unf = f"simp only [{d}] at *; " if defs else ""
    each = ("first | assumption | linarith | positivity | ring | (field_simp; ring) | norm_num"
            + (f" [{d}]" if defs else "") + (f" | (simp only [{d}]) | (simp only [{d}]; ring) | (simp only [{d}]; field_simp; ring)" if defs else ""))
    if phase == 0:
        return [
            "assumption",
            "linarith",
            "positivity",
            "ring",
            "(field_simp; ring)",
            f"norm_num [{d}]" if defs else "norm_num",
            f"(repeat' constructor) <;> ({each})",
            f"({unf}field_simp; ring)" if defs else "(field_simp; ring)",
            f"({unf}linarith)" if defs else "linarith",
            f"simp_all [{d}]" if defs else "simp_all",
        ]
    return ["nlinarith", f"({unf}nlinarith)" if defs else "nlinarith", "aesop", "grind", "tauto"]


def preamble(k, claim, premises_lean):
    seq = shape(claim["lean"])
    lines = ["intro_premises", f"refine ⟨by unfold meaningful{k}; definedness [], ?_⟩"]
    if seq:
        lines.append("intro " + " ".join(seq))
    args = " ".join(seq)
    for j in premises_lean:
        if args:
            lines.append(f"try have hc{j} := c{j} {args}")
    lines.append("try casesm* _ ∧ _")
    return lines


def candidates(k, claim, report, cached, phase):
    defs = [d["name"] for d in report.get("definitions", []) if d.get("name")]
    pre = preamble(k, claim, claim.get("premises", []))
    out = []
    if cached and phase == 0:
        out.append(("cache", cached))
    for c in dict.fromkeys(closers(defs, phase)):  # keep order, drop duplicates
        out.append((c, "\n".join(pre + [c])))
    return out


def lean_file(module, ns, items, tag):
    """One Lean file with a theorem per (claim, candidate); returns the text and the line range of each."""
    head = [f"import {module}", "", "set_option maxHeartbeats 400000", "", f"namespace {ns}.ProveTry{tag}", f"open {ns}", ""]
    lines = list(head)
    ranges = []
    for n, (k, label, script) in enumerate(items):
        start = len(lines) + 1
        lines.append(f"theorem try{n} : obligation{k} := by")
        lines += ["  " + l for l in script.splitlines()]
        lines.append("")
        ranges.append((k, label, script, start, len(lines)))
    lines.append(f"end {ns}.ProveTry{tag}")
    return "\n".join(lines) + "\n", ranges


def run_lean(root, path, timeout):
    try:
        p = subprocess.run(["lake", "env", "lean", str(path)], cwd=root, capture_output=True, text=True,
                           timeout=timeout, encoding="utf-8", errors="replace")
    except subprocess.TimeoutExpired:
        raise SystemExit(f"lean did not finish within {timeout} s; raise --timeout")
    return p.stdout + p.stderr


def verdicts(output, path, ranges):
    """{index: [messages]} of the candidates with an error (or a sorry); the others succeeded."""
    bad = {}
    name = pathlib.Path(path).name
    for line in output.splitlines():
        m = MESSAGE.match(line.strip())
        if not m or not m.group(1).replace("\\", "/").endswith(name):
            continue
        ln, sev, msg = int(m.group(2)), m.group(4), m.group(5)
        if sev == "warning" and "sorry" not in msg:
            continue
        for n, (_, _, _, a, b) in enumerate(ranges):
            if a <= ln <= b:
                bad.setdefault(n, []).append(msg)
    return bad


def check(root, module, ns, items, tag, timeout, workdir):
    """Elaborate the candidates; {k: (label, script)} for the first success of each claim, and the errors."""
    text, ranges = lean_file(module, ns, items, tag)
    path = workdir / f"Candidates{tag}.lean"
    path.write_text(text, encoding="utf-8")
    out = run_lean(root, path, timeout)
    if re.search(r"error: .*(unknown module|unknown package|file not found|could not resolve import)", out):
        raise SystemExit(f"Lean could not load {module}:\n{out}\nBuild it first: lake build {module}")
    bad = verdicts(out, path, ranges)
    found, errors = {}, {}
    for n, (k, label, script, _, _) in enumerate(ranges):
        if n in bad:
            errors.setdefault(k, (label, bad[n]))
        elif k not in found:
            found[k] = (label, script)
    return found, errors


# --- tier 1: the hook -------------------------------------------------------------------

def sentence_text(source, report, s):
    sent = report["sentences"][s]
    a, b = sent["start"], sent["stop"]
    while b < len(source) and source[b] not in ".\n":
        b += 1
    return source[a:b + 1].strip()


def payload(k, report, source, errors):
    c = report["claims"][k]
    s = c["sentence"]
    env = report["sentences"][s].get("env", 0)
    around = [sentence_text(source, report, t["index"]) for t in report["sentences"]
              if env and t.get("env") == env]
    return {
        "claim": k, "role": c["role"], "reading": c["reading"], "lean": c["lean"], "meaningful": c["meaningful"],
        "sentence": sentence_text(source, report, s), "environment": around,
        "premises": [{"claim": j, "reading": report["claims"][j]["reading"], "lean": report["claims"][j]["lean"],
                      "name": f"c{j}"} for j in c.get("premises", [])],
        "definitions": [d["name"] for d in report.get("definitions", [])],
        "stub": f"theorem proof{k} : obligation{k} := by\n  intro_premises\n  refine ⟨by unfold meaningful{k}; definedness [], ?_⟩\n  sorry",
        "instructions": "Print only the tactic block of the proof (the lines after `:= by`), with no code fences. "
                        "Premise J is available as `cJ` after `intro_premises`. Use only the premises, Mathlib and the "
                        "article's definitions: the certificate rejects anything else.",
        "previous_errors": errors,
    }


def with_preamble(k, block):
    """A hook's block, with the stub's first two lines if it left them out."""
    if "intro_premises" in block:
        return block
    return f"intro_premises\nrefine ⟨by unfold meaningful{k}; definedness [], ?_⟩\n" + block


def ask(hook, data, timeout):
    try:
        p = subprocess.run(shlex.split(hook) if isinstance(hook, str) else hook, input=json.dumps(data, ensure_ascii=False),
                           capture_output=True, text=True, timeout=timeout, encoding="utf-8", errors="replace")
    except subprocess.TimeoutExpired:
        return None
    block = p.stdout.strip()
    block = re.sub(r"^```[a-z0-9]*\n|```$", "", block, flags=re.M).strip()
    block = re.sub(r"^theorem[^\n]*:= by\n", "", block)
    return "\n".join(l[2:] if l.startswith("  ") else l for l in block.splitlines()) if block else None


# --- writing the proofs back --------------------------------------------------------------

def write_back(lines, blocks, proofs):
    out = list(lines)
    for k in sorted(proofs, key=lambda k: blocks[k][0], reverse=True):
        a, b = blocks[k]
        body = ["  " + l for l in proofs[k].splitlines()]
        out[a + 1:b] = body
    return out


def key_of(claim, report):
    prem = [report["claims"][j]["lean"] for j in claim.get("premises", [])]
    return hashlib.sha256(json.dumps([claim["lean"], claim["meaningful"], prem]).encode()).hexdigest()


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("article")
    ap.add_argument("--proofs", help="the proofs file (default: Proofs.lean next to the article)")
    ap.add_argument("--hook", help="command that proves one obligation (JSON on stdin, tactic block on stdout)")
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--rounds", type=int, default=1, help="tries of the hook per obligation")
    ap.add_argument("--timeout", type=int, default=900, help="seconds for one Lean run")
    ap.add_argument("--hook-timeout", type=int, default=600)
    ap.add_argument("--no-build", action="store_true", help="do not run `lake build` of the article module first")
    ap.add_argument("--dry-run", action="store_true", help="report what would be proved, change nothing")
    a = ap.parse_args(argv)

    article = pathlib.Path(a.article).resolve()
    report_path = article.with_suffix(".leanify.json")
    if not report_path.exists():
        raise SystemExit(f"{report_path} not found: build the certificate once (lake build NS.Certified)")
    report = json.loads(report_path.read_text(encoding="utf-8"))
    source = article.read_text(encoding="utf-8").replace("\r\n", "\n")
    proofs_path = pathlib.Path(a.proofs).resolve() if a.proofs else article.parent / "Proofs.lean"
    lines = proofs_path.read_text(encoding="utf-8").splitlines()
    m = re.search(r"^import (\S+)", "\n".join(lines), re.M)
    if not m:
        raise SystemExit(f"{proofs_path}: no import of the article module")
    module, ns = m.group(1), report["namespace"]
    root = project_root(article.parent)
    workdir = root / ".lake" / "leanify-prove"
    workdir.mkdir(parents=True, exist_ok=True)
    cache_path = workdir / "cache.json"
    cache = json.loads(cache_path.read_text(encoding="utf-8")) if cache_path.exists() else {}

    blocks = stub_blocks(lines)
    todo = sorted(k for k, blk in blocks.items() if is_open(lines, blk) and k < len(report["claims"]))
    print(f"{len(todo)} open obligation{'s' if len(todo) != 1 else ''} in {proofs_path.name}")
    if not todo:
        return 0
    if not a.no_build:
        subprocess.run(["lake", "build", module], cwd=root, check=False)

    proved, errors = {}, {}
    for phase in (0, 1):
        items = []
        for k in todo:
            if k in proved:
                continue
            c = report["claims"][k]
            for label, script in candidates(k, c, report, cache.get(key_of(c, report)), phase):
                items.append((k, label, script))
        if not items:
            break
        found, errs = check(root, module, ns, items, str(phase), a.timeout, workdir)
        for k, (label, script) in found.items():
            print(f"  claim {k}: {label}")
            proved[k] = script
        for k, e in errs.items():
            errors.setdefault(k, e)

    rest = [k for k in todo if k not in proved]
    if a.hook and rest:
        last = {k: [f"{lab}: {msgs[0]}" for lab, msgs in [errors.get(k, ("", [""]))]] for k in rest}
        for r in range(a.rounds):
            if not rest:
                break
            with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as pool:
                answers = dict(zip(rest, pool.map(lambda k: ask(a.hook, payload(k, report, source, last[k]), a.hook_timeout), rest)))
            items = [(k, "hook", with_preamble(k, s)) for k, s in answers.items() if s]
            if not items:
                break
            ok, errs = check(root, module, ns, items, f"H{r + 1}", a.timeout, workdir)
            for k, (_, s) in ok.items():
                print(f"  claim {k}: proved by the hook")
                proved[k] = s
            last = {k: errs.get(k, ("hook", ["no answer"]))[1][:3] for k in rest if k not in ok}
            rest = [k for k in rest if k not in ok]

    for k, s in proved.items():
        cache[key_of(report["claims"][k], report)] = s
    open_left = [k for k in todo if k not in proved]
    print(f"proved {len(proved)} of {len(todo)}; open: " + (", ".join(f"claim {k}" for k in open_left) or "none"))
    if a.dry_run:
        return 0
    cache_path.write_text(json.dumps(cache, indent=1, ensure_ascii=False), encoding="utf-8")
    if proved:
        proofs_path.write_text("\n".join(write_back(lines, blocks, proved)) + "\n", encoding="utf-8")
        print(f"wrote {proofs_path}; now `lake build` the certificate")
    return 0 if not open_left else 1


if __name__ == "__main__":
    sys.exit(main())
