#!/usr/bin/env python3
"""Report Leanify's verdict on each sentence of a compiled article.

`#leanify_certify` writes `<article>.leanify.json` next to the article. This script
prints one line per finding in the format editors understand:

    article.tex:694:1: warning: \\Delta is not defined: sentence not checked
    article.tex:458:1: warning: statement (claim 12) compiled but not verified: add J.proof12

Use it in CI or as a VS Code task (see `editors/vscode/tasks.json`). Exit status
is 1 if the article changed after the report was written, with --verified if a
compiled claim is not verified, and with --strict on any warning (also sentences
that did not compile). `--pin Compiled.lean` updates
the article's pin in that Lean file, so that Lake recompiles the article.
"""
import argparse
import json
import pathlib
import re
import sys

ROLE = {"statement": "statement", "proof step": "proof step", "text": "claim", "definition": "definition"}


def source_pin(text):
    """FNV-1a (64 bit) of the UTF-8 bytes with CRLF normalized, as `Leanify.sourcePin`."""
    h = 0xcbf29ce484222325
    for b in text.replace("\r\n", "\n").encode("utf-8"):
        h = ((h ^ b) * 0x100000001b3) & 0xFFFFFFFFFFFFFFFF
    return f"fnv1a64:{h:016x}"


def update_pin(lean_file, pin):
    text = lean_file.read_text(encoding="utf-8")
    new, n = re.subn(r'(#leanify_article\s+\S+\s+"[^"]+"\s+)"fnv1a64:[0-9a-f]{16}"', lambda m: m.group(1) + f'"{pin}"', text)
    if n != 1:
        raise SystemExit(f"{lean_file}: expected one #leanify_article command with a pin")
    if new != text:
        lean_file.write_text(new, encoding="utf-8")
    return new != text


GREEK = set("""alpha beta gamma delta epsilon varepsilon zeta eta theta vartheta iota kappa lambda
mu nu xi pi varpi rho varrho sigma varsigma tau upsilon phi varphi chi psi omega Gamma Delta Theta
Lambda Xi Pi Sigma Upsilon Phi Psi Omega ell""".split())


def failed_message(message):
    """What stopped a sentence, as `leanify check` says it."""
    m = re.match(r"undefined symbol: (.+)\Z", message)
    if not m:
        return message
    sym = m.group(1)
    name = re.match(r"\\([A-Za-z]+)", sym)
    return f"unknown notation {sym}" if name and name.group(1) not in GREEK else f"{sym} is not defined"


def findings(report, prose=False, standard=False, satisfiable=False):
    sentences = report["sentences"]
    stated = lambda s: s["environment"] not in ("text", "proof", "remark", "example", "conjecture")
    for s in sentences:
        where = (s["line"], s["column"])
        if s["outcome"] == "failed":
            yield (*where, "warning", f"{failed_message(s['message'])}: sentence not checked")
        elif s["outcome"] == "prose" and stated(s):
            env = [t for t in sentences if t["env"] == s["env"]]
            unread = [t for t in env if t["outcome"] == "prose"]
            if unread[0] is not s:
                continue
            name = s["environment"].capitalize() + (f" {s['label']}" if s["label"] else f" at line {env[0]['line']}")
            if all(t["outcome"] != "compiled" for t in env):
                what = ("is not checked: Leanify cannot read its statement" if len(env) == 1
                        else f"is not checked: Leanify cannot read any of its {len(env)} sentences")
            else:
                lines = sorted({t["line"] for t in unread})
                what = (f"is only partly checked: Leanify cannot read {len(unread)} of its {len(env)} sentences "
                        f"(line{'s' if len(lines) > 1 else ''} {', '.join(map(str, lines))})")
            yield (*where, "warning", f"{name} {what}")
        elif s["outcome"] == "prose" and prose and s["environment"] == "proof":
            yield (*where, "info", "proof sentence not read")
    for c in report["claims"]:
        s = sentences[c["sentence"]]
        where = (s["line"], s["column"])
        if c["status"] == "refuted":
            yield (*where, "error", f"{ROLE.get(c['role'], 'claim')} (claim {c['index']}) is false as stated: "
                   f"refuted by {c['justification']}")
        elif c["status"] == "unverified":
            certified = report["justifications"] not in ("", "[anonymous]")
            why = c.get("note") or (f"add {report['justifications']}.proof{c['index']}" if certified
                                    else "the article is not certified yet (build the module with #leanify_certify)")
            yield (*where, "warning", f"{ROLE.get(c['role'], 'claim')} (claim {c['index']}) compiled but not verified: {why}")
        elif c["status"] == "text" and prose:
            yield (*where, "info", f"claim {c['index']} derived from its citations")
        # a step that the standard tactic does not close is larger than it looks in the text
        if standard and c["status"] == "text" and c.get("step") == "argument":
            yield (*where, "warning", f"{ROLE.get(c['role'], 'claim')} (claim {c['index']}) is derived in the text, "
                   f"but the standard tactic does not close it: its proof {c['justification']} is a longer Lean argument")
        # a claim whose hypotheses cannot all hold is true for an empty reason (once for each
        # set of hypotheses: at the claim that stands for it)
        if satisfiable and c.get("hypotheses") == "open" and c.get("hypothesesOf", c["index"]) == c["index"]:
            yield (*where, "warning", f"{ROLE.get(c['role'], 'claim')} (claim {c['index']}): its hypotheses are not "
                   f"shown to hold together (prove {report.get('justifications', 'J')}.satisfied{c['index']})")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("report", type=pathlib.Path, help="the article's .leanify.json")
    ap.add_argument("--prose", action="store_true", help="also list proof sentences the grammar does not read")
    ap.add_argument("--verified", action="store_true",
                    help="fail if a compiled claim is not verified")
    ap.add_argument("--standard", action="store_true",
                    help="warn of the claims derived in the text that the standard tactic does not close")
    ap.add_argument("--satisfiable", action="store_true",
                    help="warn of the claims whose hypotheses are not shown to hold together")
    ap.add_argument("--strict", action="store_true",
                    help="fail on any warning: unverified claims and sentences that did not compile")
    ap.add_argument("--relative-to", type=pathlib.Path, default=pathlib.Path.cwd(),
                    help="print paths relative to this directory (default: the working directory)")
    ap.add_argument("--pin", type=pathlib.Path, metavar="LEAN_FILE",
                    help="update the article pin in this Lean file (the one with #leanify_article) and exit")
    args = ap.parse_args()
    report = json.loads(args.report.read_text(encoding="utf-8"))
    tex = (args.report.parent / report["article"]).resolve()
    pin = source_pin(tex.read_bytes().decode("utf-8"))
    if args.pin:
        changed = update_pin(args.pin, pin)
        print(f"{args.pin}: pin {pin} ({'updated' if changed else 'unchanged'})")
        return 0
    try:
        shown = tex.relative_to(args.relative_to.resolve())
    except ValueError:
        shown = tex
    errors = warnings = 0
    if report.get("sourceHash") != pin:
        print(f"{shown.as_posix()}:1:1: error: the article changed after it was certified "
              f"(report {report.get('sourceHash')}, file {pin}); run with --pin on the Lean file "
              f"with #leanify_article, then rebuild")
        return 1
    for line, col, severity, message in sorted(findings(report, args.prose, args.standard, args.satisfiable)):
        print(f"{shown.as_posix()}:{line}:{col}: {severity}: {message}")
        errors += severity == "error"
        warnings += severity == "warning"
    claims = report["claims"]
    count = lambda st: sum(c["status"] == st for c in claims)
    print(f"{shown.as_posix()}: {len(report['sentences'])} sentences, {len(claims)} claims "
          f"({count('text')} derived from citations, {count('companion')} by companion proofs, "
          f"{count('refuted')} refuted, {count('unverified')} unverified), {len(report['definitions'])} definitions; "
          f"{errors} errors, {warnings} warnings", file=sys.stderr)
    unverified = count('unverified')
    return 1 if errors or (args.strict and warnings) or (args.verified and unverified) else 0


if __name__ == "__main__":
    sys.exit(main())
