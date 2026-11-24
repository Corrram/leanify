#!/usr/bin/env python3
"""A ready hook for `leanify_prove.py` and `leanify_suggest.py`: it asks a model.

    python scripts/leanify_prove.py ARTICLE.tex --hook "python scripts/leanify_hook.py --model 'claude -p'"

The scripts give a hook one task as JSON on its standard input (an obligation to prove,
hypotheses to satisfy, a sentence to rephrase) and read its answer from its standard
output. This hook writes the task as a prompt and gives it to a command of yours that
reads a prompt on its standard input and prints the answer of a model: `claude -p`,
`llm -m MODEL`, `ollama run MODEL`, or a script around the API you use. The command is
`--model CMD`, or the environment variable `LEANIFY_MODEL`.

Nothing a model answers is trusted: Lean checks every proof before it is written, and
the check reads every suggested sentence like any other.
"""
import argparse
import json
import os
import shlex
import subprocess
import sys

ROLE = {
    "witness": "The task: values for the variables of a statement, so that its hypotheses hold together.",
    "prove": "The task: a Lean 4 proof (Mathlib) of one step of a mathematical article. The statement was "
             "computed from the sentence of the article and cannot be changed.",
    "suggest": "The task: rephrase one sentence of a mathematical article so that the Leanify grammar reads it, "
               "without changing what it says.",
}
# the fields of a task, in the order a reader wants them, with a heading each
FIELDS = [
    ("sentence", "The sentence of the article"), ("finding", "What the check says about it"),
    ("environment", "The sentences around it"), ("before", "The sentences before it"), ("after", "The sentences after it"),
    ("reading", "Its formal reading"), ("lean", "The Lean statement"), ("meaningful", "Its definedness condition"),
    ("premises", "The premises (earlier steps and cited results, available by these names)"),
    ("definitions", "The definitions of the article (Lean names)"), ("stub", "The theorem to complete"),
    ("previous_errors", "Lean's errors on the last attempt"), ("previous", "Earlier answers that were rejected"),
    ("guide", "The guide to the forms that Leanify reads"),
]


def prompt(task):
    kind = task.get("kind") or ("suggest" if "guide" in task else "prove")
    parts = [ROLE.get(kind, ROLE["prove"]), task.get("instructions", "")]
    for key, title in FIELDS:
        v = task.get(key)
        if v in (None, "", [], {}):
            continue
        text = v if isinstance(v, str) else json.dumps(v, ensure_ascii=False, indent=1)
        parts.append(f"## {title}\n{text}")
    parts.append("Answer with the requested text only: no explanation, no code fences.")
    return "\n\n".join(p for p in parts if p)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--model", default=os.environ.get("LEANIFY_MODEL"),
                    help="command that reads a prompt on stdin and prints a model's answer (default: $LEANIFY_MODEL)")
    ap.add_argument("--timeout", type=int, default=540)
    ap.add_argument("--show", action="store_true", help="print the prompt instead of asking")
    a = ap.parse_args(argv)
    task = json.load(sys.stdin)
    text = prompt(task)
    if a.show:
        print(text)
        return 0
    if not a.model:
        print("leanify_hook: no model: give --model CMD or set LEANIFY_MODEL (a command that reads a prompt on "
              "its standard input and prints the answer, such as `claude -p`)", file=sys.stderr)
        return 2
    try:
        p = subprocess.run(shlex.split(a.model, posix=os.name != "nt"), input=text, capture_output=True, text=True,
                           timeout=a.timeout, encoding="utf-8", errors="replace")
    except (OSError, subprocess.TimeoutExpired) as e:
        print(f"leanify_hook: {a.model}: {e}", file=sys.stderr)
        return 1
    if p.returncode != 0:
        print(f"leanify_hook: {a.model} failed: {p.stderr.strip()[:500]}", file=sys.stderr)
        return 1
    sys.stdout.write(p.stdout)
    return 0


if __name__ == "__main__":
    sys.exit(main())
