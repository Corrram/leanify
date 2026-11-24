#!/usr/bin/env python3
"""From an article to its certificate in one command, as far as it goes without you.

    python scripts/leanify_auto.py ARTICLE.tex [--model CMD | --hook CMD] [--vocab FIELDS]

It runs, in this order,

1. `leanify certify ARTICLE.tex`: the Lean project of the article (made the first time)
   and the statements of the present text;
2. `leanify_prove.py`: the routine steps by tactics, the claims that fail at simple
   values, and, with `--model CMD` or `--hook CMD`, a model for the others;
3. `leanify certify` again: Lean's kernel checks every proof that was written, and the
   certificate says which claims are derived from exactly what the text cites;
4. `leanify_status.py`: where the article stands and what is left for you.

`--model CMD` is a command that reads a prompt on its standard input and prints the
answer of a model (`claude -p`, `llm -m MODEL`, `ollama run MODEL`); `--hook CMD` is a
hook of your own (see `leanify_prove.py`). Without either, only tactics are tried.
It needs Lean (elan) and the checker `leanify`; a second run continues where the first
stopped, and proves again only what changed in the article.

The exit status is that of the last step: 0 if nothing is left to do.
"""
import argparse
import json
import pathlib
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import leanify_prove  # noqa: E402
import leanify_status  # noqa: E402


def step(n, text):
    print(f"\n== {n}. {text}", flush=True)


def proofs_file(article, report):
    """`NS/Proofs.lean` of the project of the article (next to it, or in its folder `lean`)."""
    ns = report["namespace"]
    found = [f for f in article.parent.rglob("Proofs.lean") if ".lake" not in f.parts and f.parent.name == ns]
    if not found:
        found = [f for f in article.parent.rglob("Proofs.lean") if ".lake" not in f.parts]
    if not found:
        raise SystemExit(f"no Proofs.lean for {article.name} below {article.parent}")
    return min(found, key=lambda f: len(f.parts))


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("article", type=pathlib.Path)
    ap.add_argument("--model", help="command that reads a prompt on stdin and prints a model's answer")
    ap.add_argument("--hook", help="a hook of your own for leanify_prove.py (instead of --model)")
    ap.add_argument("--vocab", help="the fields of the article, as for `leanify certify`")
    ap.add_argument("--name", help="the Lean namespace of a new project, as for `leanify certify`")
    ap.add_argument("--leanify", help="the checker (default: the one of the project, or `leanify` on the PATH)")
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--rounds", type=int, default=2, help="tries of the model per claim")
    ap.add_argument("--timeout", type=int, default=1800, help="seconds for one Lean run")
    a = ap.parse_args(argv)
    article = a.article.resolve()
    exe = [a.leanify] if a.leanify else leanify_status.find_exe(article, None)
    if not exe:
        raise SystemExit("no `leanify` found: give --leanify EXE, or put the checker on the PATH "
                         "(https://github.com/Corrram/leanify/releases)")
    certify = exe + ["certify", str(article)] + (["--vocab", a.vocab] if a.vocab else []) + (["--name", a.name] if a.name else [])

    step(1, "The statements of the article (leanify certify)")
    subprocess.run(certify, check=False)
    report_path = article.with_suffix(".leanify.json")
    if not report_path.exists():
        raise SystemExit(f"{report_path.name} was not written: see the messages of `leanify certify` above")
    report = json.loads(report_path.read_text(encoding="utf-8"))
    proofs = proofs_file(article, report)

    step(2, "Proofs: tactics, counterexamples" + (", a model" if a.model or a.hook else ""))
    hook = a.hook
    if a.model and not hook:
        hook = f'"{pathlib.Path(sys.executable).as_posix()}" "{(HERE / "leanify_hook.py").as_posix()}" --model "{a.model}"'
    args = [str(article), "--proofs", str(proofs), "--no-build", "--jobs", str(a.jobs), "--rounds", str(a.rounds),
            "--timeout", str(a.timeout)] + (["--hook", hook] if hook else [])
    leanify_prove.main(args)

    step(3, "The certificate (Lean's kernel checks every proof)")
    subprocess.run(certify, check=False)

    step(4, "Where the article stands")
    print()
    return leanify_status.main([str(article)] + (["--leanify", a.leanify] if a.leanify else []))


if __name__ == "__main__":
    sys.exit(main())
