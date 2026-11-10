#!/usr/bin/env python3
"""A stand-in for a model, to test `scripts/leanify_suggest.py` on `examples/Demo/draft.tex`.

It answers the corollary of the draft twice: first with a sentence that Leanify does not
read either, which must not be kept, and then, given the reason, with one it reads."""
import json
import sys

data = json.load(sys.stdin)
assert data["guide"] and data["instructions"]
if "attains its minimum" in data["sentence"]:
    if not data["previous"]:
        print(r"The function $f$ has its least value at $1$.")
    else:
        assert "does not read" in data["previous"][0]["rejected"], data["previous"]
        print(r"For every $x\in(0,\infty)$, $f(1)\le f(x)$.")
