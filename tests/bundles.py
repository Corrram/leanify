#!/usr/bin/env python3
"""A bundle reads an article as its fields do.

    python tests/bundles.py LEANIFY_CHECK...   (the command of `leanify check`)

Every test article with expected output (`check.txt`, for the fields of `check.args`) is
read with each bundle that has these fields, and the output is compared: the same
definitions, the same claims with the same readings, no phrase with several meanings.

One difference is by design. With the field `unitsquare` (in the bundles `dependence` and
`statistics`), `[0,1]` is a type of its own, so an article that did not name that field has
its variables in `[0,1]` and its integrals `\\int_0^1` read on that type: the same
mathematics, another Lean statement. For such a pair the findings and the counts are
compared, not the readings."""
import pathlib, re, subprocess, sys
exe = sys.argv[1:]
src = pathlib.Path('Leanify/Library/Fields.lean').read_text()
block = src[src.index('def bundles'):src.index('def bundleNames')]
bundles = {m.group(1): re.findall(r'"([a-z]+)"', m.group(2)) for m in re.finditer(r'\("([a-z]+)", \[([^\]]*)\]\)', block)}
inc = {"hilbert": ["unitsquare"], "markov": ["unitsquare", "hilbert"]}
def expand(fs):
    out = []
    for f in fs:
        for g in (expand(bundles[f]) if f in bundles else [f]):
            if g not in out: out.append(g)
    return out
def closure(fs):
    return set(fs) | {g for f in fs for g in inc.get(f, [])}
bad = n = 0
for args in sorted(list(pathlib.Path('tests').glob('*/*check.args')) + list(pathlib.Path('examples').glob('*/*check.args'))):
    a = args.read_text().split()
    if '--vocab' not in a: continue
    i = a.index('--vocab'); fields = a[i + 1].split(',')
    exp = args.with_name(args.name.replace('check.args', 'check.txt'))
    art = exp.with_name('article.tex') if exp.name == 'check.txt' else pathlib.Path(str(exp)[:-len('.check.txt')] + '.tex')
    want = exp.read_text().replace('\r\n', '\n')
    for b in bundles:
        if not set(fields) <= closure(expand([b])): continue
        got = subprocess.run([*exe, 'check', str(art), *a[:i], '--vocab', b, *a[i + 2:]], capture_output=True, text=True, encoding='utf-8').stdout.replace('\r\n', '\n')
        n += 1
        if 'unitsquare' in closure(expand([b])) and 'unitsquare' not in closure(fields):
            brief = lambda t: [l for l in t.splitlines() if ': info: ' not in l]
            if brief(got) == brief(want):
                print(f"ok   {art} with {b} (with [0,1] as a type)")
                continue
        if got != want:
            bad += 1
            w, g = want.splitlines(), got.splitlines()
            d = [(x, y) for x, y in zip(w, g) if x != y]
            print(f"DIFF {art} with {b}: {len(d)} lines differ" + (f"\n  - {d[0][0][:230]}\n  + {d[0][1][:230]}" if d else f" ({len(w)} vs {len(g)} lines)"))
        else: print(f"ok   {art} with {b}")
print(f"{n - bad} of {n} readings unchanged")
sys.exit(1 if bad else 0)
