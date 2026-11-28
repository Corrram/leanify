#!/usr/bin/env python3
"""How much of a corpus of articles Leanify reads.

    python scripts/corpus.py [--fetch] [--leanify "lake exe leanify"] [--json OUT]

The corpus is `corpus/articles.txt`: one article per line, `ARXIV-ID  MAIN.tex  NAME`
(`#` starts a comment). Its sources are not part of the repository: `--fetch` downloads
the e-print of each article that is not there yet into `corpus/ARXIV-ID/`.

For each article the table has the sentences and how many are read, and the number that
measures progress (`docs/mathlib-coverage.md`): the *results* (theorems, lemmas, …, with the
definitions) whose statement is read completely, that is, every sentence of the
environment is compiled. A result that is read with a notion that the article defines in
a sentence that is not read still counts here; the last column counts those notions, so a
row is done when it says `0`.
"""
import argparse, io, json, pathlib, shlex, subprocess, sys, tarfile, gzip, urllib.request

ROOT = pathlib.Path(__file__).resolve().parent.parent
CORPUS = ROOT / 'corpus'

def articles():
    out = []
    for line in (CORPUS / 'articles.txt').read_text(encoding='utf-8').splitlines():
        line = line.split('#')[0].strip()
        if not line: continue
        ident, main, name = line.split(None, 2)
        out.append((ident, main, name))
    return out

def fetch(ident):
    d = CORPUS / ident
    if d.exists() and any(d.iterdir()): return
    d.mkdir(parents=True, exist_ok=True)
    data = urllib.request.urlopen(f'https://arxiv.org/e-print/{ident}', timeout=120).read()
    try:
        with tarfile.open(fileobj=io.BytesIO(data), mode='r:*') as t:
            # (members of the archive only below the article's directory)
            safe = [m for m in t.getmembers() if not m.name.startswith(('/', '..')) and '..' not in pathlib.PurePosixPath(m.name).parts]
            t.extractall(d, members=safe)
    except tarfile.ReadError:
        (d / 'main.tex').write_bytes(gzip.decompress(data))

def read(exe, tex):
    r = subprocess.run([*exe, 'check', str(tex), '--json'], capture_output=True, text=True, encoding='utf-8')
    return json.loads(r.stdout)

def row(name, d):
    ss = d['sentences']
    compiled = sum(1 for s in ss if s['outcome'] == 'compiled')
    results = {}
    for s in ss:
        if s['environment'] in ('text', 'proof'): continue
        results.setdefault(s['env'], []).append(s['outcome'] == 'compiled')
    whole = sum(1 for v in results.values() if all(v))
    undefined = len(d.get('takenAsGiven', [])) + len(d.get('notDefined', []))
    return [name, len(ss), compiled, len(results), whole, undefined]

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--fetch', action='store_true')
    ap.add_argument('--leanify', default='lake exe leanify')
    ap.add_argument('--json')
    a = ap.parse_args()
    exe = shlex.split(a.leanify)
    rows = []
    for ident, main_, name in articles():
        if a.fetch: fetch(ident)
        tex = CORPUS / ident / main_
        if not tex.exists():
            print(f'{name}: {tex} is not there (python scripts/corpus.py --fetch)', file=sys.stderr)
            continue
        rows.append(row(name, read(exe, tex)))
    head = ['Article', 'Sentences', 'Read', 'Results', 'Results read completely', 'Notions used and not defined']
    print('| ' + ' | '.join(head) + ' |')
    print('| --- | ' + ' | '.join(['---:'] * (len(head) - 1)) + ' |')
    for r in rows: print('| ' + ' | '.join(str(x) for x in r) + ' |')
    if rows:
        tot = ['all'] + [sum(r[i] for r in rows) for i in range(1, len(head))]
        print('| ' + ' | '.join(f'**{x}**' for x in tot) + ' |')
    if a.json: pathlib.Path(a.json).write_text(json.dumps([dict(zip(head, r)) for r in rows], indent=1), encoding='utf-8')

if __name__ == '__main__':
    main()
