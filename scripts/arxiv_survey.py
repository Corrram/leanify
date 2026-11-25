#!/usr/bin/env python3
"""Leanify on articles it was not written for: a sample of arXiv, read and tallied.

    python scripts/arxiv_survey.py fetch  DIR [--n 30] [--categories math.CO,math.PR] [--seed 1]
    python scripts/arxiv_survey.py check  DIR [--leanify EXE] [--vocab FIELDS] [--jobs 4]
    python scripts/arxiv_survey.py report DIR [--out REPORT.md]

`fetch` asks the arXiv API for articles of mathematics at random places of its listing,
downloads the source of each (`DIR/ID/`) and names its main file (`DIR/ID/MAIN`). It needs
the network and nothing else (no package); it waits three seconds between requests, as
arXiv asks. `check` runs `leanify check MAIN --json` on each article (`DIR/ID.json`), and
`report` tallies what Leanify said: how much of the results of each article it reads, the
findings by kind with examples, the nouns and words it did not know. The report is where
the work starts: a finding is a fault of the article, a wording the grammar lacks, or a
word a field of the vocabulary should have.

The sources are the authors'; they are read here, not redistributed (`DIR` is not for a
repository).
"""
import argparse
import collections
import concurrent.futures
import gzip
import io
import json
import pathlib
import random
import re
import subprocess
import sys
import tarfile
import time
import urllib.request
import xml.etree.ElementTree as ET

CATEGORIES = ["math.AC", "math.AG", "math.AP", "math.AT", "math.CA", "math.CO", "math.CT", "math.CV",
              "math.DG", "math.DS", "math.FA", "math.GM", "math.GN", "math.GR", "math.GT", "math.HO",
              "math.LO", "math.MG", "math.NA", "math.NT", "math.OA", "math.OC", "math.PR", "math.QA",
              "math.RA", "math.RT", "math.SG", "math.SP", "math.ST"]
AGENT = "leanify-survey/0.1 (https://github.com/Corrram/leanify)"


def get(url, tries=3):
    for k in range(tries):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": AGENT})
            with urllib.request.urlopen(req, timeout=60) as r:
                return r.read()
        except Exception as e:  # noqa: BLE001
            if k == tries - 1:
                raise
            print(f"  ({e}; again in 10 s)", flush=True)
            time.sleep(10)
    return b""


def main_file(folder):
    """The file with `\\documentclass` and `\\begin{document}` (the largest, if several)."""
    best = None
    for f in folder.rglob("*.tex"):
        try:
            t = f.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        if "\\documentclass" in t and "\\begin{document}" in t:
            if best is None or len(t) > best[0]:
                best = (len(t), f)
    return best[1] if best else None


def unpack(data, folder):
    """An e-print is a gzipped tar of the source, or one gzipped TeX file (or a PDF: skipped)."""
    folder.mkdir(parents=True, exist_ok=True)
    if data[:4] == b"%PDF":
        return False
    try:
        raw = gzip.decompress(data)
    except OSError:
        raw = data
    try:
        with tarfile.open(fileobj=io.BytesIO(raw)) as tar:
            for m in tar.getmembers():
                name = pathlib.PurePosixPath(m.name)
                if not m.isfile() or name.is_absolute() or ".." in name.parts:
                    continue
                if name.suffix.lower() not in (".tex", ".bbl", ".sty", ".cls", ".bib"):
                    continue
                out = folder.joinpath(*name.parts)
                out.parent.mkdir(parents=True, exist_ok=True)
                out.write_bytes(tar.extractfile(m).read())
        return True
    except tarfile.TarError:
        if b"\\documentclass" in raw:
            (folder / "main.tex").write_bytes(raw)
            return True
        return False


def fetch(a):
    rng = random.Random(a.seed)
    root = pathlib.Path(a.dir)
    root.mkdir(parents=True, exist_ok=True)
    index_path = root / "index.json"
    index = json.loads(index_path.read_text(encoding="utf-8")) if index_path.exists() else {}
    cats = a.categories.split(",") if a.categories else CATEGORIES
    ns = {"a": "http://www.w3.org/2005/Atom"}
    while len(index) < a.n:
        cat = rng.choice(cats)
        start = rng.randrange(0, 3000)
        url = ("https://export.arxiv.org/api/query?search_query=cat:" + cat +
               f"&sortBy=submittedDate&sortOrder=descending&start={start}&max_results=3")
        print(f"{cat} at {start}", flush=True)
        try:
            feed = ET.fromstring(get(url))
        except Exception as e:  # noqa: BLE001
            print(f"  the listing failed: {e}")
            time.sleep(3)
            continue
        time.sleep(3)
        for entry in feed.findall("a:entry", ns):
            ident = entry.find("a:id", ns).text.rsplit("/abs/", 1)[-1]
            key = re.sub(r"v\d+$", "", ident).replace("/", "_")
            primary = entry.find("{http://arxiv.org/schemas/atom}primary_category")
            if key in index or len(index) >= a.n:
                continue
            try:
                data = get("https://export.arxiv.org/e-print/" + ident)
            except Exception as e:  # noqa: BLE001
                print(f"  {ident}: no source ({e})")
                time.sleep(3)
                continue
            time.sleep(3)
            folder = root / key
            if not unpack(data, folder):
                print(f"  {ident}: not a TeX source")
                continue
            main = main_file(folder)
            if main is None:
                print(f"  {ident}: no main file")
                continue
            index[key] = {"id": ident, "title": " ".join(entry.find("a:title", ns).text.split()),
                          "category": primary.get("term") if primary is not None else cat,
                          "main": str(main.relative_to(root)).replace("\\", "/")}
            index_path.write_text(json.dumps(index, indent=1), encoding="utf-8")
            print(f"  {ident}: {index[key]['main']}  ({len(index)} of {a.n})", flush=True)
    print(f"{len(index)} articles in {root}")


def check_one(root, key, entry, exe, vocab):
    out = root / (key + ".json")
    cmd = exe + ["check", str(root / entry["main"]), "--json"] + (["--vocab", vocab] if vocab else [])
    t = time.time()
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=600)
        text = r.stdout
        json.loads(text)
    except subprocess.TimeoutExpired:
        text = json.dumps({"crash": "no answer within 600 s"})
    except Exception as e:  # noqa: BLE001
        text = json.dumps({"crash": (r.stderr or r.stdout or str(e))[-600:] if "r" in dir() else str(e)})
    out.write_text(text, encoding="utf-8")
    return key, time.time() - t


def check(a):
    root = pathlib.Path(a.dir)
    index = json.loads((root / "index.json").read_text(encoding="utf-8"))
    exe = a.leanify.split() if a.leanify else ["leanify"]
    with concurrent.futures.ThreadPoolExecutor(a.jobs) as pool:
        for key, secs in pool.map(lambda kv: check_one(root, kv[0], kv[1], exe, a.vocab), index.items()):
            print(f"{key}: {secs:.1f} s", flush=True)


def kind(message):
    """The kind of a finding: its message without what is particular to the sentence."""
    m = re.sub(r'"[^"]*"', '"…"', message)
    m = re.sub(r"`[^`]*`", "`…`", m)
    m = re.sub(r"\$[^$]*\$", "$…$", m)
    m = re.sub(r"\\[A-Za-z]+", "\\\\…", m)
    m = re.sub(r"\b\d+\b", "N", m)
    m = re.split(r": sentence not checked|; the same at", m)[0]
    m = re.sub(r"^(unknown noun|unknown word|unknown adjective): \S+.*", r"\1", m)
    m = re.sub(r"^(\S+) is not defined$", "a symbol is not defined", m)
    return m[:150]


def report(a):
    root = pathlib.Path(a.dir)
    index = json.loads((root / "index.json").read_text(encoding="utf-8"))
    rows, kinds, examples, nouns, crashes = [], collections.Counter(), {}, collections.Counter(), []
    unread = []
    for key, entry in index.items():
        p = root / (key + ".json")
        if not p.exists():
            continue
        d = json.loads(p.read_text(encoding="utf-8"))
        if "crash" in d:
            crashes.append((key, d["crash"]))
            continue
        cov = d.get("coverage", {})
        res = cov.get("results", {})
        total = sum(res.get(k, 0) for k in ("compiled", "failed", "prose"))
        rows.append((key, entry["category"], res.get("compiled", 0), total, len(d.get("findings", [])), entry["title"][:60]))
        text_at = {(s["file"], s["line"]): s["text"] for s in d.get("sentences", [])}
        for f in d.get("findings", []):
            k = kind(f["message"])
            kinds[k] += 1
            examples.setdefault(k, [])
            if len(examples[k]) < 4:
                examples[k].append((key, f["line"], f["message"][:230], text_at.get((f["file"], f["line"]), "")[:230]))
        for n in d.get("notDefined", []):
            nouns[n] += 1
        for n in d.get("nounCandidates", []):
            nouns[n if isinstance(n, str) else json.dumps(n)] += 1
        for s in d.get("sentences", []):
            if s.get("environment") not in ("text", "proof") and s.get("outcome") == "prose" and "$" in s.get("text", ""):
                unread.append((key, s["line"], s["text"][:230]))
    lines = ["# Leanify on a sample of arXiv", "",
             f"{len(rows)} articles read" + (f", {len(crashes)} without an answer" if crashes else "") + ".", "",
             "## Articles", "", "| article | category | results read | findings | title |", "| --- | --- | --- | --- | --- |"]
    done = sum(r[2] for r in rows)
    tot = sum(r[3] for r in rows)
    for key, cat, c, t, nf, title in sorted(rows, key=lambda r: -(r[2] / r[3] if r[3] else 0)):
        lines.append(f"| {key} | {cat} | {c} of {t} | {nf} | {title} |")
    lines += ["", f"In all, {done} of {tot} sentences of results are read as mathematics.", "",
              "## Findings by kind", ""]
    for k, n in kinds.most_common():
        lines += [f"### {n} × {k}", ""]
        for key, line, msg, text in examples[k]:
            lines += [f"* `{key}`:{line}: {msg}", f"  > {text}" if text else ""]
        lines.append("")
    lines += ["## Sentences of results with a formula that are taken as prose", ""]
    random.Random(1).shuffle(unread)
    lines += [f"* `{key}`:{line}: {text}" for key, line, text in unread[:60]]
    lines += ["", f"({len(unread)} in all.)", "", "## Nouns the articles use and the vocabulary does not have", ""]
    lines += [f"* {n} ({c})" for n, c in nouns.most_common(80)]
    if crashes:
        lines += ["", "## No answer", ""] + [f"* `{key}`: {msg[-300:]}" for key, msg in crashes]
    out = pathlib.Path(a.out) if a.out else root / "report.md"
    out.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"wrote {out}: {len(rows)} articles, {done} of {tot} sentences of results read, {sum(kinds.values())} findings of {len(kinds)} kinds")


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    f = sub.add_parser("fetch")
    f.add_argument("dir")
    f.add_argument("--n", type=int, default=30)
    f.add_argument("--categories")
    f.add_argument("--seed", type=int, default=1)
    c = sub.add_parser("check")
    c.add_argument("dir")
    c.add_argument("--leanify")
    c.add_argument("--vocab")
    c.add_argument("--jobs", type=int, default=4)
    r = sub.add_parser("report")
    r.add_argument("dir")
    r.add_argument("--out")
    a = ap.parse_args(argv)
    {"fetch": fetch, "check": check, "report": report}[a.cmd](a)


if __name__ == "__main__":
    sys.exit(main())
