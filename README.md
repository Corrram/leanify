# Leanify

**[Documentation, tutorial and live demo](https://corrram.github.io/leanify/)**

One LaTeX source, read twice: typeset as the paper you submit, and compiled by
Lean into kernel-checked statements and proofs.

Leanify compiles an ordinary mathematical article, written in good
mathematical English, to Lean. Every symbol must be defined in the article
before it is used, every sentence has one fixed reading, and a proof step may
use only the results it cites. The kernel checks the compilation of the file,
the readable Lean form of every definition and claim, every justification and
the final certificate. There is no second, hand-written formal version that
could drift away from the paper.

```latex
Define $f:(0,\infty)\to\mathbb{R}$ by $f(x)\coloneqq x+\frac1x$.
```

becomes the Lean definition `f := fun x => x + 1 / x`, with the obligation that
it is well defined, `∀ (x : ℝ), 0 < x → ¬x = 0`, and the theorem

```latex
\begin{theorem}\label{thm:bound}
For every $x\in(0,\infty)$, $f(x)\ge2$.
\end{theorem}
```

becomes `claim2 : ∀ (x : ℝ), 0 < x → 2 ≤ f x`, derived in Lean from exactly the
sentences of its proof and the lemma they cite.

## Exemplars

Two articles are compiled in
[lean-verifications](https://github.com/Corrram/lean-verifications):

* *Rank weighting and asymmetry in Blest's rank correlation: two exact regions*
  (arXiv:2609.27634), `Papers/Rockel2026ExactBlest/Source`: 37 definitions and
  48 claims, all certified. The proof of Corollary 3.2 is checked sentence by
  sentence against what it cites; the other results are proved through bridges to
  the companion development.
* *The exact region determined by Spearman's rho and Gini's gamma*
  (arXiv:2609.19890), `Papers/AnsariRockelSteinmassl2026RhoGamma/Source`: 11
  definitions and 8 claims, all certified.

Each folder's `article-edits.diff` lists every edit the conventions asked for,
and its README the coverage: which sentences compiled, and which are still prose.

## Use

[Getting started](docs/getting-started.md) takes a one-page note from a first
draft with four mistakes to a certificate, step by step:

```sh
lake exe leanify check Note/article.tex --claims   # undefined symbols, unread statements, the reading of every claim
lake exe leanify init Note/article.tex             # the Lean files, with a stub proof of every claim
lake build Note.Certified                            # the kernel checks the article and your proofs
```

The project needs Leanify in its `lakefile.toml`:

```toml
[[require]]
name = "leanify"
git = "https://github.com/Corrram/leanify.git"
rev = "main"
```

Or start from the article alone: with the checker on the `PATH`,
`leanify certify article.tex` makes its folder a Lean project, writes the Lean
files, fetches mathlib and builds the certificate.

`leanify init` writes four files next to the article, and adds the article's
library to `lakefile.toml`:

| File | Contents |
| --- | --- |
| `Compiled.lean` | `#leanify_article Note "article.tex" "fnv1a64:…"`: the kernel compiles the article, pinned by its hash (`leanify prepare` updates the pin after an edit) |
| `Article.lean` | `#leanify_semantics`: every definition and claim as readable Lean (`claimK`, `meaningfulK`, `obligationK`) |
| `Proofs.lean` | your proofs `proofK : obligationK` and `definedI : wellDefinedI`, or `refuteK : meaningfulK ∧ ¬ claimK` for a claim that is false as stated, and `satisfiedK : satisfiableK`: the hypotheses of statement `K` can hold together |
| `Certified.lean` | `#leanify_certify`: the certificate `Note.certificate`, each verified claim `Note.verifiedK`, and the reports |

A proof that still uses `sorry` leaves its claim unverified, so an article can
be certified while its proofs are written. The certificate also reports what a
proof alone does not show: whether the hypotheses of a statement are shown to
hold together, and whether each step of a printed proof is closed by one fixed
tactic (`leanify_step`) or needed a longer Lean argument. Two scripts take a command of yours
(a model, usually): `scripts/leanify_suggest.py` proposes rewrites of the
sentences Leanify cannot read, and keeps one only if the check then reads it;
`scripts/leanify_prove.py` proves the open obligations, and writes a proof only
if Lean accepts it. The check reads an article with the files it inputs
(`\input`, `\include`, the article's own `.sty` files). Articles about probability on the
unit square use `--vocab unitsquare` ([Vocabularies and models](docs/vocabularies.md)).

The same source gives the two readable outputs:

* the PDF, with `\usepackage{leanify}`, unchanged, or with
  `\usepackage[status]{leanify}` marking every result in the margin with its
  verification status (read from `article.leanify.tex`). Compiled with shell
  escape, the package also checks the article on every compile, with the
  findings as LaTeX warnings at their lines, and with `certify` it builds the
  certificate first. `\leanifyreadings` prints the formal reading of every
  definition and statement, so that a reader of the PDF sees what Lean was asked
  to prove;
* the web reader, `node reader/build.mjs article.tex`, which renders the
  article from its source with the status of every sentence and, for each
  claim, its formal reading, Lean statement, premises and justification.

The examples are short papers in the usual style, each certified by CI:

* [`examples/Demo`](examples/Demo), the note of the guide (`draft.tex` and the
  certified `article.tex`), and [`tests/Refuted`](tests/Refuted), the same note
  with its theorem refuted;
* [`examples/Means`](examples/Means), the harmonic, geometric and arithmetic
  mean of two numbers, with symbols defined inside a theorem, in a
  `where`-clause and in apposition. Five steps of its proofs use rules for
  square roots that the standard tactic does not know, so its results are
  marked *argued*, not *derived*;
* [`tests/Arguments`](tests/Arguments), proofs with assumptions, cases,
  contradictions and an induction, each step closed by the standard tactic.

## Documentation

* [Getting started](docs/getting-started.md): set up a project, check an
  article while writing, prove its claims, read the certificate.
* [Writing for Leanify](docs/writing.md): the house style and the
  constructions of the grammar, with examples.
* [From the `.tex` file to the certificate](docs/pipeline.md): the stages,
  incremental compilation, definedness, the citation audit, the reports and
  the trust boundary.
* [Vocabularies and models](docs/vocabularies.md): where the meaning of words
  that the article does not define comes from.
* [Status and next constructions](docs/roadmap.md): what the exemplars cover
  and which constructions the remaining sentences need.

## Layout

| Path | Contents |
| --- | --- |
| `Leanify/Lex.lean`, `Segment.lean`, `Math.lean` | Lexing (macros, blocks), sentence segmentation, formulas |
| `Leanify/Grammar.lean`, `Elab.lean`, `Doc.lean` | Sentence constructions and their readings, compilation of an article (`compileArticle`) |
| `Leanify/Syntax.lean`, `Denote.lean` | The core language and its Lean denotation |
| `Leanify/Vocab.lean`, `Library/` | Vocabularies, `phrase!`, the unit-square vocabulary and its model |
| `Leanify/Meta.lean`, `Readable.lean`, `Certify.lean` | The commands `#leanify_article`, `#leanify_semantics`, `#leanify_certify` |
| `Leanify/Check.lean`, `LeanifyCli.lean` | The command line `lake exe leanify`: `check` (the native checker, with the files the article inputs), `certify` (from an article to its certificate), `init` (the Lean files of an article, and its project), `prepare` (the pin and the lexing cache), `flatten` (the article and its inputs as one file), `tex` (what `leanify.sty` runs) |
| `examples/`, `tests/` | The example articles of the documentation, and the test articles (a refuted theorem, notions in the running text), certified in CI |
| `reader/` | The web reader: the article rendered from its source with the status of every sentence |
| `tex/leanify.sty` | The check on every compile (with shell escape), the certificate with `certify`, and margin marks with `status` |
| `docs/`, `mkdocs.yml` | The documentation site, https://corrram.github.io/leanify/ |
| `scripts/leanify_diagnostics.py` | Findings from the certificate report, for editors and CI |
| `scripts/leanify_suggest.py`, `scripts/leanify_prove.py` | A hook proposes rewrites of unread sentences, or proofs of open obligations; the checker and Lean decide |

## Build

```sh
lake exe cache get
lake build
npm ci && npm test
```

The documentation site is `docs/` with `mkdocs.yml`:

```sh
npm run demos                          # the readers of the example articles, into docs/demo/
pip install -r requirements-docs.txt
mkdocs serve
```

`.github/workflows/pages.yml` publishes it from `main`.

Lean 4.34.0 with the mathlib revision in `lake-manifest.json`. The generic code
is licensed under Apache-2.0.
