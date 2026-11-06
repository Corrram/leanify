# Commands and files

Everything Leanify provides, in the order a project uses it. The
[tutorial](getting-started.md) shows each in context.

## The command line

`lake exe leanify` runs natively. Its first run builds the executable.

### `leanify check`

```sh
lake exe leanify check ARTICLE.tex [--vocab core|unitsquare] [--claims] [--prose]
```

Compiles the article natively, in about a second, and prints findings in the
`file:line:column: severity: message` format of editors. It certifies nothing.

| Finding | Severity |
| --- | --- |
| a sentence that did not compile: `G is not defined`, `unknown notation \sum`, a type mismatch, an unsupported construction, … | warning |
| a theorem, lemma, proposition, corollary or definition with sentences without a reading: `Lemma l:bound not read`, or `partly read (2 of 5 sentences not read, lines …)`, once per result, with the notation in them that neither the grammar nor the article defines | warning |
| a definition without a reading whose symbols later sentences use | warning |
| with `--claims`: every definition and the formal reading of every claim | info |
| with `--prose`: every sentence of a proof, a remark, an example or a conjecture without a reading, a proof sentence whose construction is not supported, and every definition of the running text without a reading | info |

An undefined symbol is reported once. If the sentence that defines it was not
read, the finding is at that sentence: `… are $\beta(C)\coloneqq…$,
$\xi(C)\coloneqq…$` fails on `\partial`, and `\beta and \xi then undefined at
lines …`. The defining sentence is the one with the symbol
before `\coloneqq`, a `Let` that binds it, or, in a proof, the statement it
proves. Otherwise the finding is at the first sentence that uses the symbol, with
the lines of the later sentences that fail for it: they follow from the first,
and defining the symbol fixes them all. Remarks, examples and conjectures
discuss rather than state, so their prose is not a gap in a statement.

The last lines count the compiled, failed and prose sentences of the text, the
results and the proofs. The exit status is 1 if a sentence failed to compile.
`--vocab unitsquare` adds the vocabulary of probability on the unit
square ([Vocabularies and models](vocabularies.md)).

### `leanify init`

```sh
lake exe leanify init ARTICLE.tex [--name NAME] [--vocab core|unitsquare]
```

Writes four Lean files next to the article and prints the `lean_lib` entry for
`lakefile.toml`. `NAME`, the Lean namespace, is by default the name of the
article's folder. An existing file is never overwritten.

| File | Contents |
| --- | --- |
| `Compiled.lean` | `#leanify_article NAME "article.tex" "fnv1a64:…"` |
| `Article.lean` | `#leanify_semantics NAME "article.tex"` |
| `Proofs.lean` | `namespace NAME.Proofs` with `definedI` for every definition and a stub `proofK` for every claim, each with the claim's reading, place and premises |
| `Certified.lean` | `#leanify_certify NAME "article.tex" using NAME.Proofs` |

### `leanify prepare`

```sh
lake exe leanify prepare ARTICLE.tex --lean COMPILED.lean [--cache DIR --module PREFIX]
```

Run it after every edit of the article. It updates the pin, the hash of the
article in `COMPILED.lean`, so that Lake recompiles the article. With
`--cache`, it also writes the lexing cache, one Lean module per section of the
article, so that the kernel relexes only the sections that changed
([Incremental compilation](pipeline.md#incremental-compilation)).

## The Lean commands

| Command | Declares |
| --- | --- |
| `#leanify_article NS "article.tex" "fnv1a64:…" [with V]` | `NS.source`, `NS.doc` and `NS.compiled : compileArticle NS.vocab NS.source = some NS.doc`, checked by the kernel. It fails if the pin does not match the file. `with V` names the vocabulary (default: the core vocabulary). |
| `#leanify_semantics NS "article.tex" [with M]` | For every definition `I`: a Lean definition named after its symbol and `wellDefinedI`. For every claim `K`: `claimK` (what the sentence says), `meaningfulK` (every term in it is defined) and `obligationK` (its premises imply `meaningfulK ∧ claimK`). Each is tied to the compiled document by a kernel-checked `rfl` theorem. `with M` names the model of the vocabulary. |
| `#leanify_certify NS "article.tex" using J` | `NS.certificate`, checked by the kernel, `NS.verifiedK : NS.meaningfulK ∧ NS.claimK` for every verified claim and `NS.refutedK` for every refuted one. It writes the reports below and logs a summary. |

### What `#leanify_certify` reads

In namespace `J`:

| Declaration | Type | Required |
| --- | --- | --- |
| `J.definedI` | `NS.wellDefinedI` | for every definition, without `sorry` |
| `J.proofK` | `NS.obligationK` | for each claim to verify |
| `J.refuteK` | `NS.meaningfulK ∧ ¬ NS.claimK` | for a claim that is false as stated |

A claim is verified when it has a proof without `sorry` and every claim it rests
on is verified. A claim the text derives (a proof step, or a result whose proof
compiled) is audited: its proof may use Lean, mathlib, Leanify, the compiled
article and helper declarations of the justification modules, which are audited
in turn. The certificate and every refutation may use only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

### Tactics

| Tactic | Does |
| --- | --- |
| `intro_premises` | Unfolds `obligationK` and introduces every premise `J` as `mJ : meaningfulJ` and `cJ : claimJ`. |
| `definedness [h₁, …]` | Proves a definedness condition (`meaningfulK`, `wellDefinedI`): divisions by nonzero terms, arguments in their domains. Give it the facts it cannot find. |

### Options

| Option | Effect |
| --- | --- |
| `set_option leanify.chunk n` | Sentences per kernel-checked chunk of the compilation. |
| `set_option leanify.timing "file"` | Appends the time of every stage of `#leanify_article` to `file`. |

Long articles need `set_option maxRecDepth 100000` and
`set_option maxHeartbeats 0` before `#leanify_article`, as `init` writes them.

## The reports

`#leanify_certify` writes two files next to the article.

`article.leanify.json` records every sentence (position, environment, outcome
and, if it failed, why), every definition (name, symbol, Lean value,
well-definedness condition, justification) and every claim (reading, Lean
statement, definedness condition, premises, status, justification, and for an
unverified claim why it is not verified). The status of a claim is `text`
(derived from its citations), `companion` (proved without a compiled proof in
the text), `unverified` or `refuted`. `sourceHash` pins the article.

`article.leanify.tex` holds the status of every labelled result and a
summary, for `leanify.sty`.

### `leanify_diagnostics.py`

```sh
python .lake/packages/leanify/scripts/leanify_diagnostics.py article.leanify.json \
    [--verified] [--strict] [--prose] [--pin Compiled.lean] [--relative-to DIR]
```

Prints the findings of a report in editor format: a refuted claim is an error,
an unverified claim and a sentence that did not compile are warnings. The exit
status is 1 if the article changed after it was certified, if a claim is
refuted, with `--verified` if a compiled claim is not verified, and with
`--strict` on any warning. `--pin` updates the pin in the Lean file instead.

### `leanify_prove.py`

```sh
python .lake/packages/leanify/scripts/leanify_prove.py ARTICLE.tex [--proofs Proofs.lean] \
    [--hook CMD] [--jobs 4] [--rounds 1] [--timeout 900] [--dry-run]
```

Fills in the stubs of `Proofs.lean` that still end in `sorry`. It needs the
report, so build the certificate once first (`lake build NS.Certified`).

* **Tactics, no model.** For every open claim it tries a fixed portfolio: it
  introduces the premises and the claim's variables and hypotheses, applies each
  premise to them, splits conjunctions, and closes the goal with `assumption`,
  `linarith`, `positivity`, `ring`, `field_simp; ring`, `norm_num` (unfolding the
  article's definitions), or each conjunct in turn; then, for what is left,
  `nlinarith`, `aesop`, `grind` and `tauto`. All candidates go into one Lean
  file under `.lake/leanify-prove/`, which Lean elaborates once, and the first
  candidate of each claim that elaborates without an error replaces its `sorry`.
* **A hook, optional.** `--hook CMD` gives every claim still open to `CMD`, one
  at a time and `--jobs` in parallel, as JSON on its standard input: the claim, its
  formal reading, its Lean statement and definedness condition, its premises
  (available as `cJ`), the sentence and the sentences of the proof around it, the
  article's definitions, the stub, and the errors of the last attempt. `CMD`
  prints the tactic block of a proof (the lines after `:= by`; the stub's first
  two lines are added if missing). Each block is checked the same way, and
  `--rounds 2` gives `CMD` the errors of a failed block for a second try. A
  model behind `CMD` proves single steps with their premises in context, not
  whole theorems.

Nothing is written that Lean has not accepted, and `lake build` checks every
proof again, with the citation audit. Proofs are cached by the statement they
prove (`.lake/leanify-prove/cache.json`), so after an edit only what changed is
proved again. The exit status is 1 if a claim is still open.

## The PDF: `leanify.sty`

```latex
\usepackage{leanify}           % loads mathtools and amssymb; checks the article as it compiles
\usepackage[status]{leanify}   % and marks every labelled result in the margin
\usepackage[certify]{leanify}  % and builds the certificate first, so the marks are current
\leanifymodule{Note.Certified} % optional: the module that certifies the article
\leanifyreport                 % optional: a one-line summary, where it appears
```

| Option | Effect |
| --- | --- |
| `status` | The margin of every labelled result shows *derived* (every sentence compiled and derived in the text), *checked* (every sentence compiled and verified), *partly checked*, *compiled* (not yet verified) or *false* (a claim is refuted), read from `\jobname.leanify.tex`. If the article is newer than that file, a warning says the marks may be out of date. |
| `check=false` | No quick check during the compile. |
| `certify` | Before the marks are read, `prepare` updates the pin and `lake build` builds the certificate. The first time, when the article has no Lean files yet, `init` writes them, and a warning gives the `[[lean_lib]]` entry to add to `lakefile.toml`. Implies `status`. |
| `vocab=unitsquare` | The vocabulary of the article, for `check` and `init`. |
| `lean=FILE` | The compiled Lean file of the article, by default `Compiled.lean` next to it. The module to build is `\leanifymodule`, or else `NS.Certified` for the namespace `NS` that this file compiles. |

**Checking as you compile.** When the compiler may run programs (shell escape:
`pdflatex -shell-escape`, `latexmk -shell-escape`, or the setting of the
editor) and the article lies in a Lean project (a `lakefile.toml` or
`lakefile.lean` in its folder or up to three folders above), every compile runs
`lake exe leanify check` on the article. Its findings become LaTeX warnings
at their lines of the article,

```
Package leanify Warning: g is not defined: sentence not checked on input line
(leanify)                70.
```

so editors that read the LaTeX log list them with the other warnings, and the
summary goes to the terminal. With `certify`, the errors of the Lean build and
the refuted claims are warnings too. The full output of Leanify is in
`\jobname.leanify.log`. `lake` must be on the `PATH` of the compiler; the
first check also builds the checker, which takes a few minutes once.

Without shell escape nothing runs, and in a Lean project a warning says so.
Outside a Lean project, as on arXiv or a journal's server, the package runs
nothing and says nothing. Without `status` the typeset article is unchanged,
which is what you submit. Once `leanify.sty` is on CTAN, arXiv and journals have
it; until then, upload it with the article, or leave it out: Leanify reads the
article without it.

## The web reader

```sh
npm ci --prefix .lake/packages/leanify
node .lake/packages/leanify/reader/build.mjs ARTICLE.tex \
    [--out DIR] [--title TITLE] [--bbl FILE.bbl] [--date YYYY-MM-DD] [--home URL]
```

Writes `DIR/index.html` (default `article-reader/` next to the article) with its
stylesheet, script and fonts, a copy of the article and of its report. The page
renders the article from its source, with the status of every sentence. It
refuses a report whose pin does not match the article. `--home` adds a link
back to a page of yours.

## Editors and CI

`editors/vscode/tasks.json` has two VS Code tasks, *quick check* (the native
check of the open file) and *certify* (update the pin, build, report), whose
findings appear as squiggles in the `.tex` file. A GitHub Actions workflow that
certifies an article on every push is in
[step 9 of the tutorial](getting-started.md#9-check-in-ci).
