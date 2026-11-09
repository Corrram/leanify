# Commands and files

Everything Leanify provides, in the order a project uses it. The
[tutorial](getting-started.md) shows each in context.

## The command line

`lake exe leanify` runs natively. Its first run builds the executable.

### `leanify check`

```sh
lake exe leanify check ARTICLE.tex [--vocab FIELDS] [--claims] [--prose] [--json]
```

Compiles the article natively, in about a second, and prints findings in the
`file:line:column: severity: message` format of editors. It certifies nothing.
The article is read with the `.tex` files it inputs (`\input`, `\include`,
`\subfile`) and with its own packages (a `.sty` file next to the article that it
loads): a finding in such a file is reported at that file and line.

| Finding | Severity |
| --- | --- |
| a sentence that did not compile: `G is not defined`, `unknown notation \sum`, a type mismatch, an unsupported construction, … | warning |
| a theorem, lemma, proposition, corollary or definition with sentences without a reading: `Lemma l:bound is not checked: Leanify cannot read any of its 3 sentences`, or `is only partly checked: Leanify cannot read 2 of its 5 sentences (lines …)`, once per result (named by its label, or by the beginning of its statement), with the likely reason: the notation in it that neither the grammar nor the article defines, or the noun phrase it introduces an object by (`unknown noun "Markov jump process"`) | warning |
| a definition without a reading whose symbols later sentences use | warning |
| a proof with sentences that are not read (prose, or a construction of proofs the grammar does not have), of a result whose statement is read: `the proof of thm:bound is not read completely (Leanify cannot read 1 of its 4 sentences): thm:bound can be checked, but it is not derived from this proof` | info |
| with `--claims`: every definition and the formal reading of every claim | info |
| with `--prose`: every sentence of a proof, a remark, an example or a conjecture without a reading, a proof sentence whose construction is not supported, and every definition of the running text without a reading | info |

An undefined symbol is reported once. If the sentence that defines it was not
read, the finding is at that sentence: `… are $\beta(C)\coloneqq…$,
$\xi(C)\coloneqq…$` fails on `\partial`, and `\beta and \xi are then undefined at
lines …`. The defining sentence is the one with the symbol
before `\coloneqq`, a `Let` that binds it, or, in a proof, the statement it
proves. Otherwise the finding is at the first sentence that uses the symbol, with
the lines of the later sentences that fail for it: they follow from the first,
and defining the symbol fixes them all. Remarks, examples and conjectures
discuss rather than state, so their prose is not a gap in a statement.

The last lines count the compiled, failed and prose sentences of the text, the
results and the proofs, and the proofs that are read completely (`complete
proofs: 2 of 3`): only those derive their result from the printed proof. Then
come the files the article inputs, and the inputs that were not read (a drawing,
a missing file). The exit status is 1 if a sentence failed to compile.
`--vocab unitsquare` adds the vocabulary of probability on the unit
square ([Vocabularies and models](vocabularies.md)).

`--json` prints one JSON object instead, for tools: the findings, every sentence
with its file, place, text and outcome, the definitions, the claims with their
readings, the proofs, and the version of Leanify.

### `leanify flatten`

```sh
lake exe leanify flatten ARTICLE.tex [OUT.tex]
```

Writes the article with the files it inputs in their places, as the check reads
it, to `OUT.tex` (or prints it). A certificate pins one file, so an article in
several files is certified from its flattened form.

`leanify --version` prints the version. A reading is the reading of a version of
the grammar: the reports and the PDF name it.

### `leanify init`

```sh
lake exe leanify init ARTICLE.tex [--name NAME] [--vocab core|unitsquare]
```

Writes four Lean files next to the article and prints the `lean_lib` entry for
`lakefile.toml`. `NAME`, the Lean namespace, is by default the name of the
article's folder. An existing file is never overwritten. For an article that
inputs other files, `init`, `prepare` and `#leanify_article` say that the
certificate covers the one file alone ([`leanify flatten`](#leanify-flatten)).

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
in turn. It may not use the justification (`J.proofN`, `J.refuteN`) of a claim
that is not among its premises, directly or through a helper: its premises are
the hypotheses of its obligation, and another result has to be cited in the
text. The certificate and every refutation may use only the axioms
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
the text), `unverified` or `refuted`. `sourceHash` pins the article, and
`leanify` is the version that read it.

`article.leanify.tex` holds, for `leanify.sty`, the status of every labelled
result, a summary, the version, and the formal reading of every definition and
of every statement (`\leanifyreadings` prints them).

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

### `leanify_suggest.py`

```sh
python .lake/packages/leanify/scripts/leanify_suggest.py ARTICLE.tex --hook CMD \
    [--vocab FIELDS] [--proofs] [--jobs 4] [--rounds 2] [--apply] [--leanify EXE] [--guide FILE]
```

Suggests an edit for each sentence that Leanify cannot read. `CMD` (a model
behind a small wrapper, usually) gets one sentence at a time as JSON on its
standard input: the sentence, the finding, its environment, the sentences before
and after it, the guide `docs/writing.md`, and the instructions. It prints the
LaTeX that replaces the sentence, or nothing.

A suggestion is kept only if the check then reads every sentence of it, and
still reads every sentence it read before. A suggestion that is not kept goes
back to `CMD` with the reason, `--rounds` times. So the hook never tells Leanify
what a sentence means: the grammar reads the rewritten sentence as it reads any
other, and the script prints its formal reading next to the edit:

```
draft.tex:77: corollary
  - The function $f$ attains its minimum on $(0,\infty)$ at $1$.
  + For every $x\in(0,\infty)$, $f(1)\le f(x)$.
    reads as: \forall x\in \mathbb{R},\ 0<x\Rightarrow f(1)\le f(x)
```

Whether the new sentence still says what you meant is yours to judge. The script
writes the kept suggestions as a diff, `ARTICLE.leanify.diff`, and changes the
article only with `--apply`. The targets are the sentences of results without a
reading and the sentences that failed, in the article and the files it inputs
(not an undefined symbol: its fix is where the symbol should be defined);
`--proofs` adds the sentences of proofs. The exit status is 1 if a target is left
without a suggestion.

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
\leanifyreadings               % optional: the formal reading of every definition and statement
```

`\leanifyreadings` prints what Lean was asked to prove: the reading of every
definition and of every statement, with its line, the version of Leanify, the
vocabulary and the conventions the grammar applies where the text states no
domain. Put it in an appendix: a reader of the PDF can then compare each
statement with its reading, without Lean. It prints from
`\jobname.leanify.tex`, like the margin marks.

| Option | Effect |
| --- | --- |
| `status` | The margin of every labelled result shows *derived* (every sentence compiled and derived in the text), *checked* (every sentence compiled and verified), *partly checked*, *compiled* (not yet verified) or *false* (a claim is refuted), read from `\jobname.leanify.tex`. If the article is newer than that file, a warning says the marks may be out of date. |
| `check=false` | No quick check during the compile. |
| `certify` | Before the marks are read, `prepare` updates the pin and `lake build` builds the certificate. The first time, when the article has no Lean files yet, `init` writes them, and a warning gives the `[[lean_lib]]` entry to add to `lakefile.toml`. Implies `status`. |
| `vocab=unitsquare` | The vocabulary of the article, for `check` and `init`. |
| `lean=FILE` | The compiled Lean file of the article, by default `Compiled.lean` next to it. The module to build is `\leanifymodule`, or else `NS.Certified` for the namespace `NS` that this file compiles. |
| `exe=COMMAND` | The checker to run, instead of the project's: `exe=leanify` for an executable on the `PATH`, or a path. With it the quick check also runs outside a Lean project (with shell escape), so a checker without Lean or mathlib is enough to check an article while writing (`.github/workflows/release.yml` builds that executable for Linux, macOS and Windows when a version is tagged). The certificate still needs the project. |

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
summary goes to the terminal. A finding in a file the article inputs names its
file and line. If some proofs are not read completely, one more warning says how
many: their results can be checked, but are not derived from the printed proofs. With `certify`, the errors of the Lean build and
the refuted claims are warnings too. The full output of Leanify is in
`\jobname.leanify.log`. `lake` must be on the `PATH` of the compiler; the
first check also builds the checker, which takes a few minutes once.

**Speed.** After the first build the check runs the checker directly, not through
`lake exe` (which first checks that every module of the project, mathlib's
included, is built): a compile then costs the check itself, a fraction of a
second. The executable is used when it is current (newer than the project's
`lake-manifest.json`, or in the Leanify repository newer than the compiler's
sources); otherwise lake rebuilds and runs it. If neither the article nor a file it inputs has changed
since the last run, as in the later passes of `latexmk` or a recompile for the
bibliography, nothing runs: the findings are read from `\jobname.leanify.log`
again (delete it to force a run). With `certify`, `prepare` writes the lexing
cache of the article (`LexCache/`, imported by `Compiled.lean`), so that after an
edit the kernel relexes only the sections that changed, and nothing is rebuilt
while the status file is newer than the article.

Without shell escape nothing runs, and in a Lean project a warning says so.
Outside a Lean project, as on arXiv or a journal's server, the package runs
nothing and says nothing (unless the option `exe` names a checker). Without `status` the typeset article is unchanged,
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
