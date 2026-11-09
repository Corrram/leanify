# Leanify: notes for agents and contributors

This file says what Leanify is for and which requirements every change must keep.
Read it before changing the grammar, the elaborator, the vocabulary or the LaTeX
package.

## Purpose

A Lean formalization of a mathematics paper is offered as evidence that the paper
is correct. Two questions decide whether it is:

1. **Is the Lean statement the paper's statement?** Today a reader compares two
   texts in two languages by hand. The Navier–Stokes blowup paper shows how this
   fails: its Lemma 8.6 needs four derivatives, the Lean theorem behind it five,
   and both texts look right.
2. **Is the printed proof the proof that was checked?** A correct Lean proof says
   nothing about the argument the paper prints.

Leanify removes the second text. It reads the article's own LaTeX, in ordinary
mathematical English, and compiles every definition and claim into a Lean
statement over Mathlib. The statements are the compilation of exactly that source,
by one fixed Lean function, and the source is pinned by its hash. A printed proof
is compiled sentence by sentence: each step is a claim that may use only the
results it cites.

For an author, Leanify is three steps:

1. **Compile the article as it is**, with `\usepackage{leanify}`. Leanify
   translates the mathematics by fixed grammar rules and reports, as LaTeX
   warnings at their lines, every sentence it cannot read and every word or
   symbol whose meaning the text leaves open.
2. **Edit minimally** until the warnings are gone: usually one convention
   sentence (`We write $A\subset B$ if $A\subseteq B$.`, `Throughout, $C$ and
   $C_m$ denote positive constants.`) rather than changes to the results.
3. **Prove the compiled statements**, by hand or with AI, against the obligations
   Leanify generates. The certificate then marks every result as checked.

What the certificate establishes: every certified claim holds in Lean, and it is
the reading of the printed sentence under the documented grammar and the
vocabulary the article names. A proof whose sentences are all read is checked
step by step, so a wrong or mistyped step does not go through. Sentences Leanify
cannot read are reported, never certified; a result is only as checked as its
mark in the margin says.

The goal is certainty about the paper: its results are correct, and its printed
proofs prove them, with no mathematical typo left. Certainty has four parts, and
a change may not weaken one of them:

* **The claims are true.** Every certified claim is proved in Lean and checked by
  the kernel, from the axioms `propext`, `Classical.choice` and `Quot.sound` alone.
* **The claims are the paper's.** The reading of a sentence is fixed by the
  grammar and the vocabulary, it is printed (`\leanifyreadings`, the reports), and
  it is the reading of the pinned source. The compiler is run by Lean's evaluator;
  `leanify audit` has the kernel evaluate it too.
* **The proofs are the paper's.** A step may use only what its sentence cites, and
  the report says whether one fixed tactic closes it (`leanify_step`) or a longer
  Lean argument was needed that the paper does not print.
* **Nothing is true for an empty reason.** The hypotheses of every claim are asked
  to hold together (`satisfiableK`), except those a proof makes in order to refute
  them. A result is marked *derived* only if all of this holds for it.

The trusted base is Lean's kernel, Mathlib, the grammar (what a sentence means),
and the Mathlib meanings of the core language (`Leanify/Denote.lean`) and of the
vocabulary's constants.

## Requirements

These hold for every change. A feature that cannot meet them is not added.

### Meaning

1. **The printed text fixes the meaning.** There are no hidden annotations,
   invisible macros or side files that change what a sentence means. A meaning
   comes, in this order, from the article's own definitions and convention
   sentences, the longest matching phrase, the declared type, and the fields of
   the vocabulary the article names (printed by `\leanifyreport`). Otherwise
   Leanify refuses. See `docs/vocabulary.md`.
2. **Never guess.** Every construction has exactly one documented reading. A
   sentence is read completely or it is prose; a partial match is never
   accepted. A word with several meanings, or a symbol such as `\subset`, is
   refused with a warning that names the edit that resolves it.
3. **A definition is read completely or not at all.** Leanify does not certify
   a definition with an unread condition, not even one marked as unread.
4. **No junk values.** Partial operations carry their definedness: division,
   logarithms, derivatives, limits, suprema, norms and integrals are defined only
   where they exist (`Tm.defined`, descriptions `.the`). A bound on a norm or an
   integral asserts that it is finite, wherever the bound stands. A claim asserts
   that it is meaningful and that it holds. Never denote a quantity by a Mathlib
   expression whose value is 0 when it does not exist (the Bochner integral of a
   non-integrable function, the supremum of an unbounded set).
5. **Quantifiers as mathematicians mean them.** Implicit quantifiers (generic
   constants, `\ll`, "uniform in", "for every … with …") are read from the
   article's convention sentences, and their order is the one those sentences
   state. The dependence of a constant is part of the statement.

### Generality and minimal edits

6. **General language, not one paper.** Every construction is ordinary
   mathematical English or notation that occurs across fields. A feature is
   motivated by a paper but designed and tested for many: give it examples from
   other areas in its test article, and document it in `docs/writing.md`.
7. **Prefer extending the grammar to asking for edits.** If careful authors
   write it, Leanify should read it. An edit is asked for only where the text
   leaves a meaning open; then the warning says what to write.
8. **Conventions once, not edits everywhere.** A convention stated in one
   sentence (notation, generic constants, words that stand for other words, a
   relation symbol for another) holds for the rest of the article.

### Certification

9. **The compiler is a Lean function that the kernel can evaluate.**
   `compileArticle` is a total Lean function. `#leanify_article` runs it with
   Lean's evaluator (a second per article) and records the source and the result;
   everything that is proved is proved from that result by the kernel. `leanify
   audit ARTICLE.tex` (`set_option leanify.kernel true`) has the kernel evaluate
   the compiler itself, stage by stage by `Eq.refl`, and confirm the document the
   project was built with: Lean's evaluator is then not trusted either. CI runs the
   audit on the test articles. So that it keeps working, everything on the compile
   path must reduce in the kernel:
   * recursion is structural, or bounded by a fuel argument;
   * no `termination_by`/well-founded recursion, `partial`, `implemented_by` or
     `extern` on the compile path;
   * recursion through a nested list (a `List Clause` inside a `Clause`) uses a
     mutual structural function, never `xs.mapM f` with `f` the function being
     defined: that silently turns the definition into well-founded recursion,
     and the audit then fails with
     `(kernel) declaration type mismatch, 'Foo.run0'`.
   After a change on the compile path, run the audit on the test articles, not
   only the checker.
10. **Nothing that is proved rests on evaluation.** The certificate, every
    verified claim, every refutation and every `satisfiedK` depend on the kernel
    and the three standard axioms alone: no `native_decide`, no `sorry`, no other
    axiom. Only the compilation of the article is evaluated, and the audit removes
    that.
11. **A reading may not make a step empty.** A hypothesis of a proof (an
    assumption, a case, the hypothesis of an induction) is a hypothesis of the
    claims made under it, by a documented rule that says where it ends. Such a rule
    can be applied to a text that meant something else, and a step under hypotheses
    that contradict each other is then true whatever it says. So every claim with
    hypotheses gets the obligation that they hold together, unless the proof
    refutes them, and a result with an open one is not *derived*.
12. **A field is data.** A vocabulary field is a list of phrases, symbols and
    adjectives with their types and the names of their Lean meanings (declarations
    of Mathlib, or definitions in a module the field names). The model of an
    article's vocabulary is built from these names; the kernel checks their types.
    A notion of one subject belongs to its field, not to the core language
    (`Prim`): the core is real analysis that every article may use.

### The LaTeX package

13. **The typeset article does not change.** Without options, `leanify.sty`
    changes nothing on the page. It runs an external program (`lake`, or the
    checker) only with unrestricted shell escape and inside a Lean project, or
    when the option `exe` names the checker; otherwise it runs nothing. The
    package runs one command, `leanify tex`, and reads its records
    (`\jobname.leanify.out`): what to check, build or report is decided in
    `LeanifyCli.lean`, not in TeX. Typesetting needs only `mathtools` and `amssymb`. The package is on
    CTAN; `scripts/ctan.sh` builds the upload.
14. **Findings are LaTeX warnings at their lines**, in plain words, with the
    likely fix: the undefined symbol, the unknown noun, the ambiguous word, and
    the sentence that would define it.

## Working on the code

| Path | Contents |
| --- | --- |
| `Leanify/Lex.lean`, `Segment.lean`, `Math.lean` | lexing, sentences, formulas |
| `Leanify/Grammar.lean` | the sentence constructions (each with one reading) |
| `Leanify/Elab.lean`, `Doc.lean` | the readings: formulas and clauses to core terms, the article to a document |
| `Leanify/Syntax.lean`, `Denote.lean` | the core language and its Mathlib meaning |
| `Leanify/Vocab.lean`, `Library/` | vocabulary fields (data), the Lean meanings of their constants, the field registry |
| `Leanify/Meta.lean`, `Readable.lean`, `Certify.lean` | the commands `#leanify_article` (with the kernel audit), `#leanify_semantics`, `#leanify_certify` |
| `Leanify/Check.lean`, `LeanifyCli.lean` | `lake exe leanify check/certify/audit/init/prepare/flatten/tex`; `Leanify.version` |
| `Leanify/Tactic.lean`, `Integers.lean` | `intro_premises`, `definedness`, `leanify_values`, and `leanify_step`, the measure of a standard step (a change of it changes the reports) |
| `scripts/` | `leanify_suggest.py`, `leanify_prove.py` (a hook proposes, the checker or Lean decides), `leanify_diagnostics.py` |
| `tex/leanify.sty` | the LaTeX package |
| `tests/`, `examples/` | test articles, each compiled and audited by the kernel in CI |

A change is finished when:

* the checker builds, the test articles build (`lake build Demo Means TailDependence
  Refuted Notation Vocabulary Fields Calculus PDE Conventions Statements Arguments
  Notions`), and after a change on the compile path the audit passes on them
  (`lake exe leanify audit tests/Arguments/article.tex`, and so on);
* the expected outputs that CI compares are regenerated and reviewed:
  `tests/*/check.txt`, `examples/Demo/draft.check.txt`, the readings in
  `article.leanify.json`, `docs/glossary.md` (`lake exe glossary`);
* an edited test article has its pin updated
  (`lake exe leanify prepare ARTICLE.tex --lean Compiled.lean`);
* a new test article has a `lean_lib` in `lakefile.toml` and a step in
  `.github/workflows/lean.yml`;
* `docs/writing.md` documents each new construction with an example;
* a change of a reading or of the reports has a new `Leanify.version` (the same in
  `lakefile.toml` and `leanify.sty`): a reading is the reading of a version;
* a run on the regression articles shows no unintended change.

Write documentation and messages in plain, short sentences. Commit locally; the
maintainer pushes.
