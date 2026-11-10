# From the `.tex` file to the certificate

Leanify compiles an ordinary LaTeX article and verifies it in Lean. Readers
and Lean work from one text: the definitions, statements and proof sentences
that people read are the ones the kernel checks. There is no second,
hand-written formal version that could drift away from the paper.

## Stages

| Stage | Command | What it gives |
| --- | --- | --- |
| compile | `#leanify_article Foo "article.tex" "fnv1a64:…" with V` | `Foo.source` and `Foo.doc`: the article and its compilation by `compileArticle V`, run by Lean's evaluator in about a second. The audit has the kernel evaluate the compiler too. |
| state | `#leanify_semantics Foo "article.tex"` | Every definition as a Lean constant (`Foo.nu`, `Foo.D`, …), every claim as a proposition (`Foo.claimK`) with its definedness condition (`Foo.meaningfulK`), each tied to the compiled document by an `rfl` theorem that the kernel checks (`Foo.env`, `Foo.holdsK`, `Foo.welldefI`). It also states the proof obligations `Foo.obligationK`, and `Foo.satisfiableK` for the hypotheses of the claims. |
| justify | your Lean proofs `J.proofK : Foo.obligationK`, `J.definedI : Foo.wellDefinedI`, `J.satisfiedK : Foo.satisfiableK` | Ordinary Lean proofs. |
| certify | `#leanify_certify Foo "article.tex" using J` | `Foo.certificate`, checked by the kernel: every justified claim holds, premises are verified and acyclic, every definition is well defined, and claims derived in the text pass the citation audit. Exports `Foo.verifiedK : Foo.meaningfulK ∧ Foo.claimK` and writes the reports. |

`compileArticle` is an ordinary, total Lean function of the file's contents, so
the readable statements depend on nothing but the text (and the vocabulary, see
[vocabularies](vocabularies.md)).

The pin `"fnv1a64:…"` is the hash of the article. Lake does not track the
`.tex` file, so an edited article must change the Lean file to be recompiled.
`lake exe leanify prepare article.tex --lean Compiled.lean` updates the pin
(`leanify certify` does it and builds).

## What is trusted, and the audit

Everything that is *proved* about an article is checked by Lean's kernel, from
the three standard axioms: the claims, the definedness of the definitions, the
refutations, and that the readable statements `Foo.claimK` are the meaning of the
compiled document `Foo.doc`.

An article may use notions that it does not define and quote results that it does not
prove ([Writing for Leanify](writing.md#notions-that-the-article-does-not-define)). The
notions are `opaque` constants of Lean, so nothing is assumed about them beyond their
types (and that each kind of object has an element). The quoted results are axioms
`Foo.Quoted.claimK`, stated by `#leanify_semantics` from the compiled document. They are
the only axioms beside the standard three that `#leanify_certify` accepts, the build
prints them, and the reports say which claims rest on them. Whether a quoted result
holds, and whether its reading is what its source proves, is for the reader to check.

That `Foo.doc` is the compilation of the article is, by default, the result of
running the compiler: `#leanify_article` evaluates `compileArticle` like any
program. This is what makes a compile take a second. It trusts Lean's evaluator
for that one computation, and it trusts the grammar, as every reading does: the
grammar is what says what a sentence means, and the readings it gives are
printed for you to read (`--claims`, `\leanifyreadings`, the reports).

The audit removes the evaluator:

```sh
lake exe leanify audit Note/article.tex
```

It compiles the article again with `set_option leanify.kernel true`, into the
namespace `Note.Audit`. Every stage of the compilation (preamble, lexing and
segmentation of each block, the sentences in chunks, assembly) is then a theorem
`lhs = rhs` proved by `Eq.refl`, which the kernel checks by evaluating the
compiler itself, and the stages compose to `Note.Audit.compiled`. The audit ends
with

```lean
theorem Note.Audit.built : compileArticle Note.vocab Note.source = some Note.doc := Note.Audit.compiled
```

which the kernel accepts only if the source and the document of your build are
the ones it computed. It takes from half a minute for a note to a few minutes
for a long article (`set_option leanify.chunk n` sets the number of sentences
in one kernel check, `set_option leanify.timing "file"` records the time of every
stage). Run it before you submit, and in CI.

## Definedness

Partial operations are total in Lean, as in mathlib. Every compiled term
therefore has a syntactic definedness condition, `Tm.defined`, in the style of
TCCs. A claim means `defined ∧ claim`. The condition includes:

* nonzero denominators and nonnegative bases of real powers;
* numbers used as points of an interval type (`C(\frac12,1-u)` in `[0,1]`, with the
  field `unitsquare`), and arguments in the domain a definition states: the domains
  of its variables and the hypotheses it was made under;
* integrability of integrands and measurability of measured sets;
* coverage of `cases`, and agreement where two conditions overlap;
* the body of a map `v ↦ e` at the points of the domain it is used on;
* integrability of the derivative of a function given by its value at a point and
  its derivative (`φ(x) = φ(a) + ∫_a^x φ'`);
* disjoint parameter domains of a family defined twice (`κ_w`, then `κ_b`);
* exactly one solution of a definite description ("the $b$ with $e_b=e$").

So `1/0 = 0` cannot make a claim true for a conventional reason. `leanify check
--defined` prints the condition of every claim and definition. A condition is asked
once: a guard about an argument already asks that the argument is defined.

## Justifications and the citation audit

`obligationK` is `P_{j₁} → … → P_{jₙ} → meaningfulK ∧ claimK`, where the `jᵢ`
are the premises the text gives claim `K`: the citations of its sentence, and
for a proof sentence the earlier sentences of the proof. Two tactics help:

* `intro_premises` introduces each premise `J` as `mJ`/`cJ`;
* `definedness [facts]` proves definedness conditions.

A claim is *derived in the text* when it is a proof sentence, or a statement
closed by a compiled proof. For such a claim, `#leanify_certify` audits the
justification. Every constant it uses must come from Lean or mathlib, from
Leanify, from the compiled article, or from helper declarations in the
justification modules, which are audited recursively. It may not be the
justification of another claim (`J.proofN`, `J.refuteN`) that is not among the
claim's premises. A proof sentence therefore cannot be justified by a result it
does not cite. The audit does not bound the length of the Lean argument
for a step: a step that the text makes in one line may need a long Lean proof,
with helper lemmas of its own. So the certificate measures it: it tries one
fixed tactic, `leanify_step`, on every claim derived in the text, and reports
the claim as a *standard* step if the tactic closes it and as an *argument*
otherwise. A result with an argument among its steps is *argued*, not
*derived*: it is proved from what the text cites, but the printed proof leaves
out more than routine steps. Claims without a
compiled proof (cited theorems, displayed formulas) may use any Lean proof:
typically a companion development, connected by proved bridge theorems. The
certificate permits only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

Not every claim needs a justification. A claim without one, or whose proof
still uses `sorry`, is *unverified*, and so is every claim that rests on an
unverified one: the certificate covers the others. A claim that is false as
stated is *refuted* by `J.refuteK : Foo.meaningfulK ∧ ¬ Foo.claimK` (it is
meaningful, and it does not hold). `#leanify_certify` then declares
`Foo.refutedK`, and the reports, the reader and the PDF mark the claim false.
A proof of a refuted claim can only rest on false premises, so it does not
count.

A statement can also be true for an empty reason: no object satisfies its
hypotheses. For every statement with hypotheses, `#leanify_semantics` states
`Foo.satisfiableK` (there are values of its variables for which the hypotheses
hold), and the reports say whether `J.satisfiedK` proves it. It is not required
for the certificate, and it is reported for every statement.

## Reports

`#leanify_certify` writes, next to the article:

* `article.leanify.json`: every sentence (position, environment, outcome),
  definition and claim (formal reading, Lean statement, premises, status
  `text`, `companion`, `unverified` or `refuted`, justification, why an
  unverified claim is not verified, whether a derived claim is a standard step,
  and whether the hypotheses of a statement are shown to hold together). Read by the web reader and by
  `scripts/leanify_diagnostics.py`.
* `article.leanify.tex`: the status of every labelled result, read by
  `\usepackage[status]{leanify}` to mark results in the margin of the PDF, and
  the formal reading of every definition and statement, which
  `\leanifyreadings` prints with the version of Leanify. Without the `status`
  option and that command the PDF is unchanged.

## Reading

`reader/reader.mjs` renders the article from its source (`reader/article.mjs`)
with the status of every sentence:

* derived from its citations;
* checked by a companion development;
* definition, well defined;
* compiled, not yet verified;
* false as stated, refuted in Lean;
* not compiled;
* prose.

Selecting a marker shows the sentence's formal reading, its Lean statement, its
definedness condition, its premises and its justification.

## Trust boundary

The kernel checks the compilation of the file, the identity of the readable
definitions and claims with the compiled semantics, every justification and the
certificate. Outside the proof are: the fixed readings of the grammar's
constructions (documented in `Leanify/Grammar.lean` and `Leanify/Doc.lean`; they
are the readings of a version of Leanify, which the reports and
`\leanifyreadings` name),
the vocabulary and its model (a short, reviewable list), the native evaluation
that proposes stage results (the kernel re-checks them), and the presentation
(the PDF, KaTeX typesetting of formal readings and the HTML reader).
