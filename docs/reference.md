# Commands and files

Everything Leanify provides, in the order a project uses it. The
[tutorial](getting-started.md) shows each in context.

## The command line

`lake exe leanify` runs natively. Its first run builds the executable.

### `leanify check`

```sh
lake exe leanify check ARTICLE.tex [--vocab FIELDS] [--notions NOUNS] [--quantities WORDS] [--claims] [--defined] [--prose] [--json]
```

Compiles the article natively, in about a second, and prints findings in the
`file:line:column: severity: message` format of editors. It certifies nothing.
The article is read with the `.tex` files it inputs (`\input`, `\include`,
`\subfile`) and with its own packages (a `.sty` file next to the article that it
loads): a finding in such a file is reported at that file and line.

| Finding | Severity |
| --- | --- |
| a sentence that did not compile: `G is not defined`, `unknown notation \sum`, a type mismatch, an unsupported construction, … | warning |
| a theorem, lemma, proposition, corollary or definition with sentences without a reading: `Lemma l:bound is not checked: Leanify cannot read any of its 3 sentences`, or `is only partly checked: Leanify cannot read 2 of its 5 sentences (lines …)`, once per result (named by its label, or by the beginning of its statement), with the likely reason: the notation in it that neither the grammar nor the article defines, or a noun phrase it introduces an object by that Leanify does not read as a noun where it stands (`not read as a noun: "Markov jump process"`; a phrase that is read there, such as `an integer` or `there is a constant`, is not named) | warning |
| a definition without a reading whose symbols later sentences use | warning |
| a proof with sentences that are not read (prose, or a construction of proofs the grammar does not have), of a result whose statement is read: `the proof of thm:bound is not read completely (Leanify cannot read 1 of its 4 sentences): thm:bound can be checked, but it is not derived from this proof` | info |
| with `--claims`: every definition and the formal reading of every claim, and for a claim that follows a sentence of its result or proof which is not read: `claim 4 follows a sentence that Leanify does not read (line 33): its reading has the hypotheses of the sentences that are read, and may lack one or keep one that has ended`. The summary counts these claims | info |
| with `--defined`: also what each claim and definition needs in order to be meaningful (`claim 4 is meaningful if: …`, `y is well defined if: \forall x\in\mathbb{R},\ \neg(x=0)\Rightarrow\neg(x=0)`): nonzero denominators, arguments inside the domains of the functions they are given to, integrable integrands. These are the statements `meaningfulK` and `wellDefinedI` of the Lean files | info |
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
come, if there are any: what the article uses without defining it (`not defined
here: graph, finite graph, \chi (chromatic number)`), the results it quotes from
the literature without a proof (`quoted from the literature and not proved here
(assumed): lemma clique`), and the nouns that stopped the reading and that the
article could declare (`nouns without a reading: polynomial, …`;
[Writing for Leanify](writing.md#notions-that-the-article-does-not-define)).
`--notions "graph, finite graph"` and `--quantities "degree"` read the article as
if its preamble declared these, to try a list. Then
come the files the article inputs, and the inputs that were not read (a drawing,
a missing file). The exit status is 1 if a sentence failed to compile.
`--vocab unitsquare` adds the vocabulary of probability on the unit
square ([Vocabularies and models](vocabularies.md)).

`--json` prints one JSON object instead, for tools: the findings, every sentence
with its file, place, text and outcome, the definitions, the claims with their
readings, the proofs, and the version of Leanify.

### `leanify fields`

```sh
lake exe leanify fields ARTICLE.tex [--vocab FIELDS] [--notions NOUNS] [--quantities WORDS]
```

Says which fields of the vocabulary the article needs. Nothing is guessed from
its words: every field is tried on the article, and the fields that make Leanify
read more of its sentences are named, the one that adds the most first, then the
one that adds the most to it, up to four.

```
note.tex: 1 of 19 sentences are read as mathematics with the core vocabulary alone
  graphs: 18 more sentences
note.tex: 19 of 19 with \usepackage[vocab={graphs}]{leanify}
```

It starts from the fields that the article names in its preamble (or from
`--vocab`; `--vocab core` starts from none). When the fields it finds belong to one
[bundle](libraries.md#bundles), it names the bundle too (`vocab={probability}` for
`distributions` and `information`). A field changes how words are read,
so compare the readings before you keep it: `leanify check ARTICLE.tex --vocab
FIELDS --claims`. If no field reads more, what is not read is a wording or a
notion that no field has, and `leanify check` names each. A single finding of the
check also names the field that has its noun or its notation.

### `leanify flatten`

```sh
lake exe leanify flatten ARTICLE.tex [OUT.tex]
```

Writes the article with the files it inputs in their places, as the check reads
it, to `OUT.tex` (or prints it). A certificate pins one file, so an article in
several files is certified from its flattened form.

`leanify --version` prints the version. A reading is the reading of a version of
the grammar: the reports and the PDF name it.

### `leanify certify`

```sh
leanify certify ARTICLE.tex [--vocab FIELDS] [--name NAME] [--leanify REV|PATH]
```

Everything from an article to its certificate, in one command: the Lean files of
the article if it has none yet ([`init`](#leanify-init)), mathlib if the project
has none yet (`lake update`, which downloads its compiled files), the pin
([`prepare`](#leanify-prepare)), and `lake build NAME.Certified`, whose output
it shows. Run it again after an edit of the article or of `Proofs.lean`.

An article that lies in no Lean project gets one, in the folder `lean` next to it
([`init`](#leanify-init)). The new project requires **the Leanify that
this checker was built from**, so that the Lean files and the library that reads them
are one version:

* the checker runs from a checkout of Leanify (`…/leanify/.lake/build/bin/leanify`)
  whose commit is on the remote and that has no local changes: the project requires
  that commit (`rev = "…"`), a lakefile that others can build;
* otherwise it requires the checkout by its path, and uses its packages
  (`packagesDir`): mathlib is neither fetched nor built again, and the first
  certificate takes seconds. For a project that others build, name a revision;
* a released checker (not in a checkout) requires the tag of its version (`v0.7.0`).
  The release workflow builds a checker only for the tag of its own version, so the
  tag exists for every released checker; if it is not on the remote (a checker built
  by hand outside a checkout), the message says so and names `--leanify REV`;
* `--leanify REV` or `--leanify PATH` names the revision or the folder.

### `leanify init`

```sh
lake exe leanify init ARTICLE.tex [--name NAME] [--vocab FIELDS] [--leanify REV|PATH]
```

Writes the four Lean files of the article. `NAME`, the Lean namespace, is by
default the name of the article's folder. An existing file is never
overwritten.

* **In a Lean project** (a `lakefile.toml` or `lakefile.lean` in the article's
  folder or up to three folders above), the files go next to the article (into
  a folder `NAME/` if the article lies in the folder of the project itself),
  and the `[[lean_lib]]` entry of the article is added to `lakefile.toml`. With
  a `lakefile.lean`, the entry is printed for you to add.
* **Anywhere else**, the article gets a Lean project of its own, in the folder
  `lean` next to it: `init` writes `lean/lean-toolchain` (the Lean version of the
  checker), `lean/lakefile.toml`, which requires the Leanify of the checker
  ([`certify`](#leanify-certify) says which), `lean/.gitignore` (for `.lake/`,
  what Lake builds) and the Lean files in the folder `lean/NAME/`. Everything of
  Lean and Lake is in that one folder, and it is found again from the article
  (after the folder of the article and the three above it). So an author needs
  no knowledge of Lake to start: a folder with `article.tex` is enough. The
  package makes the same project when it first checks such an article, without
  the Lean files ([`leanify tex`](#leanify-tex)); `init` then adds them.

For an article that inputs other files, `init`, `prepare` and
`#leanify_article` say that the certificate covers the one file alone
([`leanify flatten`](#leanify-flatten)).

| File | Contents |
| --- | --- |
| `Compiled.lean` | `#leanify_article NAME "article.tex" "fnv1a64:…"` |
| `Article.lean` | `#leanify_semantics NAME "article.tex"` |
| `Proofs.lean` | `namespace NAME.Proofs` with `definedI` for every definition, a stub `proofK` for every claim, each with the claim's reading, place and premises, and a stub `satisfiedK` for every set of hypotheses under which claims are made |
| `Certified.lean` | `#leanify_certify NAME "article.tex" using NAME.Proofs` |

### `leanify prepare`

```sh
lake exe leanify prepare ARTICLE.tex --lean COMPILED.lean
```

Updates the pin, the hash of the article in `COMPILED.lean`, so that Lake
compiles the article again after an edit. `leanify certify` and the package
option `certify` do this themselves.

### `leanify audit`

```sh
lake exe leanify audit ARTICLE.tex [--lean COMPILED.lean] [--module MODULE]
```

Has Lean's kernel evaluate the compiler on the article, and confirm the document
the project was built with (theorem `NS.Audit.built`). It takes half a minute to
a few minutes and changes nothing in the project
([What is trusted, and the audit](pipeline.md#what-is-trusted-and-the-audit)).

### `leanify tex`

```sh
leanify tex ARTICLE.tex [--vocab FIELDS] [--no-check] [--certify] [--status] [--no-project] [--lean FILE] [--module MODULE]
```

What `leanify.sty` runs, once per compile. It does the quick check, with
`--certify` the steps of `leanify certify`. If the article lies in no Lean
project, it makes one in the folder `lean` next to the article, as
[`init`](#leanify-init) does, but without the Lean files of the article: `lean-toolchain`,
`lakefile.toml` and `.gitignore`, three small files, and nothing is fetched or
built. The Lean files are written when the certificate is first built, from the
article as it is then, because their stub proofs follow its claims and an
existing file is never overwritten. `--no-project` (the option `project=false`
of the package) leaves the article without a project. The command writes two files next to the
article: `ARTICLE.leanify.out`, the findings as records that TeX reads without
parsing (a line `leanify VERSION`, then for each record a line with its kind and
one line for each of its fields), and, on its standard output, the full text
that the package keeps as `ARTICLE.leanify.log`. The records of an unchanged
article are the same on every run, so `latexmk` sees no change and stops.

## The Lean commands

| Command | Declares |
| --- | --- |
| `#leanify_article NS "article.tex" "fnv1a64:…" [with V]` | `NS.source` and `NS.doc`, the article and its compilation, run by Lean's evaluator. It fails if the pin does not match the file. `with V` names the vocabulary (default: the core vocabulary). With `set_option leanify.kernel true` (the audit) it also proves `NS.compiled : compileArticle NS.vocab NS.source = some NS.doc`, checked by the kernel alone. |
| `#leanify_semantics NS "article.tex" [with M]` | For every definition `I`: a Lean definition named after its symbol and `wellDefinedI`. For every claim `K`: `claimK` (what the sentence says), `meaningfulK` (every term in it is defined) and `obligationK` (its premises imply `meaningfulK ∧ claimK`). Each is tied to the compiled document by a kernel-checked `rfl` theorem. For every set of hypotheses under which claims are made: `satisfiableK`, which says that they can hold together (`K` is the first claim made under them). The model of the vocabulary is built from the names of the Lean meanings of its constants; `with M` gives a model written by hand instead. |
| `#leanify_certify NS "article.tex" using J` | `NS.certificate`, checked by the kernel, `NS.verifiedK : NS.meaningfulK ∧ NS.claimK` for every verified claim and `NS.refutedK` for every refuted one. It writes the reports below and logs a summary. |

### What `#leanify_certify` reads

In namespace `J`:

| Declaration | Type | Required |
| --- | --- | --- |
| `J.definedI` | `NS.wellDefinedI` | for every definition whose well-definedness is to be shown; a definition without it (or with `sorry` in it) is *assumed* to be well defined |
| `J.proofK` | `NS.obligationK` | for each claim to verify |
| `J.companionK` | `NS.obligationK` | instead of `J.proofK`, for a claim that the text derives (a proof sentence, a result with a compiled proof) and that is proved otherwise: from a formalization of the result, when the sentences it rests on are not read. The claim is reported as `companion`, and its justification is not audited against its citations |
| `J.refuteK` | `NS.meaningfulK ∧ ¬ NS.claimK` | for a claim that is false as stated |
| `J.satisfiedK` | `NS.satisfiableK` | for a result to be *derived*: the hypotheses of claim `K` can hold together |

A claim is verified when it has a proof without `sorry` and every claim it rests
on is verified. A claim the text derives (a proof step, or a result whose proof
compiled) is audited: its proof may use Lean, mathlib, Leanify, the compiled
article and helper declarations of the justification modules, which are audited
in turn. It may not use the justification (`J.proofN`, `J.refuteN`) of a claim
that is not among its premises, directly or through a helper: its premises are
the hypotheses of its obligation, and another result has to be cited in the
text. The certificate and every refutation may use only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

### Definitions that are assumed to be well defined

That a definition is well defined can be a theorem of its own: an integral needs an
integrable integrand, a supremum a bounded set, an inverse a bijection. A reader takes
these for granted, and their Lean proofs are often the longest part of a certificate.
So a definition without a proof `J.definedI` (or with `sorry` in it) does not stop the
certificate: the axiom `NS.Assumed.wellDefinedI` stands for the proof, as
`NS.Quoted.claimK` stands for a quoted result. The certificate then holds *given* that
these definitions are well defined. The build names them (`3 definitions are assumed to
be well defined: 6 (R), …`), the summary counts them apart (`33 definitions well
defined, 3 assumed to be`), and in `article.leanify.json` their `justification` is the
axiom. An article is fully certified when no definition is assumed.

### What a verified claim does not say

Three things are reported next to the status of a claim, because a proof without
`sorry` does not show them.

**The claim is the claim of the text.** A claim is read with the variables and
hypotheses of the sentences before it in its result or proof (in a proof: also
those of the statement). If one of these sentences is not read, the reading has
only what the other sentences say. It may lack a hypothesis (`Suppose moreover
that …`, not read), and it may keep one that the text has ended: a supposition
after the unread sentence that states the contradiction, or the first case after
an unread `In the other case, …`. The claim as read is then not what the text
claims at that place, and a proof of it shows less than it seems: under a
supposition that cannot hold, the conclusion of the proof is true for an empty
reason. Leanify cannot know what an unread sentence says, so it reports every
such claim: `after` lists the sentences in question, `leanify check --claims`
names their lines, and the summaries count a verified claim of this kind apart,
as *verified as read*. The result itself is not affected where its mark is
already cautious: a statement with an unread sentence is *partly checked*, and a
result is *derived* only from a proof that is read completely.

**The hypotheses can hold.** A statement `for every x with P(x), Q(x)` is true
if no `x` has `P`: a mistyped hypothesis (`$0<x<0$`) makes every conclusion
provable. The same holds for a step of a proof: under an assumption or a case
that cannot occur, it is true whatever it says, and was not checked. For a claim
`∀ x, P x → ∀ y, R x y → Q x y`, `satisfiableK` is `∃ x, P x ∧ ∃ y, R x y`. It is
stated once for each set of hypotheses, for the first claim `K` made under them.
With a proof `J.satisfiedK` of it the report says that the hypotheses hold
together (`"hypotheses": "shown"`), otherwise that this is not shown (`"open"`).
It is not asked of the claims that a proof makes under a hypothesis it refutes
(`Suppose, for contradiction, …`, and what a contradiction ends): those
hypotheses are not meant to hold, and that is their point.

**The step is small.** A proof in the article is checked step by step, but
nothing in Lean bounds what one step may do: a justification can be a hundred
lines that prove the theorem again, next to the printed argument and not
through it. So `#leanify_certify` tries one fixed tactic,
[`leanify_step`](#tactics), on every claim that the text derives. A claim that
it closes is a `standard` step: the sentence follows from the results it cites
by routine algebra and logic, as a reader expects of one sentence of a proof.
Any other verified claim is an `argument`: true, proved from the cited results
only, but by a longer Lean proof that is not in the article. The report counts
both, and `leanify_diagnostics.py --standard` lists the arguments.

A result is *derived* when every sentence of it and of its proof is read, every
claim is proved from what it cites, every step is standard, and the hypotheses of
every claim are shown to hold together. With a step that is an argument, or with
hypotheses that are not shown to hold together, it is *argued*: proved, with a
reservation that the report names.

### Tactics

| Tactic | Does |
| --- | --- |
| `intro_premises` | Unfolds `obligationK` and introduces every premise `J` as `mJ : meaningfulJ` and `cJ : claimJ`. |
| `definedness [h₁, …]` | Proves a definedness condition (`meaningfulK`, `wellDefinedI`): divisions by nonzero terms, arguments in their domains. Its leaves are hypotheses, numeric side conditions, bounds of points of an interval, products and powers that are not zero, a strict case or its endpoint (from the weak inequality), a witness that a hypothesis gives, a value of a definition of the article in each of its cases, and the facts of the vocabulary (`leanify_facts`). Give it the facts it cannot find. |
| `leanify_part` | Closes a goal that is a side of a hypothesis: of the conjunction that the hypothesis is once its definitions are unfolded (that `C` is a distribution function, from the hypothesis that `C` is a copula of the article). `definedness` uses it. |
| `leanify_facts` | Closes a leaf of a definedness condition with a fact of the model of the vocabulary. A library gives its rules with `macro_rules`; `definedness` uses it. For the unit square: an integral against a distribution function `F` of an expression in `F` and the coordinates that `fun_prop` finds measurable and `nlinarith` bounds by `4`, and the probability of a comparison of two expressions in the terms of a sample (`leanify_sample_event`). Also for the unit square: a continuous function on `[0,1]` is integrable, a continuous function on the square is integrable for a coupling, `Y Z` and `Y F_Y(Y)` are integrable for a joint law with an integrable `Y`, a graph `{x : (x, T(x)) ∈ A}` of a Borel map is a Borel set, and a function given by cases on comparisons with continuous cases is interval integrable (`leanify_piecewise`). An article adds its own rules the same way (that its named copulas are copulas, say). |
| `leanify_points`, `leanify_pinch`, `leanify_neq`, `leanify_unfold`, `leanify_arith` | The steps of `definedness` for arithmetic leaves: the bounds `0 ≤ x ≤ 1` of the points of an interval with `linarith`; two cases that meet in a point (`x ≤ c` and `c ≤ x` give `x = c`, then computation); an excluded point that the bounds force; the definitions of the article unfolded one level; and `linarith`, `positivity`, or `nlinarith` with the quotients cleared. |
| `leanify_sample_fun`, `leanify_sample_event` | (unit square) Prove that an expression in the terms `U_i`, `V_i` of a sample is a measurable function of the sample, and that a comparison (`<`, `≤`) of two such expressions is a measurable set of samples: sums, differences, products, quotients, maxima, minima, absolute values, powers, finite sums and case distinctions between such expressions. |
| `leanify_values v₁ v₂ …` | Proves `satisfiableK` with these values for the variables of the statement, in the order of the text (the last value serves every further variable), if its hypotheses then follow by computation. |
| `leanify_counter v₁ v₂ …` | Proves `refuteK : meaningfulK ∧ ¬ claimK` with these values for the variables of the claim, in the order of the text (the last value serves every further variable), if its hypotheses then hold and its conclusion fails, both by computation: the claim is false as it is read, at these values. |
| `leanify_step` | Proves an obligation whose claim follows from its premises by routine steps: it introduces the premises and the variables and hypotheses of the claim, takes each premise at them (a lemma about every positive `x` at `x` and at `y`), splits conjunctions, adds what a reader uses about integers without saying so (sums, differences and products of integers are integers, and `a < b` gives `a + 1 ≤ b`), uses a hypothesis `A → B` whose `A` follows at once, and closes the goal with `assumption`, `linarith`, `positivity`, `ring`, `field_simp; ring`, `norm_num` or `simp` with the article's definitions, the two directions of an equivalence by `linarith` or `nlinarith`, `nlinarith`, `grind`, `aesop` or `tauto`. It uses no other lemma of mathlib by name: a step that needs one (a rule for real powers, a named inequality) is an `argument`. Every closer has a budget of its own, so what the tactic proves does not depend on the limits of the file it is used in. It is the measure of a `standard` step, so it is fixed for a version of Leanify. |
| `leanify_int` | Proves that a real number is an integer: a hypothesis, a numeral, or a sum, difference, product, negative or power of integers. |

### Facts of the unit square for proofs

`Leanify/Library/UnitSquareModel.lean` proves what the proofs of an article about copulas
and couplings use about the meanings of the vocabulary, so that a proof (or a bridge to a
formalization of the results) does not unfold them:

| Fact | Says |
| --- | --- |
| `measureOfSetFn_prob`, `measureOfSetFn_apply`, `measureOfSetFn_eq` | a set function that is a probability measure is the measure `measureOfSetFn` on Borel sets, and that measure is unique |
| `measureOfSetFn_map_fst`, `measureOfSetFn_map_snd` | the marginals of a coupling are Lebesgue measure |
| `couplingOfCopula_isCoupling`, `copulaOfCoupling_isCopula` | the coupling of a copula is a coupling, the copula of a coupling is a copula |
| `copulaOfCoupling_couplingOfCopula`, `couplingOfCopula_copulaOfCoupling` | the two determine each other |
| `couplingExpectation_couplingOfCopula` | an expectation for the coupling of `C` is an integral against the measure of `C` at the reflected point |
| `graph_probMeasure2`, `graph_measUniformMarginals`, `lebesguePreserving_of_graph` (and `'` for `(T(Z), Z)`) | the law of `(X, T(X))` for a Borel map `T` is a probability measure; it is a coupling exactly when `T` preserves Lebesgue measure |
| `couplingExpectation_graph` | an expectation for the law of `(X, T(X))` is `∫ f(x, T(x)) dx` |
| `measureOfJoint_prob`, `measureOfJoint_apply`, `jointDistFn_eq_cdf`, `jointUniformSecond_measurePreserving` | a joint law of a real variable and a point of `[0,1]`: its measure, the distribution function of the first variable as a `cdf`, and the uniform second variable as a measure-preserving map |
| `Leanify.Prelude.limAt_eq`, `limAtConv_of` | a limit at a point from a limit along the punctured domain |
| `Leanify.Prelude.intervalIntegrable_ite` | a function given by cases on a Borel condition is interval integrable when its cases are |

### Options

| Option | Effect |
| --- | --- |
| `set_option leanify.kernel true` | The audit: `#leanify_article` proves every stage of the compilation with the kernel (`leanify audit` runs it). |
| `set_option leanify.chunk n` | In the audit: sentences per kernel-checked chunk of the compilation. |
| `set_option leanify.timing "file"` | Appends the time of every stage of `#leanify_article` to `file`. |
| `set_option leanify.steps false` | `#leanify_certify` does not try `leanify_step` on the derived claims (faster; the report then leaves the step size empty). |

`init` writes `set_option maxRecDepth 100000` and `set_option maxHeartbeats 0`
before `#leanify_article`: the literals of a long article need them.

## The reports

`#leanify_certify` writes two files next to the article.

`article.leanify.json` records every sentence (position, environment, outcome
and, if it failed, why), every definition (name, symbol, Lean value,
well-definedness condition, justification) and every claim (reading, Lean
statement, definedness condition, premises, status, justification, and for an
unverified claim why it is not verified). The status of a claim is `text`
(derived from its citations), `companion` (proved without a compiled proof in
the text), `quoted` (a statement that the article quotes from the literature and
does not prove: an assumption, the axiom `Foo.Quoted.claimK`), `unverified` or
`refuted`. `rests` lists the quoted claims that a verified claim rests on.
`after` lists the sentences before the claim, in its result or proof, that are
not read: its reading may lack a hypothesis of one of them, or keep one that it
ends.
`notDefined` lists what the article uses without defining it
([Writing for Leanify](writing.md#notions-that-the-article-does-not-define)),
and a definition that is such a quantity has `undefined`. `axioms` are the standard
three and the quoted claims. A claim of status `text` has a `step`,
`standard` or `argument`, and a claim with hypotheses has `hypotheses`,
`shown` or `open`, and `hypothesesOf`, the claim that stands for them and has the
Lean statement `satisfiable`; `refuted` marks a claim under a hypothesis that its
proof refutes
([What a verified claim does not say](#what-a-verified-claim-does-not-say)).
`sourceHash` pins the article, and `leanify` is the version that read it.

`article.leanify.tex` holds, for `leanify.sty`, the status of every labelled
result, a summary, the version, and the formal reading of every definition and
of every statement (`\leanifyreadings` prints them).

### `leanify_diagnostics.py`

```sh
python .lake/packages/leanify/scripts/leanify_diagnostics.py article.leanify.json \
    [--verified] [--strict] [--prose] [--standard] [--satisfiable] [--pin Compiled.lean] [--relative-to DIR]
```

Prints the findings of a report in editor format: a refuted claim is an error,
an unverified claim and a sentence that did not compile are warnings, and so is
a verified claim that follows a sentence which is not read (`verified as read`). With
`--standard`, a verified step that the standard tactic does not close is a
warning, and with `--satisfiable` a claim whose hypotheses are not shown to
hold together (once for each set of hypotheses). The exit status is 1 if the article changed after it was
certified, if a claim is refuted, with `--verified` if a compiled claim is not
verified, and with `--strict` on any warning. `--pin` updates the pin in the
Lean file instead.

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

Fills in the stubs of `Proofs.lean` that still end in `sorry`. It builds the
article first, and adds a stub for every claim and every set of hypotheses that
`Proofs.lean` does not mention yet (after an edit of the article; `--no-stubs`
leaves the file as it is).

* **Tactics, no model.** For every open claim it tries `leanify_step` first, the
  tactic by which the certificate measures a step: a proof by it is a `standard`
  step. Then it tries a fixed portfolio: it
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

* **Counterexamples.** A claim that no tactic proves may be false. The script
  tries `leanify_counter` on it with simple values and with the numbers of its
  statement (the ends of its ranges), and for a claim that fails there it writes
  `refuteK` in place of the stub, with the values in a comment:
  `claim 2 (line 64) is false as it is read: at x = 1`. Lean checks the
  refutation like a proof (`--no-refute` skips this). A claim that fails as it is
  read is either false or read with a hypothesis missing: both are for the author
  to see.

The last line counts what was proved by the standard tactic, by other tactics and
by the hook, what is false as read, and what is still open.

The stubs `satisfiedK` are filled in the same way: the script tries a few values
for the variables of the statement (`leanify_values 1`, `0`, `2`, `1 2`, …) and,
with a hook, asks it for values (`"kind": "witness"` in the JSON).

A candidate counts only if Lean says that its theorem is proved without `sorry`
(`#print axioms`), so a run that stops early accepts nothing. Nothing is written that Lean has not accepted, and `lake build` checks every
proof again, with the citation audit. Proofs are cached by the statement they
prove (`.lake/leanify-prove/cache.json`), so after an edit only what changed is
proved again. The exit status is 1 if a claim is still open or false as read.

### `leanify_hook.py`

```sh
python .lake/packages/leanify/scripts/leanify_prove.py ARTICLE.tex \
    --hook "python .lake/packages/leanify/scripts/leanify_hook.py --model 'claude -p'"
```

A ready hook for `leanify_prove.py` and `leanify_suggest.py`. It writes the task
that the script gives it as a prompt and passes it to `--model CMD` (or
`$LEANIFY_MODEL`): any command that reads a prompt on its standard input and
prints the answer of a model, such as `claude -p`, `llm -m MODEL`,
`ollama run MODEL`, or a script around the API you use. `--show` prints the
prompt instead. What the model answers is not trusted: Lean checks every proof,
and the check reads every suggested sentence.

### `leanify_auto.py`

```sh
python .lake/packages/leanify/scripts/leanify_auto.py ARTICLE.tex [--model CMD | --hook CMD] \
    [--vocab FIELDS] [--name NAME] [--leanify EXE] [--jobs 4] [--rounds 2]
```

From the article to its certificate in one command, as far as that goes without
you: `leanify certify` (the project and the statements of the present text),
`leanify_prove.py` (tactics, counterexamples and, with `--model` or `--hook`, a
model), `leanify certify` again (the kernel checks every proof that was written),
and `leanify_status.py`. A second run continues where the first stopped. The exit
status is 0 if nothing is left to do.

### `leanify_status.py`

```sh
python .lake/packages/leanify/scripts/leanify_status.py ARTICLE.tex [--all] [--leanify EXE] [--vocab FIELDS]
```

Where the article stands, in the words of its author, not of Lean:

```
article.tex: read by Leanify 0.9.0

What Leanify reads
  50 sentences: 10 read as mathematics, 0 with a finding, 40 running text
  1 definition, 7 claims (3 statements of results, 4 steps of proofs)

Where the claims stand
     3 proved from exactly the sentences and results they cite (3 by routine steps, 0 by a longer Lean argument)
     1 proved by a Lean proof that the text does not spell out
     1 false as read
     2 without a proof
     1 of 1 definition shown to be well defined

What is left to do
  line 64    Theorem thm:bound: the statement is false as Leanify reads it: it fails at x = 1.
             “For every $x\in(0,\infty)$, $f(x)>2$.”
             → Correct the statement (a strict inequality, the end of a range, a missing
             hypothesis). If you meant something else, compare the reading: `leanify check --claims`
             shows claim 2.
  line 77    Corollary cor:min: the statement has no proof yet (claim 5).
             “For every $x\in(0,\infty)$, $f(1)\le f(x)$.”
             → Nothing to do here: it uses claim 2, which is false as read. Correct that one first.
```

Every item names its line, quotes its sentence and says what the author can do.
The steps that are verified but not routine are listed last: nothing is wrong
with them, and an intermediate sentence in the printed proof would make each
routine. For an article without a certificate of its present text, the script
runs the quick check instead (no Lean needed) and says what a certificate would
have to prove: how many claims and definitions, and which sentences are not read
yet. The exit status is 0 if nothing is left to do.

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
| `status` | The margin of every labelled result shows *derived* (every sentence compiled and derived in the text, each step by the standard tactic, under hypotheses that are shown to hold together), *argued* (derived in the text, with a reservation: a step needs a longer Lean proof, or hypotheses are not shown to hold together), *checked* (every sentence compiled and verified), *partly checked*, *compiled* (not yet verified) or *false* (a claim is refuted), read from `\jobname.leanify.tex`. If the article is newer than that file, a warning says the marks may be out of date. |
| `check=false` | No quick check during the compile. |
| `certify` | Before the marks are read, the certificate is built, as by [`leanify certify`](#leanify-certify). The first time, when the article has no Lean files yet, `init` writes them. Implies `status`. |
| `vocab=unitsquare` | The vocabulary of the article, for `check` and `init`. |
| `notions={graph, finite graph}`, `quantities={degree}` | The nouns that the article uses without defining them, and the words that name numbers ([Writing for Leanify](writing.md#notions-that-the-article-does-not-define)). Leanify reads them from the source of the article. Nothing is printed where they are declared; `\leanifyreport` lists them, with the number of results quoted from the literature, and a quoted result has the margin mark *quoted*. |
| `lean=FILE` | The compiled Lean file of the article, by default `Compiled.lean` next to it, or `NAME/Compiled.lean` (`lean/NAME/Compiled.lean`) as `init` writes it in a folder of its own. The module to build is `\leanifymodule`, or else `NS.Certified` for the namespace `NS` that this file compiles. |
| `exe=COMMAND` | The checker to run, instead of the project's or of `leanify` on the `PATH`: a command or a path. |
| `project=false` | An article that lies in no Lean project gets none: it is checked, and nothing is written but the findings. Without this option the checker makes the project, once, in the folder `lean` next to the article ([`leanify tex`](#leanify-tex)). |

**Checking as you compile.** When the compiler may run programs (shell escape:
`pdflatex -shell-escape`, `latexmk -shell-escape`, or the setting of the
editor), every compile runs [`leanify tex`](#leanify-tex) on the article, once.
If the article lies in a Lean project (a `lakefile.toml` or `lakefile.lean` in
its folder or up to three folders above), the checker of that project runs.
Otherwise the executable `leanify` on the `PATH` runs: it needs neither Lean nor
mathlib, so that is enough to check an article while writing
(`.github/workflows/release.yml` builds it for Linux, macOS and Windows when a
version is tagged), and it gives the article its Lean project, the folder `lean`
next to it, where the certificate is built later. Its findings become LaTeX warnings
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
`\jobname.leanify.log`. In a Lean project, `lake` must be on the `PATH` of the
compiler; the first check also builds the checker, which takes a few minutes once.

**Speed.** After the first build the check runs the checker directly, not through
`lake exe` (which first checks that every module of the project, mathlib's
included, is built): a compile then costs the check itself, a fraction of a
second. The executable is used when it is current (newer than the project's
`lake-manifest.json`, or in the Leanify repository newer than the compiler's
sources); otherwise lake rebuilds and runs it. The check writes the same
records for the same article, so the later passes of `latexmk` change nothing
and it stops. With `certify`, the article is compiled to Lean again in about a
second after an edit, then its proofs are checked, and nothing is rebuilt while
the status file is newer than the article and its Lean files.

The status file records which version of the article it is of (the MD5 sum of the
article). If the article has changed since and Leanify did not run in this compile (shell
escape is off, or the checker is not on the PATH), the package warns that the article
as it is now is not checked and that the status is that of the earlier version: an
edited statement is never typeset silently with the marks of the old one.

The package is never silent about an article that it did not check. Without shell
escape, as on arXiv or a journal's server, nothing runs, and a warning says so. With
shell escape on a machine where the checker does not run (no `leanify` on the PATH, for
an article in no Lean project), a warning says what to install: the executable of the
releases checks an article without Lean or mathlib, and sets up the Lean project of the
article (the folder `lean` with its lakefile) itself. An article whose project in `lean`
is built is checked by the checker of that project, the version it requires. Load the
package with `check=false` where the article need not be checked (a submission): no
warning then. Without `status` the typeset article is unchanged, which is what you
submit. Once `leanify.sty` is on CTAN, arXiv and journals have
it; until then, upload it with the article, or leave it out: Leanify reads the
article without it.

## The web reader

```sh
npm ci --prefix .lake/packages/leanify
node .lake/packages/leanify/reader/build.mjs ARTICLE.tex \
    [--out DIR] [--title TITLE] [--bbl FILE.bbl] [--date YYYY-MM-DD] [--home URL] \
    [--proofs FILE.lean,FILE.lean | --no-proofs] [--strict]
```

Writes `DIR/index.html` (default `article-reader/` next to the article) with its
stylesheet, script and fonts, a copy of the article and of its report. The page
renders the article from its source, with the status of every sentence. It
refuses a report whose pin does not match the article. `--home` adds a link
back to a page of yours.

The inspector of a sentence shows, for each of its claims, the formal reading,
the Lean statement and the Lean proof: the declaration that justifies the claim,
with the file and the line, and each lemma of the article's Lean files that it
uses, which opens in place with the lemmas it uses in turn. So a reader gets
from a sentence of the article to the proof that Lean checked without a search.
The proofs are read from `Proofs.lean` of the article's project and the Lean
files beside it (or from `--proofs`). For a refuted claim the inspector says at
which values it fails, if its refutation is by `leanify_counter`.

A command or an environment that the reader does not render is shown as its
source, and named on the terminal; `\today` is the day of the last change of the
file. With `--strict` the reader refuses both instead, as the documentation
site does for its demos.

## Editors and CI

A repository of an article can be certified on GitHub, without Lean on your own
computer, by the workflow that this repository provides:

```yaml
name: Leanify
on: [push, pull_request]
jobs:
  certify:
    uses: Corrram/leanify/.github/workflows/certify.yml@main
    with:
      article: paper/article.tex
      module: Note.Certified
      project: paper/lean        # the folder with lakefile.toml (default: the root)
```

It builds the certificate, prints the status of the article on the summary page
of the run, fails if a claim is refuted or (unless `require-verified: false`)
not verified, and keeps the report, the status file and the web reader as the
artifact `leanify`. With `commit-status: true` (and `permissions: contents:
write` for the job) it commits the report and the status file back to the
branch.

**Overleaf.** Overleaf runs neither Lean nor the checker. The margin marks and `\leanifyreadings` need
neither: `leanify.sty` reads them from `ARTICLE.leanify.tex`. So keep the
article in a GitHub repository, let the workflow above commit the status file
(`commit-status: true`), and synchronize the Overleaf project with the
repository: after a pull in Overleaf, `\usepackage[status,check=false]{leanify}`
shows the marks of the last certified text, and warns if the article has changed
since.

`editors/vscode/tasks.json` has two VS Code tasks, *quick check* (the native
check of the open file) and *certify* (update the pin, build, report), whose
findings appear as squiggles in the `.tex` file. A GitHub Actions workflow that
certifies an article on every push is in
[step 9 of the tutorial](getting-started.md#9-check-in-ci).
