# Status and next constructions

## Where the exemplars stand

| Article | Definitions | Claims | Verified | Not read yet |
| --- | ---: | ---: | ---: | --- |
| Blest (`Papers/Rockel2026ExactBlest/Source`) | 37 | 48 | 48 | Lemmas 2.1, 2.2 and 4.2, the last two sentences of Corollary 4.6 |
| Rho-gamma (`Papers/AnsariRockelSteinmassl2026RhoGamma/Source`) | 11 | 8 | 8 | the parametrization `G`, `P` of Theorem 1.1, the lemmas of Sections 3–5 |

Every result of the first article whose statement uses only the article's own
definitions and the vocabulary is compiled and certified: Theorems 1.1 and 1.2,
Lemmas 3.1 and 4.1, Propositions 4.3 and 4.4, Corollaries 3.2 (with its proof,
sentence by sentence) and 4.5. What remains needs constructions the grammar does
not have yet. A third research article, checked as it was written, showed most
of the items below as well.

## Next constructions

1. **Random pairs and expectations under a coupling.** "If $(X,Z)$ follows the
   coupling $\gamma$, then $\alpha(F)=12\,\E[XZ]-3$", "Every $\gamma\in\Gamma$
   satisfies $\E_\gamma[c(X,Z)]\le\int_0^1\varphi+\int_0^1\psi$". Reading:
   `E_γ[f(X,Z)]` is the integral of `f` against the measure `γ`, and "the
   coupling associated with `F`" is a definite description.
2. **Results that quantify over functions with properties.** "Let
   $c:[0,1]^2\to\R$ and $\varphi,\psi:[0,1]\to\R$ be continuous functions such
   that …", "let $f:[0,1]\to\R$ be bounded and nondecreasing". Binders of
   function type with hypotheses, and finite sets (`N_1, N_2`).
3. **Arbitrary probability spaces.** "random variables on the same probability
   space" quantifies over all probability spaces, which needs a vocabulary whose
   model is parametric in the space.
4. **Anaphora to extremizers.** "For $n=-1$, this NOUN is $W$.", and the
   identification of a maximizer as `A_w^\top` or `B_b^\top`.
5. **A definition whose hypothesis speaks about other variables.** A definition made
   under hypotheses takes those about its own variables
   ([Writing for Leanify](writing.md#hypotheses-assumptions-cases-contradictions)).
   One that also speaks about a variable the definition does not use (`Assume
   $xz\ne0$. Set $y\coloneqq\frac1x$.`) is not taken.
6. **Parametric families defined by a construction**, such as the extremizers
   `F_\theta` of the second article (Section 3, `def:extremizers`), which
   Theorem 1.1 uses through `G(\theta)` and `P(\theta)`.
7. **Markov kernels.** A notion such as "We call a NOUN $F$ \emph{NAME} if its
   Markov kernel can be chosen such that, for every $v\in(0,1)$, the map
   $t\mapsto K_F(t,[0,v])$ is non-increasing." is a notion in the running text,
   which the grammar reads, but its condition needs the kernel `K_F` in the
   vocabulary, as a kernel determined up to null sets, with "can be chosen such
   that" read as an existential over its versions.
8. **Partial derivatives.** `\partial_1F(u,v)` in a definition, with its
   definedness condition (the partial derivative exists almost everywhere).
9. **Attainment and equality cases.** "the upper bound is attained by $S_s$ and by
   no other NOUN", "with equality if and only if …", "occur only at
   $\alpha=\frac{5}{32}$".

Each construction gets one documented reading in `Leanify/Grammar.lean` and
`Leanify/Doc.lean`, an example in `docs/writing.md`, and an exemplar sentence
that compiles and is certified.

## Beyond constructions

These points limit what a certificate says. None of them is a construction of the
grammar.

1. **Organizing prose.** One sentence of a proof without a reading makes the
   proof incomplete, and its result is then checked, not derived. A few
   sentences that only organize a proof are read as such (`We distinguish two
   cases:`, `We argue by induction on $n$.`); most are not. The check counts the
   complete proofs.
2. **The size of a step.** The certificate tries one fixed tactic,
   `leanify_step`, on every derived step and reports the steps it closes as
   *standard*; a result with another step is *argued*. What a careful reader
   accepts as one step is wider than what the tactic closes (a rule for real
   powers, a known inequality, a compactness argument in a line, the induction
   principle): a list of named standard facts that a step may use without the
   label of an argument is open.
3. **Statements and steps that hold for an empty reason.** For every set of
   hypotheses under which a claim is made the reports say whether they are shown
   to hold together (`satisfiedK`). The definitions of the article are not
   covered yet: a notion that no object satisfies makes every statement about it
   true.
4. **Defaults of the grammar.** Where a limit, a sum, a set or a threshold
   states no domain, the letters `n`, `m`, `k`, `j`, `i`, `N`, `M`, `K` are
   integers and every other letter is a real number. A convention sentence
   declares further letters to be integers (`Throughout, $p$ and $q$ denote
   integers.`), counting the elements of a set whose letter has no stated domain
   is refused, and `\leanifyreadings` prints the convention. Declaring an index
   letter to be a real number, or a letter to be a prime or a positive integer,
   is not read yet.
5. **Readings in the PDF name the vocabulary of the package option.** The
   vocabulary an article is compiled with is named in its Lean file, and
   `\leanifyreport` prints the option `vocab` of `leanify.sty`. The two should be
   one.
6. **The trust in the compiler.** By default the compiler is run by Lean's
   evaluator, and `leanify audit` has the kernel evaluate it. What stays trusted
   in both cases is the grammar: it says what a sentence means. The readings it
   gives are printed, and a second, independent reader of the same grammar would
   be the next step.
7. **Inverse functions and other partial functions of a field.** A symbol of a field
   is a total function (`\sinh`). A function with a domain (`\arcsin` on `[-1,1]`)
   needs the domain in the field's data, as an article's own definitions have it.

