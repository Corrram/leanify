---
hide:
  - navigation
  - toc
---

<div class="pr-hero" markdown>

# Leanify

<p class="pr-lead">Add one line to your LaTeX article. Leanify reads its definitions, theorems and
proofs as Lean statements, tells you where a sentence is ambiguous, and has Lean's kernel
check the rest.</p>

[Quick start](quickstart.md){ .md-button .md-button--primary }
[See the live demo](demo.md){ .md-button }

</div>

A formalization usually lives next to a paper: someone translates the theorems to Lean by
hand, and a reader has to trust that the Lean statement is the theorem of the paper.
Leanify removes the second text. The formal statement is computed from the sentence of
the article, by a fixed grammar, so the paper you submit is the thing that is checked.

## Three steps

<div class="grid cards" markdown>

-   :material-numeric-1-circle:{ .lg .middle } **Compile the article as it is**

    ---

    `\usepackage{leanify}`, and compile. Every sentence of a result that has no
    single reading, and every symbol that nothing defines, is a LaTeX warning at
    its line.

-   :material-numeric-2-circle:{ .lg .middle } **Remove the ambiguities**

    ---

    Small edits: a missing domain, a quantifier, a typo. The article stays
    ordinary mathematical English, and you can read what each theorem now says
    formally.

-   :material-numeric-3-circle:{ .lg .middle } **Have the statements proved**

    ---

    Leanify writes one Lean obligation per definition and claim. You, or a
    model, prove them. Lean accepts a proof or it does not, and a false theorem
    is refuted.

</div>

The first two steps need no knowledge of Lean, and they already find mistakes: the
[tutorial](getting-started.md) draft has four, of the kind that reach referees.

## From a sentence to a theorem

<div class="pr-pair" markdown>
<div markdown>

The article

```latex
Define $f:(0,\infty)\to\mathbb{R}$ by
$f(x)\coloneqq x+\frac1x$.

\begin{theorem}\label{thm:bound}
For every $x\in(0,\infty)$, $f(x)\ge2$.
\end{theorem}
```

</div>
<div markdown>

compiles to

```lean
def f : ℝ → ℝ := fun x => x + 1 / x

-- f is defined on (0,∞), where 1/x makes sense
def wellDefined0 : Prop := ∀ (x : ℝ), 0 < x → ¬x = 0

def claim2 : Prop := ∀ (x : ℝ), 0 < x → 2 ≤ f x
```

</div>
</div>

The theorem's proof compiles sentence by sentence, so Lean derives `claim2` from
exactly the steps of that proof and the lemma they cite, and each step from what
it rests on. A draft that said `$f(x)>2$` is refuted at `x = 1`, and the reader,
the diagnostics and the margin of the PDF mark it false.

## What you get

<div class="grid cards pr-two" markdown>

-   :material-spellcheck:{ .lg .middle } **Feedback while you write**

    ---

    Every compile checks the article in about a second: undefined symbols,
    statements without a reading, and the formal reading of every claim, as
    warnings in your editor.

-   :material-certificate-outline:{ .lg .middle } **A certificate**

    ---

    `lake build` has the kernel check every definition, claim and proof step.
    Certify while proofs are still `sorry`, and refute claims that are false as
    stated.

-   :material-file-document-outline:{ .lg .middle } **The paper, unchanged**

    ---

    The same `.tex` file typesets as before. `\usepackage[status]{leanify}`
    adds the status of every result in the margin.

-   :material-web:{ .lg .middle } **A reader for your readers**

    ---

    A web page of the article with a marker at every sentence: its status,
    formal reading, Lean statement, premises and justification.
    [Try it](demo.md).

</div>

## Words of your subject

An article does not define a probability measure, a prime or a graph. Such words come
from a *vocabulary*, which the article loads as a program loads a library:

```latex
\usepackage[vocab=unitsquare]{leanify}   % copulas and couplings on the unit square
```

The vocabularies form a tree: `vocab=math` loads them all, and its seven realms load a
branch, `analysis` (real functions and sets, calculus, asymptotics, transforms, Fourier
series, optimization, dynamics, special functions), `algebra` (vectors, matrices,
polynomials, groups), `topology` (topologies and metrics on the line, plane geometry),
`numerics` (approximation, quadrature, iterative methods, ODE solvers), `stochastic`
(probability on the unit square, on the natural numbers and by densities, information,
risk measures, stochastic orders, finance), `discrete` (combinatorics, permutations,
graphs) and `numbertheory`; `leanify fields article.tex` says which ones an article
needs. Each one gives its words a meaning in mathlib, and some add proved
facts about them. [All libraries](libraries.md) · [Vocabularies and models](vocabularies.md) ·
[Glossary](glossary.md)

## On the command line

```sh
leanify check article.tex --claims   # what Leanify reads, in a second
leanify certify article.tex          # the Lean project, the obligations, the certificate
```

The [quick start](quickstart.md) is the short way in. The [tutorial](getting-started.md)
takes a one-page note from a draft with four mistakes to a certificate, with the real
output of every step.

## Research articles

Two published articles are compiled from their LaTeX sources in
[lean-verifications](https://github.com/Corrram/lean-verifications):

* *Rank weighting and asymmetry in Blest's rank correlation: two exact regions*
  ([arXiv:2609.27634](https://arxiv.org/abs/2609.27634)): 37 definitions and 48
  claims, all certified. The proof of Corollary 3.2 is checked sentence by
  sentence against what it cites.
  [Source](https://github.com/Corrram/lean-verifications/tree/main/Papers/Rockel2026ExactBlest/Source)
* *The exact region determined by Spearman's rho and Gini's gamma*
  ([arXiv:2609.19890](https://arxiv.org/abs/2609.19890)): 11 definitions and 8
  claims, all certified.
  [Source](https://github.com/Corrram/lean-verifications/tree/main/Papers/AnsariRockelSteinmassl2026RhoGamma/Source)

What the grammar reads today, and what comes next, is in
[Status and roadmap](roadmap.md).
