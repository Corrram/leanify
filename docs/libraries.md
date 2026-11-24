# Libraries

The words of a subject (a copula, a prime, a graph, a Markov chain) come from a *field* of
the vocabulary: a library that an article loads in its preamble,

```latex
\usepackage[vocab={analysis,optimization}]{leanify}
```

as a Python program imports a package. Each field gives its words one meaning in Lean
(a declaration of Mathlib, or a definition written for the field); the
[glossary](glossary.md) lists every word with its meaning. You do not have to know which
fields an article needs:

```sh
leanify fields article.tex
```

tries every field on the article and names those that read more of its sentences, with
the line for the preamble.

## Bundles

If you would rather name your area than its fields, load a bundle:

```latex
\usepackage[vocab=statistics]{leanify}
```

A bundle is a name for several fields, and bundles are made of bundles:

```
statistics
├── probability
│   ├── distributions      distributions on ℕ₀
│   ├── densities          densities on the line
│   └── information        entropy and divergences
└── dependence
    └── markov             copulas, L², Markov operators (with unitsquare and hilbert)

realanalysis
├── functions
│   ├── analysis           real functions
│   ├── optimization       minimizers, conjugates
│   ├── fourier            Fourier series and transforms
│   └── dynamics           iteration
├── topology               sets of real numbers
└── elementary
    ├── special            gamma, beta, zeta
    ├── hyperbolic, trigonometry
    └── means

algebra
├── linearalgebra
│   ├── vectors
│   └── matrices
├── polynomials
└── groups

numbertheory               numbers, arithmetic, congruences
discrete                   combinatorics, permutations, graphs
```

An article with a bundle is read exactly as with its fields: a bundle has no words of its
own. Two rules keep that safe.

* **No phrase has two meanings in a bundle.** Fields can read the same words differently
  (`the order of` a permutation and of a group, `the degree of` a polynomial and of a
  permutation), and Leanify then asks the article which is meant. The fields of a bundle
  do not clash, which a check of the repository enforces, and this is why there is no
  bundle of everything. Where two fields of one area would have clashed, the phrase says
  which object it is about: `the mean of the density $f$` (in `densities`; `the mean of $p$`
  is the mean of a distribution on ℕ₀), `the infimum of the function $f$` (in
  `optimization`; `the infimum of $S$` is that of a set).
* **`statistics` and `dependence` make `[0,1]` a type.** They contain `unitsquare`, with
  which a variable in `[0,1]` is a point of that interval and `\int_0^1` its integral, as
  copulas need. The mathematics is the same, the Lean statements differ. An article
  without copulas can load `probability` instead.

Load the smallest bundle that reads your article: more words in the vocabulary mean more
phrases that your own definitions could shadow. `leanify fields` names the fields an
article needs and, when they belong together, their bundle.

## Fields

| Field | What an article gets | Load with |
| --- | --- | --- |
| [`core`](glossary.md#core) | real numbers, integers, rational numbers, signs; always there | |
| **Probability and statistics** | | |
| [`unitsquare`](glossary.md#unitsquare) | `[0,1]` and the unit square with Lebesgue measure: copulas, distribution functions, probability measures and couplings with uniform marginals, samples `(U_i,V_i)` with `\mathbb{E}_C` and `P_C` | |
| [`hilbert`](glossary.md#hilbert), [`markov`](glossary.md#markov) | `L^2` on `[0,1]`, operators, the Hoeffding decomposition; the Markov operator of a copula | each loads the ones before it |
| [`distributions`](glossary.md#distributions) | probability distributions on `ℕ₀`: Poisson, binomial, negative binomial, point masses, the mean | |
| [`densities`](glossary.md#densities) | probability densities on the line: normal, exponential, uniform, gamma, beta, χ², Cauchy, Laplace, logistic, Pareto, Weibull; distribution function, mean, variance, moments, moment generating function, median, differential entropy | |
| [`information`](glossary.md#information) | entropy, Rényi and binary entropy, Kullback–Leibler and χ² divergences, total variation and Hellinger distances | with `distributions` |
| **Analysis** | | |
| [`analysis`](glossary.md#analysis) | real functions by a noun: continuous, Lipschitz, differentiable, smooth, monotone, convex, periodic, integrable; derivative, supremum norm, total variation | |
| [`topology`](glossary.md#topology) | sets of real numbers: open, closed, compact, connected, dense, countable, null; closure, interior, supremum, Lebesgue measure | |
| [`optimization`](glossary.md#optimization) | minimizers and stationary points, strongly convex and `L`-smooth functions; minimum, infimum, convex conjugate, Moreau envelope, proximal operator | with `analysis` |
| [`fourier`](glossary.md#fourier) | Fourier coefficients, partial sums and Fejér means, Dirichlet and Fejér kernels, cosine and sine transforms | with `analysis` |
| [`dynamics`](glossary.md#dynamics) | iterates, orbits, fixed and periodic points and their stability, least period, Lyapunov exponent | with `analysis` |
| [`special`](glossary.md#special) | gamma, beta and zeta functions, Bernoulli numbers, sinc, Euler–Mascheroni constant, golden ratio | |
| [`hyperbolic`](glossary.md#hyperbolic), [`trigonometry`](glossary.md#trigonometry) | `\sinh`, `\cosh`, `\tanh`; `\arcsin`, `\arccos`, `\arctan`, `\cot` with their domains | |
| [`means`](glossary.md#means) | arithmetic, geometric, harmonic, quadratic, logarithmic, identric, power and Lehmer means of two numbers | |
| [`torus`](glossary.md#torus) | smooth functions on `𝕋²`, `C^m` norms, directional derivatives | |
| [`complex`](glossary.md#complex) | the complex numbers, a type of its own with its arithmetic | |
| **Number theory and combinatorics** | | |
| [`numbers`](glossary.md#numbers) | primes, divisibility, parity, the greatest common divisor | |
| [`arithmetic`](glossary.md#arithmetic) | Euler's totient, the Möbius function, divisor functions, the prime-counting function, `p`-adic valuations | |
| [`congruences`](glossary.md#congruences) | congruences modulo `n`, quadratic residues, the Legendre symbol, primitive roots | |
| [`combinatorics`](glossary.md#combinatorics) | Fibonacci, Catalan, Bell and harmonic numbers, derangements, partitions, Stirling numbers | |
| [`permutations`](glossary.md#permutations) | permutations of `{1, …, n}`: sign, order, cycles, inversions | |
| [`graphs`](glossary.md#graphs) | finite simple graphs: degrees, distances, chromatic and clique numbers, trees, complete and bipartite graphs | |
| **Algebra and geometry** | | |
| [`polynomials`](glossary.md#polynomials) | real polynomials: degree, coefficients, roots | |
| [`vectors`](glossary.md#vectors) | real vectors: norms, inner products, coordinates, angles | |
| [`matrices`](glossary.md#matrices) | real matrices: determinant, trace, rank, inverse, eigenvalues; symmetric, orthogonal, positive definite | |
| [`groups`](glossary.md#groups) | finite groups up to isomorphism: abelian, cyclic, simple, solvable; Sylow subgroups; cyclic, symmetric, alternating and dihedral groups | |
| [`geometry`](glossary.md#geometry) | points of the Euclidean plane: distances, triangles, lines, circles | |

## Not yet

Sample statistics (the sample mean and variance, empirical distribution functions,
estimators and tests) have no field yet: they need a sample as a sequence of numbers,
and the grammar does not yet bind an infinite sequence whose terms are written `a_n`
([roadmap](roadmap.md)). Rank statistics of a sample from a copula are read with
`unitsquare` (`P_C(\tau_n\le t)`).

A field is a file of data in `Leanify/Library/`; [Vocabularies and
models](vocabularies.md) says how to write one.
