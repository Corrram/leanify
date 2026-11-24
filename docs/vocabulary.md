# The vocabulary, and words with several meanings

Leanify reads an article's words through its *vocabulary*: nouns (`probability
distribution on $\mathbb{N}_0$`), adjectives (`prime`, `even`) and named notions
(`the Poisson distribution with mean $\lambda$`), each with one exact meaning, a
term of Leanify's formula language whose Lean reading is built on Mathlib
(`docs/glossary.md` lists every entry with its meaning and the Mathlib
definitions it rests on).

The same English word means different things in different parts of mathematics:
*normal* (a subgroup, a distribution, a vector, a space), *regular*, *closed*,
*distribution*, *natural number* (with or without 0), *increasing* (strictly or
not), *positive* (in French usage, `≥ 0`). This page explains how Leanify decides
which meaning an article uses.

## The principle: the printed text fixes the meaning

A certificate is only worth something if a reader of the PDF knows what was
certified. So Leanify never takes a meaning from anything the reader cannot see.
There are no hidden per-word annotations in the LaTeX source: an invisible
`\leanifymeaning{normal}{group theory}` would let the PDF say one thing while Lean
checks another, and "this article was leanified" would no longer tell the reader
what its theorems mean.

Every meaning is fixed by one of the following, from the most specific to the
most general; all of them are printed.

1. **The article's own definitions and conventions** come first. Besides its
   definitions (`We call a copula $C$ LTD if …`, `Let $\mathcal C$ denote the
   class of …`) an article can state which meaning it uses, in ordinary sentences:

   * `By a distribution we mean a probability distribution on $\mathbb{N}_0$.`
     (a noun: the article's own class, which takes precedence over any vocabulary
     noun with the same words);
   * `Throughout, increasing means non-decreasing.` (words that stand for other
     words in the following sentences; `strictly increasing` keeps its meaning);
   * `In this paper, positive means non-negative.`;
   * notation: `We write $\mathrm{Poi}(\lambda)$ for the Poisson distribution with
     mean $\lambda$.`, `We write $\mathcal P$ for the set of probability
     distributions on $\mathbb{N}_0$.`, `We write $a\sim b$ if $|a-b|\le1$.`,
     `We write $\langle a,b\rangle$ for $\frac{a+b}{2}$.`

   These are the sentences a careful author writes anyway, and a reader sees them.

2. **The whole phrase.** Leanify matches the longest phrase: *normal
   distribution* and *normal subgroup* are different entries, and neither is the
   adjective *normal*.

3. **The type of what the phrase is about.** An adjective applies to objects of
   one type: `$n$ is even` about an integer and `$f$ is even` about a real
   function are different entries, and the declared type of `n` or `f` (printed:
   `Let $f:\mathbb R\to\mathbb R$ …`) decides. So does the type of a notion's
   argument: `the inverse of $A$` is the inverse of a matrix for a matrix `A` and of a
   permutation for a permutation. A definition whose letter has no type yet says it with a
   noun: `We write $|G|$ for the order of a group $G$.`

4. **The fields the article names.** The vocabulary is divided into fields
   (`numbers`, `unitsquare`, `distributions`, …); within a field every phrase has at
   most one meaning. The article names the fields it uses in its preamble,
   `\usepackage[vocab={numbers,realfunctions}]{leanify}` (or a bundle of them,
   `vocab=analysis`, `vocab=math`), and `\leanifyreport` prints them with the
   verification summary (`Leanify (vocabulary: core, numbers, realfunctions): …`), so
   the printed article states its dictionary. The core
   vocabulary is always used.

5. **Otherwise Leanify refuses.** If the article's fields give a phrase two
   meanings that the steps above do not separate, the sentence is not checked and
   Leanify says so: `"normal" has several meanings (in algebra and probability);
   say which is meant in the text (By a … we mean …)`. It never picks one silently.

Words Leanify does not know are prose: the sentence is reported as not read, and
nothing about it is certified.

One declaration is not in the printed text: the list of the nouns that an article uses
*without* a meaning (`\usepackage[notions={graph}]{leanify}`,
[Writing for Leanify](writing.md#notions-that-the-article-does-not-define)). It gives a
word no meaning, so it cannot change what a sentence means. It says that the word is
left undefined, and `\leanifyreport` and every report list these words.

## Words that are ambiguous in every field

Some words are ambiguous even within one field, and Leanify does not read them
alone, whatever the fields:

* *increasing* and *decreasing* (strictly or not): write *strictly increasing* or
  *non-decreasing*, or state the convention (`Throughout, increasing means
  non-decreasing.`);
* *natural number*: say *non-negative integer* or *positive integer*, or state
  the convention (`By a natural number we mean a non-negative integer.`). The
  symbol $\mathbb{N}$ includes 0, as in Mathlib; $\mathbb{N}_0$ says so explicitly.

## The core vocabulary

Every article is read with the core vocabulary, whatever fields it names: *real
number*, *integer*, *positive*, *negative* and *nonnegative integer*, *rational* and
*irrational number*, and the adjectives *positive*, *negative*, *nonnegative*,
*nonpositive*, *nonzero*, *rational*, *irrational* of a real number. So
`Let $x$ and $y$ be positive real numbers.` needs no field. The words of number
theory (*prime*, *even*, *squarefree*, the greatest common divisor) are the field
`numbers`. A symbol or noun that a field would read is reported with the field's
name: `unknown notation \cosh: the field hyperbolic of the vocabulary reads it`.

## Fields

`docs/glossary.md` lists the fields and their entries; `lake exe glossary`
regenerates it from the vocabulary itself. A field is a Lean value
(`Leanify.Vocab`) in `Leanify/Library/`, registered in
`Leanify.Fields.all`. Fields built from the core formula language (most of them)
need nothing else: their meaning is the meaning of the formula language, which
`Leanify.Denote` gives in terms of Mathlib. A field with constants of its own
(`unitsquare`, `hilbert`, `markov`, `torus`, `complex`, `hyperbolic`, `trigonometry`, and
the fields of other branches below) names the Lean
meaning of each: a declaration of Mathlib (`Real.sinh`), or a definition written for
the field. A function of a field may have a domain (`\arcsin` on `[-1,1]`, in
`trigonometry`): a claim that uses it is meaningful only on the domain.
The field `unitsquare` also makes `[0,1]` a type of its own, with its integral and
Lebesgue measure; without it, `[0,1]` is a set of real numbers like any interval.
A function on the square is integrated against a copula, or any distribution function
on `[0,1]^2` (`\int_{[0,1]^2} f(u,v)\,\mathrm{d}C(u,v)`): the integral for the
probability measure whose distribution function it is. The field has the Markov
product of two copulas (`We write $A*B$ for the Markov product of $A$ and $B$.`) and the
Markov powers of a copula (`C^{\ast k}`), in which results on stationary Markov chains
are stated: the copula of `(X_0,X_k)` is the Markov power of order `k` of the copula of
`(X_0,X_1)`, and the chain is reversible when that copula is symmetric. It also has the sample
of a copula: independent observations `(U_i,V_i)`, each with the copula as distribution
function, their expectation `\mathbb{E}_C[\ldots]` and their probability `P_C(\ldots)`.
A kernel is a square-integrable function of finitely many terms of a sequence in `[0,1]`,
and a statistic is a measurable function of finitely many observations of the sample:
`K_F(C)\coloneqq\mathbb{E}_C[F(U)F(V)]` for a kernel `F`, and `P_C(R(C)\le T(U,V))` for a
statistic `T`. A copula may be symmetric, and it may have a bounded density. A map of the
square may be Borel measurable (`for every Borel measurable function $g:[0,1]^2\to[0,1]$`),
and a statistic may be a function of the first `n` observations.
The field `hilbert` adds, to `unitsquare`, the functions on `[0,1]` as elements of `L^2` and
`L^2_0` (square-integrable, and with integral zero), their inner product `\langle f,g\rangle` and
norm `\lVert f\rVert`, operators on them with their phrases (`$T$ fixes the constants`, `maps
$L^2_0$ into itself with norm at most $1$`, `is $r$ times the identity on $A$`), the powers
`T^k` of an operator, its norm on a subspace `\lVert T|_{L^2_0}\rVert`, tensor powers
`T^{\otimes m}` acting on kernels, and the components `F_S` of the Hoeffding decomposition of a
kernel. These are functions, not classes of functions up to null sets: `\lVert f\rVert` is
`\sqrt{\int_0^1 f^2}` of the function itself. The field `markov` adds, to `hilbert`, the Markov
operator `T_C` of a copula (`We write $T_C$ for the \emph{Markov operator} of $C$.`): the
conditional expectation `(T_Cg)(u)=\mathbb{E}[g(V)\mid U=u]`, an integral against the
conditional distribution of the copula.
Further fields cover other branches of mathematics:

* `arithmetic`: Euler's totient function, the Möbius function, the number and the sums of
  powers of the divisors, the prime-counting function, the `n`th prime, the number of
  prime factors, `p`-adic valuations, multiplicative orders, sums of digits; perfect,
  abundant and deficient numbers, Mersenne primes; multiplicative functions and the
  Dirichlet convolution;
* `combinatorics`: Fibonacci, Catalan, Bell, harmonic and triangular numbers,
  derangements, partitions of integers and of sets, Stirling numbers of both kinds;
* `polynomials`: polynomials as real functions (`p(x)`, `pq`, `p'`), their degree
  (`\deg p`, of a nonzero polynomial), coefficients and real roots; monic, quadratic,
  cubic and irreducible polynomials, polynomials with integer or rational coefficients;
* `graphs`: finite simple graphs on the vertices `1, …, n`, a type of its own: degrees,
  neighbours, distances, the chromatic, clique and independence numbers, components,
  diameter and girth; connected, bipartite, regular, Hamiltonian and triangle-free
  graphs, trees and forests; complete graphs, cycles, paths, `K_{m,n}` and the
  complement `\overline{G}`;
* `permutations`: permutations of `{1, …, n}`, a type of its own, applied to numbers
  (`\sigma(i)`) and composed (`\sigma\tau`, `\sigma^k`): the sign, order, fixed points,
  cycles and inversions; transpositions, cycles, derangements and involutions;
* `matrices`: real `m × n` matrices, a type of its own, with their algebra (`A+B`, `AB`,
  `cA`, `A^k`, `A^{-1}`, `A^\top`), `\det`, `\operatorname{tr}`, `\operatorname{rank}`,
  entries, the characteristic polynomial and the real eigenvalues; symmetric,
  orthogonal, invertible, positive definite, triangular, nilpotent and stochastic
  matrices;
* `special`: the gamma function `\Gamma`, the beta function, the zeta function `\zeta` on
  `(1,∞)`, the Bernoulli numbers, the sinc function, the Euler–Mascheroni constant and
  the golden ratio.

* `realsets` (formerly `topology`): sets of real numbers by a noun (`a nonempty compact set $S$`, `every open
  subset $U$ of $\mathbb{R}$`): open, closed, compact, bounded, connected, dense, nowhere
  dense, perfect, countable, measurable and null sets; closure, interior, boundary, limit
  points, supremum, infimum, diameter, Lebesgue measure; the Cantor set;
* `realfunctions` (formerly `analysis`): real functions by a noun (`a continuous periodic function $f$`): uniformly
  continuous, Lipschitz, differentiable, smooth, analytic, monotone, convex, even, odd,
  periodic, injective, surjective, measurable and integrable functions; the derivative,
  the supremum norm, the Lipschitz constant, the total variation, the range and the zeros;
* `vectors`: real vectors of some dimension, a type of its own: `x+y`, `cx`,
  `\lVert x\rVert`, `\langle x,y\rangle`, coordinates, the cross product, angles;
  unit, orthogonal and parallel vectors;
* `geometry`: points of the Euclidean plane, a type of its own: distances, midpoints,
  areas, perimeters and centroids of triangles, angles, slopes; lines, segments,
  perpendicular bisectors, circles and discs as sets of points;
* `congruences`: `congruent to $b$ modulo $n$`, `coprime to $n$`, quadratic residues and
  the Legendre symbol, primitive roots, inverses modulo `n`;
* `groups`: finite groups, a type of its own, up to isomorphism (`isomorphic to $H$`):
  abelian, cyclic, simple, solvable and nilpotent groups; the order, the exponent, the
  numbers of subgroups, of conjugacy classes and of Sylow subgroups; cyclic, symmetric,
  alternating and dihedral groups, the Klein four-group, direct products;
* `means`: the arithmetic, geometric, harmonic, quadratic, contraharmonic, Heronian,
  centroidal, logarithmic and identric means of two numbers, the power and Lehmer means of
  order `p`, each defined for the numbers its formula needs;
* `densities`: probability densities on the line by a noun (`Let $f$ be a probability
  density.`), symmetric, unimodal and log-concave densities, densities with a finite mean or
  variance; the normal, exponential, uniform, gamma, beta, chi-squared, Cauchy, Laplace,
  logistic, Pareto and Weibull densities with their parameters; the distribution function,
  mean, variance, moments, moment generating function, median and differential entropy;
* `fourier` (with `realfunctions`): the Fourier cosine and sine coefficients of a function
  integrable on `[-π, π]`, the partial sums of its Fourier series and their Fejér means,
  the Dirichlet and Fejér kernels, the Fourier cosine and sine transforms, trigonometric
  polynomials;
* `information` (with `distributions`): the entropy, Rényi and binary entropy, the
  Kullback–Leibler and χ² divergences, the total variation and Hellinger distances and the
  Bhattacharyya coefficient of distributions on `ℕ₀`;
* `optimization` (with `realfunctions`): `$x$ is a [local] minimizer of $f$`, a stationary point,
  a minimizer on `[a,b]`; strongly convex, `$L$-smooth`, coercive and quasiconvex functions,
  functions bounded below or above; the minimum, maximum, infimum and supremum (where they
  exist), the unique minimizer, the convex conjugate, the Moreau envelope and the proximal
  operator;
* `dynamics` (with `realfunctions`): the iterates `f^n` of a map, orbits, fixed and periodic
  points (attracting, repelling, of least period `n`, eventually periodic), the least period
  and the Lyapunov exponent;
* `calculus` (with `realfunctions`): `$n$ times (continuously) differentiable` functions,
  the `n`th derivative and the Taylor polynomial of degree `n` at `a`, antiderivatives,
  critical and inflection points; the arc length, the average value, the area between two
  graphs and the volume of revolution on `[a,b]`;
* `asymptotics` (with `realfunctions`): `asymptotically equivalent to $g$`, `dominated by
  $g$`, `negligible compared to $g$`, `of the same order as $g$`, growth classes, slow and
  regular variation, the limit at infinity;
* `transforms` (with `realfunctions`): the Laplace, Mellin and Stieltjes transforms, the
  convolution and correlations, each defined where its integrand is integrable;
* `topologies`: topologies on `ℝ` by a noun (`Let $\tau$ be a topology on $\mathbb{R}$.`),
  sets that are `$\tau$-open`, `$\tau$-compact`, `dense in $\tau$`; Hausdorff, second
  countable, separable, metrizable topologies, finer and coarser ones; maps continuous
  from `τ` to `σ`, open maps and homeomorphisms; the usual, discrete, indiscrete, cofinite
  and lower limit topologies, generated and subspace topologies, closure and interior;
* `metricspaces` (loads `topologies`): metrics on `ℝ` by a noun, complete, bounded and
  equivalent metrics, sequences `Cauchy with respect to $d$`, isometries and contractions;
  the Euclidean and discrete metrics, the topology a metric induces, balls, the diameter
  and the distance to a set;
* `approximation`: absolute and relative errors, the condition number, rounding, difference
  quotients, the trapezoidal, midpoint and Simpson's rules and Riemann sums, linear and
  Lagrange interpolation, Chebyshev nodes;
* `iteration`: the Newton map, Newton, secant and fixed-point sequences, orders of
  convergence (`quadratically convergent to $y$`), contractive maps;
* `odesolvers`: right-hand sides `f(t, y)`, solutions of an initial value problem, the
  Euler, Heun, midpoint and Runge–Kutta steps and sequences;
* `risk` (with `densities`): the survival function, hazard rate and quantile function of a
  density, the value at risk and the expected shortfall, heavy tails, monotone failure
  rates;
* `stochasticorders` (with `densities`): `$f$ is smaller than $g$ in the hazard rate order`
  and the other classical stochastic orders;
* `finance`: interest and annuities, the Black–Scholes prices and the delta.

`leanify fields article.tex` tries every field on an article and names those that read
more of it, with the line for the preamble.

A *bundle* names several fields (`vocab=probability`, `vocab=algebra`, …), and the bundles
form a tree ([Libraries](libraries.md#the-tree-of-libraries) draws it): `math` has every
field, and its seven *realms* are the branches of mathematics, `analysis`, `algebra`,
`topology`, `numerics`, `stochastic`, `discrete` and `numbertheory`. A bundle has no words
of its own: the article is read with its fields. No two fields of a bundle give a phrase
different meanings, except a notion whose meanings take arguments of different types
(`the inverse of $v$`: of a function, a matrix, a permutation), where the type of the
argument decides (step 3 above); `lake exe glossary --bundles` checks it, and
`tests/bundles.py` that every test article is read with a bundle as with its fields.

Their notions take arguments (`the $n$th Catalan number`, `the degree of $v$ in $G$`),
and an article gives them its notation (`We write $C_n$ for the $n$th Catalan number.`,
`We write $\deg_G(v)$ for the degree of $v$ in $G$.`). A modifier may take a number too:
`a graph $G$ on $n$ vertices`, `a polynomial $p$ of degree $n$`, `a $k$-regular graph`,
`an $n\times n$ matrix`. Notation that is defined for some elements only (`AB` when the
columns of `A` are as many as the rows of `B`, `\sigma\tau` for permutations of the same
degree) makes a claim meaningful only for those, as a domain does.

An article may use several such fields. A field can declare a type of
its own and say what notation means on it (`complex`: `z+w`, `|z|`, `\overline{z}` on
`\mathbb{C}`), as `docs/vocabularies.md` explains.

On the command line, `leanify check article.tex --vocab numbers,realfunctions` and
`leanify init article.tex --vocab numbers,realfunctions` use the same fields;
`leanify.sty` passes its `vocab` option on.
