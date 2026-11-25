# Libraries

The words of a subject (a copula, a prime, a graph, a topology, a quadrature rule) come from
a *field* of the vocabulary: a library that an article loads in its preamble,

```latex
\usepackage[vocab={realfunctions,optimization}]{leanify}
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

## The tree of libraries

Fields are grouped into *bundles*, and bundles into bundles, so that an article can name a
branch of mathematics instead of its fields. At the top is `math`, with every field; below
it are seven *realms*, the branches of mathematics:

```latex
\usepackage[vocab=math]{leanify}         % everything
\usepackage[vocab=analysis]{leanify}     % a realm
\usepackage[vocab=probability]{leanify}  % an area inside a realm
```

```
math
├── analysis                      real analysis
│   ├── realfunctions             real functions: continuity, derivatives, integrals
│   ├── realsets                  sets of real numbers: open, compact, measure
│   ├── calculus                  higher derivatives, Taylor polynomials, arc length, areas
│   ├── series                    summability, sums of series and power series, limits of sequences
│   ├── integration               L^p norms, essential supremum, improper integrals
│   ├── optimization              minimizers, convex conjugates, proximal operators
│   ├── asymptotics               O, o, ~ at infinity; regular variation
│   ├── transforms                Laplace, Mellin, Stieltjes transforms; convolution
│   ├── fourier                   Fourier series, kernels, cosine and sine transforms
│   ├── dynamics                  iterates, fixed and periodic points
│   ├── functionalequations       Cauchy's and Jensen's equations, subadditivity, homogeneity
│   ├── convexity                 log-, harmonically, s-, h-convex functions; Hermite–Hadamard
│   ├── fractional                Riemann–Liouville, Hadamard, Caputo; Mittag-Leffler
│   ├── summability               Cesàro and Abel summability, sequences
│   ├── integralequations         Volterra, Fredholm and Abel equations
│   ├── classicalpdes             heat, wave, transport, Laplace, Burgers
│   ├── elementary
│   │   ├── special               gamma, beta, zeta
│   │   ├── hyperbolic, trigonometry
│   │   ├── means                 the classical means of two numbers
│   │   ├── orthogonalpolynomials Legendre, Hermite, Laguerre, Chebyshev
│   │   └── higherfunctions       erf, Bessel, incomplete gamma, Lambert W, Li₂, Fresnel
│   ├── complex                   the complex numbers
│   └── torus                     functions on the torus
├── algebra
│   ├── linearalgebra
│   │   ├── vectors
│   │   └── matrices
│   ├── polynomials
│   └── groups                    finite groups
├── topology                      topology and geometry
│   ├── realsets                  (also in analysis)
│   ├── topologies                topologies on ℝ: open, compact, Hausdorff, continuous maps
│   ├── metricspaces              metrics on ℝ: balls, Cauchy sequences, completeness (with topologies)
│   ├── geometry                  the Euclidean plane
│   ├── planegeometry             lines, triangle centres, conics (with geometry)
│   └── curves                    curvature, length and area of plane and polar curves
├── numerics                      numerical mathematics
│   ├── approximation             errors, conditioning, difference quotients, quadrature, interpolation
│   ├── iteration                 Newton's method, fixed-point iteration, orders of convergence
│   ├── odesolvers                initial value problems; Euler, Heun, Runge–Kutta
│   ├── matrixnorms               matrix norms, condition numbers, diagonal dominance (with matrices)
│   └── descent                   Armijo and Wolfe steps; gradient descent, heavy-ball, proximal point
├── stochastic                    probability and statistics
│   ├── statistics
│   │   ├── probability
│   │   │   ├── distributions     distributions on ℕ₀ (Poisson, binomial, geometric, …)
│   │   │   ├── densities         densities on the line
│   │   │   ├── information       entropy and divergences
│   │   │   ├── risk              survival, hazard rate, value at risk, expected shortfall
│   │   │   ├── stochasticorders  usual, hazard rate, likelihood ratio, convex orders
│   │   │   ├── markovchains      transition matrices, stationary distributions (with matrixnorms)
│   │   │   └── branching         Galton–Watson processes, extinction probabilities
│   │   ├── samples               sample mean, variance, order statistics, correlation
│   │   ├── timeseries            autocovariance, moving averages, differences, smoothing
│   │   ├── testing               z- and t-statistics, p-values, quantiles, chi-squared
│   │   └── dependence
│   │       └── copulas           copula families, Spearman's rho, Kendall's tau, Chatterjee's xi
│   │                             (with markov: L², Markov operators; hilbert; unitsquare)
│   ├── finance                   interest, annuities, Black–Scholes
│   ├── utility                   expected utility, risk aversion, certainty equivalents
│   ├── economics                 elasticities, production functions, Lorenz curves, Gini
│   ├── queues                    M/M/1, Erlang B and C, Pollaczek–Khinchine
│   └── reliability               series, parallel, k-out-of-n systems; MTTF
├── discrete                      discrete mathematics
│   ├── combinatorics
│   ├── counting                  subsets, maps, surjections, compositions, lattice paths
│   ├── permutations
│   ├── graphs
│   ├── recurrences               progressions, Fibonacci and linear recurrences
│   └── codes                     binary words, Hamming distance, coding bounds
└── numbertheory
    ├── numbers                   primes, divisibility, parity
    ├── arithmetic                arithmetic functions
    ├── congruences               arithmetic modulo n
    ├── specialnumbers            twin and Fermat primes, perfect powers, figurate numbers
    ├── continuedfractions        convergents, badly approximable and Liouville numbers
    └── digits                    base-b digits, palindromes, digital roots, repunits
```

A field may sit in two places (`realsets` is in `analysis` and in `topology`); a bundle has
no words of its own, and an article that names one is read exactly as if it had named its
fields. `lake exe glossary --bundles` checks the tree: every field is in a realm, and no
phrase has two meanings in a bundle.

### Words with a meaning in several fields

Fields can read the same words differently. Inside a bundle this is allowed in one case
only: a notion whose meanings take arguments of different types, as mathematics overloads
its words. `the inverse of $v$` is the inverse of a real function in `realfunctions`, of a
matrix in `matrices` and of a permutation in `permutations`; `the order of $v$` is that of
a group and of a permutation. In a formula or a sentence the type of the argument decides,
as the type of an object decides between adjectives (`$n$ is even`, `$f$ is even`):

```latex
Let $A$ be an invertible $n\times n$ matrix. Then the inverse of $A$ is invertible.
```

A definition `We write $|G|$ for the order of $G$.` names a letter that has no type yet,
so in a bundle with both meanings it says which kind of object it is about, with a noun
before the letter:

```latex
We write $|G|$ for the order of a group $G$.
We write $\operatorname{ord}(\sigma)$ for the order of a permutation $\sigma$.
```

Otherwise Leanify says so and does not read the sentence. `glossary --bundles` lists these
words (`inverse of`, `order of`, `degree of`, `diameter of`, `complement of`, `distance
between … and`, `distance from … to`). Every other phrase has one meaning in each bundle;
where two fields of one area would have clashed, the phrase says what it is about: `the
mean of the density $f$` (in `densities`; `the mean of $p$` is that of a distribution on
ℕ₀), `the infimum of the function $f$` (in `optimization`; `the infimum of $S$` is that of
a set).

### Loading `math`

`math` reads every article that its fields read, with three differences, all printed in
the report:

* **More words are known.** A sentence that used a word of a field the article did not
  name is read now. This is the point of `math`.
* **Letters that a field reserves are that field's.** `special` makes `\Gamma(x)` and
  `\zeta(s)` its functions, `matrices` makes `A^\top` a transpose: an article that uses
  `\zeta` for a number of its own names the realms it needs instead of `math`. (A letter
  that the article defines by a formula, `$C^\top(u,v)\coloneqq C(v,u)$`, stays the
  article's.)
* **`[0,1]` is a type.** `math` contains `unitsquare` (through `stochastic` and `copulas`), with which a
  variable in `[0,1]` is a point of that interval and `\int_0^1` its integral, as copulas
  need. The mathematics is the same, the Lean statements differ. The same holds for
  `stochastic`, `statistics` and `dependence`; an article without copulas loads
  `probability` instead.

Load the smallest bundle that reads your article: fewer words in the vocabulary mean fewer
phrases that your own definitions could shadow, and a faster check. `leanify fields` names
the fields an article needs and, when they belong together, their bundle.

### Renamed fields

The fields `analysis` and `topology` of earlier versions are now `realfunctions` and
`realsets`, and the names `analysis` and `topology` are realms that contain them. An
article that loaded `vocab=analysis` reads the same with the realm (it has more words, no
other meanings); one that wants exactly the old field writes `vocab=realfunctions`. The
bundles `functions` and `realanalysis` are the realm `analysis`.

## Fields

| Field | What an article gets | Load with |
| --- | --- | --- |
| [`core`](glossary.md#core) | real numbers, integers, rational numbers, signs; always there | |
| **Analysis** (`analysis`) | | |
| [`realfunctions`](glossary.md#realfunctions) | real functions by a noun: continuous, Lipschitz, differentiable, smooth, monotone, convex, periodic, integrable; derivative, supremum norm, total variation, inverse | |
| [`realsets`](glossary.md#realsets) | sets of real numbers: open, closed, compact, connected, dense, countable, null; closure, interior, supremum, Lebesgue measure | |
| [`calculus`](glossary.md#calculus) | `$n$ times (continuously) differentiable`; the `n`th, second and third derivative, Taylor polynomials, antiderivatives, critical and inflection points; arc length, average value, area between graphs, volume of revolution | with `realfunctions` |
| [`series`](glossary.md#series) | summable, absolutely and conditionally summable, square-summable and alternating sequences of terms; the sum and partial sums of a series, the Cauchy product, power series and their radius of convergence, geometric series; the limit, limit superior and limit inferior of a sequence | with `realfunctions` |
| [`integration`](glossary.md#integration) | `$p$-integrable`, locally integrable and essentially bounded functions; the `L^p` norm, the essential supremum, the Hölder conjugate, improper integrals to infinity and over the line, the integral on a set | with `realfunctions`, `realsets` |
| [`optimization`](glossary.md#optimization) | minimizers and stationary points, strongly convex and `L`-smooth functions; minimum, infimum, convex conjugate, Moreau envelope, proximal operator | with `realfunctions` |
| [`asymptotics`](glossary.md#asymptotics) | asymptotically equivalent, dominated by (`O`), negligible compared to (`o`), of the same order (`Θ`); polynomial and exponential growth; slowly and regularly varying; the limit at infinity | with `realfunctions` |
| [`transforms`](glossary.md#transforms) | Laplace, Mellin and Stieltjes transforms, convolution, cross-correlation, autocorrelation; of exponential order, causal | with `realfunctions` |
| [`fourier`](glossary.md#fourier) | Fourier coefficients, partial sums and Fejér means, Dirichlet and Fejér kernels, cosine and sine transforms | with `realfunctions` |
| [`dynamics`](glossary.md#dynamics) | iterates, orbits, fixed and periodic points and their stability, least period, Lyapunov exponent | with `realfunctions` |
| [`functionalequations`](glossary.md#functionalequations) | additive (Cauchy), subadditive and superadditive, midpoint convex and concave, Jensen-affine, multiplicative on the reals, logarithmically additive, involutive, idempotent, homogeneous of degree `k` and positively homogeneous functions; solutions of d'Alembert's equation | |
| [`convexity`](glossary.md#convexity) | log-convex, harmonically convex and concave, geometrically and GA-convex, star-shaped, quasiconcave, `$s$-convex in the second sense`, `$h$-convex`, Wright-convex functions, P-functions and Godunova–Levin functions; the integral mean on `[a,b]`, the Hermite–Hadamard gap, the Jensen gap | |
| [`fractional`](glossary.md#fractional) | left- and right-sided Riemann–Liouville fractional integrals, the Hadamard fractional integral, Riemann–Liouville and Caputo fractional derivatives of order in `(0,1)`, the gamma function, the one- and two-parameter Mittag-Leffler functions | |
| [`summability`](glossary.md#summability) | Cesàro and Abel summable sequences, convergent, null, Cauchy, eventually nondecreasing and bounded-variation sequences, subadditive and log-concave sequences; Cesàro means, arithmetic means, the Abel sum, forward differences | |
| [`integralequations`](glossary.md#integralequations) | solutions of Volterra and Fredholm equations of the second kind (and homogeneous ones) and of Abel's equation; symmetric kernels and kernels of Volterra type; the second iterated kernel, the integral operator | |
| [`classicalpdes`](glossary.md#classicalpdes) | solutions of the heat, wave, transport, Laplace and Burgers equations in one space dimension, harmonic functions of two variables; partial derivatives, the heat kernel, d'Alembert's solution | |
| [`special`](glossary.md#special) | gamma, beta and zeta functions, Bernoulli numbers, sinc, Euler–Mascheroni constant, golden ratio | |
| [`hyperbolic`](glossary.md#hyperbolic), [`trigonometry`](glossary.md#trigonometry) | `\sinh`, `\cosh`, `\tanh`; `\arcsin`, `\arccos`, `\arctan`, `\cot` with their domains | |
| [`orthogonalpolynomials`](glossary.md#orthogonalpolynomials) | the Legendre, Hermite (physicists' and probabilists'), Laguerre and Chebyshev (first and second kind) polynomials of degree `n` | |
| [`higherfunctions`](glossary.md#higherfunctions) | the error and complementary error functions, Bessel and modified Bessel functions of the first kind of integer order, the lower incomplete gamma function, the Lambert W function, the dilogarithm, the sine integral, the Fresnel integrals, Dawson's function | |
| [`means`](glossary.md#means) | arithmetic, geometric, harmonic, quadratic, logarithmic, identric, power and Lehmer means of two numbers | |
| [`complex`](glossary.md#complex) | the complex numbers, a type of its own with its arithmetic | |
| [`torus`](glossary.md#torus) | smooth functions on `𝕋²`, `C^m` norms, directional derivatives | |
| **Algebra** (`algebra`) | | |
| [`vectors`](glossary.md#vectors) | real vectors: norms, inner products, coordinates, angles | |
| [`matrices`](glossary.md#matrices) | real matrices: determinant, trace, rank, inverse, eigenvalues; symmetric, orthogonal, positive definite | |
| [`polynomials`](glossary.md#polynomials) | real polynomials: degree, coefficients, roots | |
| [`groups`](glossary.md#groups) | finite groups up to isomorphism: abelian, cyclic, simple, solvable; Sylow subgroups; cyclic, symmetric, alternating and dihedral groups | |
| **Topology and geometry** (`topology`) | | |
| [`topologies`](glossary.md#topologies) | topologies on `ℝ`: `$\tau$-open`, `-closed`, `-compact`, `-connected`, `-dense`; Hausdorff, second countable, separable, metrizable, finer and coarser; continuous, open maps and homeomorphisms between topologies; convergent sequences; the usual, discrete, indiscrete, cofinite and lower limit topologies, generated and subspace topologies; closure, interior, boundary | |
| [`metricspaces`](glossary.md#metricspaces) | metrics, pseudometrics and ultrametrics on `ℝ`: complete, bounded, (strongly) equivalent; Cauchy and convergent sequences, isometries, contractions; the Euclidean and discrete metrics, the induced topology, balls, diameter, distance to a set | loads `topologies` |
| [`geometry`](glossary.md#geometry) | points of the Euclidean plane: distances, triangles, lines, circles | |
| [`planegeometry`](glossary.md#planegeometry) | the distance from a point to a line, feet of perpendiculars, reflections; circumcentre, incentre, orthocentre, circumradius and inradius of a triangle; ellipses, hyperbolas and parabolas by their foci, eccentricity | loads `geometry` |
| [`curves`](glossary.md#curves) | the speed, signed curvature, length and signed area of a curve with coordinate functions `x`, `y`; regular and singular points; the curvature and radius of curvature of a graph; the area and length of a polar curve | |
| **Numerical mathematics** (`numerics`) | | |
| [`approximation`](glossary.md#approximation) | absolute and relative errors, the condition number, rounding, machine epsilon; forward, backward, central and second difference quotients; trapezoidal, midpoint and Simpson's rules (simple and composite), Riemann sums; linear and Lagrange interpolation, Chebyshev nodes | with `realfunctions` |
| [`iteration`](glossary.md#iteration) | the Newton map, secant step and relaxation; Newton, secant and fixed-point sequences; convergent with order `p`, linearly, superlinearly, quadratically, cubically; contractive maps | with `realfunctions` |
| [`odesolvers`](glossary.md#odesolvers) | right-hand sides `f(t, y)`, Lipschitz in the second variable; solutions of a differential equation and of an initial value problem, of linear equations of order two with constant coefficients and of the logistic equation; Euler, Heun, midpoint and Runge–Kutta steps and sequences | with `realfunctions` |
| [`matrixnorms`](glossary.md#matrixnorms) | Frobenius norm, maximum absolute row and column sums, condition numbers; strictly diagonally dominant, tridiagonal, upper Hessenberg, banded and entrywise nonnegative matrices | loads `matrices` |
| [`descent`](glossary.md#descent) | Armijo and Wolfe steps, descent directions; gradient descent, heavy-ball (Polyak) and proximal point sequences of a differentiable function | |
| **Probability and statistics** (`stochastic`) | | |
| [`unitsquare`](glossary.md#unitsquare) | `[0,1]` and the unit square with Lebesgue measure: copulas, distribution functions, probability measures and couplings with uniform marginals, samples `(U_i,V_i)` with `\mathbb{E}_C` and `P_C` | |
| [`hilbert`](glossary.md#hilbert), [`markov`](glossary.md#markov) | `L^2` on `[0,1]`, operators, the Hoeffding decomposition; the Markov operator of a copula | each loads the ones before it |
| [`copulas`](glossary.md#copulas) | the independence, comonotonicity and countermonotonicity copulas; Clayton, Gumbel, Frank, FGM, Ali–Mikhail–Haq, Cuadras–Augé, Marshall–Olkin and Gaussian copulas; Spearman's rho, Kendall's tau, Blomqvist's beta, Spearman's footrule, Gini's gamma, Chatterjee's xi, tail dependence coefficients; positively and negatively quadrant dependent, radially symmetric, left tail decreasing, max-stable; the concordance order | loads `markov` |
| [`distributions`](glossary.md#distributions) | probability distributions on `ℕ₀`: Poisson, binomial, negative binomial, geometric, Bernoulli, discrete uniform, hypergeometric, point masses; the mean, the variance, the probability generating function | |
| [`samples`](glossary.md#samples) | the first `n` terms of a sequence as a sample: sample mean, variance and standard deviation, moments, the empirical distribution function, order statistics, median and range, sample covariance and correlation, least-squares slope and intercept | |
| [`timeseries`](glossary.md#timeseries) | the sample autocovariance and autocorrelation at a lag, moving averages, cumulative sums, difference sequences and seasonal differences, exponential smoothing; autoregressive sequences of order one and random walks | |
| [`testing`](glossary.md#testing) | the z- and t-statistics of a sample for a mean, one- and two-sided p-values, standard normal quantiles, the margin of error at a confidence level, Pearson's chi-squared statistic | |
| [`densities`](glossary.md#densities) | probability densities on the line: normal, exponential, uniform, gamma, beta, χ², Cauchy, Laplace, logistic, Pareto, Weibull, lognormal, Student t, F, Rayleigh, Gumbel, Fréchet, generalized Pareto, inverse Gaussian, Erlang, triangular; distribution function, mean, variance, moments, moment generating function, median, differential entropy, skewness, excess kurtosis | |
| [`information`](glossary.md#information) | entropy, Rényi and binary entropy, Kullback–Leibler and χ² divergences, total variation and Hellinger distances | with `distributions` |
| [`risk`](glossary.md#risk) | survival function, hazard rate, cumulative hazard, quantile function, stop-loss transform, mean excess function; value at risk, expected shortfall; heavy- and light-tailed, increasing and decreasing failure rate | with `densities` |
| [`stochasticorders`](glossary.md#stochasticorders) | `$f$ is smaller than $g$` in the usual stochastic, hazard rate, likelihood ratio, convex and increasing convex orders | with `densities` |
| [`markovchains`](glossary.md#markovchains) | doubly stochastic, irreducible and primitive matrices; absorbing states; stationary and reversible distributions, distributions on `n` states; `k`-step transition probabilities, the distribution after `k` steps, the stationary probability of a state | loads `matrixnorms` |
| [`branching`](glossary.md#branching) | offspring distributions on `ℕ₀` that are subcritical, critical or supercritical; the offspring mean and generating function, the expected size of generation `n`, the extinction probability | with `distributions` |
| [`finance`](glossary.md#finance) | the standard normal distribution function; present and future values, continuous compounding, annuities; Black–Scholes prices of calls and puts, the delta | |
| [`utility`](glossary.md#utility) | utility functions, risk averse, strictly risk averse, risk seeking and risk neutral, with decreasing absolute risk aversion; the Arrow–Pratt coefficients of absolute and relative risk aversion, exponential (CARA) and power (CRRA) utilities; expected value, expected utility, certainty equivalent and risk premium of a lottery with two outcomes | |
| [`economics`](glossary.md#economics) | elastic, inelastic and unit elastic functions, linearly homogeneous functions and constant returns to scale, Lorenz curves; elasticity and price elasticity, marginal and average values, Cobb–Douglas and CES functions, the Gini coefficient, consumer surplus | |
| [`queues`](glossary.md#queues) | the traffic intensity; for the M/M/1 queue the mean numbers in the system and waiting, the mean sojourn and waiting times, the probability of `n` customers; the Erlang B and C formulas; the Pollaczek–Khinchine mean waiting time of M/G/1 | |
| [`reliability`](glossary.md#reliability) | the reliability of series, parallel, `k`-out-of-`n` and bridge systems (equal or given component reliabilities), of a component with constant failure rate; mean times to failure of series and parallel systems; availability | |
| **Discrete mathematics** (`discrete`) | | |
| [`combinatorics`](glossary.md#combinatorics) | Fibonacci, Catalan, Bell and harmonic numbers, derangements, partitions, Stirling numbers | |
| [`counting`](glossary.md#counting) | the numbers of `k`-element subsets, subsets, `k`-permutations, permutations, multisets, maps, injective and surjective maps, compositions and lattice paths; multinomial coefficients | |
| [`permutations`](glossary.md#permutations) | permutations of `{1, …, n}`: sign, order, cycles, inversions | |
| [`graphs`](glossary.md#graphs) | finite simple graphs: degrees, distances, chromatic and clique numbers, trees, complete and bipartite graphs | |
| [`recurrences`](glossary.md#recurrences) | arithmetic and geometric progressions with their terms and sums, solutions of the Fibonacci recurrence and of linear recurrences of order two, characteristic roots | |
| [`codes`](glossary.md#codes) | binary words of length `n`; the Hamming weight and distance of the first `n` letters, the volume of a Hamming ball; the sphere-packing, Singleton and Gilbert–Varshamov bounds; the rate of a code | |
| **Number theory** (`numbertheory`) | | |
| [`numbers`](glossary.md#numbers) | primes, divisibility, parity, the greatest common divisor | |
| [`arithmetic`](glossary.md#arithmetic) | Euler's totient, the Möbius function, divisor functions, the prime-counting function, `p`-adic valuations | |
| [`congruences`](glossary.md#congruences) | congruences modulo `n`, quadratic residues, the Legendre symbol, primitive roots | |
| [`specialnumbers`](glossary.md#specialnumbers) | twin, Sophie Germain, safe and Fermat primes, perfect cubes and powers, powers of two, sums of two squares, triangular numbers; Fermat and Mersenne numbers, repunits, pentagonal, tetrahedral, square pyramidal and oblong numbers | with `numbers` |
| [`continuedfractions`](glossary.md#continuedfractions) | the complete and partial quotients and the convergents (with numerators and denominators) of an irrational number, the value of a finite continued fraction; badly approximable numbers, Liouville numbers, quadratic irrationals, best approximations | |
| [`digits`](glossary.md#digits) | the `k`th digit and the number of digits in base `b`, digit reversal, palindromes, digital roots, repunits; Harshad (Niven) and narcissistic (Armstrong) numbers | |

## Not yet

Topology and metrics are on the real line: a field has types of its own, but not yet an
abstract space whose points are of a type the article declares (`Let $(X,d)$ be a metric
space.`). Sample statistics (the sample mean and variance, empirical distribution
functions, estimators and tests) have no field yet: they need a sample as a sequence of
numbers, and the grammar does not yet bind an infinite sequence whose terms are written
`a_n` ([roadmap](roadmap.md)); a sequence is written as a function of the natural numbers
(`$x(n)$`), as in `iteration` and `metricspaces`. Rank statistics of a sample from a copula
are read with `unitsquare` (`P_C(\tau_n\le t)`).

A field is a file of data in `Leanify/Library/`; [Vocabularies and
models](vocabularies.md) says how to write one.
