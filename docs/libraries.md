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

**Without the option, every field is loaded.** `\usepackage{leanify}` reads the article with the
whole vocabulary, as `vocab=math` does, so a first article needs no choice. Three things follow:

* An article that already has a certificate keeps the fields of that certificate, so that its
  reading does not change under it (its Lean files name them; an older certificate without
  fields is the core alone).
* `vocab=core` is the core vocabulary alone, and `vocab={…}` names fields. Naming them keeps the
  reading of an article the same when the vocabulary grows; `leanify fields article.tex` finds
  them.
* With every field loaded, a few phrases have a meaning for each kind of argument (`the inverse
  of`, `the order of`, …): a definition names the kind (`the inverse of a permutation $\sigma$`).
  A variable in `[0,1]` is a point of the unit interval (see the bundles below), and the kernel
  audit of a certificate takes about five times as long as with one field.

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
│   ├── signals                   pulses, Nyquist rate, decibels, first-order filters
│   ├── dynamics                  iterates, fixed and periodic points
│   ├── functionalequations       Cauchy's and Jensen's equations, subadditivity, homogeneity
│   ├── convexity                 log-, harmonically, s-, h-convex functions; Hermite–Hadamard
│   ├── fractional                Riemann–Liouville, Hadamard, Caputo; Mittag-Leffler
│   ├── summability               Cesàro and Abel summability, sequences
│   ├── functionsequences         pointwise and uniform convergence, equicontinuity
│   ├── odes                      linear, Bernoulli, Riccati, Euler–Cauchy, oscillators
│   ├── epidemics                 reproduction numbers, final sizes, the SIS model
│   ├── populationdynamics        logistic growth, harvesting, Ricker, Lotka–Volterra
│   ├── pharmacokinetics          one-compartment model, clearance, steady state, loading dose
│   ├── variations                actions, Euler–Lagrange equation, minimizers
│   ├── physics
│   │   ├── mechanics             projectiles, pendulums, oscillators, orbits
│   │   ├── waves                 Doppler, harmonics, Snell's law, decibels, lenses
│   │   ├── relativity            Lorentz factor, rapidity, velocity addition, γmc²
│   │   ├── circuits              resistors, RC charging, LC resonance, RLC impedance
│   │   ├── thermodynamics        Carnot efficiency, ideal gases, cooling, Boltzmann factors
│   │   ├── kinetics              reaction orders, half-lives, Arrhenius, Michaelis–Menten, pH
│   │   ├── fluids                Reynolds and Froude numbers, Poiseuille, drag, Stokes
│   │   ├── quantum               particle in a box, oscillator, hydrogen, de Broglie
│   │   ├── materials             stress, moduli, beam deflections, buckling
│   │   ├── astronomy             parallax, magnitudes, Hubble's law, Schwarzschild radius
│   │   ├── electromagnetism      Coulomb's law, fields of wires and solenoids, cyclotrons
│   │   ├── kinematics            constant acceleration, circular motion, collisions
│   │   ├── optics                lensmaker, image distances, gratings, Bragg, Malus
│   │   ├── acoustics             speed of sound, decibels, pipe resonances, reverberation
│   │   ├── music                 piano keys, semitones, cents, commas, MIDI numbers
│   │   ├── crystallography       Miller indices, cubic lattices, packing fractions
│   │   └── orbits                vis-viva, apsides, Hohmann transfers, Hill radius
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
│   │   ├── matrices
│   │   └── majorization          majorization of vectors (with vectors)
│   ├── polynomials
│   ├── quadratics                discriminants, roots and Vieta; Cardano's root of a cubic
│   ├── structures                groups, rings, fields, vector spaces, with their elements (also in topology)
│   ├── finitefields              GL_n(F_q), Gaussian binomials, projective spaces
│   └── liealgebras               dimensions, positive roots, Coxeter numbers
├── topology                      topology and geometry
│   ├── realsets                  (also in analysis)
│   ├── structures                topological and metric spaces, ordered sets (also in algebra)
│   ├── topologies                topologies on ℝ: open, compact, Hausdorff, continuous maps
│   ├── metricspaces              metrics on ℝ: balls, Cauchy sequences, completeness (with topologies)
│   ├── geometry                  the Euclidean plane
│   ├── planegeometry             lines, triangle centres, conics (with geometry)
│   ├── triangles                 triangles by their sides, regular polygons
│   ├── solids                    volumes and surface areas, balls in n dimensions
│   ├── polyhedra                 Euler's formula, Platonic solids, dihedral angles
│   ├── sphericalgeometry         central angles, Girard's theorem, caps, solid angles
│   ├── mapprojections            Mercator, Lambert, sinusoidal, stereographic
│   ├── surfaces                  Euler characteristic, genus, Gauss–Bonnet, curvature
│   ├── curves                    curvature, length and area of plane and polar curves
│   └── fractals                  similarity dimensions, Cantor, Koch, Sierpinski, Menger
├── numerics                      numerical mathematics
│   ├── approximation             errors, conditioning, difference quotients, quadrature, interpolation
│   ├── iteration                 Newton's method, fixed-point iteration, orders of convergence
│   ├── odesolvers                initial value problems; Euler, Heun, Runge–Kutta
│   ├── matrixnorms               matrix norms, condition numbers, diagonal dominance (with matrices)
│   ├── descent                   Armijo and Wolfe steps; gradient descent, heavy-ball, proximal point
│   ├── floatingpoint             machine epsilon, unit roundoff, ranges, errors, rounding
│   └── convergence               bisection counts, Richardson and Aitken extrapolation
├── stochastic                    probability and statistics
│   ├── statistics
│   │   ├── probability
│   │   │   ├── distributions     distributions on ℕ₀ (Poisson, binomial, geometric, …)
│   │   │   ├── densities         densities on the line
│   │   │   ├── information       entropy and divergences
│   │   │   ├── channels          channel capacities, rate distortion
│   │   │   ├── concentration     tail bounds, sample sizes, sample complexity
│   │   │   ├── classicalprobability birthday, coupon collector, ballot, secretary problems
│   │   │   ├── geometricprobability random distances, triangles, acute triangles (as integrals)
│   │   │   ├── risk              survival, hazard rate, value at risk, expected shortfall
│   │   │   ├── stochasticorders  usual, hazard rate, likelihood ratio, convex orders
│   │   │   ├── markovchains      transition matrices, stationary distributions (with matrixnorms)
│   │   │   ├── branching         Galton–Watson processes, extinction probabilities
│   │   │   ├── randomwalks       gambler's ruin, Brownian hitting probabilities
│   │   │   ├── poissonprocesses  arrivals, waiting times, thinning, compound sums
│   │   │   ├── extremes          GEV and generalized Pareto laws, domains of attraction
│   │   │   ├── populationgenetics Hardy–Weinberg, fixation probabilities, drift
│   │   │   └── betting           implied probabilities, Kelly criterion, margins
│   │   ├── samples               sample mean, variance, order statistics, correlation
│   │   ├── regression            residuals, sums of squares, R², standard errors
│   │   ├── timeseries            autocovariance, moving averages, differences, smoothing
│   │   ├── testing               z- and t-statistics, p-values, quantiles, chi-squared
│   │   ├── bayesian              conjugate posteriors, Bayes' formula
│   │   ├── diagnostictests       predictive values, likelihood ratios, odds ratios
│   │   ├── learning              activations, losses, precision, recall, F1, MCC
│   │   ├── surveysampling        sample sizes, finite population correction, design effects
│   │   ├── variograms            spherical, exponential, Gaussian and power models, nuggets
│   │   └── dependence
│   │       └── copulas           copula families, Spearman's rho, Kendall's tau, Chatterjee's xi
│   │                             (with markov: L², Markov operators; hilbert; unitsquare)
│   ├── finance                   interest, annuities, Black–Scholes
│   ├── fixedincome               bond prices, durations, perpetuities, loans
│   ├── options                   payoffs, forwards, put–call parity, binomial model
│   ├── utility                   expected utility, risk aversion, certainty equivalents
│   ├── economics                 elasticities, production functions, Lorenz curves, Gini
│   ├── macroeconomics            Solow model, Fisher equation, multipliers, Taylor rule
│   ├── games                     two-by-two zero-sum games, values, optimal strategies
│   ├── ratings                   Elo, Bradley–Terry, Pythagorean expectation
│   ├── queues                    M/M/1, Erlang B and C, Pollaczek–Khinchine
│   ├── reliability               series, parallel, k-out-of-n systems; MTTF
│   ├── actuarial                 survival laws, premiums, annuities
│   ├── inventory                 economic order quantity, newsvendor
│   ├── voting                    Hare and Droop quotas, D'Hondt and Webster divisors
│   └── traffic                   Greenshields model, capacity, headway, spacing
├── discrete                      discrete mathematics
│   ├── combinatorics
│   ├── counting                  subsets, maps, surjections, compositions, lattice paths
│   ├── words                     palindromes, necklaces, de Bruijn sequences
│   ├── permutations
│   ├── graphs
│   ├── graphcounts               Cayley's formula, chromatic polynomials, Turán graphs
│   ├── recurrences               progressions, Fibonacci and linear recurrences
│   ├── codes                     binary words, Hamming distance, coding bounds
│   ├── algorithms                comparisons of searching and sorting, Hanoi, master theorem
│   ├── combinatorialgames        nim-sums, Grundy values, Wythoff pairs
│   └── designs                   block designs, Steiner triple systems, finite planes
└── numbertheory
    ├── numbers                   primes, divisibility, parity
    ├── arithmetic                arithmetic functions
    ├── congruences               arithmetic modulo n
    ├── specialnumbers            twin and Fermat primes, perfect powers, figurate numbers
    ├── analyticnumbertheory      von Mangoldt, Chebyshev functions, primes in progressions
    ├── continuedfractions        convergents, badly approximable and Liouville numbers
    ├── digits                    base-b digits, palindromes, digital roots, repunits
    ├── collatz                   the 3n+1 map, stopping times
    ├── cryptography              RSA, discrete logarithms, Diffie–Hellman
    ├── diophantine               Frobenius numbers, sums of two squares, Pythagorean triples
    ├── latticepoints             Gauss's circle problem, visible points, Pick's theorem
    └── calendar                  leap years, month lengths, Zeller's congruence
```

Areas group fields inside a realm (`physics` in `analysis`: `mechanics`, `waves`,
`relativity`, `circuits`, `thermodynamics`, `kinetics`, `fluids`, `quantum`,
`materials`, `astronomy`, `electromagnetism`, `kinematics`, `optics`, `acoustics`, `music`, `crystallography`, `orbits`). A field may sit in two places (`realsets` is in `analysis` and in `topology`); a bundle has
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

For an article you certify, name the smallest bundle that reads it: fewer words in the vocabulary
mean fewer phrases that your own definitions could shadow, a faster audit, and a reading that
stays the same when fields are added. `leanify fields` names
the fields an article needs and, when they belong together, their bundle.

### Renamed fields

The field `groups` (finite groups as a type of their own) is now part of `structures`,
where a group is the set of its elements, finite or not; `vocab=groups` loads
`structures`, and an article reads the same with it, except that `the order of` has a
meaning for groups and for their elements, so a `We write` definition names the kind (`We
write $|G|$ for the order of a group $G$`).


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
| [`series`](glossary.md#series) | sequences of real numbers `(a_n)` (positive, nonnegative, of integers), converging to a number, convergent and divergent; summable, absolutely and conditionally summable, square-summable and alternating sequences of terms; the sum and partial sums of a series, the Cauchy product, power series and their radius of convergence, geometric series; the limit, limit superior and limit inferior of a sequence | with `realfunctions` |
| [`integration`](glossary.md#integration) | `$p$-integrable`, locally integrable and essentially bounded functions; the `L^p` norm, the essential supremum, the Hölder conjugate, improper integrals to infinity and over the line, the integral on a set | with `realfunctions`, `realsets` |
| [`optimization`](glossary.md#optimization) | minimizers and stationary points, strongly convex and `L`-smooth functions; minimum, infimum, convex conjugate, Moreau envelope, proximal operator | with `realfunctions` |
| [`asymptotics`](glossary.md#asymptotics) | asymptotically equivalent, dominated by (`O`), negligible compared to (`o`), of the same order (`Θ`); polynomial and exponential growth; slowly and regularly varying; the limit at infinity | with `realfunctions` |
| [`transforms`](glossary.md#transforms) | Laplace, Mellin and Stieltjes transforms, convolution, cross-correlation, autocorrelation; of exponential order, causal | with `realfunctions` |
| [`fourier`](glossary.md#fourier) | Fourier coefficients, partial sums and Fejér means, Dirichlet and Fejér kernels, cosine and sine transforms | with `realfunctions` |
| [`signals`](glossary.md#signals) | the normalized sinc, rectangular, triangular and unit step functions and Gaussian pulses; the Nyquist rate; signal-to-noise ratios in decibels; the cutoff frequency of an RC filter and the gain of a first-order low-pass filter | |
| [`dynamics`](glossary.md#dynamics) | iterates, orbits, fixed and periodic points and their stability, least period, Lyapunov exponent | with `realfunctions` |
| [`functionalequations`](glossary.md#functionalequations) | additive (Cauchy), subadditive and superadditive, midpoint convex and concave, Jensen-affine, multiplicative on the reals, logarithmically additive, involutive, idempotent, homogeneous of degree `k` and positively homogeneous functions; solutions of d'Alembert's equation | |
| [`convexity`](glossary.md#convexity) | log-convex, harmonically convex and concave, geometrically and GA-convex, star-shaped, quasiconcave, `$s$-convex in the second sense`, `$h$-convex`, Wright-convex functions, P-functions and Godunova–Levin functions; the integral mean on `[a,b]`, the Hermite–Hadamard gap, the Jensen gap | |
| [`fractional`](glossary.md#fractional) | left- and right-sided Riemann–Liouville fractional integrals, the Hadamard fractional integral, Riemann–Liouville and Caputo fractional derivatives of order in `(0,1)`, the gamma function, the one- and two-parameter Mittag-Leffler functions | |
| [`summability`](glossary.md#summability) | Cesàro and Abel summable sequences, convergent, null, Cauchy, eventually nondecreasing and bounded-variation sequences, subadditive and log-concave sequences; Cesàro means, arithmetic means, the Abel sum, forward differences | |
| [`functionsequences`](glossary.md#functionsequences) | for a sequence of functions `f(n, x)`: pointwise and uniform convergence (on `[a,b]` or the line), uniformly Cauchy, uniformly bounded, equicontinuous, monotone in the index; the supremum distance to a limit, partial sums of a series of functions | |
| [`odes`](glossary.md#odes) | solutions of first-order linear, separable, Bernoulli and Riccati equations, of second-order linear and Euler–Cauchy equations, of the harmonic and damped oscillator equations; the Wronskian | |
| [`epidemics`](glossary.md#epidemics) | the basic reproduction number of the SIR model (with and without mortality), the herd immunity threshold, the final size, the doubling time, the endemic equilibrium of the SIS model and the critical vaccination coverage; solutions of the SIS model and of exponential growth | |
| [`populationdynamics`](glossary.md#populationdynamics) | exponential and logistic populations, doubling times, the maximum sustainable yield and the harvested equilibrium; the Ricker and Beverton–Holt maps; the prey and predator equilibria of the Lotka–Volterra system | |
| [`pharmacokinetics`](glossary.md#pharmacokinetics) | the concentration after an intravenous dose, clearance, elimination half-life, area under the curve, the average steady-state concentration, the accumulation factor and the loading dose | |
| [`variations`](glossary.md#variations) | for a Lagrangian `L(t, y, p)`: the action, solutions of the Euler–Lagrange equation, minimizers with the same endpoint values, the Hamiltonian; the arc-length functional and the Dirichlet energy; functions with given endpoint values | |
| [`mechanics`](glossary.md#mechanics) | the range, maximal height and time of flight of a projectile; the period of a pendulum; the natural frequency, period and damping ratio of an oscillator; kinetic energy; the circular orbital speed, escape velocity and orbital period (Kepler's third law) for a gravitational parameter | |
| [`waves`](glossary.md#waves) | the wavelength, Doppler and beat frequencies, the harmonics of a string and the wave speed on it; the angle of refraction (Snell's law), the critical and Brewster angles; levels in decibels; the focal length of a thin lens | |
| [`relativity`](glossary.md#relativity) | the Lorentz factor, rapidity and redshift factor of a speed; the relativistic sum of velocities; dilated times and contracted lengths; relativistic energy and momentum, rest energy (the speed of light is an argument) | |
| [`circuits`](glossary.md#circuits) | resistances in series and in parallel, dissipated power; the time constant and capacitor voltage of an RC circuit; energies stored in capacitances and inductances; the resonant frequency of an LC circuit; the impedance and quality factor of a series RLC circuit | |
| [`thermodynamics`](glossary.md#thermodynamics) | the Carnot efficiency and refrigerator coefficient of performance; the pressure of an ideal gas; Newton's law of cooling; entropy changes of heating; black-body radiation; Boltzmann factors and the mean energy of a two-level system (constants of nature are arguments) | |
| [`kinetics`](glossary.md#kinetics) | concentrations in reactions of order zero, one and two; half-lives and decay constants; the Arrhenius rate constant; the Michaelis–Menten rate; the pH | |
| [`fluids`](glossary.md#fluids) | the Reynolds and Froude numbers; hydrostatic and dynamic pressure; Torricelli's efflux speed; the Poiseuille flow rate; the drag force; the Stokes terminal velocity | |
| [`quantum`](glossary.md#quantum) | the levels of a particle in a box, a harmonic oscillator and the hydrogen atom; the probability density in a box; de Broglie wavelengths, photon energies, hydrogen transition wavelengths (Rydberg), the Compton shift | |
| [`materials`](glossary.md#materials) | stress and strain; the axial stiffness of a rod; shear and bulk moduli from Young's modulus and Poisson's ratio; second moments of area; deflections of cantilevers and simply supported beams; the Euler buckling load | |
| [`astronomy`](glossary.md#astronomy) | distances from parallaxes, distance moduli, magnitude differences; redshifts, recession speeds (Hubble's law) and the Hubble time; the Schwarzschild radius; stellar luminosity; Wien's peak wavelength | |
| [`electromagnetism`](glossary.md#electromagnetism) | the Coulomb force, the field and potential of a point charge; parallel-plate capacitance and field energy density; the magnetic fields of a long wire and a solenoid; the magnetic force on a moving charge, cyclotron frequency and Larmor radius | |
| [`kinematics`](glossary.md#kinematics) | displacement and velocity at constant acceleration, stopping distances; centripetal acceleration and the period of circular motion; velocities after elastic and perfectly inelastic collisions and the kinetic energy lost | |
| [`optics`](glossary.md#optics) | the lensmaker's equation, image distances and magnification of a thin lens; the Rayleigh angle; the angles of grating orders, single-slit minima and Bragg reflection; Malus's law | |
| [`acoustics`](glossary.md#acoustics) | the speed of sound in an ideal gas; sound intensity and pressure levels; the intensity of a point source; resonances of open and closed pipes; the Sabine reverberation time | |
| [`music`](glossary.md#music) | the frequencies of piano keys and of equal-tempered semitones, intervals in cents, the Pythagorean and syntonic commas, ratios of equal temperaments, MIDI note numbers | |
| [`crystallography`](glossary.md#crystallography) | interplanar spacings by Miller indices; packing fractions, coordination numbers, atoms per unit cell and nearest-neighbour distances of cubic lattices | |
| [`orbits`](glossary.md#orbits) | the vis-viva speed, periapsis and apoapsis distances, specific orbital energy, the burns of a Hohmann transfer, synodic periods, the Hill radius | |
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
| [`majorization`](glossary.md#majorization) | vectors majorized, weakly submajorized or weakly supermajorized by another, decreasingly ordered vectors; the `k`th largest coordinate, the sum of the `k` largest coordinates, the positive-part sum | loads `vectors` |
| [`polynomials`](glossary.md#polynomials) | real polynomials: degree, coefficients, roots | |
| [`quadratics`](glossary.md#quadratics) | for `ax² + bx + c`: the discriminant, the larger and smaller root, the sum and product of the roots, the vertex and extreme value, the number of real roots; the discriminant and Cardano's real root of `x³ + px + q` | |
| [`structures`](glossary.md#structures) | structures with their elements (`Let $G$ be a group and $g\in G$`): groups, subgroups and normal subgroups, monoids and semigroups, finitely generated groups and modules; rings, ideals (prime, maximal, principal), integral domains, fields and field extensions (finite, finitely generated, algebraic; the degree `[L:K]`, algebraic and transcendental elements), characteristic; modules and vector spaces over a ring or field, subspaces, bases, linear independence, span, dimension; real normed, Banach, inner product and Hilbert spaces, bounded linear operators; topological and metric spaces, open, closed, dense and compact subsets, limit and isolated points, neighbourhoods, first countable, Lindelöf, σ-compact, totally disconnected, Hausdorff, compact, connected, complete; partially and totally ordered sets, lattices, bounds; maps between structures with their domain and codomain, bound by a signature (`$\varphi\colon G\to H$`): kernel, image, rank, composition, eigenvalues and fixed points; homomorphisms, isomorphisms, automorphisms, contractions, linear, continuous and monotone maps, injective, surjective and bijective maps, homeomorphisms, isometries; cyclic, symmetric, alternating and dihedral groups, direct products. Also loaded as `groups`, `rings` or `spaces` | |
| [`finitefields`](glossary.md#finitefields) | prime powers; the orders of `GL_n(F_q)` and `SL_n(F_q)`; square matrices, subspaces (Gaussian binomials) and projective points over `F_q`; primitive elements | |
| [`liealgebras`](glossary.md#liealgebras) | the dimensions, numbers of positive roots and Coxeter numbers of the classical simple Lie algebras `A_n`, `B_n`, `C_n`, `D_n` | |
| **Topology and geometry** (`topology`) | | |
| [`topologies`](glossary.md#topologies) | topologies on `ℝ`: `$\tau$-open`, `-closed`, `-compact`, `-connected`, `-dense`; Hausdorff, second countable, separable, metrizable, finer and coarser; continuous, open maps and homeomorphisms between topologies; convergent sequences; the usual, discrete, indiscrete, cofinite and lower limit topologies, generated and subspace topologies; closure, interior, boundary | |
| [`metricspaces`](glossary.md#metricspaces) | metrics, pseudometrics and ultrametrics on `ℝ`: complete, bounded, (strongly) equivalent; Cauchy and convergent sequences, isometries, contractions; the Euclidean and discrete metrics, the induced topology, balls, diameter, distance to a set | loads `topologies` |
| [`geometry`](glossary.md#geometry) | points of the Euclidean plane: distances, triangles, lines, circles | |
| [`planegeometry`](glossary.md#planegeometry) | the distance from a point to a line, feet of perpendiculars, reflections; circumcentre, incentre, orthocentre, circumradius and inradius of a triangle; ellipses, hyperbolas and parabolas by their foci, eccentricity | loads `geometry` |
| [`triangles`](glossary.md#triangles) | for a triangle with sides `a`, `b`, `c`: the semiperimeter, the area (Heron), the angle opposite a side, the inradius and circumradius, altitudes, medians and angle bisectors; for a regular `n`-gon the interior angle, area, circumradius and apothem; the number of diagonals | |
| [`solids`](glossary.md#solids) | the volume of the ball and the area of the sphere in `n` dimensions; volumes and surface areas of cylinders and cones; volumes of ellipsoids, tori, the regular tetrahedron, octahedron, dodecahedron and icosahedron and of the standard simplex | |
| [`polyhedra`](glossary.md#polyhedra) | the Euler characteristic of a polyhedron; the vertices, edges, faces and dihedral angle of the Platonic solid `{p,q}`; angle defects | |
| [`sphericalgeometry`](glossary.md#sphericalgeometry) | the central angle between two points given by latitude and longitude; chords; the spherical excess and the area of a spherical triangle (Girard); the area and volume of a spherical cap; the solid angle of a cone | |
| [`mapprojections`](glossary.md#mapprojections) | the Mercator ordinate, scale factor and its inverse; the Lambert equal-area ordinate; the sinusoidal abscissa; stereographic coordinates | |
| [`surfaces`](glossary.md#surfaces) | the Euler characteristic of closed orientable and nonorientable surfaces, the genus, the total curvature (Gauss–Bonnet); the Gaussian and mean curvature of spheres and cylinders; the area and Gaussian curvature of a torus | |
| [`curves`](glossary.md#curves) | the speed, signed curvature, length and signed area of a curve with coordinate functions `x`, `y`; regular and singular points; the curvature and radius of curvature of a graph; the area and length of a polar curve | |
| [`fractals`](glossary.md#fractals) | the similarity dimension of a self-similar set (`N` pieces scaled by `r`, or two ratios by Moran's equation); the dimension, lengths and intervals of the Cantor set; the Koch curve and snowflake; the Sierpinski triangle; the Menger sponge | |
| **Numerical mathematics** (`numerics`) | | |
| [`approximation`](glossary.md#approximation) | absolute and relative errors, the condition number, rounding, machine epsilon; forward, backward, central and second difference quotients; trapezoidal, midpoint and Simpson's rules (simple and composite), Riemann sums; linear and Lagrange interpolation, Chebyshev nodes | with `realfunctions` |
| [`iteration`](glossary.md#iteration) | the Newton map, secant step and relaxation; Newton, secant and fixed-point sequences; convergent with order `p`, linearly, superlinearly, quadratically, cubically; contractive maps | with `realfunctions` |
| [`odesolvers`](glossary.md#odesolvers) | right-hand sides `f(t, y)`, Lipschitz in the second variable; solutions of a differential equation and of an initial value problem, of linear equations of order two with constant coefficients and of the logistic equation; Euler, Heun, midpoint and Runge–Kutta steps and sequences | with `realfunctions` |
| [`matrixnorms`](glossary.md#matrixnorms) | Frobenius norm, maximum absolute row and column sums, condition numbers; strictly diagonally dominant, tridiagonal, upper Hessenberg, banded and entrywise nonnegative matrices | loads `matrices` |
| [`descent`](glossary.md#descent) | Armijo and Wolfe steps, descent directions; gradient descent, heavy-ball (Polyak) and proximal point sequences of a differentiable function | |
| [`floatingpoint`](glossary.md#floatingpoint) | numbers representable with `p` digits in base `b`; the machine epsilon and unit roundoff; the largest number, the smallest normal and subnormal numbers, the number of normal numbers; absolute and relative errors; rounding to decimal places | |
| [`convergence`](glossary.md#convergence) | the numbers of bisection steps and contraction steps; Richardson and Aitken extrapolation; the estimated order of convergence; correct significant digits | |
| **Probability and statistics** (`stochastic`) | | |
| [`unitsquare`](glossary.md#unitsquare) | `[0,1]` and the unit square with Lebesgue measure: copulas, distribution functions, probability measures and couplings with uniform marginals, samples `(U_i,V_i)` with `\mathbb{E}_C` and `P_C` | |
| [`hilbert`](glossary.md#hilbert), [`markov`](glossary.md#markov) | `L^2` on `[0,1]`, operators, the Hoeffding decomposition; the Markov operator of a copula | each loads the ones before it |
| [`copulas`](glossary.md#copulas) | the independence, comonotonicity and countermonotonicity copulas; Clayton, Gumbel, Frank, FGM, Ali–Mikhail–Haq, Cuadras–Augé, Marshall–Olkin and Gaussian copulas; Spearman's rho, Kendall's tau, Blomqvist's beta, Spearman's footrule, Gini's gamma, Chatterjee's xi, tail dependence coefficients; positively and negatively quadrant dependent, radially symmetric, left tail decreasing, max-stable; the concordance order | loads `markov` |
| [`distributions`](glossary.md#distributions) | probability distributions on `ℕ₀`: Poisson, binomial, negative binomial, geometric, Bernoulli, discrete uniform, hypergeometric, point masses; the mean, the variance, the probability generating function | |
| [`samples`](glossary.md#samples) | the first `n` terms of a sequence as a sample: sample mean, variance and standard deviation, moments, the empirical distribution function, order statistics, median and range, sample covariance and correlation, least-squares slope and intercept | |
| [`regression`](glossary.md#regression) | for the least-squares line of `y` on `x` and the first `n` observations: fitted values, residuals, residual, total and explained sums of squares, the (adjusted) coefficient of determination, the residual standard error and the standard error of the slope | |
| [`timeseries`](glossary.md#timeseries) | the sample autocovariance and autocorrelation at a lag, moving averages, cumulative sums, difference sequences and seasonal differences, exponential smoothing; autoregressive sequences of order one and random walks | |
| [`testing`](glossary.md#testing) | the z- and t-statistics of a sample for a mean, one- and two-sided p-values, standard normal quantiles, the margin of error at a confidence level, Pearson's chi-squared statistic | |
| [`bayesian`](glossary.md#bayesian) | posterior mean, mode and parameters of a beta prior after binomial data, the posterior mean of a gamma prior after Poisson data, posterior mean and variance of a normal prior after normal data; Bayes' formula and the Bayes factor | |
| [`diagnostictests`](glossary.md#diagnostictests) | positive and negative predictive values, accuracy, likelihood ratios and the Youden index of a test; post-test odds; the odds ratio and relative risk of a 2×2 table; the number needed to treat | |
| [`learning`](glossary.md#learning) | the sigmoid, ReLU and softplus functions; binary cross-entropy and hinge loss; the precision, recall, F1 score, accuracy and Matthews correlation coefficient of confusion counts | |
| [`surveysampling`](glossary.md#surveysampling) | sample sizes for proportions and means, with the finite population correction; margins of error; design effects and effective sample sizes; sampling fractions | |
| [`variograms`](glossary.md#variograms) | spherical, exponential, Gaussian and power variograms, nuggets, the exponential covariance, the practical range | |
| [`densities`](glossary.md#densities) | probability densities on the line: normal, exponential, uniform, gamma, beta, χ², Cauchy, Laplace, logistic, Pareto, Weibull, lognormal, Student t, F, Rayleigh, Gumbel, Fréchet, generalized Pareto, inverse Gaussian, Erlang, triangular; distribution function, mean, variance, moments, moment generating function, median, differential entropy, skewness, excess kurtosis | |
| [`information`](glossary.md#information) | entropy, Rényi and binary entropy, Kullback–Leibler and χ² divergences, total variation and Hellinger distances | with `distributions` |
| [`channels`](glossary.md#channels) | the binary entropy in bits; capacities of the binary symmetric, binary erasure, Z, Gaussian and band-limited Gaussian channels; rate-distortion functions of Bernoulli and Gaussian sources | |
| [`concentration`](glossary.md#concentration) | Markov, Chebyshev, Cantelli, Hoeffding, Bernstein, Chernoff and McDiarmid bounds; the Hoeffding sample size; the realizable and agnostic sample complexity of a finite hypothesis class | |
| [`classicalprobability`](glossary.md#classicalprobability) | the birthday problem, the coupon collector, the ballot problem, derangements, Buffon's needle, the secretary problem (cutoff and success probability), runs of heads | |
| [`geometricprobability`](glossary.md#geometricprobability) | expected distances between random points in the unit interval, square and disk, the expected area of a random triangle, the probability of an acute triangle on a circle, each as the integral it is | |
| [`risk`](glossary.md#risk) | survival function, hazard rate, cumulative hazard, quantile function, stop-loss transform, mean excess function; value at risk, expected shortfall; heavy- and light-tailed, increasing and decreasing failure rate | with `densities` |
| [`stochasticorders`](glossary.md#stochasticorders) | `$f$ is smaller than $g$` in the usual stochastic, hazard rate, likelihood ratio, convex and increasing convex orders | with `densities` |
| [`markovchains`](glossary.md#markovchains) | doubly stochastic, irreducible and primitive matrices; absorbing states; stationary and reversible distributions, distributions on `n` states; `k`-step transition probabilities, the distribution after `k` steps, the stationary probability of a state | loads `matrixnorms` |
| [`branching`](glossary.md#branching) | offspring distributions on `ℕ₀` that are subcritical, critical or supercritical; the offspring mean and generating function, the expected size of generation `n`, the extinction probability | with `distributions` |
| [`randomwalks`](glossary.md#randomwalks) | gambler's ruin: the ruin probability and the expected duration, the probability of reaching the target; the distribution of the simple random walk after `n` steps; for Brownian motion the hitting probability, the expected exit time and the transition density | |
| [`poissonprocesses`](glossary.md#poissonprocesses) | probabilities of arrival counts, waiting times for the `k`th arrival, thinned rates, the mean and variance of compound Poisson sums | |
| [`extremes`](glossary.md#extremes) | the GEV, standard Gumbel, Fréchet and reversed Weibull distribution functions, return levels, the generalized Pareto distribution function and its mean excess; distribution functions in the maximum domain of attraction of the Gumbel, Fréchet or Weibull law, regularly varying tails | |
| [`populationgenetics`](glossary.md#populationgenetics) | Hardy–Weinberg homozygote and heterozygote frequencies; allele frequencies after selection; Moran and Kimura fixation probabilities; heterozygosity under drift; the effective size of a population with males and females; mutation equilibria | |
| [`betting`](glossary.md#betting) | implied probabilities and fair odds, odds in favour, the expected profit of a stake, the Kelly fraction and logarithmic growth, the bookmaker's margin | |
| [`finance`](glossary.md#finance) | the standard normal distribution function; present and future values, continuous compounding, annuities; Black–Scholes prices of calls and puts, the delta | |
| [`fixedincome`](glossary.md#fixedincome) | the price, Macaulay and modified duration and current yield of a bond; perpetuities and growing perpetuities; effective annual rates; loan payments and balances | |
| [`options`](glossary.md#options) | call and put payoffs, forward prices, put–call parity; the risk-neutral probability, Cox–Ross–Rubinstein factor and one-step price of the binomial model | |
| [`utility`](glossary.md#utility) | utility functions, risk averse, strictly risk averse, risk seeking and risk neutral, with decreasing absolute risk aversion; the Arrow–Pratt coefficients of absolute and relative risk aversion, exponential (CARA) and power (CRRA) utilities; expected value, expected utility, certainty equivalent and risk premium of a lottery with two outcomes | |
| [`economics`](glossary.md#economics) | elastic, inelastic and unit elastic functions, linearly homogeneous functions and constant returns to scale, Lorenz curves; elasticity and price elasticity, marginal and average values, Cobb–Douglas and CES functions, the Gini coefficient, consumer surplus | |
| [`macroeconomics`](glossary.md#macroeconomics) | steady-state capital and output of the Solow model and its golden-rule saving rate; the Harrod–Domar growth rate; the real interest rate (Fisher); the compound annual growth rate; money and Keynesian multipliers; the Taylor rule | |
| [`games`](glossary.md#games) | the value, lower and upper values and expected payoffs of a two-by-two zero-sum game; optimal strategies of the row and column players | |
| [`ratings`](glossary.md#ratings) | the Elo expected score and update; the Bradley–Terry and logistic win probabilities; the Pythagorean expectation | |
| [`queues`](glossary.md#queues) | the traffic intensity; for the M/M/1 queue the mean numbers in the system and waiting, the mean sojourn and waiting times, the probability of `n` customers; the Erlang B and C formulas; the Pollaczek–Khinchine mean waiting time of M/G/1 | |
| [`reliability`](glossary.md#reliability) | the reliability of series, parallel, `k`-out-of-`n` and bridge systems (equal or given component reliabilities), of a component with constant failure rate; mean times to failure of series and parallel systems; availability | |
| [`actuarial`](glossary.md#actuarial) | survival functions and the force of mortality of the Gompertz and Gompertz–Makeham laws; life expectancy, net single premiums of whole life insurance and annuities under constant forces, annuities-certain, the complete expectation of life, pure endowments | |
| [`inventory`](glossary.md#inventory) | the cost per unit time of a lot size, the economic order quantity and its cost, cycle lengths, reorder points, the economic order quantity with backorders, the economic production quantity; the critical fractile and the newsvendor quantity for uniform and exponential demand | |
| [`voting`](glossary.md#voting) | the Hare, Droop and majority quotas; the D'Hondt and Webster quotients; the number of pairwise contests; the largest Borda score | |
| [`traffic`](glossary.md#traffic) | the Greenshields speed and flow, capacity, critical density and uncongested speed; headway and spacing | |
| **Discrete mathematics** (`discrete`) | | |
| [`combinatorics`](glossary.md#combinatorics) | Fibonacci, Catalan, Bell and harmonic numbers, derangements, partitions, Stirling numbers | |
| [`counting`](glossary.md#counting) | the numbers of `k`-element subsets, subsets, `k`-permutations, permutations, multisets, maps, injective and surjective maps, compositions and lattice paths; multinomial coefficients | |
| [`words`](glossary.md#words) | words, palindromes and words without equal adjacent letters; binary words without two consecutive ones; necklaces; de Bruijn sequences | |
| [`permutations`](glossary.md#permutations) | permutations of `{1, …, n}`: sign, order, cycles, inversions | |
| [`graphs`](glossary.md#graphs) | finite simple graphs: degrees, distances, chromatic and clique numbers, trees, complete and bipartite graphs | |
| [`graphcounts`](glossary.md#graphcounts) | numbers of edges of complete, complete bipartite and hypercube graphs; labelled graphs; spanning trees (Cayley); chromatic polynomials of complete graphs, trees and cycles; edges of Turán graphs; the binomial bound on Ramsey numbers | |
| [`recurrences`](glossary.md#recurrences) | arithmetic and geometric progressions with their terms and sums, solutions of the Fibonacci recurrence and of linear recurrences of order two, characteristic roots | |
| [`codes`](glossary.md#codes) | binary words of length `n`; the Hamming weight and distance of the first `n` letters, the volume of a Hamming ball; the sphere-packing, Singleton and Gilbert–Varshamov bounds; the rate of a code | |
| [`algorithms`](glossary.md#algorithms) | worst-case comparisons of binary search, insertion sort and merge sort, the expected comparisons of quicksort, the sorting lower bound `⌈log₂ n!⌉`, maximum and minimum finding; the Tower of Hanoi; the critical exponent of the master theorem; perfect binary trees and minimal heights | |
| [`combinatorialgames`](glossary.md#combinatorialgames) | the nim-sum of two and three heaps and the winning moves of Nim; the Grundy value of a subtraction game; the Wythoff pairs | |
| [`designs`](glossary.md#designs) | orders admissible for Steiner triple systems; the replication number and number of blocks of a 2-design; the triples of a Steiner triple system; points and lines of projective and affine planes | |
| **Number theory** (`numbertheory`) | | |
| [`numbers`](glossary.md#numbers) | primes, divisibility, parity, the greatest common divisor | |
| [`arithmetic`](glossary.md#arithmetic) | Euler's totient, the Möbius function, divisor functions, the prime-counting function, `p`-adic valuations | |
| [`congruences`](glossary.md#congruences) | congruences modulo `n`, quadratic residues, the Legendre symbol, primitive roots | |
| [`specialnumbers`](glossary.md#specialnumbers) | twin, Sophie Germain, safe and Fermat primes, perfect cubes and powers, powers of two, sums of two squares, triangular numbers; Fermat and Mersenne numbers, repunits, pentagonal, tetrahedral, square pyramidal and oblong numbers | with `numbers` |
| [`analyticnumbertheory`](glossary.md#analyticnumbertheory) | the von Mangoldt function, Chebyshev's `ϑ` and `ψ`, the offset logarithmic integral, the number of primes up to `x` in a residue class, the number of twin prime pairs, prime gaps, the sum of the reciprocals of the primes | with `numbers` |
| [`continuedfractions`](glossary.md#continuedfractions) | the complete and partial quotients and the convergents (with numerators and denominators) of an irrational number, the value of a finite continued fraction; badly approximable numbers, Liouville numbers, quadratic irrationals, best approximations | |
| [`digits`](glossary.md#digits) | the `k`th digit and the number of digits in base `b`, digit reversal, palindromes, digital roots, repunits; Harshad (Niven) and narcissistic (Armstrong) numbers | |
| [`collatz`](glossary.md#collatz) | the Collatz map and its accelerated form, iterates, the total stopping time and the stopping time, the highest point of a trajectory; numbers with finite total stopping time | |
| [`cryptography`](glossary.md#cryptography) | residues and modular powers; the RSA modulus, totient, decryption exponent and ciphertext; discrete logarithms; the Diffie–Hellman key | |
| [`diophantine`](glossary.md#diophantine) | congruent numbers, numbers representable as a sum of two squares; the Frobenius number and the genus of the numerical semigroup of two coprime integers; the number of representations by two integers and as a sum of two squares; Euclid's formula for Pythagorean triples | |
| [`latticepoints`](glossary.md#latticepoints) | lattice points in a disk (Gauss's circle problem) and a ball, on a segment from the origin, visible lattice points in a square; the area of a lattice polygon by Pick's theorem | |
| [`calendar`](glossary.md#calendar) | leap years; the numbers of days of years and months; the day of the week (Zeller's congruence); the number of leap years up to a year | |

## Not yet

Abstract structures (`structures`) have at most `2^𝔠` elements: their elements are
points that are sets of real numbers, which every structure of analysis and algebra in
practice can be (`docs/vocabularies.md`). A structure written with its operations as a
tuple (`Let $(X,d)$ be a metric space.`, `$(G,\cdot)$`) is not read yet; name it (`Let $X$
be a metric space.`). Sample statistics (the sample mean and variance, empirical distribution
functions, estimators and tests) have no field yet: they need a sample as a sequence of
numbers, and the grammar does not yet bind an infinite sequence whose terms are written
`a_n` ([roadmap](roadmap.md)); a sequence is written as a function of the natural numbers
(`$x(n)$`), as in `iteration` and `metricspaces`. Rank statistics of a sample from a copula
are read with `unitsquare` (`P_C(\tau_n\le t)`).

A field is a file of data in `Leanify/Library/`; [Vocabularies and
models](vocabularies.md) says how to write one.
