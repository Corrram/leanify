# Writing for Leanify

Leanify reads an article the way a careful referee does: every symbol has to
be defined before it is used, every sentence has one meaning, and a proof step
may use only what it cites. The conventions below are ordinary good style for
mathematical writing. Following them is what lets the same `.tex` file be
typeset for a journal and compiled to Lean.

A sentence that matches none of the constructions is *prose*. Prose is fine:
motivation, remarks and proof sketches stay prose. It is shown in the reader
and in the diagnostics, but it asserts nothing checked. Inside results and
proofs, prose is reported, so uncompiled mathematics stays visible.

The examples come from the example articles of this documentation and from
research articles compiled with Leanify. Where an example needs a word of the
article's vocabulary, it is written NOUN (plural NOUNS): a noun of the
vocabulary, such as *probability measure on $[0,1]^2$*, or of a class the
article defines. Symbols such as $\alpha$, $\beta$ or $\mathcal{X}$ stand for
quantities and classes defined earlier in the article.

## Notation

Formulas are read as they are typeset: `T^0_q` and `T_q^0` are the same symbol,
`\widehat S_s` is the hat of `S_s`, `\min\{a,b,c\}` takes three arguments, a
variable before parentheses is a factor (`xz(x+z)`, `v(s-v)^2`; but `Q(x)` with a single
variable in the parentheses may be a name that states its dependence, and is refused), and
`\{(x,x):0\le x\le1\}` is the diagonal.

| Notation | Read as |
| --- | --- |
| `(f\circ g)(x)`, `f\circ g` | `f(g(x))`, with `g(x)` in the domain of `f`; of real functions `f`, `g`, the function `x\mapsto f(g(x))` |
| `$\sin$`, `$\exp$`, `\exp\circ f` (`\log`, `\cos`, `\tan`) | the standard function itself, a real function: `The function $\sin$ is $2\pi$-periodic.` |
| `|AB|`, `\angle ABC` of points (field `geometry`) | the distance between `A` and `B`; the angle at `B` between `A` and `C`, in `[0,\pi]`, defined for `A\neq B` and `C\neq B` |
| `A\subseteq B`, `A\supseteq B` | every real number in `A` is in `B` (and the reverse), for intervals, sets `\{x\in A : …\}` and sets the article defines |
| `\sup_{x\in A} e`, `\sup\{e : x\in A\}`, `\sup S` (and `\inf`) | the least upper (greatest lower) bound: defined only when it exists, so a claim about an unbounded or empty set is not meaningful |
| `\sum_{j=1}^{4} e`, `\prod_{k=0}^{2} e` | with numeral bounds: the terms written out |
| `\sum_{j=a}^{b} e`, `\prod_{j=a}^{b} e` | over the integers from `a` to `b`, which must be integers (`b<a`: the empty sum `0`, product `1`) |
| `x_1+\cdots+x_n`, `\frac1{1}+\dots+\frac1{N}`, `x_0\cdot\cdots\cdot x_{N-1}` | the sum (product) over the integers `i` from the index of the first term to that of the last, of the term both are instances of; the terms may differ in one place only, the index (`1+2+\cdots+n` is `1+\sum_{i=2}^{n} i`) |
| `a_1<\cdots<a_m`, `2\le n_1<\dots<n_k` | each term is in the relation to the next, for every integer index from the first to the last but one (and the rest of the chain as written) |
| `\sum_{k=a}^{\infty} e` | the limit of the partial sums, defined only when it exists (so conditionally convergent series such as `\sum_{k=1}^{\infty}\frac{(-1)^{k+1}}{k}` are read) |
| `\sum a_n`, `\sum_n a_n` | without bounds: only the series of the terms of an infinite sequence `(a_n)` that converges, diverges or converges absolutely (`$\sum a_n$ converges`; from the index `0`, which does not matter there); elsewhere a sum needs its bounds |
| `\sum_{d\mid n} e`, `\prod_{d\mid n} e` | over the positive divisors of a positive integer `n` (`\sum_{d\mid n}\varphi(d)=n`) |
| `f^\prime`, `f^{\prime\prime}` | as `f'` and `f''`: the derivatives |
| `\sum_{i=1}^n x_i^2\sum_{i=1}^n y_i^2` | a sum over the same index after the terms of a sum ends it: the product of the two sums |
| `\lim_{x\to a} e`, `\lim_{x\to\infty} e` | the limit within the points where `e` is defined (`x\ne a`), defined only when it exists and the points accumulate at `a` |
| `\limsup_{n\to\infty} a_n`, `\liminf_{x\to\infty} f(x)` | the number `L` such that for every `ε>0` the values exceed `L-ε` beyond every bound and eventually stay below `L+ε` (`\liminf`: the reverse); defined only when it is finite. An index runs through the natural numbers |
| `$a_n\to L$ as $n\to\infty$`, `$f(x)\sim g(x)$ as $x\to\infty$`, `$f(x)=o(g(x))$ as $x\to c$` | `\lim a_n=L`, `\lim\frac{f}{g}=1`, `\lim\frac{f}{g}=0`, as limits are read |
| `with $a_n\to0$`, `with $a_n\to L$ as $n\to\infty$`, `Suppose $a_n\to L$.` | the terms converge to `L`: for every `ε>0` there is `N` with `|a_n-L|<ε` for every natural number `n\ge N` (as `converging to $L$`); no limit has to exist beforehand, so a hypothesis needs no side condition |
| `$f\ge0$`, `$f\le g$` for real functions `f`, `g` (`f\colon[0,1]\to\mathbb{R}`), `$f''\ge0$` | at every point of the domain of the signature (without one, at every real number), `f(x)\ge0`, `f(x)\le g(x)` |
| `\lim_{x\to a} e=\infty`, `\lim_{n\to\infty} a_n=-\infty`, `$a_n\to\infty$ as $n\to\infty$` | the points where `e` is defined accumulate at `a` (are unbounded), and for every `M` there is `δ>0` such that `e>M` (`e<M`) at every such point with `0<|x-a|<δ` (there is `N` such that … at every such point `x\ge N`); an index runs through the natural numbers |
| `\lim_{n\to\infty} a_n` | for an index `n`, `m`, `k`, `j`, `i` (or `N`, `M`, `K`): the limit of the sequence through the natural numbers |
| `(-1)^k`, `2^{n+1}` | an exponent built from indices is an integer power, for any base. An exponent written as a quotient (`x^{1/k}`, `x^{\frac{1}{2k}}`) is a root: a real power of a nonnegative base, whatever its letters |
| `n!`, `\binom{n}{k}` | for natural numbers `n`, `k` |
| `\exp(x)`, `\exp x`, `e^{x}`, `\frac{1}{e}` | the exponential function, and `e` alone Euler's number `\exp(1)` (unless the article names something `e`, or a sentence binds it: `For every $e>0$`) |
| `\log x`, `\ln x` | the natural logarithm, applied only to positive numbers (the claim asks that the argument be positive) |
| `\sin x`, `\cos x`, `\tan x`, `\sin^2 x` | the trigonometric functions (`\tan` only where `\cos` is not zero); `\sin^2 x` is the square of `\sin x` |
| `\pi` | the number π, unless the article defines `\pi` |
| `\operatorname{sgn}(x)` | the sign of `x`: 1, −1 or 0 |
| `\max(a,b)`, `\min(a,b)` | as `\max\{a,b\}` |
| `\max_{x\in A} e`, `\max_{1\le k\le n} e`, `\sup_{\substack{n\ge1\\ \omega(n)\le k}} e`, `\min_{n\ge1,\ φ} e` | over the variable of the first condition, with all the conditions; a variable bounded by inequalities alone ranges over the real numbers, an index (`n`, `m`, `k`, `j`, `i`, `N`, `M`, `K`) over the integers. `e` must be defined at every such point |
| `\#\{x\in A : φ\}`, `\#A`, `|\{x : φ\}|`, `|A|` for a set `A` | the number of elements, defined only when the set is finite. `\#\{1\le t\le N : φ\}` for a letter `t` that is not an index and has no convention is refused: it would count real numbers. Write `t\in\mathbb{Z}`, or state the convention (`Throughout, $t$ denotes an integer.`) |
| `\sqrt[3]{x}` | `x^{1/3}`, for `x\ge0` |
| `2\times3` | the product of two numbers (between sets, `\times` is the product of the sets) |
| `A\cap B`, `A\setminus B`, `\{a,b\}`, `\emptyset` | intersection, difference, finite sets and the empty set of real numbers; `(a,b)` as a set is the open interval |
| `x\notin A` | not `x\in A` |
| `\mathbb{R}_{>0}`, `\mathbb{R}_{\ge0}`, `\mathbb{R}_+` | `(0,\infty)`, `[0,\infty)`, `[0,\infty)` |
| `\{x\in A\mid φ\}` | as `\{x\in A : φ\}` |
| `\forall x,y\in A: φ`, `\exists x\in A: φ` | quantifiers over real numbers in `A` (the domain ends at the first `:` or `,`; the body extends to the end of the formula) |
| `\neg`, `\land`/`\wedge`, `\lor`/`\vee`, `\Rightarrow`/`\implies`, `\iff`/`\Leftrightarrow` | the connectives, binding in this order (`\neg` the tightest) |
| `\int_0^1 x\,dx` | as `\int_0^1 x\,\mathrm{d}x` |
| `\int_a^b e\,dx`, `\int_1^2\frac1x\,dx`, `\int_0^x t^2\,dt` | the oriented integral of a function of a real variable. It is meaningful when `e` is defined at almost every point between `a` and `b` and integrable there (so `\int_1^2\frac1x\,dx` and `\int_0^1\frac{1}{\sqrt x}\,dx` are, and `\int_{-1}^1\frac1x\,dx` is not): an integral does not depend on a set of measure zero, so the integrand may be undefined on one. With the field `unitsquare`, `\int_0^1` is the integral over the type `[0,1]` |
| `\int_{[0,1]^2} e\,\mathrm{d}C(u,v)` | with the field `unitsquare`: the integral of `e`, a function of the points `u`, `v` of the unit square, against the probability measure whose distribution function is `C` (a copula). It is meaningful when `C` is a distribution function on `[0,1]^2` and `e` is integrable for that measure and defined at almost every point for it (`\Phi_{\mathrm N}^{-1}(u)` has no value at `u=0`) |
| `\max_{(u,v)\in[0,1]^2} e`, `\sup_{u,v\in A} e`, `\inf_{s\in A,\ t\in B} e` | an extremum over the values of `e` at all pairs |
| `\sup\{e : f,g\in\mathcal F\}` | the variables before a membership are in the same set; a variable in a class of the article ranges over its members (functions, if it is a class of functions) |
| `f^{-1}(a)`, `\Phi_{\mathrm N}^{-1}(u)` | the inverse of a function that the article defined, at `a`: the element of the domain that the function sends to `a`. It is meaningful where exactly one element is sent to `a` |
| `\{(0,0)\}`, `\{(0,0)\}\cup\{(k,r) : 0<k\le r\le1\}` | braces around a pair are the set of that pair; sets of pairs are joined and compared like sets of numbers |
| `e^x` beside a family `e_t` | a family is written with its subscript and does not take its letter: `e^x` is still `\exp(x)` |
| `\mathbb{E}_C[e]`, `P_C(φ)` | with the field `unitsquare`: the expectation of `e` and the probability of the condition `φ` for a sample of independent observations `(U_i,V_i)`, `i=0,1,2,\ldots`, each with the copula `C` as distribution function. Inside the brackets, `U_i` and `V_i` are the coordinates of the observation with index `i`: `\mathbb{E}_C[\sgn(U_1-U_2)\sgn(V_1-V_2)]`, `P_C(|U_1-V_1|\le\varepsilon)`. The expectation is meaningful when `e` is integrable for the law of the sample, the probability when the condition has one |
| `Let $F$ be a kernel and let $C$ be a copula.`, `Let $T$ be a statistic.`, `K_F(C)\coloneqq\mathbb{E}_C[F(U)F(V)]`, `P_C(R(C)\le T(U,V))` | with the field `unitsquare`: inside `\mathbb{E}_C[…]` and `P_C(…)`, the letters `U` and `V` alone are the two sequences of the sample. A *kernel* is a real function of a sequence in `[0,1]` that depends on finitely many of its terms and is square-integrable for independent uniform terms (a function in `L^2([0,1]^m)` for some `m`), and a *statistic* is a real function of two sequences that depends on finitely many observations and is measurable in them. `Let $\mathcal B$ denote the class of copulas with bounded density.`: a copula *with bounded density* is the iterated integral of a bounded measurable function |
| `For every sequence $x$ in $[0,1]$ and every integer $n\ge1$, …`, `Let $y$ be a sequence in $[0,1]$.` | with the field `unitsquare`: a variable that is a sequence of points of `[0,1]`. `x_n` is its term at the natural number `n`, and a condition on its terms (`if $U_1\le V_1$, then …`) is a hypothesis about the sequence, not a new variable `U_1`. A noun of a vocabulary with its variable inside the phrase is a binder in the same way (`every probability measure $\gamma$ on $[0,1]^2$`) |
| `On the event $|\tau_n-\tau(C)|<\varepsilon$, we have $|\tau(C)|\ge|\tau_n|-\varepsilon$.` | with the field `unitsquare`: the first formula implies the second for all values of the two sequences `U`, `V` of a sample (`∀ U, ∀ V, φ ⇒ ψ`). It is the step of a proof that compares two events; the probabilities are compared in the next sentence (`Hence $P_C(ψ)\ge P_C(φ)$.`) |
| `C^{\ast k}`, `M_r^{\ast k}` | with the field `unitsquare`: the Markov power of order `k` of a copula, the Markov product of `k` factors `C` (the copula of `(X_0,X_k)` for a stationary Markov chain whose steps have the copula `C`). It is meaningful for a copula `C` and an integer `k\ge1`. A star alone, `\tau^*`, is part of a name |
| `\tau^*(C)`, `\Phi^2(C)` | a symbol may carry a star, and it may carry a numeral as superscript while its letter alone names nothing in the article (`\Phi^2` is then a name, never a square; defining both `\Phi` and `\Phi^2` is refused) |
| `\int_{-\infty}^x e\,dt`, `\int_a^\infty e\,dt`, `\int_{-\infty}^\infty e\,dt` | the integral over a ray or the line: meaningful when `e` is defined at almost every point of it and integrable over it |
| `\int_0^1\int_0^1 e\,ds\,dt` | iterated integrals: the innermost integral takes the first differential |
| `\cosh x`, `\sin^2 x`, `\arctan x` | a named function (LaTeX's operator names) applies to what follows it, with or without parentheses. What the name means is said by the core (`\exp`, `\log`, `\sin`, `\cos`, `\tan`) or by a field (`\cosh` in `hyperbolic`, `\arcsin` with its domain `[-1,1]` in `trigonometry`); a name without a meaning is reported, with the field that reads it |
| `\mathbb{N}`, `\mathbb{N}_0`, `\mathbb{Z}` | the natural numbers (with 0, as in mathlib; write `n\ge1` for the positive ones) and the integers, as real numbers |
| `\lfloor x\rfloor`, `\lceil x\rceil` | the largest integer at most `x`, the smallest at least `x` |
| `\mathbf 1\{x\le v\}`, `\mathbf{1}_{\{φ,\ ψ\}}`, `\mathbb{1}\{φ\}`, `\mathbf 1_A(x)`, `\mathbf{1}_{[0,1]}(x)` | the indicator: `1` where the condition holds (where all the conditions hold) and `0` elsewhere; of a set `A` at `x`, the indicator of `x\in A`, for a set that is read after `\in` (for a half-open interval, write the condition: `\mathbf 1\{1<x\le2\}`) |
| `x^{-1}`, `x^{-2}` | `\frac1x`, `\frac1{x^2}`: defined for `x\ne0`, of either sign |
| `(x-1)^+`, `f(x)^-` | the positive part `\max\{x-1,0\}` and the negative part `\max\{-f(x),0\}` of a value that is not a name: `x^+` and `R^+` are names of their own (`We write $x^+$ for …` gives `x^+` a meaning) |
| `$$…$$` | a display, like `\[…\]` |
| `:=`, `\vcentcolon=`, `\colonequals`, `\triangleq`, `\mathrel{:=}` | the defining sign, as `\coloneqq` (so a macro `\defeq` of the article for one of them is read too) |
| `\colon`, `\leqslant`, `\geqslant`, `\lvert`/`\rvert`, `\lbrace`/`\rbrace` | `:`, `\le`, `\ge`, a vertical bar, `\{`/`\}` |
| `||x|-|y||`, `\big||x|-|y|\big|` | absolute values inside an absolute value: a bar where an operand begins opens another (`\big`, `\left`, `\right` are layout) |
| `a\mid b`, `a\nmid b` | `a` and `b` are integers and `b=ak` for an integer `k` (and its negation, for integers); the first `\mid` of a set `\{x\in A\mid φ\}` separates the condition, and a `\mid` after it is divisibility |
| `a\equiv b\pmod m`, `a\equiv b\ (\bmod m)`, `(\operatorname{mod} m)` | `a` and `b` are integers and `m\mid a-b` |
| `\{1\le n\le N : φ\}`, `\{x>0 : φ\}` | the variable bounded by the inequalities, with `φ`: an index (`n`, `m`, `k`, `j`, `i`, `N`, `M`, `K`) among the integers, any other variable among the real numbers |
| `\gcd(a,b)` | for integers `a`, `b`: the natural number `d` that divides both and that every common divisor divides (so `\gcd(0,0)=0`) |
| `\mathbb{Q}` | the rational numbers, as real numbers |
| `\mathbb{C}`, `complex number`, `\mathrm{i}` (`\mathrm i`), `z+w`, `zw`, `z/w`, `z^n`, `\lvert z\rvert`, `\overline{z}`, `\bar z`, `\operatorname{Re}(z)`, `\Re z`, `\Im z`, `e^{z}`, `\exp(z)`, `\sum_{k=a}^{b}` of complex terms | with the field `complex` (`\usepackage[vocab={complex}]{leanify}`): the complex numbers (Mathlib `ℂ`). Notation means what the type of its operands says, as in Python: with a complex operand, `+` is complex addition, and a real operand is a complex number; `z/w` is defined for `w\ne0`, `z^n` for a natural number `n` (`z^{-n}` is `1/z^n`), `\lvert z\rvert` is the modulus. `\mathbb{C}` has no order, so `z\le w` is refused with a finding. A bare `i` that nothing in the article names (no variable, no definition, no sentence that Leanify does not read) is the imaginary unit, as `e` alone is Euler's number (`e^{i\theta}`); `\mathrm{i}` always is. `docs/vocabularies.md` explains how a field gives notation a meaning on its own types |
| `\mathbb{F}_p`, `\mathbb{Z}/p\mathbb{Z}` | refused with a finding: write their elements as integers, and equations between them as congruences (`a\equiv b\pmod p`) |
| `\hat x`, `\hat{x}` | a name of its own (a variable `\hat x` beside `x`), unless the article or its vocabulary defines `\widehat` as an operation |
| `\tilde x`, `\bar x`, `\dot x`, `\ddot x`, `\vec x`, `\breve x`, `\check x`, … | names of their own |

The period of an abbreviation (i.e., e.g., cf., resp., Thm., Eq., Fig., …)
does not end a sentence.

### The article's own notation and conventions

An article introduces notation and conventions in sentences of its own; they hold
for the rest of the article (`tests/Vocabulary/article.tex` uses each form):

| Sentence | Effect |
| --- | --- |
| `We write $\langle a,b\rangle$ for $\frac{a+b}{2}$.` | later formulas `\langle x,y\rangle` are read as `\frac{x+y}{2}`; the letters and commands of the pattern that occur on the right are its arguments (`Let us write …` too) |
| `We write $a\sim b$ if $|a-b|\le1$.` | a relation, read the same way |
| `We write $r_k$ for $R(C^{\ast k})$.`, `We write $x^+$ for $\max\{x,0\}$.` | an argument in a subscript or a superscript is one symbol or one group, as in TeX: `r_k^{1/k}` is `r_k` to the power `1/k`, and `r_{k+1}` has the argument `k+1`. An argument before a script is the symbol or group before it, with the scripts the notation does not use: `x_1^+` is `\max\{x_1,0\}`. A letter on the right that is not an argument (`C`) is the one of the sentence that uses the notation |
| `We write $h_a$ for $a^2+1$.`, then in a result `For $x\in\mathbb R$, let $h_y(x)\coloneqq x+y$.` | a symbol that a result or its proof defines hides a notation of the article written with the same letter: in the sentence that defines it and after it, in the result and its proof, `h_y` is that symbol; elsewhere `h_2` is the notation |
| `We write $\ell_A(x)$ for $\min\{R(C) : C\in\mathcal C,\ A(C)=x\}$.` | a notation may bind a variable (the `C` of the set, the variable of an integral, a sum or a limit). Where it is written with a formula that uses the same letter, `\ell_\beta(\beta(C))`, the bound variable is another one: the minimum is over the copulas whose `\beta` is `\beta(C)` |
| `We write $A\subset B$ if $A\subseteq B$.` | one relation symbol for another: every later `\subset` is `\subseteq`, whatever stands on either side (Leanify refuses `\subset` without such a sentence, since it also means strict inclusion) |
| `We write $\mathrm{Poi}(\lambda)$ for the Poisson distribution with mean $\lambda$.` | a symbol for a notion of the vocabulary, with its arguments |
| `We write $C_n$ for the $n$th Catalan number.`, `We write $\deg_G(v)$ for the degree of $v$ in $G$.`, `We write $M_n$ for the set of $n\times n$ matrices.` | the same, for the notions of the fields of other branches (`docs/vocabulary.md`); `$n$-th` is `$n$th`, and a letter that stands for several arguments (`n` of `$n\times n$`) is one argument of the notation |
| `We write $\mathcal P$ for the set of probability distributions on $\mathbb{N}_0$.` | a symbol for the class of a vocabulary noun |
| `By a distribution we mean a probability distribution on $\mathbb{N}_0$.` | a noun of the article (`Let $\nu$ be a distribution.`) |
| `Throughout, increasing means non-decreasing.`, `In this paper, …` | the words stand for the others in the following sentences (`strictly increasing` is unchanged) |
| `Throughout, $p$ and $q$ denote integers.`, `In this paper, the letters $s,t$ always denote integers.`, `Here and below, $d$ is an integer.` | from here on, each of the letters is an integer wherever it is bound: `For every $p\ge2$`, `If $q>2$`, `Let $p\in[1,3]$`, `\{1\le p\le5 : φ\}`, `\max_{1\le p\le3}`, `\forall p\in A`; `\lim_{q\to\infty}` is the limit of a sequence, and an exponent built from them is an integer power. Without the convention, a letter other than `n`, `m`, `k`, `j`, `i`, `N`, `M`, `K` bounded by inequalities alone is a real number |

### Objects of the fields, and modifiers with numbers

A field may have objects of a type of its own (graphs, permutations, matrices), which an
article binds as it binds numbers, and modifiers that take numbers:

| Sentence | Reading |
| --- | --- |
| `Let $G$ be a graph on $n$ vertices.`, `For every positive integer $n$ and every tree $T$ on $n$ vertices, …`, `For every $k$-regular graph $G$ on $n$ vertices, …` | a modifier with numbers (`on $v$ vertices`, `$v$-regular`): its formulas are terms of the sentence, here the variable `n` of the result, and not variables that the noun phrase binds |
| `Let $p$ be a polynomial of degree $n$.`, `Let $A$ and $B$ be $n\times n$ matrices.`, `Let $A$ be an invertible $n\times n$ matrix.` | the same before the noun (a formula with `\times`, or followed by a hyphen) and after it |
| `$\sigma(i)$`, `$\sigma\tau$`, `$\sigma^k$` | a permutation applied to a number, a composition and a power: the field's notation, defined where it fits (`\sigma(i)` for `1\le i\le n`, `\sigma\tau` for permutations of the same degree) |
| `$AB$`, `$2A$`, `$A+B$`, `$A^{-1}$`, `$A^\top$` (or `$A^T$`), `$\det A$`, `$\operatorname{tr}(A)$` | the algebra of matrices: `AB` asks that the columns of `A` are as many as the rows of `B`, `A^{-1}` that `A` is invertible; a claim that uses them is meaningful only then |
| `$\deg p$`, `$\deg(pq)=\deg p+\deg q$` | `\deg` and `\det` apply to what follows them, as `\sin` does; the product of two real functions, or of a number and a real function, is taken value by value |
| `$\overline{G}$` | the complement of a graph (a decoration of the field's type) |

Structures with their elements (the field `structures`):

| Sentence | Reading |
| --- | --- |
| `Let $G$ be a group and let $g,h\in G$.`, `Let $g$ be an element of $G$.` | a structure is the set of its elements: `g\in G` binds an element as `x\in A` binds a number |
| `$(gh)^{-1}=h^{-1}g^{-1}$`, `$g^2=1$`, `$a(b+1)=ab+a$`, `$c(v+w)=cv+cw$` | the operations of the structure the elements belong to; `1` and `0` are its identity and zero; `cv` with a scalar `c` of the field over which `v`'s space is a vector space is the scalar multiple; `x^{-1}` and `x/y` ask that the element is invertible (every element of a group, a nonzero element of a field) |
| `Let $H$ be a subgroup of $G$.`, `Let $I$ be a prime ideal of $R$.`, `Let $V$ be a vector space over $K$.`, `Let $F$ be a closed subset of $X$.`, `$H$ is a normal subgroup of $G$.` | a noun with a complement (`of`, `over`, `in`): the object it names is a term of the sentence |
| `Let $\varphi\colon G\to H$ be a homomorphism.`, `Let $T\colon V\to W$ be a linear map.`, `Let $f\colon X\to Y$ be a continuous map.` | a map bound by its signature: it maps `G` into `H`, and the noun (`homomorphism`, `linear map`, `isometry`) and adjectives (`injective`, `continuous`) are meant on its domain; `\varphi(1)` is its value at the identity of `G` |
| `Let $f\colon X\to\mathbb{R}$ be continuous.`, `$f$ is bounded`, `uniformly continuous`, `Lipschitz`, `Every continuous function on a compact metric space is bounded.` | a real function on a space, said on the space: `|f(x)|\le M` for some `M`; for every `\varepsilon>0` a `\delta>0` with `|f(x)-f(y)|<\varepsilon` where `d(x,y)<\delta` (Mathlib `UniformContinuousOn`); `|f(x)-f(y)|\le K\,d(x,y)` for some `K\ge0` (`LipschitzOnWith`) |
| `the image of $K$ under $f$` | `f(K)`, of a set `K` of the domain of a map (Mathlib `Set.image`) |
| `$A\cap B\neq\emptyset$`, `$H\neq\emptyset$` | the empty set of the kind of the other side (of the elements of a structure) |
| `Let $a\in G$ have order $n$.` | `Let $a\in G$ be of order $n$.` (also `characteristic`, `dimension`, `index`, `degree`) |
| `Let $A$ be a set of real numbers and $f\colon A\to A$ a function.`, `Let $B$ be a subset of $A$.` | the same for sets of real numbers: `f` maps `A` into `A`, `B\subseteq A` |
| `Let $V$ be a vector space over a field $K$.`, `Let $H$ be a subgroup of a finite group $G$.` | a complement that introduces its own object binds it first: `K`, then `V` |
| `Let $x\in A$ be positive.`, `Let $a\in L$ be algebraic over $K$.`, `Let $g\in G$ be an element of order $2$.` | an element of the domain that is as the words say (`an element $x$ of $A$` with the adjectives, or the noun phrase with the variable's domain, which decides between nouns with the same words) |
| `Let $\varphi\colon G\to H$ be an isomorphism.`, `$\varphi$ is surjective`, `Let $f\colon G\to H$ be a bijection.` | a map between structures carries its domain and codomain (as Mathlib's bundled maps): `isomorphism`, `automorphism`, `bijection`, `surjective`, `bijective` are about them; a signature also decides between nouns of maps of different types (of structures, of real numbers) |
| `$\ker\varphi=\{1\}$`, `$\ker\varphi$ is a normal subgroup of $G$`, `$\psi\circ\varphi$`, `Let $c$ be an eigenvalue of $T$.`, `Let $f\colon X\to X$ be a contraction.` | the kernel and image (`\ker`, `\operatorname{im}`, `the kernel of $\varphi$` in a `We write` definition), rank and nullity (`\operatorname{rank} T` with or without parentheses), composition, eigenvalues, eigenvectors and fixed points of a map; a finite set of numbers compared with a set of elements is a set of elements |
| `Let $X$ be a Banach space.`, `$\|x+y\|\le\|x\|+\|y\|$`, `$\langle x,y\rangle=0$`, `$\|cx\|=|c|\|x\|$` | real normed, Banach, inner product and Hilbert spaces: the norm and the inner product of the space; a real number times an element is the scalar multiple |
| `Let $B$ be a basis of $V$.`, `$B$ is linearly independent`, `the dimension of $V$`, `$V$ is finite-dimensional` | linear algebra over the space's own scalars (those of `vector space over $K$`) |
| `$\dim(U+W)=\dim U+\dim W-\dim(U\cap W)$`, `$V=U\oplus W$` | the sum of two subspaces of one module (the sums `u+w`; meaningful for subspaces with the same operations), and the direct sum: `V=U\oplus W` says that `U` and `W` have only `0` in common and that their sum is `V` |
| `Let $B$ be an orthonormal subset of $V$.`, `an orthogonal subset $C$ of $V$ with $0\notin C$` | a subset of an inner product space whose elements have norm `1` and are orthogonal to each other (`orthogonal`: only the latter) |
| `$V=U\oplus U^{\perp}$`, `$W^{\perp}\subseteq U^{\perp}$`, `the orthogonal complement of $U$` (of a subspace `U` of `V`), `the orthogonal complement of $U$ in $V$` | the elements of the inner product space `V` that `U` is a subset of whose inner product with every element of `U` is `0` (Mathlib `Submodule.orthogonal`, `Uᗮ`); `U^{\perp}` is this where the article defines no `^{\perp}` |
| `Let $P$ be a Sylow $p$-subgroup of $G$.`, `$G$ has a Sylow $p$-subgroup.`, `every Sylow $p$-subgroup of $G$` | a subgroup of `G` that is a `p`-group for a prime `p` and lies in no larger `p`-subgroup of `G` (Mathlib `Sylow`); read as `subgroup of $G$ with $p$ as Sylow prime` |
| `$R/I$ is a field if and only if $I$ is a maximal ideal`, `$|G/N|=|G|/|N|$`, `$G/\ker\varphi$ is isomorphic to $\operatorname{im}\varphi$`, `$\dim(V/W)=\dim V-\dim W$` | the quotient of a ring by an ideal, of a group by a normal subgroup, of a module by a subspace: one element for each class, with the operations of the structure on the classes (Mathlib `R ⧸ I`); meaningful for these pairs only |
| `$K[x]$ is a principal ideal domain`, `$R[x]$ is an integral domain`, `the polynomial ring over $R$` | the ring of polynomials in one variable over a ring (a capital letter before `[x]`, any small letter as the variable): the lists of coefficients without zeros at the end, with the sum and the product of polynomials (Mathlib `Polynomial R`); meaningful for a ring |
| `Let $f\in K[x]$ be a nonzero polynomial of degree $n$.`, `$f$ has at most $n$ roots in $K$`, `$f$ has a root in $K$`, `$f$ has no root in $K$`, `$f$ is irreducible over $K$`, `$\deg f=1$`, `the degree of $f$` | an element of a ring of polynomials (`polynomial over $K$`; `polynomial` of a variable `f\in K[x]` is over `K`); its degree, of a nonzero polynomial, is the highest power of `x` with a nonzero coefficient (Mathlib `Polynomial.natDegree`); its roots in `K` are the elements of `K` where its value is `0`, and `at most $n$ roots` says that they are finitely many, at most `n` (Mathlib `Polynomial.roots` as a set); `irreducible over $K$` is irreducible in `K[x]` |
| `the symmetric group $S_n$`, `the alternating group $A_n$`, `the cyclic group $C_n$` | `the symmetric group of degree $n$`, `the alternating group of degree $n$`, `the cyclic group of order $n$` (the standard letter of the group, after its name) |
| `$X$ is Hausdorff if and only if the diagonal of $X$ is closed in $X\times X$` | the pairs `(x,x)` of the product space (Mathlib `Set.diagonal`) |
| `$1\in H$`, `$0\notin C$` | a number in a set of elements is that element of the set's structure: the identity of the subgroup `H`, the zero of the space of `C` |

Further forms that the fields use (they are read for any vocabulary):

| Sentence | Reading |
| --- | --- |
| `Every cyclic group $G$ is abelian.`, `Every point $P$ lying on $\Gamma$ is distinct from $O$.` | `Every NP $x$ is …` is `For every NP $x$, $x$ is …`: adjectives and nouns of the vocabulary about each object of the noun phrase; without a variable (`Every subgroup of $G$ of order $2$ is cyclic.`) the object has one of its own, after the noun's words |
| `Every ideal $M$ of $R$ is maximal if and only if $R/M$ is a field.`, in a result `An ideal $M$ of $R$ is prime if and only if $R/M$ is an integral domain.` | `For every ideal $M$ of $R$, $M$ is maximal if and only if $R/M$ is a field.`: the letter is bound for the whole sentence |
| `Every integer greater than $1$ has a prime divisor.`, `Let $n$ be an integer greater than or equal to $2$.`, `a real number less than $0$` | a number with a bound after the noun: `greater than`, `larger than`, `less than`, `smaller than`, `greater than or equal to`, `less than or equal to` (core vocabulary) |
| `Every increasing sequence that is bounded above converges.`, in a result `A nonempty set of integers that is bounded above has a greatest element.` | `that is` (`which is`, `that are`) before words about the noun: the words as adjectives of the noun, `Every bounded above increasing sequence converges.` (the clause ends before the last verb) |
| `$S$ is compact if and only if $S$ is closed and bounded.`, `$G$ is cyclic or $G$ is isomorphic to $V$.`, `$n_3(G)=1$ or $n_3(G)=4$.` | two clauses joined by `if and only if` or by `or`, each a clause of its own (a formula, adjectives, a noun) |
| `Let $M$ be the midpoint of $A$ and $B$.`, `let $H$ be the direct product of $C_2$ and $C_3$` | a variable that is the value of a notion of the vocabulary with its arguments (a number or an object of a field's type): a hypothesis `M = …` of what follows |
| `$a$ is congruent to $b$ modulo $n$`, `$x$ is orthogonal to $y$`, `$G$ is isomorphic to $C_4$`, `$S$ is null` | a modifier of the vocabulary after `is`, with its arguments: numbers, or objects of the type the modifier names (a vector, a group, a set of points) |
| `Let $a$ be an integer coprime to $n$.`, `Let $P$ be a point equidistant from $A$ and $B$.`, `Let $S$ be a set of measure zero.` | a modifier after its noun in a `let`, with or without arguments |
| `Let $a$, $b$ and $c$ be real numbers with $a\ge0$.`, `Let $a$ and $b$ be real numbers with $a\ge0$, $b\ge0$ and $|b|<c$.`, `Let $x>0$ and $x<1$.` | a condition joins the domain of the last variable that it mentions (here `a`; each of several joined by `and` on its own), so that it stays when the claim does not use `c`. A formula after a comma or an `and` that only restates variables the sentence has bound (`$b\ge0$`, `$|b|<c$` with `c` bound before) is a further condition on them, not a new variable that hides the first |
| `$\mathcal{C}$ is compact and perfect and nowhere dense` | adjectives of the core language (`compact`) and of a field (`perfect`) in one list, joined by `and`: where the core language has no such property of the object, the field's adjective with these words is meant |
| `$\lVert x+y\rVert\le\lVert x\rVert+\lVert y\rVert$`, `$\langle x,y\rangle$` | the norm and the inner product of objects of a field's type that has them (vectors) |
| `the area of the triangle with vertices $A$, $B$ and $C$` | a phrase of the vocabulary may have commas |
| `$C_n$ is connected, Hamiltonian and $2$-regular.` | a list of adjectives with commas is the list joined by `and`; an adjective may begin with a formula and a hyphen (`$1$-Lipschitz`, `$2$-regular`), also after `is` (`$f$ is $1$-Lipschitz`) |
| `If $|f'(x)|\le1$ for every $x\in\mathbb{R}$, then …`, `If $a\le\varepsilon$ for every $\varepsilon>0$, then …` | a hypothesis that binds its own variable: `(∀ x, …) → …` |
| `If $\alpha(C,A,B)=\frac{\pi}{2}$, then …` | a standard constant (`\pi`, `\mathbb{R}`) in a hypothesis is the constant, never a new variable |
| `$f'(0)=0$`, `$|f'(x)|\le1$` | the derivative of a real function bound by a noun (`a differentiable function $f$`) |
| `$f''\ge0$`, `$f''(0)$`, `$(fg)'=f'g+fg'$`, `$(f+g)'(x)$` | the derivative of the derivative, of a sum or product of functions (as functions: `t\mapsto f(t)g(t)`), defined where it exists |
| `$\gcd(a,b)\cdot\operatorname{lcm}(a,b)=ab$`, `$\dim\ker T+\dim\operatorname{im}T=\dim V$` | the least common multiple (a natural number, `0` if `a` or `b` is); an operator name after another applies to what follows (`\dim(\operatorname{im}(T))`) |
| `Suppose that $f(x)\ge0$ for all $x$.`, `… for all $a_n$` | a letter without a domain after `for all`: a real number (a natural number where it is the index of a subscript) |
| `Every bounded monotone sequence converges.`, `Every NP diverges`, `… vanishes`, `… divides $n$` | for every object of the noun phrase, the verb said of it |
| `Let $a<b$ and let $f\colon[a,b]\to\mathbb{R}$ be continuous on $[a,b]$ and differentiable on $(a,b)$.` | the numbers `a`, `b` with `a<b` (a letter that only bounds the interval is bound with it), the map, then the hypothesis `Suppose that $f$ is continuous on $[a,b]$ and differentiable on $(a,b)$.` |
| `The set $\mathbb{Q}$ is dense in $\mathbb{R}$.`, `a set of real numbers that is dense in $[0,1]$` (field `realsets`) | a subset of the set whose closure contains it; with the field `topologies` too, `dense in $\tau$` of a topology is that field's: the words have the meaning whose argument the formula fits |
| `If $G$ and $H$ are isomorphic, then …`, `$X$ and $Y$ are homeomorphic`, `$M$ and $N$ are quasi-isometric` | two objects in a relation: `$G$ is isomorphic to $H$` (the vocabulary's `WORDS to $v$`, `with $v$` or `from $v$`) |
| `Let $A$ and $B$ be similar matrices.`, `Let $G$ and $H$ be isomorphic groups.` | the first object, and the second one in the relation to it (`a matrix $B$ similar to $A$`) |
| `$A$ and $B$ have the same characteristic polynomial.`, `Similar matrices have the same trace.` | `the characteristic polynomial of $A$ equals the characteristic polynomial of $B$`; of a plural noun phrase with a relation, for every two such objects |
| `$G$ has no cycle of odd length`, `$v$ has even degree`, `every vertex of $G$ has even degree` (field `graphs`) | `has no NOUN of WORDS` is `without NOUN of WORDS`; `has WORDS` without an article is `with WORDS` (`with even degree in $G$` for a vertex of `G`) |
| `$G$ is Eulerian if and only if every vertex of $G$ is of even degree.` | a clause about every object of a noun phrase on either side of `if and only if` |
| `the sum of the degrees of the vertices of $G$`, `the number of vertices of $G$ of odd degree` (field `graphs`) | the notions of the handshake lemma |
| `Every graph has an even number of vertices of odd degree.`, `$G$ has an odd number of …` | the number of those objects of the subject (the notion `number of … of $G$`) is `2k` (`2k+1`) for an integer `k` |
| `The sum of the degrees of the vertices of $G$ is twice the number of edges of $G$.` (`thrice`) | the subject equals `2` (`3`) times the notion or formula after `twice` |
| `$2\pi(1-\cos t)$` | `\pi` before parentheses is a factor: no function is named `\pi` |
| `The number of $2$-permutations of $4$ elements is $12$.`, `The multinomial coefficient of $4$ over $1$, $2$ and $1$ is $12$.` (field `counting`) | a notion of the vocabulary as the subject: its hyphens (`$k$-element`) and the commas of a list of arguments ending in `and` are words of the notion |
| `For all $n\in\mathbb{N}$, the number of subsets of a set of $n$ elements is $2^n$.` (in a result) | a claim about the notion at the binder's variables, when it is no definition of the words (`For B, the NAME of $x$ is DEF` that defines nothing) |
| `Any two bases of a finite-dimensional vector space have the same number of elements.`, `Any two groups of order $3$ are isomorphic.` | for every two objects of the noun (of one object of a noun after `of a`, `of an`, bound first), the notion of the one equals that of the other; `are WORDS`: the first is WORDS to (with, from) the second |
| `Let $f\colon X\to X$ be injective. Then $f$ is surjective.`, `a bijective function $g\colon[0,1]\to[0,1]$` | of a function with a signature: onto its codomain (every point of `X` is a value at a point of `X`); bijective is injective on the domain and onto the codomain |
| `For all real numbers $a$, $b$ and $c$, …`, `For all sets $A$, $B$ and $C$, …` | a binder for each name, the last after `and` |
| `Every nonempty set of natural numbers has a least element.`, `a set of integers that is bounded above` (field `realsets`) | sets of natural numbers, of integers and of positive integers; `with a least element` (`has a least element`), `with a greatest element` |
| `$P(|X-\mathbb{E}X|\ge t)\le\frac{\operatorname{Var}X}{t^2}$`, `\operatorname{Var}(X+Y)=\operatorname{Var}X+\operatorname{Var}Y` (field `randomvariables`) | an expectation or a variance inside a probability is a number, not a function of the outcome; `\operatorname{Var}X` is `\operatorname{Var}(X)` |
| `$\mathbb{E}[XY]=\mathbb{E}X\,\mathbb{E}Y$` | in a product, an expectation without parentheses is of the factor right after it |
| `E[X]`, `\mathrm{E}[X^2]` (field `randomvariables`) | the expectation, as `\mathbb{E}[X]` (the brackets are no application, whatever `E` names) |
| `Let $A$ be an $n\times n$ matrix with $n$ distinct eigenvalues.`, `the row rank of $A$`, `the column rank of $A$` (field `matrices`) | a square matrix with exactly `n` real eigenvalues; the ranks of `Aᵀ` and of `A` |
| `Let $K\subseteq L\subseteq M$ be fields.`, `Let $A\subseteq B$ be finite sets.` | new variables, each an object of the plural noun, with the chain of inclusions as a condition (`$A\subseteq X$ be finite`, of a bound `X`, is a subset of it) |
| `Let $K\subseteq L$ be fields with $[L:K]=2$.` | the condition after `with` comes after the inclusions (which it may need) |
| `every closed and bounded subset of $X$` | adjectives joined by `and`, one of them relative to the complement (`closed in $X$`) |
| `Let $T\colon V\to W$ be a linear map between finite-dimensional vector spaces.` | both letters of the signature are objects of the noun after `between` (in the singular), then the map |
| `$U\cap W$ and $U+W$ are subspaces of $V$`, `$a^2$ and $b^2$ are nonnegative` | each of the two formulas is as the words say (a plural noun in the singular); not for a relation of the two (`isomorphic`, `distinct`, …) |
| `every subspace of $V$ has dimension at most $3$`, `has order at most $6$` (`at least`) | finite-dimensional of dimension `\le 3`; finite with at most `6` elements (at least: or infinite) |
| `Let $G$ be a group of order $p^n$, where $p$ is a prime and $n\ge1$.`, `Let $H$ be a subgroup of $G$, where $G$ is a finite group and $|G|=6$.` | the letters after `where` first, each as its part says (`$v$ is a NP`, a condition `$n\ge1$`; a condition on the letter of the part before is said `with` it), then the object |
| `$[M:K]=[M:L][L:K]$` | a degree or an index after another is a factor |
| `$N$ contains $H$`, `$N$ contains the commutator subgroup of $G$`, `$A$ contains $x$` | `H\subseteq N` of a set, `x\in A` of an element |
| `The closure of a connected subset of a topological space is connected.`, `Let $B$ be the interior of $A$.` (field `structures`) | the closure and the interior of a subset `A` of `X` in the space `X` of its noun's complement |
| `For every cyclic group $X$ and every subgroup $Y$ of $X$, …. Let $X$ be a group.` | a variable bound again is a new object: the variables bound about the old one (`Y`) end with it |
| `Every finite field has prime power order.`, `the commutator subgroup of $G$` (field `structures`) | `|F|=p^k` for a prime `p` and `k\ge1`; the subgroup generated by the commutators |
| `Every prime $p\equiv1\pmod4$ is a sum of two squares.` | a noun with its variable and a congruence about it |
| `$x$ is zero`, `the Lebesgue measure of $A$ is zero`, `Every countable subset of $\mathbb{R}$ has Lebesgue measure zero.` | a number equal to `0`; a set with `with Lebesgue measure zero` (field `realsets`) |
| `$|A\cup B|=|A|+|B|-|A\cap B|$` | the numbers of elements of the union and the intersection of finite sets |
| `Let $L$ be a complete lattice.`, `Every partially ordered set in which every chain has an upper bound has a maximal element.` (field `structures`) | every subset of a complete lattice has a least upper bound; every subset of comparable elements has an upper bound in the set (the hypothesis of Zorn's lemma) |
| `For every integer $x$ with $x>1$ and $x<5$, …`, `There is an integer $x$ with $x\equiv a\pmod m$ and $x\equiv b\pmod n$.` | a formula after `and` about the variable that the noun phrase has just bound is one more condition on it (not a new variable with the same letter); after `there is`, both conditions hold for the one object |
| `Then there exists a primitive root modulo $p$.`, `Let $g$ be a primitive root modulo $p$.` (field `congruences`) | the nouns `primitive root`, `quadratic residue` and `quadratic nonresidue` with their modulus |
| `Every bounded entire function is constant.`, `Let $U$ be a connected open subset of $\mathbb{C}$ and let $g\colon U\to\mathbb{C}$ be holomorphic.`, `Let $V$ be a domain in $\mathbb{C}$.` (field `complex`) | a complex function that is bounded, constant or holomorphic on its domain (`\mathbb{C}` for an entire function, `U` for `g`); `holomorphic on $V$` is complex differentiable at every point of `V`, and a domain in `\mathbb{C}` is a nonempty open connected set |
| `Let $f$ be an entire function with $f(z+1)=f(z)$ and $f(z+\mathrm{i})=f(z)$ for all $z\in\mathbb{C}$.` | two conditions joined by `and` under one `for all`: both hold for every `z` |
| `Then $f'$ is holomorphic on $U$.`, `If $h'(z)=0$ for all $z\in\mathbb{C}$, then $h$ is constant.` (field `complex`) | the complex derivative of a complex function: at each point `z` of the domain of its signature (`U` for `f\colon U\to\mathbb{C}`, `\mathbb{C}` for an entire function), the one `d` with `HasDerivAt f d z` (Mathlib `deriv`); a claim about `f'` is meaningful where `f` is complex differentiable |
| `Let $F(x)=\int_a^x f(t)\,dt$. Then $F$ is differentiable on $(a,b)$ and $F'(x)=f(x)$ for all $x\in(a,b)$.` | `F'` of a real function that the article defines (where it defines no `F'` of its own): its derivative, defined where it exists |
| `Every nonconstant polynomial with complex coefficients has a root in $\mathbb{C}$.`, `a complex polynomial` | a polynomial function `z\mapsto p(z)` for some `p\in\mathbb{C}[X]` (Mathlib `Polynomial.eval`); `has a root in $U$` (`a zero in $U$`): `f(z)=0` for some `z\in U` |
| `If $|g|$ attains a maximum in $D$, then $g$ is constant.` | the modulus of the values: there is `c\in D` with `|g(z)|\le|g(c)|` for all `z\in D` (also `on $D$`, and of a real function) |
| `Let $(a_n)$ be a sequence with $a_n\to s$ and $(b_n)$ a sequence with $b_n\to t$.`, `Then $a_n+b_n\to s+t$.` | two binders (`be` left out in the second); a limit of a term with a subscript, along its index |
| `Every integer $n>1$ has a prime divisor.` | for every such `n` |
| `$f$ has at most $n$ real roots`, `exactly`, `at least` (field `polynomials`) | the set of real roots is finite with at most `n` elements (the zero polynomial has infinitely many) |
| `Then $n^2>n$ if $n$ is odd.`, `Then $\sqrt{n}$ is irrational if $n$ is not a perfect square.`, `Then $p$ divides $k^p-k$ for $k>0$.` | as `If $n$ is odd, then $n^2>n$.` (not `if and only if`, `only if`, `even if`; and not after a clause that binds variables of its own, `there exists $\delta>0$ such that …`, where the condition is part of that clause) |
| `there exists $\delta>0$ such that $|x^2-1|<\varepsilon$ whenever $|x-1|<\delta$` | `whenever $ψ$` is `for $ψ$`: for every value of the new variables of `ψ`, inside the clause |
| `Let $(X,d)$ be a metric space.` | the space `X`, with the vocabulary's distance `d` |
| `Let $f\in C([0,1])$.`, `Let $f\in C^1([a,b])$.` | a real function continuous (continuously differentiable) on the set, which is its domain, as for `f\colon[0,1]\to\mathbb{R}`: its adjectives are said there. Where `[0,1]` is a type of a field (`unitsquare`), `C([0,1])` is the continuous functions on that type (`C^1([0,1])` is not read) |
| `Let $X$ be a topological space and let $A\subseteq X$ be closed.`, `$A\subseteq X$` | a subset of the space (of its elements, not of numbers) |
| `Let $H\subseteq G$ be a normal subgroup.`, `Let $I\subseteq R$ be an ideal.`, `Let $a\in R$ be a unit.` | a noun whose complement is left out takes the set of the variable's domain (`a normal subgroup of $G$`, `a unit of $R$`) |
| `Then $(x_n)$ is a Cauchy sequence.` | the adjectives, of a sequence in a space: the noun of its own objects after them says nothing more |
| `Every positive integer $n\ge2$ can be written as a product of primes.`, `… can be expressed as …` | `… is a product of primes` |
| `Let $f\colon[0,1]\to\mathbb{R}$ be continuous and nonnegative with $\int_0^1f(x)\,dx=0$.` | adjectives joined by `and`, then the conditions |
| `The series $\sum_{n=1}^\infty\frac{1}{n^2}$ converges absolutely.`, `… is absolutely convergent` | the series of the absolute values converges |
| `Let $f$ be an integrable function on $[0,1]$.` (field `unitsquare`) | Lebesgue integrable on `[0,1]` |
| `The function $f(x)=x^3$ is injective.`, `The function $x\mapsto e^x$ is strictly increasing.` | the map `x\mapsto e`, on the whole line (with `on $D$`, on `D`) |
| `Let $a,b,c$ be the side lengths of a triangle.`, `Let $a$, $b$, $c$ be the sides of a triangle.`, `the lengths of the sides of a triangle` | real numbers with `a,b,c>0`, `a<b+c`, `b<a+c`, `c<a+b` |
| `Let $\mathcal{F}$ be a family of subgroups of $G$.`, `a collection of real numbers`, `a set of finite subsets of $\mathbb{R}$` | a set each of whose elements is as the plural noun phrase says (`family` and `collection` are `set`) |
| `Let $\varphi\colon G\to G$ be a mapping.`, `an injective mapping` | `mapping` is `map` |
| `Let $(a,b)$ be a pair of integers with $a<b$.`, `a triple of positive integers`, `an ordered pair of …` | as `Let $a,b$ be integers with $a<b$.` |
| `Let $M$ be a finitely generated $R$-module.`, `a finite-dimensional $K$-vector space` | `a … module over $R$`: a formula and a hyphen before a noun that has a complement after `over` |
| `Let $X$ be a complete and separable metric space.` | adjectives before a noun joined by `and` |
| `Then either $n$ is even or $n$ is odd.`, `Then $n$ has a prime factor $p\le\sqrt{n}$ or $n$ is prime.` | one of the clauses (`either` is left out; the noun phrase after `has a` ends before `or`) |
| `Let $X$ be a Poisson random variable with parameter $\lambda>0$.`, `a binomial random variable with parameters $n$ and $p$`, `a normal random variable with mean $\mu$ and variance $\sigma^2$`, `an exponential random variable with rate $\lambda$` | as `a random variable that is Poisson distributed with parameter $\lambda>0$` (and so on) |
| `Every bounded sequence of real numbers has a convergent subsequence.`, `Let $(x_n)$ be a sequence in $X$. Then $(x_n)$ has a convergent subsequence.` | a strictly increasing `φ : ℕ → ℕ` with `x_{φ(n)}` convergent (in the space, to one of its points) |
| `Let $F$ be a field with at least four elements.`, `with at most $n$ elements`, `a commutative ring with $1$` (`with identity`, `with unity`) | infinite or of order at least `n`; finite of order at most `n`; every ring of the vocabulary has an identity |
| `Let $X$ be a random variable with values in $\{0,1\}$.` | `X\in\{0,1\}` almost surely |
| `Let $f\colon\mathbb{R}\to\mathbb{R}$ be continuous at $0$.` | the map, then the hypothesis `Suppose that $f$ is continuous at $0$.` |
| `$\operatorname{Var}(X_1+\dots+X_n)$`, `$\frac{x_1+\cdots+x_n}{n}$` | a sum (product) with an ellipsis inside brackets as well |
| `Let $S$ be a finite set with $n$ elements.`, `Let $G$ be a group with $6$ elements.`, `every nonzero element of $K$ is invertible` | a finite set with `n` elements; a finite structure of order `n`; elements `a\ne0`, and with an inverse |
| `Let $U$ be a nonempty open set. Then there is $x\in U$ such that …`, `$\sigma(S)\in S$`, `… for every $x\in U$` | membership in a set that the result binds |
| `Let $T$ be the closure of $S$.`, `let $\ell$ denote the line through $A$ and $B$` | `be the` and `denote the` alike; the value of the notion may be a set or a function (then the variable is that set: `$M\in\ell$`) |
| `Let $\varphi$ denote Euler's totient function.` | as `We write $\varphi$ for Euler's totient function.`: a symbol for a notion of the vocabulary |
| `We write $K$ for the circle with centre $O$ and radius $5$.` | in a notation, a letter that the article has defined (`O`) is that object; the other letters are the notation's parameters |
| `$S$ is of measure zero` | a modifier of the vocabulary that begins with `of`, after `is` |
| `the M\"obius function` | TeX accents in words are read as the letters they print (`Möbius`) |
| `\newif\ifmarked`, `\newcommand{\rev}[1]{\ifmarked{\color{magenta}#1}\else#1\fi}`, `\marginpar{…}` | the marks of a revision: a conditional of the preamble (`\newif`, `\…true`, `\…false`, `\ifdefined`) selects its branch, and colour and margin notes are layout. The sentences are read as in the clean version |
| `Let $\mathcal C$ denote the class of bivariate copulas, that is, distribution functions on $[0,1]^2$ with uniform marginals, and we refer to … for background.` | a class that is a noun of the vocabulary: when the gloss after `that is,` is not read, the noun is the definition |
| `The copulas $M(u,v)\coloneqq\min\{u,v\}$, $W(u,v)\coloneqq…$, and $\Pi(u,v)\coloneqq uv$ describe comonotonicity, countermonotonicity, and independence, respectively.` | as `Let DEFS denote the comonotonicity, countermonotonicity, and independence copulas.` (`describe`, `represent`, `model`, `correspond to`) |
| `For a copula $C$, Spearman's rho is \begin{equation}\rho(C)=12\int_0^1\!\int_0^1C(u,v)\,du\,dv-3,\end{equation} as given in \cite{…}, a classical measure of concordance.` | `For a NOUN $x$, the NAME is DISPLAY` defines the symbol also with `=`, when the symbol is new; words without a formula after the display (`, as given in \cite{…}, …`, `, which emphasizes …`) assert nothing |
| `For a copula $C$, we write $C^\top(u,v)\coloneqq C(v,u)$ for the transpose of $C$.` | a definition with its name: `its transpose` is then read |
| `For a copula $C$, the reflections of $C$ in the first and in the second argument are \[C_{1}^{*}(u,v)\coloneqq v-C(1-u,v)\qquad\text{and}\qquad C_{2}^{*}(u,v)\coloneqq u-C(u,1-v).\]` | a decoration with a star, also with a number below it (`C^{*}`, `C_{1}^{*}`), is an operation on the objects of the noun, like `C^\top` and `\widehat C` |
| `The boundary of the region is described by the function $\Phi:[-1,1]\to[-1,1]$ given by DISPLAY, which satisfies $2r-\Phi(r)=-\Phi(-r)$ for every $r\in[-1,1]$.` | as `Define $\Phi:[-1,1]\to[-1,1]$ by DISPLAY and observe that …`: the words before `the function` describe it |
| `For every $C\in\mathcal C$, DISPLAY, and the two reflections satisfy DISPLAY, as well as DISPLAY.` | words that only lead to the next formula (`and … satisfy`, `as well as`); in a display, `,\quad` separates formulas like `,\qquad` |

Couplings and random pairs, with the field `unitsquare` (`tests/Couplings/article.tex` uses
each form):

| Sentence | Reading |
| --- | --- |
| `Let $\Gamma$ denote the set of couplings.` | a *coupling* is a probability measure on `[0,1]^2` with uniform marginals, the law of a pair `(X,Z)` of uniform random variables |
| `\mathbb{E}_\gamma[XZ(X+Z)]`, `\mathbb{E}_\gamma[c(X,Z)]` | the integral of a function of the two coordinates, written `X` and `Z`, against the coupling `γ`; defined when the function is integrable |
| `Let $C\in\mathcal C$, and let $\gamma$ be the coupling associated with $C$.`, `let $D_c$ denote the copula associated with $\gamma_{\zeta_c}$` | the coupling of a copula `C` is the law of `(1-U,1-V)` for `(U,V)` with the copula `C`; the copula of a coupling `γ` is the copula of `(1-X,1-Z)`. A real function with values in `[0,1]`, such as `\zeta_c:[0,1]\to[0,1]`, is a map of the interval where one is expected |
| `Consequently, $\rho$, $\nu$, and $\eta$ are affine on $\mathcal C$.` | what is said of several symbols is said of each; a quantity is *affine* on a class when it respects the convex combinations of its members |
| `We therefore set $B_{1/2}\coloneqq A_{1/2}$.` | a family at one further parameter: from here on the family is defined there too |
| `For $b\in(0,\frac12)$ and $x\in(1-b,1]$, set $z_-(x)\coloneqq…$.` | the first variables of the binder that no defined symbol shows are implicit: `z_-(x)` takes `b` from where it is used |
| `… if and only if $C=D_{1/2}$`, `The maximum is attained only by $D_{1/2}$, that is, for every $C\in\mathcal C$, $\nu(C)-\rho(C)=\frac14$ if and only if $C=D_{1/2}$.` | an equality case as an equivalence; after `, that is,` the formal restatement is what is read |
| `Let $c:[0,1]^2\to\mathbb{R}$ be a continuous function, and let $\varphi,\psi:[0,1]\to\mathbb{R}$ be continuous functions.` | functions of the points of the interval and of the square as variables of a result, with adjectives of the vocabulary |
| `Suppose that $\Delta(x,z)\ge0$ for all $x,z\in[0,1]$, and let $K\coloneqq\{(x,z)\in[0,1]^2:\Delta(x,z)=0\}$ be their contact set.` | a set of pairs of points defined in a result (its name is not read); `$\gamma(K)$` is its measure, defined when it is measurable |
| `Every $\gamma\in\Gamma$ satisfies DISPLAY, with equality if and only if $\gamma(K)=1$.` | the inequality, and: equality in it holds exactly when the condition does |
| `If there is $\mu\in\Gamma$ such that $\mu(K)=1$, then …` | an existence as a hypothesis |
| `If $f$ is negligible compared to $g$ and $g$ is dominated by $h$, then …`, `Suppose that $y$ is a solution of … and that $z$ is …` | several clauses as the hypothesis, each read on its own |
| `If $a$ is a gradient descent sequence for $f$ with step size $h$ and $a(0)=4$, then $a(1)=2$ and $a(2)=1$.` | the hypothesis is one of every claim after `then` (`A and B`, `A, and B`), unless a later claim has an `if` of its own |
| `Let $A$ be a symmetric $2\times2$ matrix.`, `an irreducible $2\times2$ stochastic matrix`, `a real $m\times n$ matrix`, `Let $A$ and $B$ be invertible $n\times n$ matrices.` | adjectives before a size: they are of the noun after it (`real` too, which before a variable alone is a real number) |
| `Let $G$ be a non-abelian group.`, `a nonabelian group`, `a non-zero integer`, `a non-compact metric space`, `$f$ is non-constant` | `non-X` and `nonX`: not `X`, for each adjective `X` of one word, where the vocabulary has no word `nonX` of its own (`nonempty`, `nonzero`, `nontrivial`, `nonnegative` are its own). `non-negative`, `non-positive`, `non-decreasing` and `non-increasing` are the vocabulary's `nonnegative` (at least `0`) and so on, never `not positive` |
| `Let $f\colon\mathbb{R}\to\mathbb{R}$ be a polynomial function.` | with the field `polynomials`, `polynomial` is an adjective of the function of the signature |
| `Every Harshad number is a positive integer.`, `Every Liouville number is irrational.` | every object of the first noun is one of the second (or has the adjective); the sentence needs no variable |
| `Every integer $n\ge2$ is a product of primes.` | the same, for the variable of the condition |
| `Every prime $p$ with $p\equiv1\pmod 4$ is a sum of two squares.`, `a sum of three squares`, `a sum of four squares`, `a sum of two primes` | `a^2+b^2` (`a^2+b^2+c^2`, …) for integers; `p+q` for primes |
| `$z$ and $o$ are binary words of length $3$.`, `If $f$ and $g$ are P-functions, then …` | a plural after `are`: the phrase of the vocabulary in the singular (`a binary word of length $3$`), said of each |
| `the mean number of customers in the M/M/1 queue with arrival rate $\lambda$ and service rate $\mu$` | a slash in a phrase of the vocabulary (`M/M/1`) is read as written |
| `$c$ is a solution of the Fredholm integral equation with kernel $K$, right-hand side $o$ and parameter $\frac12$ on $[0,1]$.` | a phrase of the vocabulary goes on after an object: with `and` and a word, a preposition (`from $0$`), or a list of arguments after a comma |
| `$v$ is a solution of the wave equation with speed $1$ and a solution of the transport equation with speed $1$.` | two noun phrases after `is`, joined by `and a`: each is said of the subject |
| `$\frac12$ is an optimal strategy for the row player in the zero-sum game with payoffs $1$, $-1$, $-1$ and $1$` | the arguments of a phrase, formulas separated by commas and a last `and` (formulas that state something are claims) |
| `Let $x$ be a vector in $\mathbb{R}^n$.` | a modifier with a formula after the noun (`in $\mathbb{R}^n$`) is of the variable |
| `with coefficients $p$ and $q$ and exponent $n$` | a phrase goes on after `and $q$` with `and`, `or`, `with` or a preposition |
| `We write $N_a$ for the integral mean of $f$ on $[0,a]$.`, `We write $V(f)$ for the total variation of $f$ on $[0,1]$.` | a notation may fix arguments of a notion; the conditions of the fixed ones on the variables before them (`f` of bounded variation on `[0,1]`) are conditions of the notation's variables, which its uses ask for |
| `$f$ is bounded below`, `$f$ is bounded at infinity`, `$f$ is Lipschitz with respect to $d$`, `$U$ is open in $\tau$`, `$f$ is continuous from $\tau$ to $\sigma$`, `$f$ is Lipschitz in the second variable` | an adjective of the vocabulary that begins with a standard one (`bounded`, `Lipschitz`, `open`, `continuous`) and goes on |
| `$f$ is smaller than $g$ in the hazard rate order` | a stochastic order (field `stochasticorders`), not a comparison of numbers |
| `Let $f$ be a $3$ times differentiable function.`, `an $n$ times continuously differentiable function` | a number of times before the noun, the argument of a modifier (field `calculus`) |
| `Let $f$ and $g$ be probability densities with finite mean.` | a modifier after a plural noun, said of each variable |
| `We write $\operatorname{ord}(\sigma)$ for the order of a permutation $\sigma$.` | a noun before a letter of a definition gives its type; with fields in which `the order of` has a meaning for groups and for permutations, it says which ([Libraries](libraries.md#words-with-a-meaning-in-several-fields)) |
| `If $K\subseteq\{(x,z)\in[0,1]^2:z=T(x)\}\cup(N_1\times[0,1])\cup([0,1]\times N_2)$, then every $\gamma\in\Gamma$ with $\gamma(K)=1$ satisfies $\gamma=\gamma_T$, and $T$ is Lebesgue measure preserving.` | sets of pairs of points: unions, products with a *finite subset of `[0,1]`*, inclusion; two couplings are equal when they agree on every measurable set |
| `Let $Y$ be an integrable random variable with continuous distribution function $F$, and let $Z$ be uniformly distributed on $[0,1]$ and defined on the same probability space. Then $\mathbb{E}[YZ]\le\mathbb{E}[Y\,F(Y)]$, with equality if and only if $Z=F(Y)$ almost surely.` | the two random variables of a result are a random pair: the result is about every joint law of such a pair, a probability measure on `ℝ × [0,1]` whose second coordinate is uniform. `\mathbb{E}[…]` is the expectation for that law, `F` is the distribution function of `Y`, and `almost surely` is for that law. A statement about a pair on any probability space depends only on the joint law, so this is the same statement |

Freer wordings (`tests/Wordings/article.tex` uses each form). A sentence that has no
reading as it stands, or whose reading does not compile, is read through sentences of the
forms above that say the same. What such a sentence says beyond them stays unread:

| Sentence | Reading |
| --- | --- |
| `Consequently, if $C^\top(u,v)\coloneqq C(v,u)$ denotes the transpose of $C$, then …`, `For $(U,V)\sim C$, the survival copula $\widehat C(u,v)\coloneqq…$ is the copula of $(1-U,1-V)$.` | a definition (`\coloneqq`) inside a sentence of prose: the definition alone, with the name that the words give it (`denotes the NAME` after it, `the NAME` before it) |
| `… $\nu$ arises from Spearman's rho, DISPLAY, see \cite{…}, by replacing …` with the display `\rho(C)=…` | a displayed `f(x)=…` after a name defines the symbol `f` if nothing has defined it |
| `… one introduces the symmetrized coefficient DISPLAY, which emphasizes …` | likewise for a displayed definition; a footnote is not part of the sentence |
| `\widehat C(u,v)\coloneqq…`, `\rho(C)=…` after `For a copula $C$, …` earlier | a definition about a letter that it does not introduce takes the latest introduction of that letter by a definition (`For a copula $C$,`, `For $w\in[0,1]$,`); so does a statement of the text or of a result that is not read otherwise (`… and $\nu(D_c)=\Phi(\rho(D_c))$.` after `For $c\in[0,1]$, …`) |
| `… a family indexed by $w\in[0,1]$: let $A_w$ be the copula associated with $\gamma_{T_w}$, where DISPLAY` | after a colon, the definitions that the words before it announce, for the values they give (`For $w\in[0,1]$, …`); the definition after `, where` comes first; `set … and let …` are two definitions |
| `For $c\in[0,1]$, the corresponding rank map $\zeta_c:[0,1]\to[0,1]$ is DISPLAY, which takes its values in $[0,1]$ by construction.` | as `define the rank map $\zeta_c:[0,1]\to[0,1]$ by DISPLAY` |
| `…, the conditional law carries two atoms: DISPLAY` with rows `z_-(x)&\coloneqq…,&\quad\text{with probability }&…` | the definitions in the rows of an aligned display; what the rows say beside them is not read |
| `the copula associated with the coupling $\gamma_{\zeta_c}$ from Section~\ref{…}`, `… for the function $\Phi$ in \eqref{…}` | words that only point to an object (`the coupling` before its symbol, a reference to where it is defined) |
| `DISPLAY as given in \cite{…}, a normalization that makes $\nu(M)=1$, $\nu(W)=-1$, and $\nu(\Pi)=0$.` | the sentence before the comma, and the formulas as claims |
| `We may identify $\mathcal C$ with the set $\Gamma$ of all such couplings, …` | `Let $\Gamma$ denote the set of couplings.`, if `\Gamma` is not defined |
| `If $(X,Z)$ follows the coupling associated with $C\in\mathcal C$, then DISPLAY` with `\mathbb{E}[XZ]` | `Let $C\in\mathcal C$, and let $\gamma$ be the coupling associated with $C$. Then …` with `\mathbb{E}_\gamma[XZ]` |
| `Consequently, $\rho$, $\nu$, and $\eta$ depend affinely on the copula.` | each of them is affine on its domain |
| `For $w\in[0,1]$ and $b\in(0,\frac12]$, DISPLAY. In particular, $\nu(A_w)-\eta(A_w)=…$.` | in a result, the values that open a displayed statement are those of the sentences after it |
| `The maximum $\nu-\rho=\frac14$ is attained only by $D_{1/2}$, which has $\rho=0$.`, `The minimum $\nu-\rho=-\frac14$ is attained only by its survival copula.` | the bound, its value at the object, and uniqueness; `\rho=0` is the value of `\rho` at the object; `its` refers to the object of the sentence before, with an operation that the article names |
| `Both constants are sharp: the maximum $a$ of $\nu-\eta$ is attained only by $A_{3/4}$, at which $(\eta,\nu)=(e,n)$, and the minimum $-a$ only by $A_{3/4}^\top$.` | as `The maximum $\nu-\eta=a$ is attained only by $A_{3/4}$.`, the two values at `A_{3/4}`, and `The minimum $\nu-\eta=-a$ is attained only by $A_{3/4}^\top$.` |
| `In particular, if some $\gamma^*\in\Gamma$ satisfies $\gamma^*(K)=1$, then the maximizers of $\gamma\mapsto\mathbb{E}_\gamma[c(X,Z)]$ over $\Gamma$ are exactly the couplings concentrated on $K$.` | if there is such a coupling, then for every `γ∈Γ` the value at `γ` is the supremum over `Γ` if and only if `γ(K)=1` |
| in a proof: `Hence $\Delta(x,z)\ge\Delta(1-w,z)$.` after `On this rectangle, …`, `$\Delta(1-w,\cdot)\ge0$` | a step about a letter that the proof introduces in words, or with a placeholder, is not read (no warning; the proof is then not read completely). A letter with an argument (`$t(x)$`) is a symbol that must be defined |

Functions of several variables are curried: `f:\mathbb R^2\to\mathbb R` (or
`\mathbb R\times\mathbb R\to\mathbb R`) has type `ℝ → ℝ → ℝ`, and `f(x,y)` applies it to
`x` and `y`.

| Sentence | Reading |
| --- | --- |
| `Define $f:\mathbb R^2\to\mathbb R$ by $f(x,y)\coloneqq x^2y$.`, `Let $g:\mathbb R^2\to\mathbb R$ be given by $g(s,t)=s-t$.`, `For $x,y\in\mathbb R$ set $h(x,y)\coloneqq xy$.` | a function of several variables; the names of its variables are remembered |
| `\partial_x f(1,2)`, `\partial_2 h(x,y,z)`, `\frac{\partial f}{\partial y}(x,y)`, `\partial_x\partial_y f`, `\partial_x^2 f` | partial derivatives: in the argument named `x` (by the application, or by the definition of `f`) or numbered from 1; the derivative of `t ↦ f(…,t,…)`, defined where it exists. Of a function on an interval type of the vocabulary (`\partial_1C(u,v)` for a function `C` on the unit square, with the field `unitsquare`): the derivative within the interval, one-sided at its end points. It is the derivative at every point, not a version of it: an integral of `\partial_1C` asks that the derivative exists everywhere on the square |
| `\Delta f(x,y)` | the Laplacian, `∑ⱼ ∂ⱼ∂ⱼ f` |
| `For every $I\in\mathbb N_0^2$, $|\partial^If(x,y)|\le C_I$` | a multi-index `I` (in `\mathbb N_0^n`, `\mathbb N^n`) is the `n` natural numbers `I_1`, …, `I_n`; `\partial^I f` is the derivative of order `I_k` in the `k`-th argument, defined only where `f` is smooth (`C^∞`); a constant `C_I` may depend on the components |

Generic constants and existence (`tests/Fields/article.tex`,
`tests/Conventions/article.tex` and `tests/Statements/article.tex` use each form):

| Sentence | Reading |
| --- | --- |
| `Throughout, $C$ and $C_m$ denote positive constants.` | in every later claim, a constant `C_{…}` is existential: for all values of its indices there is a `C > 0` such that the claim holds for all other variables (it depends only on its indices and on the fixed data) |
| `Here and below, $K$ denotes a positive constant that depends only on $n$.` | `K` comes right after `n` when the claim binds `n` (`∀ n, ∃ K > 0, ∀ x, …`), and before every binder otherwise. The sentence may begin with `Throughout`, `In this paper`, `Here and below`, `In what follows`, `In the following`, `Below` or `In the lemmas below` (any words before `below`); the constants may be `nonnegative` |
| `In the lemmas below, $A_k>0$ and $b_k\ge0$ may depend on $k$ and the fixed data, and are uniform in $N$ and $x$.` | each constant comes right after the variables it may depend on, its indices included: `∀ k, ∃ A_k > 0, ∃ b_k ≥ 0, ∀ N, ∀ x, …`. Also `depends only on`, `depending only on`, `independent of`. A dependence is a list of variables or a phrase with `fixed`; another phrase (`the shape of the domain`) is refused, since its variables are not named. A claim whose binders cannot be ordered so (a domain of `k` that uses `N`) is refused |
| `The constants $c$ and $c_m$ are positive and independent of $N$.` | as above; without a list of dependencies, a constant may depend on everything except the variables named after `independent of` or `uniform in` |
| `$\forall I\in\mathbb N_0^2\ \exists C_I: |\partial^If(0,0)|\le C_I$` | an explicit `\exists` of a constant of a convention: the convention places it (`C_I > 0`) |
| `For every positive integer $m$ there is $c>0$ such that $c\,n^m\le n^{m+1}$ for every positive integer $n$.` | `∀ m, ∃ c > 0, ∀ n, …` (`there is|exists $c>0$ such that`, `there exists a constant $C$ such that`) |
| `Let $V$ be a vector space over a field $K$, let $v_1,\ldots,v_n\in V$, and suppose that CLAUSE.`, `Let $G$ be a group and assume that $G$ is abelian.` | the binders, then the hypothesis (as `Suppose that CLAUSE.`); `$x_1,\ldots,x_n\in A$` with a letter `n` that nothing defines binds `n` with the sequence, and `Suppose that $x_1>0$.` after a sequence `x` is about its term |
| `Then there is exactly one smooth function $\varphi$ on $\mathbb{T}^2$ of zero Haar mean with $N\varphi=F$.` | existence and uniqueness (`there is a NP`, `there is a unique NP`, `… such that CLAUSE`) |
| `There is a unique $x>0$ such that $x^2=2$.`, `there is a unique $y\in C$ with $\|x-y\|=\inf_{z\in C}\|x-z\|$` | the same with a formula that binds the variable and its domain; `\inf_{z\in C}` and `\sup_{z\in C}` range over a set that the sentence binds, also of elements of a field's type |
| `For $0<h\ll\lambda\ll1$, …`, `Let $0<\varepsilon\ll1$.` | smallness, chosen from right to left: there is `c > 0` such that for every `λ ∈ (0, c)` there is `c' > 0` such that for every `h ∈ (0, c'λ)` the claim holds (`C^{-1}\ll b`: `C > 1/(c b)`) |
| `For all sufficiently large $n$, …`, `For every positive integer $k$ and every sufficiently large integer $t$, …`, `… for all sufficiently large $n$`, `For sufficiently small $\varepsilon>0$, …` | there is a threshold `N` such that the claim holds for every `n\ge N` (of the noun, if one is written; without a noun, an index name, `n`, `m`, `k`, `j`, `i`, `N`, `M`, `K`, is an integer, as in `\lim_{n\to\infty}`, and another name a real number); for a small variable, there is `δ>0` such that it holds for every `0<\varepsilon<δ`. The threshold comes after the binders before it, so it may depend on them. A small variable needs its lower bound `0` (`$\varepsilon>0$`, or the word `positive`) |
| `If $n$ is sufficiently large, then …`, `If $n$ is a sufficiently large integer, …`, `For $t$ large enough, …`, `… provided that $\varepsilon>0$ is sufficiently small` | as `for all sufficiently large $n$` (`small`) at that place, when `n` is not bound yet; a variable already bound (`Let $n$ be a positive integer. If $n$ is sufficiently large, …`) is refused with a finding: its threshold would come after the variable, so say `sufficiently large` where the variable is introduced |
| `… for every integer $m\ge0$ and every smooth function $\varphi$ on …` | binders after a claim, the first one outermost |
| `For every positive integer $k$, every positive integer $N$ and every $x\in[0,1]$, …` | several binders before a claim (`, every`, `and every`, `and each`, `and all`, `and $y\in[0,1]$`), the first one outermost |
| `For every integer $n\ge1$, …`, `For every real $\nu>2$, …`, `For every fixed real $c>0$, …` | a noun with a bounded variable; `fixed` marks a parameter and does not change the binder |
| `For every positive integer $n_0$ there is an integer $d_0$ such that $d_0>n_0$.`, `Let $x_0\in(0,1)$.`, `If $m_0$ is a positive integer, then …` | a letter with a subscript that is a number or a letter (`n_0`, `x_{12}`, `x_k`) is the name of one variable: after a noun, before a domain, and with a bound (`$c_0>0$`). Later sentences find the variable under this name (after `Let $x_k>0$.`, `x_k` is that number, and `k` is part of the name). A family of the article (`S_s`) stays the family. A term of a sequence is written with the sequence (`$a_1,\ldots,a_n$`) |
| `For all integers $a,b\ge1$, …`, `For all positive integers $a$ and $b$, …` | a binder for each variable, the first outermost; a bound after the last variable bounds each (`a\ge1` and `b\ge1`) |
| `There is an absolute constant $C>0$ such that …`, `there is an integer $Q$ such that …` | an existential constant (also `a universal constant`, `absolute constants`), an object of a noun |
| `There are absolute constants $c_1,c_2>0$ and an integer $b_0\ge2$ such that, for every integer $b\ge b_0$, …` | several constants (`a,b>0` bounds each), then binders of the clause after `such that`, whose bounds may use the constants |
| `For every real $\nu>2$, there is an integer $Q(\nu)$ such that $\nu\le Q(\nu)$.`, `there is $N_0=N_0(\eta)$ such that …`, `there are constants $c(C)>0$ and $K(C)$ such that …` | a constant whose name lists what it depends on: `Q(\nu)` is `Q` in the conditions. Its name must list every variable bound before it (otherwise the claim is refused: it would say more or less than the text); `Q(3)` is refused, since `Q` is a number, not a function |
| `there is $w_0=w_0(d,\kappa)>0$ with the following property. For every $x\in(0,w_0)$, …`, `there is $\delta>0$ such that the following holds: …` | the next sentence (after `.` or `:`) is the condition of the constants |
| `There are infinitely many primes $p$ such that $p+2$ is prime.`, `We have $q^2\ge q$ for infinitely many integers $q$.` | the numbers the noun phrase and the condition describe are not finitely many (for numbers of any kind, not only integers) |
| `The equation $x^4+y^4=z^4$ has no solution in positive integers.`, `The equation $x^2+y^2=z^2$ has infinitely many solutions in positive integers.`, `the equation $x^2-dy^2=1$ has a solution in integers`, `has no integer solutions` (`rational`, `real`, `positive integer`) | the unknowns of the equation are its letters that nothing binds, in their order, each a number of the noun: there are none, there is one, or the set of solutions, of points of `ℝⁿ`, is infinite (Mathlib `Set.Infinite`); `e` and `i` are not taken as unknowns (a finding asks to name them) |
| `There are no positive integers $x,y,z$ with $x^4+y^4=z^4$.` | no numbers of the noun satisfy the condition |
| `there is $c>0$ such that $c\le C$ and $K\ge C$` | the conditions after `such that` joined by `and` are all conditions of the constants |
| `Implied constants are absolute.`, `Throughout, implied constants may depend on $k$.` then `For every $x\ge1$, $x\ll x^2$.`, `$2x+1=O(x)$`, `$x^2\gg x$` | `A\ll B` is `|A|\le CB`, `A\gg B` is `|B|\le CA`, `A=O(B)` is `|A|\le C|B|`, with an implied constant `C>0` placed by the convention, as a generic constant: an absolute one before every binder, one that may depend on `k` right after `k`. `A\asymp B` is `A\ll B` and `B\ll A`, with one implied constant. Without such a convention the claim is refused |
| `\[ k\le Ck^2\qquad\text{for every integer }k\ge1. \]` | words after a display formula bind its variables, as `for every NP` after a clause (`\text{for all }x\in A`; `\text{if }x>0` is a condition) |
| `\[ \left|\pi-\frac pq\right|\ge q^{-\nu}\qquad(p\in\mathbb Z,\ q\in\mathbb Z,\ q\ge Q). \]` | the parts in parentheses after a display formula bind its variables from left to right; a part about variables bound before (`q\ge Q`) is a condition. Such a part is never read as one more claim |
| `Let $\varphi$ be a smooth function on $\mathbb{T}^2$ of zero Haar mean with $N\varphi=F$.` | a condition may use the variables bound before it |

Fields and equations (`tests/PDE/article.tex` uses each form). A field on a product
`\mathbb R^n\times I` has `n` spatial coordinates and a time; a vector field takes
the index of its component first, and an equation between fields holds
componentwise at every point of the domain of its first field. Derivatives are
taken within the domain of each coordinate, so `\partial_t u` at `t=0` is the
one-sided derivative on `[0,1)`.

| Sentence | Reading |
| --- | --- |
| `there exist a force $f\in C_c^\infty(\mathbb R^3\times(0,\infty);\mathbb R^3)$, a compact set $K\subset\mathbb R^3$, and smooth velocity and pressure fields $u,p$ on $\mathbb R^3\times[0,1)$ satisfying DISPLAY such that …` | several objects, each a noun phrase, then the conditions: a display after `satisfying`, clauses and displays after `such that` (`velocity`, `vector` and `force` fields are vector fields, `pressure` and `scalar` fields real ones; `C^\infty(D;\mathbb R^m)` is smooth on `D`, `C_c^\infty` also with compact support in `D`) |
| `there are no NPs … such that …` | no such objects exist |
| `…, and consequently there are no …` | one more condition on the objects already introduced, which may use them |
| `satisfying \eqref{l}` | the display `l` of the same sentence, read again for the objects of this noun phrase |
| `\partial_tu+(u\cdot\nabla)u-\nu\Delta u+\nabla p=f`, `\nabla\cdot u=0`, `u(\cdot,0)=0` | componentwise at every point of the domain (`u(\cdot,0)`: at every spatial point) |
| `\supp u(\cdot,t)\cup\supp p(\cdot,t)\subset K for every $0\le t<1$` | the closed supports of the slices lie in `K` |
| `\lVert u(t)\rVert_{L^2(\mathbb R^3)}`, `\lVert u(t)\rVert_{L^\infty(\mathbb R^3)}` | the norm over space of the Euclidean length of `u(\cdot,t)`, defined only when it is finite |
| `\int_{\mathbb R^3}|u(x,t)|^2\,dx` | the integral over the point `x` of `\mathbb R^3`, defined only when the integrand is integrable |
| `\sup_{0\le t<1} e<\infty` | `e` is defined and at most some `M` for every such `t` |
| `fields $U,P_{\mathrm{per}}$ on $\mathbb T^3\times[0,1)$`, `f\in C_c^\infty(\mathbb T^3\times(0,\infty);\mathbb R^3)` | on the torus: functions on `\mathbb R^3` of period 1 in each spatial coordinate; compact support is support in a compact time interval inside `(0,\infty)`; `\supp U(\cdot,t)\subset K` is in `K` up to integer translations; `\|U(t)\|_{L^\infty(\mathbb T^3)}` is the norm over a period. A field's name may carry a subscript |
| `a compact set $K\subset(-1/2,1/2)^3$` | a compact set in the box |
| `\|x\|` | as `\lVert x\rVert` |
| `\limsup_{t\uparrow1} e=\infty` | for every `M` there are `t` arbitrarily close to `1` from below, in the domain of the fields of `e`, where `e` is defined and greater than `M` |

A bound on a norm or an integral asserts that it is finite, wherever the bound
stands; so `there are no fields … such that $\sup_{t\geq0}\frac12\int|u|^2<\infty$`
excludes exactly the fields of finite, bounded energy.

Nouns, adjectives and notions of the vocabulary are also read after `is`: `$\nu$
is a probability distribution on $\mathbb{N}_0$`, `$n$ is prime`, `$\nu$ is not
the point mass at $0$`. `docs/vocabulary.md` explains how the article chooses the
fields of the vocabulary and what happens when a word has several meanings.

## House style

1. **Define before use.** The defining sentence of a symbol comes before its
   first use. Its definition is its only meaning, so defining a symbol twice is
   an error. Preamble macros (`\newcommand` and `\renewcommand`, with or
   without arguments, `\def`, `\DeclareMathOperator`, `\let`) are expanded
   first. The article's own theorem environments (`\newtheorem{thm}{Theorem}`,
   `\declaretheorem`) are read by their printed names: a claim, a fact or an
   observation as a lemma, a question or a problem as a conjecture.
2. **Write definitions with a defining sign.** `f(x)\coloneqq x+\frac1x` defines
   `f`, and so does `f(x):=x+\frac1x` (or `\triangleq`, `\vcentcolon=`).
   `f(x)=x+\frac1x` is a claim about an `f` that must already exist, except
   after `set`, `put`, `let` or `define`.
3. **One definition or claim per sentence.** Move side remarks into their own
   sentence. "We refer to \cite{…} for background." is a sentence of its own,
   and so is "This normalization makes $\alpha(e)=1$, …".
4. **Name the class of the argument.** Write "For $a,b\in(0,\infty)$, the
   quadratic mean $Q\coloneqq…$", "For a NOUN $x$, the NAME of $x$ is …", "For
   $c\in[0,1]$, let $D_c$ denote …". A family gets its parameter domain in the
   sentence that introduces it: "For $w\in[0,1]$, let $A_w$ be the NOUN
   associated with $T_w$", not "indexed by $w\in[0,1]$: let …".
5. **Give every map its signature.** "where $T_w:[0,1]\to[0,1]$ is given by
   …", "define $\Phi:[-1,1]\to[-1,1]$ by …". A parametrized piece states its
   parameter range on the same line: `e_b\coloneqq…,\qquad b\in(0,\tfrac12]`.
   An argument whose domain the article does not state has its natural domain:
   `$T_w(x)\coloneqq\begin{cases}…\end{cases}$` is defined at the `x` where one of its
   cases applies, and `$\Delta(x,z)\coloneqq\varphi(x)+\psi(z)-c(x,z)$` at the points
   where the functions on its right side are. A use of the symbol outside this domain is
   a definedness condition that fails, so a formula `$e_b\coloneqq…$` with a range
   `$b\in(0,\tfrac12)$` cannot be used at `$b=\tfrac12$`: state the range the article
   uses.
6. **Make every quantifier explicit.** "for every $r\in[-1,1]$" instead of a
   free $r$. A variable bound at the start of a result ("For $w\in[0,1]$, …")
   stays bound in the result's later sentences that use it.
7. **Cite what a step uses.** "By Lemma~\ref{…}, …", "By \cref{…}, …", "…, by
   \eqref{…}", "\eqref{…} gives …", and with several results "By \eqref{…} and
   Lemma~\ref{…}, we have …". A proof sentence may use the earlier sentences of its
   proof and the results it cites, and nothing else. The citation audit rejects
   a Lean justification that uses anything more.
8. **Split a statement into its claims.** "Both constants are sharp. The
   maximum $\frac{27}{128}$ of $\beta-\alpha$ is attained only by $A_{3/4}$, …"
   is two sentences: a remark and a claim.
9. **Decimal values are approximations.** Write `g_*\coloneqq\frac{173-16\sqrt3}{363}\approx0.4002`,
   not `=0.4002\ldots`: an `\approx` value is an illustration and asserts
   nothing.
10. **Image sets name the class of their variable.** Write
    `\{\alpha(x):x\in\mathcal{X},\ \beta(x)=0\}`, not `\{\alpha(x):\beta(x)=0\}`.
11. **No semicolons in prose.** A semicolon joins two claims without saying how
    they relate. Use a period, ", and", ", so" or ", whereas".
12. **Fixed variables stay fixed.** "fix $b\in(0,\frac12)$" binds `b` for the
    following sentences of the section, and "Let $w\in[\frac12,1)$." at the
    start of a result binds `w` for the rest of the result. A symbol defined
    under a binder whose name does not show the variable (`z_-(x)` under "For
    $b\in(0,\frac12]$") depends on it implicitly: each use takes the `b` of its
    context.
13. **Overloading needs disjoint domains.** A family defined again on a further
    parameter domain (`\kappa_w` for `w\in[\frac12,1)`, later `\kappa_b` for
    `b\in(0,\frac12)`) is one family on the union. Its well-definedness asks
    that the domains do not overlap, which is the paper's "no confusion can arise".

## Definitions

| Form | Example |
| --- | --- |
| class | `let $\mathcal{X}$ denote the class of NOUNS, that is, NOUNS with PROPERTY.` (the description after "that is" is in the vocabulary's words) |
| quantity of an object | `For a NOUN $x$, the NAME of $x$ is \begin{equation}\alpha(x)\coloneqq…\end{equation}` |
| several quantities | `For a NOUN $F$, the transpose of $F$ is $F^\top(u,v)\coloneqq F(v,u)$, and the NAME of $F$ is …` |
| map on a ray | `Define $f:(0,\infty)\to\mathbb{R}$ by $f(x)\coloneqq x+\frac1x$.` (an interval may have an infinite end: `(0,\infty)`, `[1,\infty)`, `(-\infty,0]`. Its domain makes `\frac1x` well defined) |
| map with signature | `define $\Phi:[-1,1]\to[-1,1]$ by \[…\]` (a `cases` display is a piecewise definition; a piece may follow as `on $(-1,-\frac34)$, parametrically by \[…\]`) |
| definition with an observation | `… and observe that $2r-\Phi(r)=-\Phi(-r)$ for every $r\in[-1,1]$.` (the observation is a claim) |
| family | `For $c\in[0,1]$, let $D_c$ denote the NOUN associated with $\gamma_{\zeta_c}$ from Section~\ref{sec:preliminaries}.` |
| family with a local map | `For $w\in[0,1]$, let $A_w$ be the NOUN associated with $\gamma_{T_w}$, where $T_w:[0,1]\to[0,1]$ is given by \begin{equation}…\end{equation}` |
| auxiliary symbol | `For $b\in(0,\frac12]$, set $z_b\coloneqq\frac{b}{2(1-b)}$ and let $B_b$ be …` |
| functions of several variables | `For $u,v\in[0,1]$, set $M(u,v)\coloneqq\min\{u,v\}$, $W(u,v)\coloneqq\max\{u+v-1,0\}$ and $\Pi(u,v)\coloneqq uv$.` (the arguments are the binder's variables, in its order; on $[0,1]$ the result is a function on the unit square) |
| part of the binder's variables | `For $t\in[0,1]$ and $u,v\in[0,1]$, let $f_t(v)\coloneqq\frac{1-t}2v+t\min\{v,\frac12\}$ and \[Q_t(u,v)\coloneqq\max\{uv,\ f_t(v)-(\tfrac12-u)^+\}.\] Then $Q_t$ is a copula.` (each definition takes the variables of the binder that it names, in the binder's order. In the statement of a result, the parameter of a family it defines stays bound in its later sentences and in its proof: `Then $Q_t$ is a copula` is about every `t\in[0,1]`) |
| a family of functions | `For $s\in[0,1]$ and $u,v\in[0,1]$, set $S_s(u,v)\coloneqq\min\{u,v,1-s\}+\max\{u+v+s-2,0\}$.` (indexed by the first variable, a function of the others) |
| a piecewise function | `For $a\in(0,1]$ and $u,v\in[0,1]$, let \[A_a(u,v)\coloneqq\begin{cases}\min\{u,v\}&\text{if }\min\{u,v\}\le a,\\ a+\frac{(u-a)(v-a)}{1-a}&\text{otherwise.}\end{cases}\]` (a display; each row is a value and its condition, `v & φ` or `v & \text{if } φ`, and the first row whose condition holds gives the value. A last row `\text{otherwise}` is for the points where no row before it applies; without it the function is defined only where a row applies. A value has to be meaningful only where its row applies: `1-a` is not zero in the second row) |
| combinations of functions on the square | `For $r\in[0,1]$, set $M_r\coloneqq(1-r)\Pi+rM$.`, `$\frac{M+W}2$`, `$-C$` (functions on the unit square are added, subtracted, and multiplied or divided by a number, value by value: `(1-r)\Pi+rM` is the function `(u,v)\mapsto(1-r)\Pi(u,v)+rM(u,v)`; an order between two of them, `$W\le C\le M$`, is the order of their values at every point) |
| a letter for a function and for a family | `$M$` and `$M_r$` (a letter may name a constant or function and, written with a subscript, a family: the two are different symbols, and the readings show the family as `M_{r}`) |
| a family of maps | `For $s\in(0,1]$, define $\varphi_s:[0,1]\to\R$ by \[\varphi_s(t)\coloneqq\begin{cases}…\end{cases}\]` (also `T^0_q`, `R_b^-`; the map takes values in its codomain, a claim) |
| a definition in a proof | `For $v\in[0,s]$ and $w\in[0,1-s]$, set $g_v(w)\coloneqq(v+w)^2(2s-3v+3w)$.` inside the proof of a result about $s$, or `Fix $t\in[0,1]$. For $v\in(0,1)$, let $a(v)\coloneqq\frac{t}{1-v}$.` (the variables of the result or the proof that it uses are implicit arguments: `g_v(0)` is `g` at `s`, `v`, `0`, and `a(v)` is `a` at `t`, `v`. A function or a family defined in a result or a proof is local to it: it is visible there and in the proof of the result, and its letter is free again afterwards) |
| a definition with a binder | `For every $r\in(-1,1)$ and $s\coloneqq(\frac{1-r}{2})^{1/3}$, $S_s$ is …` (a function of the binder's variables, local to the result) |
| decorated names | `For $b\in[-1,1]$, set \begin{equation}r_-(b)\coloneqq-1+\tfrac{3}{16}(1+b)^3,\qquad r_+(b)\coloneqq1-\tfrac{3}{16}(1-b)^3.\end{equation}` |
| named map | `For $c\in[0,1]$, the corresponding rank map $\zeta_c:[0,1]\to[0,1]$ reads \[…\]` |
| notion of the vocabulary | `Lebesgue measure on $[0,1]$ is denoted by $\mathrm{Leb}$.` |
| relation | `We say that a NOUN $F$ is \emph{supported on the graph} of a Borel measurable $f:[0,1]\to[0,1]$ if $F(u,v)=…$ for all $u,v\in[0,1]$.` |
| a class described by its members | `Let $\mathcal F$ denote the class of Borel measurable functions $f:[0,1]\to\mathbb{R}$ with $\int_0^1 f(x)\,dx=0$ and $\int_0^1 f(x)^2\,dx=1$.` (the objects for which the conditions are meaningful and hold: the functions that are integrable with integral zero; it is not asked that every function be integrable) |
| a function on a class, and a family indexed by it | `For a function $A:\mathcal C\to\mathbb{R}$, let $\mathcal R_A\coloneqq\{(A(C),R(C)) : C\in\mathcal C\}$.`, then `$\mathcal R_\beta=\mathcal R_\rho=\{(m,r) : |m|\le r\le1\}$`, `$\mathcal R_{\tau^*}$` (the domain of the signature is a class of the article, `Let $\mathcal C$ denote the set of NOUNS.`; the value of the variable is asked for at members of the class only) |
| a family with two subscripts | `For $r\in[0,1]$ and $g\in[-r,r]$, set $C_{r,g}\coloneqq(1-r)\Pi+\frac{r+g}2M+\frac{r-g}2W$.` (the subscripts are the binder's variables, all of them and in its order; then `C_{r,r}`, `C_{r,-r}`) |
| class of the vocabulary | `Let $\mathcal{X}$ denote the class of NOUNS.`, `We denote by $\mathcal{X}$ the set of NOUNS.` |
| definitions named by a noun | `Let \[M(u,v)\coloneqq\min\{u,v\},\qquad W(u,v)\coloneqq\max\{u+v-1,0\}\] denote the comonotonicity and countermonotonicity copulas.` (with the field `unitsquare`), `let \[e(k)\coloneqq…,\qquad c(k)\coloneqq…\] denote the trivial and the fair-coin distributions.` (each definition has one of the names, in their order, and the names are not read. The variables of a definition range over the arguments of the noun's objects, the points of `[0,1]` for a copula, and that each defined function is such an object is a claim) |
| definitions announced | `We consider five signed coefficients of a copula $C$, DISPLAY`, `We further consider two weights of a distribution $\nu$, DISPLAY` (as `For a copula $C$, set DISPLAY`: the words before `of` name what the display defines) |
| a notation in a `where` | `Set $z\coloneqq\mathrm{NB}(1,\frac12)(0)$, where $\mathrm{NB}(r,p)$ is the negative binomial distribution with parameters $r$ and $p$.`, `…, where $\Phi_{\mathrm N}^{-1}$ is the standard normal quantile function.` (as `We write $\mathrm{NB}(r,p)$ for the …`, before the rest of the sentence) |
| several definitions in one sentence | `Let $\mathcal C$ denote the set of bivariate copulas, and let DISPLAY denote …`, `For $x\in\mathbb R$, set $\phi(x)\coloneqq x^2+1$, and let $\psi(x)\coloneqq2\phi(x)$.`, `For a copula $C$, we write $C^\top(u,v)\coloneqq C(v,u)$, and $h_C$ for the conditional distribution function of $C$.` (the sentences it is made of, one after the other, joined by `, and` before `let`, `set`, `put`, `define`, `we`, `write`, `denote` or `fix`. A formula after `, and` continues the verb before it (`we write`), and a binder at the start of the sentence is the binder of each part. Read so only if every part is read, and if the sentence as a whole has no reading that compiles) |
| `we write` a definition | `We write $s(t)\coloneqq t^3-t$.`, `For a copula $C$, we write $C^\top(u,v)\coloneqq C(v,u)$.` (as `set`) |
| two quantities at once | `For a NOUN $x$, the NAME and the NAME of $x$ are \begin{equation}\alpha(x)\coloneqq…,\qquad\beta(x)\coloneqq….\end{equation}` |
| constants | `Set $r_0\coloneqq\frac{144+9\sqrt6}{500}\approx0.33209$.`, `Define \begin{equation}d_0\coloneqq…,\qquad\Delta_0\coloneqq….\end{equation}` |
| a named set | `The joint range of $\alpha$ and $\beta$ is \begin{equation}\Omega\coloneqq\{(\alpha(x),\beta(x)):x\in\mathcal{X}\}.\end{equation}` |
| a maximum | `For $t\in[-1,1]$, set \begin{align}u(t)\coloneqq\max\{\alpha(x):x\in\mathcal{X},\ \beta(x)=t\}.\end{align}` (a definite description: well defined when the maximum exists) |
| quantities of a parameter | `For a positive integer $\ell$, we set $Q=2^{-\ell}$ and $\varepsilon=Q^{1/2}$.` (`=` after `we set`, `we put`, `let us set` or `set` defines the left side, as `\coloneqq`; `\ell` is an implicit argument of `Q` and `\varepsilon`) |
| a class of functions | `A map $a:\mathbb R^2\to\mathbb R$ belongs to $\mathcal S_m$ if $|\partial^Ia(x,\xi)|\le B_I(1+|\xi|)^{m-I_2}$ for every $I\in\mathbb N_0^2$ and every $x,\xi\in\mathbb R$.` (also `is in`, `lies in`; the subscript is a parameter of the class, `f\in\mathcal S_m` its use; the constants are placed by their conventions, `B_I` after `I`) |
| a class of families | the same with a quantity of a parameter (`\lambda=2^j` set for every positive integer `j`) and a constant `uniform in $j$`: the members are families `j ↦ f_j`, `f` in the condition is the member at `j`, and `j` is bound after the constants, so the bound is uniform in `j` |
| a fixed variable | `To describe the supporting lines of the region, fix $\kappa>0$ and define \[d_\kappa(x,z)\coloneqq x^2z-\kappa\,xz^2.\]`, `For the second regime, fix $b\in(0,\frac12)$ and put $\kappa_b\coloneqq\frac{2(1-b)}{b}$.` |
| an implicit parameter | `For $b\in(0,\frac12]$, set \begin{equation}z_-(x)\coloneqq\frac{x+b-1}{2(1-b)},\qquad z_+(x)\coloneqq\frac{1-b-(1-2b)x}{2(1-b)}.\end{equation}` |
| value and derivative | `define continuous functions $\varphi_w,\psi_w:[0,1]\to\R$ by $\varphi_w(1-w)=0$, $\psi_w(0)=0$, and DISPLAY` with `\varphi_w'(x)=\begin{cases}…\end{cases}` in the display, or `Let $\varphi_b,\psi_b:[0,1]\to\R$ be continuous, normalized by $\varphi_b(1-b)=0$ and $\psi_b(0)=0$, with derivatives DISPLAY` (read as `φ(x) = φ(a) + ∫_a^x φ'`; the derivative may be given on open pieces) |
| a set of pairs | `For $w\in[\frac12,1)$, the support of $\gamma_{T_w}$ is \[S_w\coloneqq\{(x,1-x):0\le x\le1-w\}\cup\{(x,x+w-1):1-w\le x\le1\}.\]` (unions `\cup`, products `[a,b]\times\{c\}`) |
| the variable of a result or a proof | `Let $w\in[\frac12,1)$.` (in a proof, `Let $x\in(0,\infty)$. Then $\frac{(x-1)^2}{x}\ge0$.` binds `x` in the later steps of the proof); a condition binds its variables as well: `Let $c>0$.`, `Let $c>0$ and $z\in(0,1)$.` |
| a bound as the domain | `For every $c>0$, …`, `For $c\ge1$, set …`, `For $0<t\le1$, …` (`c>0` is `c\in(0,\infty)`, `0<t\le1` is `t\in(0,1]`) |
| a fixed variable of a result | `Fix $x>0$.`, `Fix an integer $k\ge3$.`, `Fix an integer $k\ge3$ and $\lambda>0$.`, `Fix a sufficiently large $R$.`, `Let $c>0$ be fixed.`, `Let $m\ge1$ be a fixed integer.`, `Let $\gamma$ be fixed.` (in a result or a proof, as `Let …`; in the running text, the variable is fixed for the section). `Fix a small $\zeta>0$` does not say how small, and is refused with a finding |
| a symbol of a result | `Let $x>0$. Set $y\coloneqq x^2$. Then $y>0$.` (a definition that uses the variables of the result or proof, or the fixed variables of the section, takes them as implicit parameters) |
| a symbol with a variable as its subscript | `Let $c>0$, and let $n\ge2$ be an integer. Set $\delta_n\coloneqq\frac cn$. Then $\delta_n>0$.` (the name of the symbol is `\delta_n`, and it takes `c` and `n` as implicit parameters: each use is the symbol at the `n` of its context. Outside the result the name is not defined; a family for every `n` is defined under a binder, `For $n\ge2$, set …`) |
| a domain that uses an earlier variable | `Let $x\in(0,1]$ and $e\in[0,x]$.` (the claims that use `e` are also about `x`) |
| upper and lower signs | `For $c\in(0,\infty)$, set $x_\pm(c)\coloneqq c\pm1$.` defines `x_+` and `x_-`; a claim with `\pm` or `\mp` is the two claims, one for each sign |
| the variable after the definition | `Write $g(t)\coloneqq\min\{\max\{t,0\},1\}$ for $t\in\mathbb{R}$.`, `Define the weight \[a(x,z)\coloneqq x(x+2z),\qquad (x,z)\in[0,1]^2.\]` |
| the least or the greatest | `For a positive integer $n$, let $j(n)$ be the least positive integer $m$ such that $m^2\ge n$.` (also `smallest`, `minimal`, `largest`, `greatest`, `maximal`; `for which DISPLAY`; `Define $L$ to be|as …`, `We write $L$ for …`, `Denote by $L$ …`): a definite description, well defined where such a least number exists |
| how many | `Let $N$ be the number of primes $p\le 10$.`, `Write $\omega(n)$ for the number of primes $p$ such that $p\mid n$.` (well defined where finitely many numbers are described) |
| how many, as a value | `Let $n$ be a positive integer and let $N$ be the number of primes less than $n$.`, `Then the number of positive divisors of $n$ is at most $n$.` (the objects of the noun phrase, real numbers, counted where no notion of the vocabulary has the words; defined where they are finitely many) |
| a symbol after `let` | `Let $c\coloneqq2$.`, `For $k\ge1$, let \[h(k)=\sup_{\substack{n\ge1\\ n\le k}} j(n).\]` (as after `set`) |
| law of a construction | `For a Borel measurable $T:[0,1]\to[0,1]$, let $\gamma_T$ denote the law of $(X,T(X))$ for $X$ uniformly distributed on $[0,1]$.` |

## Definitions in the running text

A paper defines most of its notation in passing: a notion in the middle of a
paragraph, a symbol in the statement of the theorem that uses it, an
abbreviation after a `where`. Leanify reads these where they stand.

| Form | Example |
| --- | --- |
| a notion of an object | `We call a NOUN $F$ \emph{dominating} (\emph{DOM}) if $F(u,v)\ge uv$ for all $u,v\in[0,1]$.` (the abbreviation in parentheses is optional, and the notion may then be used by either name) |
| a notion by a monotone map | `A NOUN $F$ is called \emph{ray-monotone} (\emph{RM}) if, for every $v\in[0,1]$, the map \begin{equation}u\longmapsto\frac{F(u,v)}{u},\qquad u\in(0,1],\end{equation} is non-increasing.` (`the map` may be left out: `$F$ is \emph{RM} if, for every $v\in(0,1)$, DISPLAY is non-increasing.`) |
| a notion by a clause | `A group $G$ is called \emph{nice} if $G$ is abelian.`, `We say that a group $G$ is \emph{boolean} if $g^2=1$ for all $g\in G$.`, `Let $G$ be a group. An element $g\in G$ is called an \emph{involution} if …` (a notion of objects of the result's variables, `G`: an object is an involution if it is one for some group `G` it belongs to; `let $g\in G$ be an involution` uses it; the condition is any clause about the subject, or several joined by `and`; the binders after it may use it, and `for all distinct $x,y\in X$` asks `x\neq y`) |
| the forms of such a definition | The same notion, however the sentence is built: `A group $G$ is called \emph{agreeable} when $G$ is abelian.` (`when`, `whenever`, `provided [that]`, `if and only if`, `iff`, `in case`); `We say that a group $G$ is \emph{good} provided that …` (`we call`, `is said to be`, `is termed`, `is known as`, `will be called`, with `then`, `also`, `often` inside the verb); `If a group $G$ is abelian, then we say that $G$ is \emph{fine}.` (the condition first); `A group $G$ such that $G$ is abelian is called a \emph{calm group}.` (`such that`, `satisfying`, `with`, `for which`); `A \emph{quiet group} is a group $G$ such that …`, `By a \emph{tiny number} we mean a real number $x$ such that $x<0$.` (the name first: a kind of object, `let $G$ be a quiet group`, `every quiet group`); `A group is said to be \emph{mild} if it is abelian.` (the subject without a variable: `it`, and `its NOUN` for `the NOUN of` it); `Let $G$ be a group and let $H$ be a subgroup of $G$. Then $H$ is called \emph{wide} if $[G:H]=2$.` (a notion of a variable of the result: an object is wide if it is, for some values of the other variables). Words that only lead to it are skipped (`Recall that`, `Here,`, `Following \cite{a},`), and so are its citations (`(cf. \cite{b})`) and `\index{…}`. Without a verb that names (`A group $G$ is \emph{nice} if …`, `A \emph{NAME} is a NP …`) the sentence is a definition only in a definition |
| the same subject again | `Similarly, $F$ is called \emph{NAME} (\emph{ABBR}) if …` (`$F$` is the NOUN of the previous notion) |
| using a notion | `Every RM NOUN is DOM.`, `Let $F$ be an RM NOUN, and let $u,v\in[0,1]$.`, `For every RM NOUN $F$, …`, `If $F$ is an RM NOUN, then …`, `Every RM NOUN $F$ satisfies $F(u,v)\ge uv$ for all $u,v\in[0,1]$.`, `$F$ is RM`, `both RM and DOM` |
| symbols inside a result | `Let $a,b\in(0,\infty)$, and let $A\coloneqq\frac{a+b}{2}$, $G\coloneqq\sqrt{ab}$ and $H\coloneqq\frac{2ab}{a+b}$. Then $H\le G\le A$.` (the symbols belong to the result and its proof, and depend on `a` and `b`) |
| `where`-clause | `Then $\frac{a+b}{2}-\sqrt{ab}=\frac{d^2}{2}$, where $d\coloneqq\sqrt a-\sqrt b$.` |
| in apposition | `For $a,b\in(0,\infty)$, the quadratic mean $Q\coloneqq\sqrt{\frac{a^2+b^2}{2}}$ is at least the arithmetic mean $\frac{a+b}{2}$.` |

A notion is a property of the objects of a class, and its definition is its
only meaning: `RM(F)` unfolds to the condition after "if". A monotone map is
`non-increasing`, `non-decreasing`, `strictly increasing` or `strictly
decreasing` on the domain written after it (`u\in(0,1]`). A bare `increasing`
is not read, because papers use it in both senses. A symbol defined inside a
result (`A`, `G`, `H`) is not visible after the result and its proof, so the
next theorem may define its own `A`. A notion whose condition needs words the
vocabulary does not have yet (a Markov kernel, say) stays prose, and so do the
sentences that use it. Its subject still counts: after `We call a NOUN $F$
\emph{NAME} if its Markov kernel can be chosen such that …`, the sentence `$F$
is \emph{RM} if …` defines RM for NOUNS.

## Claims

A claim sentence is an optional discourse marker ("Hence", "In particular",
"Consequently", …), optional binders ("For every $x\in A$,", "For a NOUN
$x$,", "On $I$,"), and clauses joined by ", and" or ", so", each with its
citations.

| Form | Example |
| --- | --- |
| formula, chain, equivalence | `$\lvert\alpha(x)-\beta(x)\rvert\le\frac14$`, `$0\le\Upsilon(e)\le\frac{27}{128}$ for every $e\in[-1,1]$` |
| joint range | `It holds that \[\bigl\{(\alpha(x),\beta(x)):x\in\mathcal{X}\bigr\}=\bigl\{(s,t)\in[-1,1]^2:2s-\Phi(s)\le t\le\Phi(s)\bigr\}.\]` |
| unique attainment | `exactly one NOUN $x$ with $\alpha(x)=s$ satisfies $\beta(x)=\Phi(s)$` |
| the only one | `its transpose is the only NOUN with $\alpha=s$ and $\beta=2s-\Phi(s)$`, `$S_{3/4}$ is the only NOUN $C$ with $\eta(C)-\rho(C)=\frac{27}{128}$` |
| a condition on the variable | `Every NOUN $C$ with $\rho(C)=0$ satisfies $|\eta(C)|\le1-2^{-1/3}$.` |
| a condition after the variable of a binder | `For every NOUN $C$ with $C^\top=C$ and every integer $k\ge1$, we have …` |
| a noun with conditions, said of an object | `For every $t\in[0,1]$, $Q_t$ is a NOUN with $D(Q_t)=0$ and $R(Q_t)=\sqrt t$.` (what follows `with` is said of the same object: three claims) |
| several statements about each object | `Every NOUN $C$ satisfies $φ$, $ψ$, and $χ$.` (as `For every NOUN $C$, $φ$, $ψ$, and $χ$.`: one claim for each statement) |
| a sentence through a list | `Every NOUN $C$ satisfies \begin{enumerate}[(i)] \item $φ$, $ψ$, \item $χ$. \end{enumerate}`, `Then \begin{enumerate} … \end{enumerate}`, `Then the following hold: \begin{enumerate} … \end{enumerate}` (a sentence that stops at `satisfies`, `Then`, `we have`, `that`, or announces its list with `the following hold:`, continues through the list: the items are its statements, one after the other, each a claim) |
| the value of a function, named by its letter | `Every NOUN $C$ with maximal correlation $R=R(C)$ satisfies $|\tau(C)|\le\frac13R(2+R)$.`, `Let $C$ be a NOUN with $R=R(C)$.` (in the result and its proof, `R` alone is `R(C)`, and `R(2+R)` is a product; words before the formula are the name under which the article introduced the function, `We write $R(C)$ for the maximal correlation of a NOUN $C$.`) |
| words between a binder and its claim | `For every NOUN $C$ and all $u,v\in[0,1]$, we have $C(u,v)\le M(u,v)$.` (`we have`, `one has`, `it holds that` after the binders say nothing) |
| extremum | `The maximum $\frac{27}{128}$ of $\beta-\alpha$ is attained only by $A_{3/4}$, at which $(\alpha,\beta)=(-\frac{5}{32},\frac{7}{128})$, and the minimum $-\frac{27}{128}$ only by $A_{3/4}^\top$.` |
| monotone bijection | `$c\mapsto\alpha(D_c)$ increases bijectively from $[0,1]$ onto $[-1,1]$` |
| monotone maps, ranges | `Both parameter maps $w\mapsto\alpha(A_w)$ and $b\mapsto\alpha(B_b)$ are strictly increasing. For $w\in[\frac12,1]$, the first ranges over $[-\frac34,1]$, …` |
| derivative | `whose derivative $1-(1+r)^{1/3}$ is positive for $r<0$` |
| relation | `$D_{1/2}$ is supported on the graph of the tent map $u\mapsto\min\{2u,2-2u\}$` |
| transformation | `the map $F\mapsto\widehat F$ sends $\beta-\alpha$ to $\alpha-\beta$ by \eqref{eq:reflection}` |
| condition | `If $-1\le t\le t_*$, then \begin{equation}u(t)=\frac{144+420t+(9+65t)\sqrt{6-10t}}{500}.\end{equation}`, `If $x>0$ and $y>x$, then $y^2>x^2$.` (several conditions joined by `and`) |
| maximum of a quantity | `Then \begin{equation}\max_{x\in\mathcal{X}}|\alpha(x)-\beta(x)|=\Delta_0.\end{equation}` |
| image sets | `\{\alpha(x):x\in\mathcal{X},\ \beta(x)=0\}=[-r_0,r_0]` |
| extrema at a fixed value | `For every $n\in[-1,1]$, the maximum $\Lambda(n)$ and the minimum $\Lambda^{-1}(n)$ of $\alpha(x^\top)$ over all NOUNS $x$ with $\alpha(x)=n$ are each attained by exactly one NOUN.` |
| an inequality on a square | `Then every $(x,z)\in[0,1]^2$ satisfies \begin{equation}\varphi_w(x)+\psi_w(z)\ge d_{\kappa_w}(x,z).\end{equation}` |
| sharpness | `Both constants are sharp.` (after a claim `a\le c` about every element of a domain: for every `ε > 0` some element has `c - a < ε`) |
| shape | `Moreover, $\Om$ is compact, convex and centrally symmetric, and $\rhoup$ is continuous, concave and strictly increasing.` (a function on the domain its definition states) |
| standard properties | `The function $g$ is convex, nondecreasing on $[0,\infty)$ and Lipschitz on $[0,1]$.`, `Then $c$ is positive.`, `Moreover, $\xi$ is convex on $\CC$ and lower semicontinuous with respect to uniform convergence.` (see [Standard notions](#standard-notions)) |
| comparison in words | `$Q$ is at least the arithmetic mean $\frac{a+b}{2}$`, `is at most`, `is less than`, `is greater than`, `is equal to`, `does not exceed` |
| one of several values, a negated noun | `$x$ is $0$ or $1$`, `$p$ is either $2$, $3$ or $5$` (equal to one of them: `x=0` or `x=1`; values, not conditions); `$0$ is not a divisor of $n$`, `$H$ is not a normal subgroup of $G$`, `$0$ is not an eigenvalue of $A$` (the negation of `is a divisor of $n$`) |
| containing | `$[0,1]$ contains $1/2$`, `$(0,1)$ does not contain $0$`, `the kernel of $\varphi$ contains $1$`, `$C$ contains $B$` (an element, `x\in S`; a set of the same elements, `B\subseteq C`: the types decide); `Let $A$ be a set of real numbers containing $0$.`, `Let $H$ be a subgroup of $G$ containing $g$.`, `every open subset of $X$ containing $x$` (the same, of the object of the noun) |
| membership and divisibility in words | `the identity of $G$ lies in $H$`, `$g$ belongs to $H$`, `does not lie in`, `the order of $H$ divides the order of $G$`, `does not divide`, `exceeds` (either side a formula or a notion of the vocabulary with its arguments) |
| having an object | with a vocabulary: `$f$ has a fixed point`, `$f$ has a unique fixed point`, `$G$ has an element of order $2$` (there is a `fixed point of $f$`, an `element of $G$ of order $2$`: the noun's complement is the subject). `$B$ spans $V$`, `$S$ generates $V$`: a spanning or generating set of it |
| having an object with a condition, the value of a notion | `$n$ has a divisor $d$ with $1<d<n$`, `$n$ has a divisor $e$ such that $e^2\le n$` (there is a `divisor $d$ of $n$` with the condition); `$A$ has determinant zero`, `every nilpotent matrix has trace $0$`, `$G$ has exponent $6$` (the value of the notion `determinant of $A$`: `the determinant of $A$ is zero`; only a notion of the vocabulary, not a noun of several objects: `$A$ has eigenvalue $2$` is not read) |
| the same subject after `and` | `$G$ is finite and has exponent at most $4$`, `A graph is a tree if and only if it is connected and has no cycle.` (`$G$ is connected and $G$ has no cycle`, both: inside `if and only if` as one side); `has chromatic number at most $2$`, `has rank at most $n$` (also `at least`, `less than`, `greater than`: a bound on the value of the notion) |
| a notion as the subject, a notion plus a number | `The complete graph on $n$ vertices has $n(n-1)/2$ edges.` (the value of the notion, as `Let $X$ be the complete graph on $n$ vertices.` binds it, then the claim about it); `the chromatic number of $G$ is at most the maximum degree of $G$ plus $1$` (`\Delta(G)+1`; also `minus`, `times`) |
| equal to a sum of notions | `the degree of $pq$ is the degree of $p$ plus the degree of $q$` (as `equals`; also `minus`, `times`) |
| in every object | `In every tree, the number of edges is the number of vertices minus $1$.` (as `For every tree $X$, the number of edges in $X$ is the number of vertices in $X$ minus $1$.`, also `of $X$`: the notions of the object) |
| a function by its name | with the field `realfunctions`: `The exponential function is convex.`, `The sine function is bounded.`, `The derivative of the sine function is the cosine function.`, `The identity function is continuous.`; `The image of a compact space under a continuous map is compact.` (with the field `structures`: as `A continuous image of a compact space is compact.`) |
| elements of a structure in formulas | with the field `structures`: `If $g^2=1$ for all $g\in G$, …`, `$\exists g\in G: g=1$` (a variable bound in a structure is one of its elements); `$f(K)$` of a map and a set of its domain (the image); `$d(x,y)$` of two points of a metric space where the article defines no `d` (its distance) |
| an object of a structure | with the field `structures`: `every subgroup of $G$ is normal`, `Let $H$ be a subgroup of $G$. Then $H$ is normal.` (an adjective the vocabulary has relative to a structure, `normal in $G$`, is relative to the structure the noun names: the subgroup is normal in `G`); `there is a fixed point of $f$` (an object without a name) |
| if and only if | `Moreover, $G=A$ if and only if $a=b$.` |
| several objects of a noun | `there are integers $x$ and $y$ with $ax+by=1$`, `there are integers $x,y$ such that …`; `For every integer $n\ge0$, the number $n^3-n$ is divisible by $6$.` (after a comma or `then`, `the number $X$` is `$X$`) |
| parameters in a noun phrase | `Let $G$ be a graph with $n$ vertices and $m$ edges.`, `Let $A$ be an $n\times n$ matrix.`, `Let $x_1,\ldots,x_n$ be positive real numbers.`, `Let $x_1,\ldots,x_n$ be elements of $R$.` (a finite sequence of elements of a structure), `Every tree with $n$ vertices has $n-1$ edges.` (a letter that nothing defines, in a formula of the noun phrase of a binder, is a number bound with the object: the statement is for every `n`); `Let $K$ be a field of characteristic $p>0$.` (with its bound: for every `p>0`); `$G$ has $n-1$ edges` (the modifier `with $n-1$ edges`); `$g$ has finite order`, `$G$ has order $n$`, `$K$ has characteristic $p$` (the modifiers `of finite order`, `of order $n$`, `of characteristic $p$`) |
| a field extension | with the field `structures`: `Let $L/K$ be a field extension.`, `Let $L/K$ be a finite field extension.` (the field `K`, and `L` an extension of it with the noun's words) |
| a common bound | `If $a,b>0$ and $a+b=1$, then …` (`a>0` and `b>0`); `such that $f(x)=f(-x)$ for every real number $x$` (also `for all integers $n$`, `for every natural number $n$`) |
| existence of a term | `$\sup A$ exists`, `$A$ has a maximum` (a minimum, a supremum, an infimum, a largest element): the term is defined |
| a relative clause | `Let $A$ be a nonempty set of real numbers that is bounded above.` (the adjectives after `that is`, `which are`, as modifiers after the noun); `Let $H$ be a normal subgroup of $G$ that is cyclic.` (also after the noun's complement); `Let $p$ be a quadratic polynomial that has no real roots.` (`that has`: the modifier `with …`, `without …`); `Let $A\subseteq\mathbb{R}$ be finite and nonempty.` (a subset of the domain); `Let $g\in G$ be of finite order.` (a modifier after the noun `element`); `The interval $[0,1]$ is compact.` |
| a negated modifier, a relative clause after a modifier | `Let $a$ be an integer not coprime to $6$.`, `Every integer not congruent to $0$ modulo $2$ is odd.` (`not` before a modifier after the noun: its negation, as `that is not coprime to $6$`); `Let $n$ be an integer greater than $1$ that is not prime.`, `Every integer greater than $1$ that is not prime has a prime divisor.`, `Every integer that is not prime is …`, `For every integer $m$ that is odd, …` (the relative clause after the modifier, of the same object); `Let $q$ be a prime congruent to $1$ modulo $4$.` (a modifier with two formulas after the noun) |
| a sequence named before its terms, a limit of the same letter | `Every convergent sequence $(u_n)$ of real numbers is bounded.`, `For every sequence $(v_n)$ of real numbers with $v_n\to0$, …` (as `sequence of real numbers $(u_n)$`); `Let $a$ be a real number and let $(a_n)$ be a sequence of real numbers converging to $a$.` (`a` alone is the number, `a_n` the term of the sequence) |
| converging in a condition, a generic noun phrase with `it` | `$(a_n)$ converges if and only if $(a_n)$ is bounded`, `… converges if …`, `… converges and …` (as `is convergent`); `A sequence of real numbers converges if and only if it is a Cauchy sequence.`, `A sequence of real numbers diverges if and only if it is not convergent.` (for every such sequence `$X$`, with `it` as `$X$`) |
| variables of a chain | `Let $a<b$ be real numbers.`, `Let $0<s<t$ be real numbers.` (each variable of the noun, and the chain) |
| variables with conditions | `Let $R>0$ and $h$ be real numbers with $0\le h\le2R$.`, `Let $a$, $b>1$ and $c$ be integers.` (each variable of the noun, and the condition on it) |
| a function on a domain | `Let $f\colon[a,b]\to\mathbb{R}$ be a continuous function.`, `Let $f\colon(0,\infty)\to\mathbb{R}$ be an increasing function.` (the standard adjectives before the noun, `continuous`, `increasing`, `convex`, `bounded`, `differentiable`, …, are said on the domain of the signature, as `$f$ is continuous` is afterwards); `Let $f\colon\mathbb{R}\to\mathbb{R}$ be a differentiable function with $f'(x)=0$ for all $x$.` (conditions after the noun); `Let $f\colon[0,1]\to\mathbb{R}$ be continuous with $f(0)<0<f(1)$.` (adjectives without a noun); `Suppose $f\colon\mathbb{R}\to\mathbb{R}$ is differentiable and $f'$ is bounded.` (the map with its adjectives, then the other hypotheses); `Let $f,g\colon\mathbb{R}\to\mathbb{R}$ be differentiable.` (several maps, each with the adjectives); `uniformly continuous` (with `\varepsilon` and `\delta` on the domain) and `constant` are said on the domain as well, and so are `uniformly continuous`, `Lipschitz`, `constant`, `bounded`, `positive`, `nonnegative` and the monotonicities of a function on `[0,1]` when `[0,1]` is a type (field `unitsquare`) |
| a condition that is a clause | `Let $a\colon\mathbb{N}\to\mathbb{R}$ be a function such that $\sum_{k=0}^\infty a_k$ converges.` (the binder, then the hypothesis `Suppose that $\sum_{k=0}^\infty a_k$ converges.`); `$\sum_{k=0}^\infty a_k$ converges`, `diverges`, `The series $\sum_{n=1}^\infty\frac{1}{n^2}$ converges.`: the series |
| extrema in words | `$f$ attains its maximum on $[a,b]$`, `attains a minimum on $D$` (a point of the set where no value is larger, or smaller) |
| every object has one | `Every bounded sequence of real numbers has a convergent subsequence.` (as `For every … $x$, $x$ has a convergent subsequence`, see *having an object*) |
| a binder with a condition | `Let $f,g\colon[a,b]\to\mathbb{R}$ be continuous with $f(x)\le g(x)$ for all $x\in[a,b]$.` (the condition for all of them), `For every $x\in\mathbb{R}$ with $x\neq0$, $x^{-1}x=1$.`, `For all $x\in\mathbb{R}$ such that $x>0$ and $x<1$, $x^2<x$.`, `For every $y\in\mathbb{R}\setminus\{0\}$, …` |
| several binders with a condition for all of them | `Let $(b_n)$ and $(c_n)$ be sequences of real numbers with $0\le b_n\le c_n$ for all $n$.` (the binders, then the hypothesis `Suppose that $0\le b_n\le c_n$ for all $n$.`) |
| two sequences | `Let $a_1,\ldots,a_n$ and $b_1,\ldots,b_n$ be real numbers.`, `For all real numbers $a_1,\ldots,a_m$ and $b_1,\ldots,b_m$, …` (each sequence of the noun) |
| a condition after the names | `For all real numbers $a$ and $b$ with $a<b$, …`, `For all real numbers $a$, $b$ with $a<b$, …`, `… $a$, $b$ and $c$ with $a<b<c$` (a condition on all of them) |
| a complement after the names | `For all vectors $x$ and $y$ in $\mathbb{R}^n$, …`, `For all vectors $u$, $v$ and $w$ in $\mathbb{R}^n$, …` (each of them in the space) |
| `has no`, `contains`, `in which` | `$G$ has no odd cycle.`, `$G$ contains no triangle.` (the modifier `without odd cycle`); `$G$ has a Hamiltonian cycle.`, `$G$ contains an Eulerian circuit.` (the modifier `with a Hamiltonian cycle`, where no noun `Hamiltonian cycle of` is in the vocabulary); `Let $G$ be a connected graph in which every vertex has even degree.` (as `Suppose that every vertex of $G$ is of even degree.` after the binder) |
| every object with a modifier | `Every vertex of $G$ has even degree.`, `If every element of $G$ is of order $2$, then …` (a modifier after the noun, also in a hypothesis; `of even degree in $v$` of a vertex of `G`); `a graph with $n\ge3$ vertices and minimum degree at least $n/2$` (`and` between the phrases of `with`) |
| chains of variables, counts in words | `Let $n\ge k\ge0$ be integers.`, `For all integers $n\ge k\ge0$, …` (each variable of the chain, and the chain; after a plural noun); `at least two vertices` (`at least $2$`, also `at most`, `exactly`, up to ten); `with more than $n-1$ edges` (as `with at least $\lfloor n-1\rfloor+1$ edges`; `fewer than $k$`: `at most $\lceil k\rceil-1$`), `with exactly $n-1$ edges` (as `with $n-1$ edges`); `$T$ has at least $2$ leaves` (the modifier `with at least $2$ leaves`); otherwise, with a number up to six, the number of such objects of the subject: `$x$ has no square root` (none), `$K$ has exactly two ideals.` (two distinct ideals of `K`, and every ideal of `K` is one of them), `$G$ has at least two elements of order $2$`, `$R$ has at most one maximal ideal` (among any two of them, two are the same) |
| random variables (field `randomvariables`) | `Let $X$ and $Y$ be independent random variables with finite variance.`, `Let $X_1,\ldots,X_n$ be independent and identically distributed random variables with mean $\mu$.`, `Let $X\sim\mathrm{Bin}(n,p)$.`, `Let $X$ follow a Poisson distribution with parameter $\lambda>0$.`, `If $X$ and $Y$ are independent, then …`; `$\mathbb{E}[X^2]<\infty$`, `$P(|X-\mu|\ge k\sigma)\le1/k^2$`, `$P(X>s+t\mid X>s)=P(X>t)$`, `$\operatorname{Var}(X+Y)$` (expectations and probabilities of expressions in the random variables) |
| `not both zero`, pairs | `Let $a$ and $b$ be integers, not both zero.` (`a\neq0` or `b\neq0`); `$(a,b)\neq(0,0)$` (pairs, not intervals) |
| a function on a set | `Let $f$ be a continuous function on $[0,1]$.` (as `Let $f\colon[0,1]\to\mathbb{R}$ be a continuous function.`; also `defined on`) |
| a binder with `whose`, a binder without `be`, `satisfies` | `Let $G$ be a finite group whose order is divisible by $p$.` (as `Suppose that the order of $G$ is divisible by $p$.` after the binder); `Let $R$ be a ring and $I$ an ideal of $R$.`, `Let $V$ be a finite-dimensional vector space and $T\colon V\to V$ a linear map.`, `Let $K$ be a field and $a\in K$ nonzero.` (`be` left out after the first binder, also before a map with its signature and before the adjectives of an element); `If $a,b\in R$ satisfy $ab=0$, then …` (as `If $a,b\in R$ and $ab=0$`; `If $x$ satisfies $φ$` as `If $φ$`) |
| several variables of a noun | `Let $a,b$ be positive integers with $a<b$.`, `If $a$ and $b$ are positive integers, then …`, `For all $n\times n$ matrices $A$ and $B$, …`, `There are integers $c,d$ with $c+d=1$.` (each variable is of the noun; the condition after `with` is about all of them, and without `such that` it is what `there are` asserts) |
| a sequence of variables | `For all $x_1,\ldots,x_n\in[0,1]$, …`, `for all $a_1,\ldots,a_n>0$`, `Let $a_1,\dots,a_k$ be positive integers.`, `If $b_1,\ldots,b_k$ are real numbers with $b_1\ge1$, then …`, `there are $\varepsilon_1,\ldots,\varepsilon_N\in\{-1,1\}$ such that …` (a sequence `x`, a real function, each of whose terms `x_i`, for the integers `i` from the first index to the last, is as the noun or the domain says; the terms written before the dots are the first ones, `x_1,x_2,\ldots,x_n`. A term `x_i` is defined only for those `i`: a claim about `x_{n+1}` is not meaningful) |
| an infinite sequence | with the field `series`: `Let $(a_n)$ be a sequence of real numbers.`, `Let $(a_n)_{n\ge1}$ be a sequence of positive real numbers.`, `Let $(a_n)$ and $(b_n)$ be sequences of real numbers converging to $0$.`, `Let $a$ be a real sequence with $a_n\ge0$ for all $n$.`, `… such that $a_n\le a_{n+1}$ for all $n$`, `Let $a\colon\mathbb{N}\to\mathbb{R}$ be a function.` (a real function whose values at the natural numbers, `0` included, are its terms, `0` elsewhere: Mathlib `ℕ → ℝ`. `a_n` is its term at `n`, and `for all $n$` after a condition on terms ranges over the natural numbers. `$(a_n)$ converges to $l$`, `$(a_n)$ converges`, `diverges`; `increasing`, `strictly increasing`, `decreasing`, `monotone`, `bounded`, `positive`, `nonnegative`, `negative` are said of its terms. A sequence written by its terms, `$(a_n^2)$`, `the sequence $(a_n+b_n)$`, has these terms at the natural numbers and `0` elsewhere) |
| a sequence of objects of a noun | `Let $(U_n)$ be a sequence of dense open subsets of $X$.`, `Let $(A_n)$ be a sequence of countable sets of real numbers.`, `… sets of real numbers with $A_{n+1}\subseteq A_n$ for all $n$` (a function of the natural numbers, `0` included, whose terms `U_n` are each as the noun phrase says; its values elsewhere are not used) |
| `$\bigcap_n U_n$`, `$\bigcup_{n=1}^{\infty}A_n$`, `$\bigcap_{n=0}^{3}B_n$` | the elements in every (some) term of a sequence of sets, at the integers from the lower to the upper bound (`\bigcap_n`: at all natural numbers); a set of the terms' kind (Mathlib `Set.iInter`, `Set.iUnion`) |
| variables together | `Let $p,q$ be distinct primes.`, `there are distinct positive integers $a,b,c$ with …`, `pairwise coprime integers $a,b,c$`, `$r$ and $s$ are relatively prime`, `$x_1,\ldots,x_n$ are distinct` (`distinct`: any two are different; `relatively prime`, `coprime`: their greatest common divisor is 1, for exactly two of them; of more, `pairwise` says that any two are; for a sequence, any two terms with different indices) |
| families of vectors (field `structures`) | `Let $v_1,\ldots,v_n$ be linearly independent vectors in $V$.`, `Let $v,w\in V$ be linearly independent.`, `$u$ and $v$ are linearly dependent`, `Let $V$ and $W$ be vector spaces over a field $K$.` (one field for both) | `linearly independent` of several vectors, or of a sequence of them, is of the family: its terms are distinct and their set is linearly independent (as Mathlib `LinearIndependent` of a family); `linearly dependent`: not so. `vectors in $V$` are elements of the vector space `V` |
| a family that spans (field `structures`) | `$v_1,\ldots,v_n$ span $V$`, `$u$ and $w$ span $V$` (their set is a spanning set of `V`, Mathlib `Submodule.span`); `Let $V$ be a vector space of dimension $n$ over a field $K$.` (the field, then the space: a phrase with a formula before the nested indefinite) |
| points together (field `planegeometry`) | `Let $A$, $B$ and $C$ be non-collinear points.`, `Let $A$, $B$ and $C$ be points that are not collinear.`, `Let $D$, $E$ and $F$ be collinear points.` | `collinear` of exactly three points: they lie on one line (as `collinear with $B$ and $C$`); `non-collinear`, `noncollinear`, `not collinear`: not so |
| a triangle (field `geometry`) | `Let $ABC$ be a triangle.`, `Let $ABC$ be a triangle with $|AB|=|AC|$.` (the points `A`, `B`, `C`, not collinear); then `\angle A` is the angle of the triangle at `A` (`\angle BAC`): `\angle A+\angle B+\angle C=\pi` |
| several subjects | `$a$ and $b$ are positive`, `$a,b$ are odd integers`, `$x_1,\ldots,x_n$ are positive` (each of them is as the words say) |
| a statement as a hypothesis | `If $n$ is even, then …`, `For all integers $a,b$, if $a$ and $b$ are odd, then …`, `Let $k\ge1$ be an integer. If $k$ is an even integer, then …` (a statement about variables bound before, by the result or by the sentence's binders, as a hypothesis; `If $n$ is an even integer` about an `n` not bound yet binds it, as `For every even integer $n$`) |
| adjectives without a noun | `for every positive $a\in J$`, `for every nonzero $x$`, `a rational $s\in(0,1)$`, `for all sufficiently small positive $\varepsilon$` (a real number with the adjectives, in the domain if one is written; before an index name, `n`, `m`, `k`, `j`, `i`, `N`, `M`, `K`, without a domain, refused with a finding: say `every positive integer $n$`) |
| equivalent statements | `Then the following are equivalent: \begin{enumerate}\item $x^2=1$; \item $\lvert x\rvert=1$; \item $(x-1)(x+1)=0$. \end{enumerate}` (each item a formula, or a statement: `\item[(i)] $G$ is abelian;`; each is equivalent to the next). The list may also follow `the following statements are equivalent:` (`conditions`, `assertions`, `properties`); its items are then parts of the claim, not claims of their own |
| several facts | `We have $(\sqrt a)^2=a$, $(\sqrt b)^2=b$ and $\sqrt a\sqrt b=\sqrt{ab}$.` (each fact is a claim of the same sentence) |
| facts used by a step | `Since $G\le A$ and $G>0$, it follows that $H=G\cdot\frac{G}{A}\le G$.` (the facts after "Since" are premises of the step, so the step may use them) |
| a reason in words | `Moreover, $\sqrt a=\sqrt b$ if and only if $a=b$, since the square root is injective.` (the reason is prose, the claim before it is checked) |
| equality sets | `If $w>\frac12$, equality holds exactly on $S_w$, and if $w=\frac12$, it holds exactly on $S_{1/2}\cup([\frac12,1]\times\{\frac12\})$.`, `…, and equality holds exactly when $x=R_b(z)$.`, `For every $x\in(0,\infty)$, $f(x)\ge2$. Equality holds exactly when $x=1$.` (about the preceding inequality, for every point of its domain) |

In `If $φ$, then …` the free variables of `φ` range over the real numbers, except the
variables of the result (`Let $m\ge1$ be an integer. If $x\in[0,m]$, then …` binds `x`
only); the domains of binders may use the variables of the result as well. A symbol
that an earlier sentence introduces in words that Leanify does not read (`Let $q$
denote the charge of the surface.`, `Consider the idempotent $e$.`) is an object of the
article, not such a variable: the claim is refused (`q is not defined`), and so is `e^2`
with that `e`, which otherwise is the exponential. Words before a formula name it only
without a preposition: `the arithmetic mean $\frac{a+b}{2}$ is at least …` compares the
mean. With a preposition, the words and formulas are a notion of the vocabulary with its
arguments, the subject of the claim as a formula would be: `The kernel of $\varphi$ is a
normal subgroup of $G$.`, `The order of $G$ is $6$.`, `The distance between $P$ and $Q$ is
at least $0$.`. A notion may be the argument of another, after `the`: `the rank of the
transpose of $A$`, `the order of the center of $G$`, `$\det(A^{-1})$ is the reciprocal of the
determinant of $A$` (where no notion has all these words); and two notions may be added,
subtracted or multiplied: `the dimension of the kernel of $T$ plus the dimension of the image
of $T$` (`minus`, `times`). Words that are no notion (`the
probability of an exit at $-1$ is at least …`) are prose.

### Other wordings of the same forms

A sentence need not be worded as in the tables above. These wordings are replaced by the
form they stand for before the sentence is read, so they are read as that form:

| written | read as |
| --- | --- |
| `For any $x$, …`, `Any NOUN $x$ satisfies …` | `For every $x$, …`, `Every NOUN $x$ satisfies …`. Inside the condition of an `if`, `any` is left alone and the sentence is not read: `If $f(x)=0$ for any $x$, then …` may ask for one `x` only. Write `for every` or `for some` there |
| `Given $x>0$, we have …` | `For $x>0$, we have …` |
| `… so that $φ$` | `… such that $φ$` |
| `$φ$ iff $ψ$` | `$φ$ if and only if $ψ$` |
| `one has`, `one gets`, `one obtains`, `it holds that`, `we have that`, and `we get`, `we obtain`, `we find` before a formula | `we have` |
| `$φ$ holds`, `the inequality $φ$` (also `identity`, `equality`, `estimate`, `bound`, `formula`, `relation`) | `$φ$` |
| `If $φ$ then $ψ$`, `For all $x$ we have $φ$` | the same with the comma (`If $φ$, then $ψ$`) |
| `there is some $y>0$ with $y<x$` | `there is a $y>0$ such that $y<x$` |
| `Let $x$ and $y$ be two positive real numbers.`, `let $x$, $y$ be two elements of $G$` | `Let $x$ and $y$ be positive real numbers.` (`two`, `three`, `four` do not say that the objects differ; the word goes where it counts the letters before it) |
| `Let $X$ be a compact, connected metric space.` | `Let $X$ be a compact connected metric space.` (a comma between two adjectives after `a`, `every`, `any`, …) |
| `Let $G$ be a (possibly infinite) group.`, `a (not necessarily commutative) ring` | `Let $G$ be a group.`, `a ring`: a parenthetical that says what need not hold constrains nothing |
| `We denote by $Z$ the center of $G$.`, `We denote the center of $G$ by $Z$.`, `Let $Z$ denote the center of $G$.`, `The center of $G$ is denoted by $Z$.` | `Let $Z$ be the center of $G$.` (where the words name a value of the vocabulary; `NAME is denoted by $S$` for a named constant comes first) |
| `Let $\mathcal{S}$ denote the set of subgroups of $G$.`, `Let $S$ be the set of all open subsets of $X$.`, `… the class of …` | the set of the objects that the noun phrase describes: `H\in\mathcal{S}` exactly when `H` is a subgroup of `G` (the noun phrase may name variables of the result) |
| `Neither $a$ nor $b$ is negative.` | `$a$ is not negative and $b$ is not negative.` |
| `In particular, the metric space $X$ is a topological space.` | `$X$ is a metric space and $X$ is a topological space`: what `the NOUN` says of the symbol is a part of the claim |
| `Let $x$ be real.`, `for all real $x$` | `Let $x$ be a real number.`, `for all real numbers $x$` |
| `for every $1\neq g\in G$`, `Let $0<x\in\mathbb{R}$.` | an element of the set with the relation: `g\in G` and `1\neq g`, `x\in\mathbb{R}` and `0<x` |
| `Let $g$ be an arbitrary element of $G$.`, `a given group`, `a fixed integer` | `Let $g$ be an element of $G$.`: the words say how the object is chosen, not what it is |
| `a one-to-one map` | `an injective map` (not `one-to-one correspondence`, a bijection) |

In formulas, `\rightarrow` and `\longrightarrow` are `\to`, `\coloneq` and `\defeq` are
`\coloneqq`, `\backslash` and `\smallsetminus` are `\setminus`, `\thicksim` is `\sim`,
`\not\in` is `\notin` and `\not=` is `\neq`; the sizes `\bigg`, `\Bigg`, `\middle`, `\large`,
`\small`, the struts and the spaces `\mkern-2mu`, `\kern1pt` are skipped, as are the old font
switches `\rm`, `\sf`; `\smash{x}`, `\ensuremath{x}` and `\raisebox{…}{x}` are `x`, `\phantom{x}` is
nothing. `\mathsf`, `\mathfrak`, `\mathscr`, `\mathtt`, `\boldsymbol`, `\bm`, `\EuScript`,
`\mathpzc`, `\mathds`, `\mathbbm` and `\pmb` name a symbol as `\mathcal` and `\mathbb` do, and so do
the old switches `{\cal G}`, `\bf x`, `\Bbb R` (`\mathcal{G}`, `\mathbf{x}`, `\mathbb{R}`). `{n
\choose k}` is `\binom{n}{k}`. A relation with a note above it, `\stackrel{(a)}{\le}` or
`\overset{(1)}{=}`, is the relation (the note is a reason); `\overset{\text{def}}{=}` (`def`,
`\triangle` or `:` above `=`) is `\coloneqq`.

`A\subsetneq B` (`\subsetneqq`, `\varsubsetneq`) is `A\subseteq B` and `A\neq B`, and `A\supsetneq
B` the same the other way; `Let $A\subsetneq X$.` binds a subset of `X` other than `X`. `\subset`
alone stays ambiguous (see the finding it gets).

### Indefinites inside other noun phrases

An object that a noun phrase names with `a` inside `every`, `let` or `the` is one more
variable, bound as widely as the phrase around it: in a statement, such an indefinite is
universal. These sentences are read as the sentences on the right, with a letter for the
object that is not in use:

| written | read as |
| --- | --- |
| `Every subgroup of a cyclic group is cyclic.` | `For every cyclic group $X$, every subgroup of $X$ is cyclic.` |
| `Every continuous map from a compact metric space to a metric space is uniformly continuous.` | `For every compact metric space $X$ and every metric space $Y$, every continuous map $f\colon X\to Y$ is uniformly continuous.` |
| `The center of a group $G$ is a normal subgroup of $G$.` | `For every group $G$, the center of $G$ is a normal subgroup of $G$.` |
| `For every closed subset $F$ of a compact space, …` | `For every compact space $X$ and every closed subset $F$ of $X$, …` |
| `Let $H$ be a subgroup of a cyclic group.` | `Let $X$ be a cyclic group and let $H$ be a subgroup of $X$.` |
| `Let $f\colon X\to Y$ be a continuous bijection from a compact space to a Hausdorff space.` | `Let $X$ be a compact space, let $Y$ be a Hausdorff space and let $f\colon X\to Y$ be a continuous bijection.` |
| `Let $T\colon V\to V$ be a linear operator on a finite-dimensional vector space.` | `Let $V$ be a finite-dimensional vector space and let $T\colon V\to V$ be a linear operator.` |
| `Let $\varphi\colon G\to H$ be a group homomorphism.`, with new letters `G`, `H` (also in a later `let`: `Let $V$ be a vector space and let $T\colon V\to W$ be a linear map.`) | `Let $G$ be a group, let $H$ be a group and let $\varphi\colon G\to H$ be a group homomorphism.` (the noun of the map says what its domain and codomain are: groups, rings, vector spaces, topological or metric spaces, partially ordered sets) |
| `The intersection of two normal subgroups of $G$ is a normal subgroup of $G$.` (`union`, `product`; `The union of two bounded sets of real numbers is bounded.`, the noun before its complement in the singular; `The sum of two odd integers is even.`, `difference`; `The composition of two continuous functions is continuous.`, `$X\circ Y$`; the product of two functions, `$X\cdot Y$`) | `For every normal subgroup $X$ of $G$ and every normal subgroup $Y$ of $G$, $X\cap Y$ is a normal subgroup of $G$.` |
| `The continuous image of a compact space is compact.` | `For every compact space $X$, every topological space $Y$ and every continuous map $f\colon X\to Y$, the image of $f$ is compact.` |
| in a result, `A continuous image of a connected space is connected.` | the same, as `The continuous image of a connected space is connected.` |
| `The square of an odd integer is odd.`, `The cube of a negative real number is negative.` | `For every odd integer $X$, $X^2$ is odd.` |
| in a result, `A metric space is compact if and only if it is sequentially compact.` | `For every metric space $X$, $X$ is compact if and only if $X$ is sequentially compact.` |
| in a result, `A subset of $\mathbb{R}$ is compact if and only if it is closed and bounded.`, `Every subset of $\mathbb{R}$ is …` with `it` | `For every subset $X$ of $\mathbb{R}$, $X$ is compact if and only if $X$ is closed and bounded.` |
| in a result, `A finite abelian group is cyclic if its order is squarefree.`, `Then $n^2$ is even if $n$ is even.` | `If $n$ is even, then $n^2$ is even.`: a condition after the claim (not `only if`, `if and only if`, `, even if`) |
| in a result, `There is no largest prime.` (`greatest`; `smallest`, `least`) | `For every prime $X$ there is a prime $Y$ with $Y>X$.` |
| in a result, `The rank of a matrix equals the rank of its transpose.` | `For every matrix $X$, the rank of $X$ equals the rank of the transpose of $X$.` (`its` after the nested indefinite is its object's) |
| in a result, `Between any two real numbers there is a rational number.` (`any two distinct`) | `For all real numbers $X,Y$ with $X\neq Y$, there is a rational number $Z$ with $\min(X,Y)<Z<\max(X,Y)$.` (two numbers are distinct) |
| in a result, `A compact subset of a Hausdorff space is closed.`, `A finite integral domain is a field.`, `An integer is even or odd.` | `Every compact subset of a Hausdorff space is closed.` (an indefinite subject of a result is generic), then the indefinites inside it as above |
| `Let $G$ be a group of order $p^2$, where $p$ is a prime.` | `Let $p$ be a prime and let $G$ be a group of order $p^2$.` |
| `Let $p$ be a prime dividing $n$.` | `Let $p$ be a prime with $p\mid n$.` |
| `Let $T$ be a linear operator between normed spaces.` | `Let $X$ be a normed space, let $Y$ be a normed space and let $T\colon X\to Y$ be a linear operator.` |
| `For all vectors $x$ and $y$ in an inner product space, …` | `For every inner product space $X$ and every vector $x$ in $X$ and every vector $y$ in $X$, …` |
| `Every subgroup of index $2$ is normal.` | `For every group $X$ and every subgroup $Y$ of $X$ of index $2$ in $X$, $Y$ is normal.` |
| `Every subsequence of a convergent sequence of real numbers converges.`, `Every Cauchy sequence in a complete metric space converges.` | `For every convergent sequence of real numbers $X$ and every subsequence $Y$ of $X$, $Y$ converges.` (`of real numbers`, `of integers` stay with the noun) |
| `Every group of order $p$, where $p$ is a prime, is cyclic.` | `For every prime $p$, every group of order $p$ is cyclic.` |
| in a result, `A differentiable function whose derivative is zero everywhere is constant.`, `An integer whose square is even is even.` | `For every differentiable function $X$, if the derivative of $X$ is zero everywhere, then $X$ is constant.` (the clause ends before the last verb) |
| `There is no rational number whose square is $2$.` (`there is a`) | `There is no rational number $X$ such that the square of $X$ is $2$.` |
| in a result, `The order of every element of $G$ divides the order of $G$.` (`each`) | `For every element $X$ of $G$, the order of $X$ divides the order of $G$.` |
| `If $ab=0$ for $a,b\in R$, then $a=0$ or $b=0$.` | `For all $a,b\in R$, if $ab=0$, then $a=0$ or $b=0$.` |
| in a result, `A group in which every element has order at most $2$ is abelian.` | `For every group $X$, if every element of $X$ has order at most $2$, then $X$ is abelian.` (the clause ends before the last verb) |
| `Every graph with $n$ vertices and at least $n$ edges contains a cycle.` | `For every graph $X$ with $n$ vertices and at least $n$ edges, $X$ contains a cycle.` |
| `Let $G$ be a finite $p$-group.`, with a new letter `p` | `Let $p$ be a prime and let $G$ be a finite $p$-group.` (the letter of a `$p$-group` is a prime, not any number) |
| `Every continuous function $f\colon[a,b]\to\mathbb{R}$ attains its maximum and its minimum.`, `$f$ attains its maximum on $[a,b]$` | `For every continuous function $f\colon[a,b]\to\mathbb{R}$, there is $c\in[a,b]$ such that $f(x)\le f(c)$ for all $x\in[a,b]$, and there is …` (the domain is the signature's, or written after `on` or `in`) |
| `Every continuous function on $[a,b]$ is bounded.`, `Every monotone function $f\colon[a,b]\to\mathbb{R}$ is Riemann integrable.`, `Every continuous function on $[a,b]$ attains its maximum.`, in a result `A continuous function on a compact interval attains its maximum.` | `Every continuous function $f\colon[a,b]\to\mathbb{R}$ is …`; the maximum on the domain of the function (`For every compact interval $X$ and every continuous function $Y$ on $X$, there is $c\in X$ such that …`). An interval may be empty, and then nothing is attained on it |
| `In a principal ideal domain, every irreducible element is prime.` | `For every principal ideal domain $X$, every irreducible element of $X$ is prime.` |
| `The characteristic of $R$ is either $0$ or a prime.` | `The characteristic of $R$ is $0$ or the characteristic of $R$ is a prime.` |
| `The set of nilpotent elements of $R$ is an ideal of $R$.` | the set, bound as `Let $X$ be the set of nilpotent elements of $R$.` binds it, and `$X$ is an ideal of $R$` |
| `The number $\sqrt2$ is irrational.`, `The polynomial $x^2-2$ is …` | `$\sqrt2$ is irrational.`; `$x^2-2$ is a polynomial and $x^2-2$ is …` (what the noun says of a formula is a part of the claim; `number`, `real number` and `integer` say nothing more) |
| `Let $f\colon[a,b]\to\mathbb{R}$ be continuous on $[a,b]$ and differentiable on $(a,b)$ with $f(a)=f(b)$.` | the map, `Suppose that $f$ is continuous on $[a,b]$ and differentiable on $(a,b)$.` and `Suppose that $f(a)=f(b)$.` |

A noun whose meaning is in its complement (`prime ideal of $R$`, `normal subgroup of $G$`,
`element of $G$`) is read with its complement, written or implied: alone, it would say less
than the noun means, and the sentence is not read (`"ideal" is read with its complement`).
The complement is implied by the variable's domain (`a subgroup $H\le G$`, `an element
$g\in G$`) and, after `is`, by the complement the subject was introduced with: of an ideal `I`
of `R`, `$I$ is a prime ideal` and `$I$ is prime` say that `I` is a prime ideal of `R`; of a
subgroup `H` of `G`, `$H$ is a normal subgroup` that `H` is normal in `G`. `vector space` and
`module` without `over $K$` are over their scalars, some field (some ring). An adjective that
the vocabulary has only relative to a structure is relative to the noun's complement: `a
closed subspace of $X$` is a subspace of `X` closed in `X` (`dense`, `normal`, `prime`, …).
`orthogonal` (`pairwise`, `mutually`) of several vectors (`Let $x$ and $y$ be orthogonal
vectors in $H$`) says that any two of them are orthogonal; of matrices, each is orthogonal.

### Notions that the article defines in words that are not read

A definition whose condition Leanify does not read still introduces its notion. A sentence
of a definition, or of the text, that is not read and names a notion makes it a notion of
the article, as if the preamble had declared it (below), and the statements about it are
read. What it names is found from the sentence itself: one of the forms of a definition
above; or a verb that names with a subject before it and a name after it (`… SUBJECT is
called [a] NAME …`, the subject after the last comma: `[a|the|such a|any] WORDS [$x$] [of
…]`), once for each such verb of the sentence; or else an emphasized name (`\emph`,
`\textit`, `\textbf`, `\term`, `{\em …}`) after `is`, `is called` or `a`/`an`. In the
running text, an emphasized phrase counts only with a verb that names, or as `… is
\emph{NAME} if …` and `A \emph{NAME} is …`.

| Write | Reading |
| --- | --- |
| `A metric space is \emph{homogeneous} if its isometry group acts transitively on points.`, `A subgroup $H$ of a group $G$ is called \textbf{malnormal} if …` | an adjective of the noun of the subject (`a homogeneous metric space`, `$X$ is homogeneous`, `a malnormal subgroup of $G$`), a property of which nothing is known |
| `A group $G$ is called a \emph{Tarski monster} if …`, `Such a group is called a \emph{monster}.`, `A \emph{code} is a subset of …` | after `a`/`an`: a noun, of the objects of the noun of the subject (a Tarski monster is a group with a property of which nothing is known) |
| `A \emph{Kripke frame} is an ordered pair $(W,R)$ where …` | with no noun of the vocabulary in the sentence: a kind of object of its own (`\mathrm{KripkeFrame}`) |
| `A loop $L$ is said to be \emph{Moufang} if …, and a Moufang loop $L$ is called a \emph{code loop} if …`, `… then the cone is said to be \emph{simplicial}.`, `Finite-dimensional algebras $A$ with this property are called \emph{weakly Gorenstein} algebras.` | a subject whose noun no field knows: its last word is a kind of object of its own (`loop`, `cone`, `algebra`), the words before it an adjective of it (`finite-dimensional algebra`), and the name an adjective of it or a noun of its objects (`Moufang loop`, `code loop`, `simplicial cone`, `weakly Gorenstein algebra`). Not for words that name what a sentence speaks of (`theorem`, `case`, `property`, …), nor for a noun of a field that takes a complement (`subset of $A$`) |

The check lists them as *defined here in sentences that are not read, and taken as given*
(`takenAsGiven` in its JSON). A definition that is read defines its notion with its
meaning: the condition after `if` may be a formula or any statement that is read as a
claim (`We call a metric space $X$ \emph{homogeneous} if for all $x,y\in X$ there is an
isometry $f\colon X\to X$ with $f(x)=y$.`). As for a declared notion, what is proved about
a notion that is taken as given is proved for whatever it means: in Lean it is an `opaque`
constant.

### Notions that the article does not define

An article on graphs does not define *graph*. If the vocabulary has no field for its
subject, the article can still be read: it names the nouns it uses without a
definition in its preamble, and Leanify treats each as a kind of object of which nothing
is known. Nothing is printed for this, and the text stays as it is.

```latex
\usepackage[notions={graph, finite graph, connected graph, vertex (vertices)},
            quantities={degree, distance}]{leanify}
```

| Write | Reading |
| --- | --- |
| `notions={graph}` | *graph* is a noun with a type of its own (`\mathrm{Graph}` in the readings): `Let $G$ be a graph.`, `for all graphs $G$ and $H$`. The plural is formed by rule (`graphs`, `families`, `classes`); an irregular one is given in parentheses, `vertex (vertices)` |
| `notions={finite graph}` | an entry that ends with a noun is an adjective of that noun: a property of graphs of which nothing is known (`\operatorname{finite}(G)`). It also applies to a noun of the vocabulary (`admissible integer`) |
| `quantities={degree}` | a word that names a real number, for the names of quantities below |
| `Let $\chi(G)$ denote the chromatic number of a graph $G$.`, `We write $\Delta(G)$ for the maximum degree of a graph $G$.`, `We denote by $d(G,H)$ the edit distance of graphs $G$ and $H$.`, `Let $L(G)$ denote the line graph of a graph $G$.`, `Let $\kappa$ denote the Catalan constant.` | a symbol for a quantity that the article does not define (in the running text, and only if the sentence has no other reading). Its arguments are the variables of the noun phrases. Its name says the kind of its values: a `number`, `constant`, `value` or `quantity` is a real number, a name that ends with a word of `quantities` is one too, and a name that ends with a noun (`line graph`) is an object of that noun. No property of the values is assumed. A name that does not say the kind (`the independence ratio`) is not read |
| `\begin{lemma}[{\cite[Theorem~5.2.4]{diestel}}]`, `\begin{theorem}[Brooks, \cite{brooks}]` | a result whose heading cites its source and that the article does not prove is *quoted from the literature*: the article assumes it. A result with a proof in the article is proved there, whatever its heading |

What this gives, and what it does not:

* A statement about graphs is read like any other, and its reading fixes its
  quantifiers and hypotheses. What *graph* means is not fixed: the reports list the
  notions as **not defined here**.
* What is proved about them is proved for whatever they mean. In Lean each is an
  `opaque` constant (`Foo.Notion.Graph`, `Foo.Notion.chi`), of which the kernel knows the
  type and nothing else, so a step that uses only what it cites is checked, and a step
  that needs what a graph is cannot be proved.
* Such a step needs a fact from the literature. Quote it as a result with its source in
  the heading. The certificate then holds *given the quoted results*: each is an axiom
  `Foo.Quoted.claimK`, the axioms of the certificate are these and the standard three,
  and every verified claim records which quoted results it rests on.
* A kind of object is assumed to have an element, as every type of the core language
  has. A sentence that says only that such an object exists (`There is a graph $G$.`,
  `For every graph $G$ there is a vertex $v$.`) would be verified by this assumption, so it is not read as a claim, and the finding
  says so. With a condition (`There is a graph $G$ such that …`) it is a claim like any
  other, and a proof of it may use the assumed element (`Foo.Notion.Graph.2`). So do not
  declare a noun whose existence is what the article shows (*counterexample*,
  *solution*).
* That the hypotheses of a statement about undefined notions can hold together is
  not shown, and the result is marked *argued*.
* A quoted result is not checked. A false one makes everything provable. The article
  is correct *if* the results it quotes are, which is what a referee assumes as well.

`leanify check` ends with the nouns that stopped the reading (`nouns without a reading:
polynomial, …`): the candidates for the list. `--notions "graph, finite graph"` tries
entries without editing the article.

### Standard notions

A claim `$X$ is ADJ, ADJ [on $A$] and ADJ` (also `The function|map|set|number
$X$ is …`) uses the standard notions below, with their mathlib meaning
(`Leanify.Prelude` in `Leanify/Denote.lean`). A function has them on the
domain its definition states, or on `A`, which must lie in that domain.

| Of | Adjectives | Meaning |
| --- | --- | --- |
| a number | positive, negative, nonnegative, nonpositive | `0 < x`, `x < 0`, `0 ≤ x`, `x ≤ 0` |
| a real function | continuous, differentiable, continuously differentiable | `ContinuousOn`, `DifferentiableOn ℝ`, `ContDiffOn ℝ 1` |
| | convex, concave, strictly convex, strictly concave | `ConvexOn ℝ`, `ConcaveOn ℝ`, `StrictConvexOn ℝ`, `StrictConcaveOn ℝ` |
| | strictly increasing, strictly decreasing, nondecreasing, nonincreasing | `StrictMonoOn`, `StrictAntiOn`, `MonotoneOn`, `AntitoneOn` |
| | bounded, nonnegative, positive, injective | bounded image, `0 ≤ f x`, `0 < f x` on the domain, `Set.InjOn` |
| | lower semicontinuous, upper semicontinuous, Lipschitz (continuous) | `LowerSemicontinuousOn`, `UpperSemicontinuousOn`, `∃ K, LipschitzOnWith K` |
| a set of the plane | compact, convex, centrally symmetric, closed, open, bounded, connected | `IsCompact`, `Convex ℝ`, `(a,b) ↦ (-a,-b)`, `IsClosed`, `IsOpen`, `Bornology.IsBounded`, `IsConnected` |
| a quantity of NOUNS on the unit square (on its class, or on `A`) | convex, concave | `ConvexOn ℝ`, `ConcaveOn ℝ`, with the pointwise mixture of functions |
| | lower semicontinuous, upper semicontinuous, continuous, each *with respect to uniform convergence* | semicontinuity and continuity for the topology of uniform convergence on `[0,1]²` |
| a class of such NOUNS | convex, compact with respect to uniform convergence, closed with respect to uniform convergence | `Convex ℝ`, `IsCompact`, `IsClosed` for uniform convergence |

`Increasing` and `decreasing` alone are not read, because articles use them both
for the strict and for the weak property: write *strictly increasing* or
*nondecreasing*. A hyphen may join the words (`non-decreasing`, `lower
semi-continuous`). `Continuous` for a quantity of NOUNS needs its topology:
*continuous with respect to uniform convergence*.

The readings are fixed and documented next to each construction in
`Leanify/Grammar.lean` (parsing) and `Leanify/Doc.lean` (meaning). Run
`lake exe leanify check article.tex --claims` to see the formal reading of
every claim while you write.

## Proofs

Inside `\begin{proof}`, a sentence may use the earlier sentences of the same
proof and the results cited so far in it. When every sentence of a proof
compiles, the result it proves gets those sentences and citations as its
premises, and the result is *derived in the text*. Sentences that only
organize the argument ("Nonnegativity away from that set is proved rectangle by
rectangle.") are prose and assert nothing. A proof with such a sentence is not
read completely: its result can still be checked, by any Lean proof, but it is
not derived from the printed proof. The check counts the complete proofs
(`complete proofs: 2 of 3`) and names each proof that is not complete, so an
article without warnings is not taken for an article whose proofs are all read.

A section whose title announces a proof, `\subsection{Proof of
Theorem~\ref{thm:main}}`, is a proof of that result up to the next sectioning
command.

### Hypotheses: assumptions, cases, contradictions

A proof makes hypotheses, and every step after one is a claim under it: after
`Assume that $x>1$.`, the step `Then $x^2>x$.` is read as `∀ x, 1 < x → x < x²`.
A hypothesis lasts until its proof ends (inside an item of a list: until the
item ends), until a contradiction refutes it, or until another case takes its
place. `tests/Arguments/article.tex` uses each form.

| Sentence | Reading |
| --- | --- |
| `Assume that $x>1$.`, `Suppose $0<x$ and $x<y$.`, `We assume that $n$ is even.`, `Let us assume …` | hypotheses of the following sentences of the result or proof (inside an item of a list: of the item). In the statement of a result they are hypotheses of the result, and its proof starts with them |
| `Assume $c>0$.`, `Suppose $x\in A$.` about a variable that is not bound yet | the variable, as `Let $c>0$.` |
| `Let $G$ and $H$ be groups, with $H$ abelian.`, `…, with $n\ge3$.` | the variables, then the hypothesis `Suppose that $H$ is abelian.` |
| `Assume that $a>0$ and let $n$ be an integer such that $n>a$.` | the hypothesis, then the variable (each part read as a sentence of its own, and split again where it needs to be) |
| `For a group $G$, let $H$ be a subgroup of $G$.`, `Given $x\in A$, let …` (in a result or a proof) | `Let $G$ be a group.`, then the rest |
| `Let $Q\in\mathbb{R}^{n\times m}$ have orthonormal columns.` (`satisfy`, `contain`, `admit`, `lie`, `belong`) | the variable, then `Suppose that $Q$ has orthonormal columns.` |
| `Let $G$, $n$ and $H$ be as in Theorem~\ref{t}.` | the variables of the result `t`, with its hypotheses: the letters name all of its variables, and they are the first of this result |
| `Fix $a>0$, $b\in A$ and $c$.` | each of them fixed, as `Fix $a>0$.` |
| a second `Assume that $y>x$.` | one more hypothesis: assumptions add up. Each can end on its own |
| `Assume further that $y>0$.` (`moreover`, `furthermore`, `in addition`, `also`) | one more hypothesis, which belongs to the assumption before it: the two end together |
| `Assume now that $x<0$.` (`next`, `instead`, `conversely`, `otherwise`, `secondly`, `finally`, `on the other hand`) | another case: the hypothesis takes the place of the latest assumption (with what `further` added to it). `Assume first that …` is an assumption like any other, which the next case replaces |
| `Without loss of generality, assume that $y\le x$.`, `We may assume that …`, `We can assume …` | an assumption like any other. That it costs nothing is not a sentence of the proof: the result has to follow, in Lean, from the steps made under it |
| `\item \emph{$x\ge0$.} …`, `\item \emph{Case 2: $x<0$ and $y>0$.} …`, `\item \textbf{Case (b): $n$ is even.} …` | the heading of a case: a hypothesis of the sentences of its item of an `enumerate`, `itemize` or `description`. It ends with the item, so the sentence after the list (`In both cases, …`) is made without it |
| `Suppose, for contradiction, that $x\ge1$.` (`for a contradiction`, `by contradiction`, `to the contrary`) | a hypothesis made to be refuted |
| `This is a contradiction.`, `We obtain a contradiction.`, `This is absurd.`, `This contradicts Lemma~\ref{l}.`, `Then $0\le x^2<0$, a contradiction.` (`, which is impossible.`) | the false statement under the hypotheses made (`∀ x, x² < 1 → 1 ≤ x → ⊥`), after the claims of the sentence. It ends the latest hypothesis made for contradiction, with the hypotheses made after it; if none was, the latest assumption. The assumptions before it remain |
| `We distinguish two cases:`, `There are three cases.`, `We argue by contradiction.`, `The proof is by contradiction.` | a sentence that says how the proof is organized: it asserts nothing, and does not leave the proof incomplete |
| `We argue by induction on $n$.` | organizes the proof, and names the variable of the induction: a variable of the result (`Let $n$ be a positive integer.`, `For every positive integer $n$, …`) |
| `\item \emph{Base case: $n=1$.} …`, `\item \emph{Induction step: $n\ge2$.} …`, `\item \emph{Induction step.} …` | the cases of an induction: cases like any other; the heading `Induction step.` makes no hypothesis |
| `the statement holds for $n$` (`the claim`, `the assertion`, `the formula`, …; `is true for`), as a hypothesis (`Assume that the statement holds for $n$.`) or as a claim (`Hence the statement holds for $n+1$.`) | the statement of the result that is being proved, about the given value of the variable of the induction: for `$n-1$`, `(n - 1 ∈ ℤ ∧ 0 < n - 1) → …`, with the domain of the variable and the hypotheses of the result about it |
| `the statement holds for all $m<n$` (`every`, `each`), in a strong induction | the statement about every such `m`: `∀ m, m < n → (m ∈ ℤ ∧ 0 < m → …)` |
| `the statement holds for all smaller values` (`for every smaller integer`, `for all smaller values of $n$`, `for all positive integers less than $n$`) | the same, in words: the statement about every value of the variable of the induction below it |
| `Let $x$ and $y$ be positive real numbers.`, `Let $a$, $b$ and $c$ be integers.`, `Suppose that $a$ and $b$ are positive real numbers.`, `Suppose that $n$ is a positive integer.` | several variables of one kind; an assumption about variables that are not bound yet introduces them, as `Let` does |

**The rules can be applied to a text that meant something else.** `Assume that
$x\ge0$. … Assume that $x<0$. …`, meant as two cases, is read as one assumption
added to the other, and every step after the second is then made under `x ≥ 0`
and `x < 0`: it is true whatever it says, and would pass unchecked. Leanify
guards against this, whatever the cause. For every set of hypotheses under which
a claim is made it states that they can hold together (`satisfiableK`: here
`∃ x, 0 ≤ x ∧ x < 0`, which nobody can prove), and a result with a claim under
hypotheses that are not shown to hold together is not marked *derived*
([What a verified claim does not say](reference.md#what-a-verified-claim-does-not-say)).
The steps of a proof by contradiction are exempt: their hypotheses are refuted,
and that is their point. Write the second case as `Assume now that $x<0$.`, or
both as the items of a list.

**A sentence that is not read may have said something.** A hypothesis lasts
until a sentence that Leanify reads ends it. If the sentence that ends a case or
states the contradiction is not read, the steps after it are still read under the
hypothesis, and if a sentence that makes a hypothesis is not read, the claims
after it lack it. `leanify check --claims` names every claim that follows an
unread sentence of its result or proof, and the reports count such a claim apart
when it is verified
([What a verified claim does not say](reference.md#what-a-verified-claim-does-not-say)).
The remedy is to write the sentence in a form that is read: `This is a
contradiction.`, `Assume now that $x<0$.`.

**Induction.** A proof by induction names its variable and states its hypothesis
as a sentence:

```latex
\begin{lemma}\label{lem:square}
Let $n$ be a positive integer.
Then $n^2\ge n$.
\end{lemma}
\begin{proof}
We argue by induction on $n$.
\begin{itemize}
\item \emph{Base case: $n=1$.} We have $n^2=1$.
\item \emph{Induction step.} Assume that the statement holds for $n$.
Then $(n+1)^2=n^2+2n+1\ge n+2n+1$.
By the induction hypothesis, $(n+1)^2\ge n+1$.
Hence the statement holds for $n+1$.
\end{itemize}
\end{proof}
```

The base case is read as `∀ n, … → n = 1 → n² = 1`, the last sentence as
`∀ n, … → n ≤ n² → (n + 1 ∈ ℤ ∧ 0 < n + 1 → n + 1 ≤ (n + 1)²)`: every positive
integer `n` for which the statement holds gives it for `n+1`. The lemma rests on
these steps. That it follows from them is the induction principle, which is a
Lean argument and not a step of the text; the standard tactic does not apply it,
so a result that it cannot prove otherwise is *argued*. The statement for another
value is not read when no sentence names the variable of the induction (the finding
says so; `for all smaller values of $n$` names it itself). When another variable of
the result depends on the variable of the induction, write the hypothesis out
(`Assume that $(n-1)^2\ge n-1$.`).

**A definition under a hypothesis.** A definition made among the variables of a
result or proof is a function of the variables it uses: after `Let $x$ be a real
number.`, `Set $y\coloneqq\frac1x$.` defines `y(x)`, and each use of `y` is `y(x)`.
Its domain is what the text says about those variables:

* the domains of the variables (`Let $x>0$.`);
* the hypotheses in force that speak only about them: after `Assume that
  $x\ne0$.`, the definition is well defined if `∀ x, x ≠ 0 → x ≠ 0`, and each use
  of `y` asks that `x ≠ 0` (`leanify check --defined` prints both);
* what a hypothesis that also speaks about other variables says about them: after
  `Let $x$ and $z$ be real numbers. Assume that $xz\ne0$.`, `Set
  $w\coloneqq\frac1x$.` defines `w(x)` for the `x` for which there is such a `z`.
  It is well defined if `∀ x, (∃ z, x z ≠ 0) → x ≠ 0`, and a use of `w` asks that
  there is a `z` with `x z ≠ 0`, which the hypothesis gives. The other variable
  comes with its own domain and with the hypotheses about it alone;
* a variable whose domain uses the variables before it brings them along: after
  `Let $n\ge1$ and $x\in[0,n]$.`, `Set $r\coloneqq\frac1{x+1}$.` defines `r(n,x)`
  for `x ∈ [0,n]`, although its formula does not mention `n`.

### Reasons, restatements and objects chosen in a proof

A proof says why a step holds and which objects it works with, often in words. A
reason in words asserts nothing: the claim it supports is checked, and the step may
use what the sentence cites, nothing else. A restatement replaces an informal sentence
by one that Leanify reads. `tests/Steps/article.tex` uses these forms with examples from
elementary analysis, `tests/Operators/article.tex` with operators on `L^2`.

| Sentence | Reading |
| --- | --- |
| `Every square of a real number is nonnegative, that is, for every real number $x$, we have $x^2\ge0$.` | `INFORMAL, that is, FORMAL`: only the formal restatement after the first `, that is,` is read; the words before it may state the same informally, with formulas. Also when the words before it would be read on their own and their reading fails |
| `Since the hypothesis applies to $\varepsilon$, which is positive, $a\le\varepsilon$.`, `Since $c$ is positive, $b^2<b$.` | a reason in words before the claim (at least two words, with formulas that state nothing); a relative clause after a comma (`, whose maximal correlation is $1$,`, `, which is positive,`) belongs to it |
| `Hence $(x-y)^2\ge0$ by Section~\ref{sec:squares}, and since the square is the expansion above, $x^2+y^2-2xy\ge0$.` | a second claim of the sentence with its own reason in words. A section (`Section~\ref{s}`, also an item `Section~\ref{s}~(d)`) is cited as a reason: it names no result, and the step may use no claim through it |
| `The number $c$ is the distance from $b$ to $1$, so $b^2=b(1-c)$.`, `…, so that, by Lemma~\ref{l}, …` | a description in words before `, so`: a reason; the clauses after `so` are claims |
| `With the Markov operator $\frac{r+g}2\id+\frac{r-g}2J$ of $C_{r,g}$, this gives DISPLAY` | the words after `With` are a reason, the display is the claim (also `this yields`) |
| `Let $c>0$ be such that $b+c=1$.`, `Let $n$ be such that $T$ is a function of the first $n$ observations.` | a variable of the rest of the proof, and the condition it is chosen with: a hypothesis of the steps after it, which has to be shown to hold together with the others (`satisfiableK`) |
| `By the Archimedean property of the real numbers, we can find a positive integer $n$ such that $n>\frac1\varepsilon$.`, `…, we may choose $c>0$ such that …`, `Taking the integer part of $x$, we obtain an integer $k$ such that $k\le x<k+1$.` | as `Let`: the object of the noun phrase, and the condition it is chosen with. The words before it are a description and assert nothing; the step after it is checked under the condition |
| `For Kendall's tau, we use the kernel $F=F_{\{1\}}+F_{\{2\}}+F_{\{1,2\}}$ from the proof of Theorem~\ref{t}.` | the definitions of another proof, available in this one; `$Q_{r^2}$ from Lemma~\ref{l} has $R=r$ and $D=0$` states the formulas about an object a result defines |
| `Here $A_a$ is the ordinal sum of Section~\ref{sec:prelim}.` | a reminder of a definition the article made: it organizes the proof and asserts nothing |
| `\emph{Expanding the square.}` at the start of a paragraph | the heading of a paragraph of the proof: it organizes the proof and asserts nothing |
| `Letting $\varepsilon\to0$ gives the claim.` (`the assertion`) | the end of an argument by a limit: it organizes the proof. The result has to follow, in Lean, from the steps before it |
| `We have $x^3=x$ for each of the three numbers $x\in\{-1,0,1\}$.` | `for each of the WORDS $x\in S$`: the words describe the members of `S`, and the claim is for every `x ∈ S` |
| `$\varphi,\qquad\text{hence}\qquad\psi$` in a display (`so`, `thus`, `and`) | both formulas are claims |
| `$a$ and $b$ are nonincreasing on $(0,1)$`, `the map $\theta\mapsto\Psi(C_\theta)$ is continuous on $[0,1]$` | functions of one variable that are monotone, or continuous, on a domain |
| `$T$ is a function of the first $n$ observations` (field `unitsquare`) | a statistic that depends only on the observations `(U_i,V_i)` with `i < n`, for a natural number `n` |
| `$T_C$ fixes the constants and maps $L^2_0$ into itself with norm at most $1$`, `$T$ is $r$ times the identity on $A$` (field `hilbert`) | the phrases of an operator: `T` maps every constant function to itself (up to a null set); maps the functions of `L^2_0` into `L^2_0`, with `\lVert T|_{L^2_0}\rVert\le1`; and `\lVert Tg-rg\rVert=0` for the `g` of `A` |
| `\lVert T_C^{k+1}f\rVert\le\lVert T_C^kf\rVert` (field `hilbert`) | the powers of an operator, for a natural number `k` (`T^0` is the identity) |
| `for every Borel measurable function $g:[0,1]^2\to[0,1]$` (field `unitsquare`) | a map of the square to `[0,1]`, measurable as a function of the pair; `\int g(u,v)\,\mathrm{d}C(u,v)` is its integral against the copula `C` |

## Checking while writing

```sh
lake exe leanify check article.tex            # undefined symbols, failed sentences, unread statements
lake exe leanify check article.tex --claims   # and the reading of every claim
lake exe leanify check article.tex --prose    # and the prose inside proofs
```

Add `--vocab unitsquare` for articles about probability on the unit square
([Vocabularies and models](vocabularies.md)). A sentence of a theorem, lemma or
corollary that the grammar does not read is a warning: that part of the
statement would not be checked.

An article in several files is checked as a whole: the check reads the `.tex`
files it inputs (`\input{sections/intro}`, `\include{…}`, `\subfile{…}`) and
its own packages (`\usepackage{mymacros}` with `mymacros.sty` next to the
article) where they are input, and reports each finding at its own file and
line. A certificate pins one file: `lake exe leanify flatten article.tex
flat.tex` writes the article with its inputs as one file.

For the sentences without a reading, `scripts/leanify_suggest.py` asks a command
of yours (a model, usually) for the sentence in one of the forms above, and
keeps a suggestion only if the check then reads it
([`leanify_suggest.py`](reference.md#leanify_suggestpy)). The grammar still
fixes what the rewritten sentence means; you decide whether it still says what
you meant.

A sentence that is read but cannot be given a meaning says why and how to write
it: `a variable without a noun or a domain: say what it ranges over (every
integer $n$, every $x\in A$)` for `Every $M_r$ is positive.`, `Q(…) is a product
or a name that states what it depends on` for `$Q(x)$` with `Q` a number, `the left
side of a definition is a symbol or a function of variables` for `$A_{ij}=…$`
without a binder, or that a norm, a set or a subscript is not one Leanify knows.

The check takes about a second and certifies nothing. `lake build` of the
certifying module checks everything in the kernel. `editors/vscode/tasks.json`
shows both as problems in the `.tex` file. With `\usepackage{leanify}`, an
article compiled with shell escape is checked on every compile, and the
findings are LaTeX warnings at their lines
([`leanify.sty`](reference.md#the-pdf-leanifysty)).
