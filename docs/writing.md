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
| `(f\circ g)(x)` | `f(g(x))`, with `g(x)` in the domain of `f` |
| `A\subseteq B`, `A\supseteq B` | every real number in `A` is in `B` (and the reverse), for intervals, sets `\{x\in A : …\}` and sets the article defines |
| `\sup_{x\in A} e`, `\sup\{e : x\in A\}`, `\sup S` (and `\inf`) | the least upper (greatest lower) bound: defined only when it exists, so a claim about an unbounded or empty set is not meaningful |
| `\sum_{j=1}^{4} e`, `\prod_{k=0}^{2} e` | with numeral bounds: the terms written out |
| `\sum_{j=a}^{b} e`, `\prod_{j=a}^{b} e` | over the integers from `a` to `b`, which must be integers (`b<a`: the empty sum `0`, product `1`) |
| `x_1+\cdots+x_n`, `\frac1{1}+\dots+\frac1{N}`, `x_0\cdot\cdots\cdot x_{N-1}` | the sum (product) over the integers `i` from the index of the first term to that of the last, of the term both are instances of; the terms may differ in one place only, the index (`1+2+\cdots+n` is `1+\sum_{i=2}^{n} i`) |
| `a_1<\cdots<a_m`, `2\le n_1<\dots<n_k` | each term is in the relation to the next, for every integer index from the first to the last but one (and the rest of the chain as written) |
| `\sum_{k=a}^{\infty} e` | the limit of the partial sums, defined only when it exists (so conditionally convergent series such as `\sum_{k=1}^{\infty}\frac{(-1)^{k+1}}{k}` are read) |
| `\lim_{x\to a} e`, `\lim_{x\to\infty} e` | the limit within the points where `e` is defined (`x\ne a`), defined only when it exists and the points accumulate at `a` |
| `\limsup_{n\to\infty} a_n`, `\liminf_{x\to\infty} f(x)` | the number `L` such that for every `ε>0` the values exceed `L-ε` beyond every bound and eventually stay below `L+ε` (`\liminf`: the reverse); defined only when it is finite. An index runs through the natural numbers |
| `$a_n\to L$ as $n\to\infty$`, `$f(x)\sim g(x)$ as $x\to\infty$`, `$f(x)=o(g(x))$ as $x\to c$` | `\lim a_n=L`, `\lim\frac{f}{g}=1`, `\lim\frac{f}{g}=0`, as limits are read |
| `\lim_{x\to a} e=\infty`, `\lim_{n\to\infty} a_n=-\infty`, `$a_n\to\infty$ as $n\to\infty$` | the points where `e` is defined accumulate at `a` (are unbounded), and for every `M` there is `δ>0` such that `e>M` (`e<M`) at every such point with `0<|x-a|<δ` (there is `N` such that … at every such point `x\ge N`); an index runs through the natural numbers |
| `\lim_{n\to\infty} a_n` | for an index `n`, `m`, `k`, `j`, `i` (or `N`, `M`, `K`): the limit of the sequence through the natural numbers |
| `(-1)^k`, `2^{n+1}` | an exponent built from indices is an integer power, for any base |
| `n!`, `\binom{n}{k}` | for natural numbers `n`, `k` |
| `\exp(x)`, `\exp x`, `e^{x}` | the exponential function (`e` unless the article names something `e`) |
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
| `\int_a^b e\,dx`, `\int_1^2\frac1x\,dx`, `\int_0^x t^2\,dt` | the oriented integral of a function of a real variable. It is meaningful when `e` is defined between `a` and `b` and integrable there (so `\int_1^2\frac1x\,dx` is, and `\int_{-1}^1\frac1x\,dx` is not). With the field `unitsquare`, `\int_0^1` is the integral over the type `[0,1]` |
| `\int_0^1\int_0^1 e\,ds\,dt` | iterated integrals: the innermost integral takes the first differential |
| `\cosh x`, `\sin^2 x`, `\arctan x` | a named function (LaTeX's operator names) applies to what follows it, with or without parentheses. What the name means is said by the core (`\exp`, `\log`, `\sin`, `\cos`, `\tan`) or by a field (`\cosh` in `hyperbolic`, `\arcsin` with its domain `[-1,1]` in `trigonometry`); a name without a meaning is reported, with the field that reads it |
| `\mathbb{N}`, `\mathbb{N}_0`, `\mathbb{Z}` | the natural numbers (with 0, as in mathlib; write `n\ge1` for the positive ones) and the integers, as real numbers |
| `\lfloor x\rfloor`, `\lceil x\rceil` | the largest integer at most `x`, the smallest at least `x` |
| `x^{-1}`, `x^{-2}` | `\frac1x`, `\frac1{x^2}`: defined for `x\ne0`, of either sign |
| `$$…$$` | a display, like `\[…\]` |
| `:=`, `\vcentcolon=`, `\colonequals`, `\triangleq`, `\mathrel{:=}` | the defining sign, as `\coloneqq` (so a macro `\defeq` of the article for one of them is read too) |
| `\colon`, `\leqslant`, `\geqslant`, `\lvert`/`\rvert`, `\lbrace`/`\rbrace` | `:`, `\le`, `\ge`, a vertical bar, `\{`/`\}` |
| `a\mid b`, `a\nmid b` | `a` and `b` are integers and `b=ak` for an integer `k` (and its negation, for integers); the first `\mid` of a set `\{x\in A\mid φ\}` separates the condition, and a `\mid` after it is divisibility |
| `a\equiv b\pmod m`, `a\equiv b\ (\bmod m)`, `(\operatorname{mod} m)` | `a` and `b` are integers and `m\mid a-b` |
| `\{1\le n\le N : φ\}`, `\{x>0 : φ\}` | the variable bounded by the inequalities, with `φ`: an index (`n`, `m`, `k`, `j`, `i`, `N`, `M`, `K`) among the integers, any other variable among the real numbers |
| `\gcd(a,b)` | for integers `a`, `b`: the natural number `d` that divides both and that every common divisor divides (so `\gcd(0,0)=0`) |
| `\mathbb{Q}` | the rational numbers, as real numbers |
| `\mathbb{C}`, `complex number`, `\mathrm{i}` (`\mathrm i`), `z+w`, `zw`, `z/w`, `z^n`, `\lvert z\rvert`, `\overline{z}`, `\bar z`, `\operatorname{Re}(z)`, `\Re z`, `\Im z`, `e^{z}`, `\exp(z)`, `\sum_{k=a}^{b}` of complex terms | with the field `complex` (`\usepackage[vocab={complex}]{leanify}`): the complex numbers (Mathlib `ℂ`). Notation means what the type of its operands says, as in Python: with a complex operand, `+` is complex addition, and a real operand is a complex number; `z/w` is defined for `w\ne0`, `z^n` for a natural number `n` (`z^{-n}` is `1/z^n`), `\lvert z\rvert` is the modulus. `\mathbb{C}` has no order, so `z\le w` is refused with a finding. A bare `i` is a variable, not the imaginary unit. `docs/vocabularies.md` explains how a field gives notation a meaning on its own types |
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
| `We write $A\subset B$ if $A\subseteq B$.` | one relation symbol for another: every later `\subset` is `\subseteq`, whatever stands on either side (Leanify refuses `\subset` without such a sentence, since it also means strict inclusion) |
| `We write $\mathrm{Poi}(\lambda)$ for the Poisson distribution with mean $\lambda$.` | a symbol for a notion of the vocabulary, with its arguments |
| `We write $\mathcal P$ for the set of probability distributions on $\mathbb{N}_0$.` | a symbol for the class of a vocabulary noun |
| `By a distribution we mean a probability distribution on $\mathbb{N}_0$.` | a noun of the article (`Let $\nu$ be a distribution.`) |
| `Throughout, increasing means non-decreasing.`, `In this paper, …` | the words stand for the others in the following sentences (`strictly increasing` is unchanged) |
| `Throughout, $p$ and $q$ denote integers.`, `In this paper, the letters $s,t$ always denote integers.`, `Here and below, $d$ is an integer.` | from here on, each of the letters is an integer wherever it is bound: `For every $p\ge2$`, `If $q>2$`, `Let $p\in[1,3]$`, `\{1\le p\le5 : φ\}`, `\max_{1\le p\le3}`, `\forall p\in A`; `\lim_{q\to\infty}` is the limit of a sequence, and an exponent built from them is an integer power. Without the convention, a letter other than `n`, `m`, `k`, `j`, `i`, `N`, `M`, `K` bounded by inequalities alone is a real number |

Functions of several variables are curried: `f:\mathbb R^2\to\mathbb R` (or
`\mathbb R\times\mathbb R\to\mathbb R`) has type `ℝ → ℝ → ℝ`, and `f(x,y)` applies it to
`x` and `y`.

| Sentence | Reading |
| --- | --- |
| `Define $f:\mathbb R^2\to\mathbb R$ by $f(x,y)\coloneqq x^2y$.`, `Let $g:\mathbb R^2\to\mathbb R$ be given by $g(s,t)=s-t$.`, `For $x,y\in\mathbb R$ set $h(x,y)\coloneqq xy$.` | a function of several variables; the names of its variables are remembered |
| `\partial_x f(1,2)`, `\partial_2 h(x,y,z)`, `\frac{\partial f}{\partial y}(x,y)`, `\partial_x\partial_y f`, `\partial_x^2 f` | partial derivatives: in the argument named `x` (by the application, or by the definition of `f`) or numbered from 1; the derivative of `t ↦ f(…,t,…)`, defined where it exists |
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
| `Then there is exactly one smooth function $\varphi$ on $\mathbb{T}^2$ of zero Haar mean with $N\varphi=F$.` | existence and uniqueness (`there is a NP`, `there is a unique NP`, `… such that CLAUSE`) |
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
6. **Make every quantifier explicit.** "for every $r\in[-1,1]$" instead of a
   free $r$. A variable bound at the start of a result ("For $w\in[0,1]$, …")
   stays bound in the result's later sentences that use it.
7. **Cite what a step uses.** "By Lemma~\ref{…}, …", "By \cref{…}, …", "…, by
   \eqref{…}", "\eqref{…} gives …". A proof sentence may use the earlier sentences of its
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
| a family of functions | `For $s\in[0,1]$ and $u,v\in[0,1]$, set $S_s(u,v)\coloneqq\min\{u,v,1-s\}+\max\{u+v+s-2,0\}$.` (indexed by the first variable, a function of the others) |
| a family of maps | `For $s\in(0,1]$, define $\varphi_s:[0,1]\to\R$ by \[\varphi_s(t)\coloneqq\begin{cases}…\end{cases}\]` (also `T^0_q`, `R_b^-`; the map takes values in its codomain, a claim) |
| a definition in a proof | `For $v\in[0,s]$ and $w\in[0,1-s]$, set $g_v(w)\coloneqq(v+w)^2(2s-3v+3w)$.` inside the proof of a result about $s$ (the result's variables it uses are implicit arguments: `g_v(0)` is `g` at `s`, `v`, `0`) |
| a definition with a binder | `For every $r\in(-1,1)$ and $s\coloneqq(\frac{1-r}{2})^{1/3}$, $S_s$ is …` (a function of the binder's variables, local to the result) |
| decorated names | `For $b\in[-1,1]$, set \begin{equation}r_-(b)\coloneqq-1+\tfrac{3}{16}(1+b)^3,\qquad r_+(b)\coloneqq1-\tfrac{3}{16}(1-b)^3.\end{equation}` |
| named map | `For $c\in[0,1]$, the corresponding rank map $\zeta_c:[0,1]\to[0,1]$ reads \[…\]` |
| notion of the vocabulary | `Lebesgue measure on $[0,1]$ is denoted by $\mathrm{Leb}$.` |
| relation | `We say that a NOUN $F$ is \emph{supported on the graph} of a Borel measurable $f:[0,1]\to[0,1]$ if $F(u,v)=…$ for all $u,v\in[0,1]$.` |
| class of the vocabulary | `Let $\mathcal{X}$ denote the class of NOUNS.`, `We denote by $\mathcal{X}$ the set of NOUNS.` |
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
| a domain that uses an earlier variable | `Let $x\in(0,1]$ and $e\in[0,x]$.` (the claims that use `e` are also about `x`) |
| upper and lower signs | `For $c\in(0,\infty)$, set $x_\pm(c)\coloneqq c\pm1$.` defines `x_+` and `x_-`; a claim with `\pm` or `\mp` is the two claims, one for each sign |
| the variable after the definition | `Write $g(t)\coloneqq\min\{\max\{t,0\},1\}$ for $t\in\mathbb{R}$.`, `Define the weight \[a(x,z)\coloneqq x(x+2z),\qquad (x,z)\in[0,1]^2.\]` |
| the least or the greatest | `For a positive integer $n$, let $j(n)$ be the least positive integer $m$ such that $m^2\ge n$.` (also `smallest`, `minimal`, `largest`, `greatest`, `maximal`; `for which DISPLAY`; `Define $L$ to be|as …`, `We write $L$ for …`, `Denote by $L$ …`): a definite description, well defined where such a least number exists |
| how many | `Let $N$ be the number of primes $p\le 10$.`, `Write $\omega(n)$ for the number of primes $p$ such that $p\mid n$.` (well defined where finitely many numbers are described) |
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
| if and only if | `Moreover, $G=A$ if and only if $a=b$.` |
| a binder with a condition | `For every $x\in\mathbb{R}$ with $x\neq0$, $x^{-1}x=1$.`, `For all $x\in\mathbb{R}$ such that $x>0$ and $x<1$, $x^2<x$.`, `For every $y\in\mathbb{R}\setminus\{0\}$, …` |
| several variables of a noun | `Let $a,b$ be positive integers with $a<b$.`, `If $a$ and $b$ are positive integers, then …`, `There are integers $c,d$ with $c+d=1$.` (each variable is of the noun; the condition after `with` is about all of them, and without `such that` it is what `there are` asserts) |
| a sequence of variables | `For all $x_1,\ldots,x_n\in[0,1]$, …`, `for all $a_1,\ldots,a_n>0$`, `Let $a_1,\dots,a_k$ be positive integers.`, `If $b_1,\ldots,b_k$ are real numbers with $b_1\ge1$, then …`, `there are $\varepsilon_1,\ldots,\varepsilon_N\in\{-1,1\}$ such that …` (a sequence `x`, a real function, each of whose terms `x_i`, for the integers `i` from the first index to the last, is as the noun or the domain says; the terms written before the dots are the first ones, `x_1,x_2,\ldots,x_n`. A term `x_i` is defined only for those `i`: a claim about `x_{n+1}` is not meaningful) |
| variables together | `Let $p,q$ be distinct primes.`, `there are distinct positive integers $a,b,c$ with …`, `pairwise coprime integers $a,b,c$`, `$r$ and $s$ are relatively prime`, `$x_1,\ldots,x_n$ are distinct` (`distinct`: any two are different; `relatively prime`, `coprime`: their greatest common divisor is 1, for exactly two of them; of more, `pairwise` says that any two are; for a sequence, any two terms with different indices) |
| several subjects | `$a$ and $b$ are positive`, `$a,b$ are odd integers`, `$x_1,\ldots,x_n$ are positive` (each of them is as the words say) |
| a statement as a hypothesis | `If $n$ is even, then …`, `For all integers $a,b$, if $a$ and $b$ are odd, then …`, `Let $k\ge1$ be an integer. If $k$ is an even integer, then …` (a statement about variables bound before, by the result or by the sentence's binders, as a hypothesis; `If $n$ is an even integer` about an `n` not bound yet binds it, as `For every even integer $n$`) |
| adjectives without a noun | `for every positive $a\in J$`, `for every nonzero $x$`, `a rational $s\in(0,1)$`, `for all sufficiently small positive $\varepsilon$` (a real number with the adjectives, in the domain if one is written; before an index name, `n`, `m`, `k`, `j`, `i`, `N`, `M`, `K`, without a domain, refused with a finding: say `every positive integer $n$`) |
| equivalent statements | `Then the following are equivalent: \begin{enumerate}\item $x^2=1$; \item $\lvert x\rvert=1$; \item $(x-1)(x+1)=0$. \end{enumerate}` (each item a formula; each is equivalent to the next) |
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
mean, `the probability of an exit at $-1$ is at least …` is not read.

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
