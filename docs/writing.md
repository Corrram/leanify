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
variable before parentheses is a factor (`xz(x+z)`, `v(s-v)^2`), and
`\{(x,x):0\le x\le1\}` is the diagonal.

| Notation | Read as |
| --- | --- |
| `(f\circ g)(x)` | `f(g(x))`, with `g(x)` in the domain of `f` |
| `A\subseteq B`, `A\supseteq B` | every real number in `A` is in `B` (and the reverse), for intervals, sets `\{x\in A : …\}` and sets the article defines |
| `\sup_{x\in A} e`, `\sup\{e : x\in A\}`, `\sup S` (and `\inf`) | the least upper (greatest lower) bound: defined only when it exists, so a claim about an unbounded or empty set is not meaningful |
| `\sum_{j=1}^{4} e`, `\prod_{k=0}^{2} e` | with numeral bounds: the terms written out |
| `\sum_{j=a}^{b} e`, `\prod_{j=a}^{b} e` | over the integers from `a` to `b`, which must be integers (`b<a`: the empty sum `0`, product `1`) |
| `\sum_{k=a}^{\infty} e` | the limit of the partial sums, defined only when it exists (so conditionally convergent series such as `\sum_{k=1}^{\infty}\frac{(-1)^{k+1}}{k}` are read) |
| `\lim_{x\to a} e`, `\lim_{x\to\infty} e` | the limit within the points where `e` is defined (`x\ne a`), defined only when it exists and the points accumulate at `a` |
| `\lim_{n\to\infty} a_n` | for an index `n`, `m`, `k`, `j`, `i` (or `N`, `M`, `K`): the limit of the sequence through the natural numbers |
| `(-1)^k`, `2^{n+1}` | an exponent built from indices is an integer power, for any base |
| `n!`, `\binom{n}{k}` | for natural numbers `n`, `k` |
| `\exp(x)`, `\exp x`, `e^{x}` | the exponential function (`e` unless the article names something `e`) |
| `\log x`, `\ln x` | the natural logarithm, applied only to positive numbers (the claim asks that the argument be positive) |
| `\sin x`, `\cos x`, `\tan x`, `\sin^2 x` | the trigonometric functions (`\tan` only where `\cos` is not zero); `\sin^2 x` is the square of `\sin x` |
| `\pi` | the number π, unless the article defines `\pi` |
| `\operatorname{sgn}(x)` | the sign of `x`: 1, −1 or 0 |
| `\max(a,b)`, `\min(a,b)` | as `\max\{a,b\}` |
| `\sqrt[3]{x}` | `x^{1/3}`, for `x\ge0` |
| `2\times3` | the product of two numbers (between sets, `\times` is the product of the sets) |
| `A\cap B`, `A\setminus B`, `\{a,b\}`, `\emptyset` | intersection, difference, finite sets and the empty set of real numbers; `(a,b)` as a set is the open interval |
| `x\notin A` | not `x\in A` |
| `\mathbb{R}_{>0}`, `\mathbb{R}_{\ge0}`, `\mathbb{R}_+` | `(0,\infty)`, `[0,\infty)`, `[0,\infty)` |
| `\{x\in A\mid φ\}` | as `\{x\in A : φ\}` |
| `\forall x,y\in A: φ`, `\exists x\in A: φ` | quantifiers over real numbers in `A` (the domain ends at the first `:` or `,`; the body extends to the end of the formula) |
| `\neg`, `\land`/`\wedge`, `\lor`/`\vee`, `\Rightarrow`/`\implies`, `\iff`/`\Leftrightarrow` | the connectives, binding in this order (`\neg` the tightest) |
| `\int_0^1 x\,dx` | as `\int_0^1 x\,\mathrm{d}x` |
| `\mathbb{N}`, `\mathbb{N}_0`, `\mathbb{Z}` | the natural numbers (with 0, as in mathlib; write `n\ge1` for the positive ones) and the integers, as real numbers |
| `\lfloor x\rfloor`, `\lceil x\rceil` | the largest integer at most `x`, the smallest at least `x` |
| `x^{-1}`, `x^{-2}` | `\frac1x`, `\frac1{x^2}`: defined for `x\ne0`, of either sign |
| `$$…$$` | a display, like `\[…\]` |
| `\colon`, `\mid`, `\leqslant`, `\geqslant`, `\lvert`/`\rvert`, `\lbrace`/`\rbrace` | `:`, `:`, `\le`, `\ge`, a vertical bar, `\{`/`\}` |

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

Functions of several variables are curried: `f:\mathbb R^2\to\mathbb R` (or
`\mathbb R\times\mathbb R\to\mathbb R`) has type `ℝ → ℝ → ℝ`, and `f(x,y)` applies it to
`x` and `y`.

| Sentence | Reading |
| --- | --- |
| `Define $f:\mathbb R^2\to\mathbb R$ by $f(x,y)\coloneqq x^2y$.`, `Let $g:\mathbb R^2\to\mathbb R$ be given by $g(s,t)=s-t$.`, `For $x,y\in\mathbb R$ set $h(x,y)\coloneqq xy$.` | a function of several variables; the names of its variables are remembered |
| `\partial_x f(1,2)`, `\partial_2 h(x,y,z)`, `\frac{\partial f}{\partial y}(x,y)`, `\partial_x\partial_y f`, `\partial_x^2 f` | partial derivatives: in the argument named `x` (by the application, or by the definition of `f`) or numbered from 1; the derivative of `t ↦ f(…,t,…)`, defined where it exists |
| `\Delta f(x,y)` | the Laplacian, `∑ⱼ ∂ⱼ∂ⱼ f` |
| `For every $I\in\mathbb N_0^2$, $|\partial^If(x,y)|\le C_I$` | a multi-index `I` (in `\mathbb N_0^n`, `\mathbb N^n`) is the `n` natural numbers `I_1`, …, `I_n`; `\partial^I f` is the derivative of order `I_k` in the `k`-th argument, defined only where `f` is smooth (`C^∞`); a constant `C_I` may depend on the components |

Generic constants and existence (`tests/Fields/article.tex` and
`tests/Conventions/article.tex` use each form):

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
| `… for every integer $m\ge0$ and every smooth function $\varphi$ on …` | binders after a claim, the first one outermost |
| `For every positive integer $k$, every positive integer $N$ and every $x\in[0,1]$, …` | several binders before a claim (`, every`, `and every`, `and each`, `and all`, `and $y\in[0,1]$`), the first one outermost |
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
2. **Write definitions with `\coloneqq`.** `f(x)\coloneqq x+\frac1x` defines
   `f`. `f(x)=x+\frac1x` is a claim about an `f` that must already exist.
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
| a domain that uses an earlier variable | `Let $x\in(0,1]$ and $e\in[0,x]$.` (the claims that use `e` are also about `x`) |
| upper and lower signs | `For $c\in(0,\infty)$, set $x_\pm(c)\coloneqq c\pm1$.` defines `x_+` and `x_-`; a claim with `\pm` or `\mp` is the two claims, one for each sign |
| the variable after the definition | `Write $g(t)\coloneqq\min\{\max\{t,0\},1\}$ for $t\in\mathbb{R}$.`, `Define the weight \[a(x,z)\coloneqq x(x+2z),\qquad (x,z)\in[0,1]^2.\]` |
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
| condition | `If $-1\le t\le t_*$, then \begin{equation}u(t)=\frac{144+420t+(9+65t)\sqrt{6-10t}}{500}.\end{equation}` |
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
| equivalent statements | `Then the following are equivalent: \begin{enumerate}\item $x^2=1$; \item $\lvert x\rvert=1$; \item $(x-1)(x+1)=0$. \end{enumerate}` (each item a formula; each is equivalent to the next) |
| several facts | `We have $(\sqrt a)^2=a$, $(\sqrt b)^2=b$ and $\sqrt a\sqrt b=\sqrt{ab}$.` (each fact is a claim of the same sentence) |
| facts used by a step | `Since $G\le A$ and $G>0$, it follows that $H=G\cdot\frac{G}{A}\le G$.` (the facts after "Since" are premises of the step, so the step may use them) |
| a reason in words | `Moreover, $\sqrt a=\sqrt b$ if and only if $a=b$, since the square root is injective.` (the reason is prose, the claim before it is checked) |
| equality sets | `If $w>\frac12$, equality holds exactly on $S_w$, and if $w=\frac12$, it holds exactly on $S_{1/2}\cup([\frac12,1]\times\{\frac12\})$.`, `…, and equality holds exactly when $x=R_b(z)$.`, `For every $x\in(0,\infty)$, $f(x)\ge2$. Equality holds exactly when $x=1$.` (about the preceding inequality, for every point of its domain) |

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
rectangle.") are prose and assert nothing.

A section whose title announces a proof, `\subsection{Proof of
Theorem~\ref{thm:main}}`, is a proof of that result up to the next sectioning
command. The heading of a case, `\item \emph{$x\ge0$.}`, is prose: it is the
case's assumption, not a claim. The steps under it are read without that
assumption, so a step that holds only in its case is not derived.

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

The check takes about a second and certifies nothing. `lake build` of the
certifying module checks everything in the kernel. `editors/vscode/tasks.json`
shows both as problems in the `.tex` file. With `\usepackage{leanify}`, an
article compiled with shell escape is checked on every compile, and the
findings are LaTeX warnings at their lines
([`leanify.sty`](reference.md#the-pdf-leanifysty)).
