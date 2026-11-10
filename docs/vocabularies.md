# Vocabularies and models

An article defines its own symbols. What it does not define, such as
"probability measure on $[0,1]^2$" or "Lebesgue measure", comes from a *vocabulary*: a reviewed
list of fixed phrases, each with a closed term of the core language. The
constants of a vocabulary name their Lean meanings: declarations of Mathlib, or
definitions written for the field. A field is therefore data. It is written
once, reviewed once and shared by every article that uses it.

## The core language

`Leanify/Syntax.lean` defines the terms (`Tm`) and types (`Ty`) that
sentences compile to: real numbers, propositions, functions, base
types `Ty.base k` supplied by a vocabulary, and a small set of primitives
(`Prim`) with mathlib meanings: real powers, `min`, `max`,
derivatives within a set, integrals `\int_a^b`, sums, limits and the standard
properties of real functions. A subject's own notions are not among them: they are
constants of its field. This includes the interval `[0,1]` as a type of its own, with
its Lebesgue measure and its integral: they belong to the field `unitsquare`
([below](#an-interval-as-a-type)). `Leanify/Denote.lean` gives every term its Lean
denotation, relative to a model. Definite descriptions ("the unique $b$ with
…") denote `Classical.epsilon`, and are well defined when the description has
exactly one solution.

## A vocabulary

```lean
structure Vocab where
  types : List Codes        -- names of the base types (for readings)
  consts : List Ty          -- types of the constants `Tm.const i`
  constNames : List Codes   -- their names (for readings)
  constLean : List Codes    -- their Lean meanings: `Real.sinh`, `Leanify.Torus.smoothT2`
  typeLean : List (Codes × Codes)  -- the Lean type of each base type, and an element of it
  modules : List Codes      -- the Lean modules that define the meanings
  nouns : List Noun         -- "distribution function on $[0,1]^2$"
  mods : List Modifier      -- "Borel measurable", "with uniform marginals"
  adjectives : List Adjective  -- "convex", "compact with respect to uniform convergence"
  notions : List Notion     -- "Lebesgue measure on $[0,1]$"
  methods : List Method     -- `z+w` on the complex numbers (below)
  symbols : List Symbol     -- `\mathrm{i}`, `\mathbb{C}`, `\sinh`
  intervals : List IntervalType  -- `[0,1]` as a type of its own (below)
```

The smallest field is `hyperbolic` (`Leanify/Library/Hyperbolic.lean`), all of it:

```lean
def vocab : Vocab where
  consts := [.real ⟶ .real, .real ⟶ .real, .real ⟶ .real]
  constNames := [w!"\\sinh", w!"\\cosh", w!"\\tanh"]
  constLean := [w!"Real.sinh", w!"Real.cosh", w!"Real.tanh"]
  modules := [w!"Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic"]
  symbols := [
    { sym := w!"\\sinh", ty := .real ⟶ .real, const := some 0 },
    { sym := w!"\\cosh", ty := .real ⟶ .real, const := some 1 },
    { sym := w!"\\tanh", ty := .real ⟶ .real, const := some 2 }]
```

Three symbols, their type, and the names of three Mathlib functions. With
`--vocab hyperbolic`, `$\cosh(x)^2-\sinh(x)^2=1$` and `$\cosh x\ge1$` are read, and
their Lean statements are about `Real.cosh` and `Real.sinh`. (That a named function
applies to what follows it, `\cosh x`, is syntax: it holds for LaTeX's operator names,
whatever field gives one its meaning.) Nothing else was written for the field: no
constructor of the core language, no denotation, no model.

Phrases are written with `phrase!`. Words are matched literally, any formula in
the phrase is matched token for token, and `$v$` marks the variable the phrase
binds:

```lean
def vocab : Vocab where
  consts := [Ty.sq ⟶ .prop, Ty.sq ⟶ .prop, Ty.meas2 ⟶ .prop, Ty.meas2 ⟶ .prop]
  nouns := [
    { sing := phrase!"distribution function on $[0,1]^2$",
      plural := phrase!"distribution functions on $[0,1]^2$", ty := sq, pred := .const 0 },
    { sing := phrase!"probability measure $v$ on $[0,1]^2$",
      plural := phrase!"probability measures $v$ on $[0,1]^2$", ty := meas2, pred := .const 2 }]
  mods := [
    { phrase := phrase!"with uniform marginals", prenominal := false, ty := Ty.sq, pred := .const 1 },
    { phrase := phrase!"with uniform marginals", prenominal := false, ty := Ty.meas2, pred := .const 3 }]
```

This is a part of `Leanify.UnitSquare.vocab`. With it, the sentence

> let $\mathcal{D}$ denote the class of standard distribution functions, that is,
> distribution functions on $[0,1]^2$ with uniform marginals.

defines `\mathcal{D}` as the predicate `fun F => DistFn F ∧ UnifMarg F`. The
full list of its phrases is in `Leanify/Library/UnitSquare.lean`.

Vocabularies combine with `++` (`Vocab.core ++ UnitSquare.vocab`): the base
types and constants of the second are renumbered after those of the first. An
article may name several fields with constants and types of their own
(`--vocab numbers,torus,hyperbolic`).

An *adjective* is a property of objects of one type that a sentence states with
`$X$ is ADJ [on $A$]`: the unit square's field has `convex`, `concave` and
`lower semicontinuous with respect to uniform convergence` for a quantity of
copulas on a class, and `convex` and `compact with respect to uniform
convergence` for a class. The adjectives of real numbers, real functions and
sets of points of the plane belong to the core.

## Notation on a vocabulary's types

As in Python, where `+` calls the `__add__` of its operands' class, notation means
what the type of its operands says. The core reads `+`, `-`, products, `/`, powers,
`\lvert\cdot\rvert`, `\le`, `<` and finite sums of real numbers. A vocabulary that
declares a type of its own says what that notation means on it, by *methods*: each
method names a piece of notation (`OpKey`) and the constant it is on that type.

```lean
structure Method where
  ty : Ty          -- the type (a base type of the vocabulary)
  op : OpKey       -- ofReal, add, sub, mul, div, neg, pow, abs, sum, prod, le, lt,
                   -- fn "\exp" (a named function), decor "\overline" (a decoration)
  const : Nat      -- the constant that is this notation on the type
```

`ofReal` makes a real number an element of the type where one is expected (`1+z`),
`z/w` is defined when `w` is not the image of `0`, and `z^n` when `n` is a natural
number. A type without `le` has no order: `z\le w` is refused with a finding. *Symbols*
name a constant (`\mathrm{i}`) or all the elements of a type (`\mathbb{C}`, as a
domain), or a function (`\sinh`). The field `complex` (`Leanify/Library/Complex.lean`,
with the definitions of `ComplexModel.lean`) is such a vocabulary: one base type,
whose Lean meaning is Mathlib's `ℂ`, and fifteen constants for its notation. A
constant's name says how a reading writes it: an operator (`+`), `#` for its
argument (`\lvert #\rvert`), `#1` and `#2` for two arguments
(`\operatorname{convex}(#1)\text{ on }#2`), or nothing (a real number as a
complex one).

## An interval as a type

In an article about copulas, `$u\in[0,1]$` is a point of the unit interval and
`$C:[0,1]^2\to\mathbb{R}$` a function of two such points, which has no values outside
the square. The field `unitsquare` says so, as data:

```lean
structure IntervalType where
  lo hi : Nat        -- the interval `[lo,hi]` as written
  ty : Ty            -- the base type that it is
  val : Nat          -- the constant `T → ℝ`: the number that a point is
  point : Nat        -- `ℝ → T`: a number of the interval as a point
  integral : Nat     -- `(T → ℝ) → ℝ`, with `integrable : (T → ℝ) → Prop`
  measurable1 measurable2 lebesgue : Nat   -- measurable sets, Lebesgue measure
```

Each part is a constant of the field with a Lean meaning that it names: the type is
Mathlib's `↥unitInterval`, `val` is `Subtype.val`, `point` is `Set.projIcc 0 1 _`, the
integral is the Bochner integral for `volume`. With the field named,

* a variable in `[0,1]` has that type, and is the number `val u` wherever a number is
  expected (`u+v`, `u\le\frac12`);
* a number used as a point (`C(\frac12,1-u)`) is `point x`, which is meaningful only
  for `0 ≤ x ≤ 1`: the condition is part of what makes the claim meaningful;
* `\int_0^1 e\,dt` is the integral over the type, meaningful when the integrand is
  integrable.

Without the field, `[0,1]` is a set of real numbers like `[0,2]`: a variable in it is
a real number with `0 ≤ x ≤ 1`, and `\int_0^1` is the core's `\int_a^b`. The readable
Lean statements of an article of the field are about `↥unitInterval`, `Subtype.val`,
`Set.projIcc` and `∫ x, …`, as Mathlib writes them (`tests/Square`).

## The meanings

`#leanify_semantics` builds the model of an article's vocabulary from the names
in it:

```lean
structure Model where
  base : Nat → Type                -- the base types
  default : (k : Nat) → base k     -- an element of each (for totalized terms)
  consts : List (Val base)         -- each constant: its type and its value
```

The article's Lean file imports the modules the vocabulary names (`leanify init`
writes the imports), and the kernel checks that every named declaration has the
type the vocabulary gives its constant. A meaning that is an `abbrev` is written
out in the readable statements (`z + w`, not `add z w`).

For the unit square, `Leanify/Library/UnitSquareModel.lean` says what the
constants mean in mathlib terms:

```lean
def distFn2 (F : I → I → ℝ) : Prop :=
  ∃ μ : Measure (I × I), IsProbabilityMeasure μ ∧
    ∀ u v : I, F u v = (μ (Set.Iic u ×ˢ Set.Iic v)).toReal

def dfUniformMarginals (F : I → I → ℝ) : Prop :=
  (∀ u : I, F u 1 = u) ∧ ∀ v : I, F 1 v = v
```

Reviewing a vocabulary means checking that each phrase means what its Lean
meaning says. That review is the only place where words acquire meaning.
Everything an article adds is defined in the article and checked.

## Using a vocabulary

```lean
-- Compiled.lean
#leanify_article Foo "article.tex" "fnv1a64:…" with MyVocab.vocab
-- Article.lean
import MyProject.VocabMeanings
#leanify_semantics Foo "article.tex"
```

A vocabulary whose constants do not name their meanings needs a model written
by hand: `#leanify_semantics Foo "article.tex" with MyVocab.model`.

The native checker knows the vocabularies it was built with
(`lake exe leanify check article.tex --vocab unitsquare`). A project with its
own vocabulary adds a small executable:

```lean
import Leanify.Check
import MyProject.Vocab

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: check ARTICLE.tex"; pure 2
  let failed ← Leanify.checkArticle (Leanify.Vocab.core ++ MyProject.vocab) path false true
  pure (if failed == 0 then 0 else 1)
```

## Adding to the core

The core vocabulary (`Leanify/Library/Core.lean`) has the words every article may
use: *real number*, *integer*, *positive integer*, *rational number*, and the signs
*positive*, *negative*, *nonnegative*, *nonzero*. A phrase belongs there when it is
standard across subjects and has one established mathlib meaning. The notions of one subject (measures on the
unit square, functions on the torus, …) are a field, in `Leanify/Library/` or in
the project that uses them: a field needs no change of the core. A new primitive
in `Prim` needs its denotation, its definedness condition and its readable Lean
form (`Leanify/Readable.lean`), and is for what the grammar itself builds
(limits, sums, integrals), not for the words of a subject.
