# Vocabularies and models

An article defines its own symbols. What it does not define, such as
"probability measure on $[0,1]^2$" or "Lebesgue measure", comes from a *vocabulary*: a reviewed
list of fixed phrases, each with a closed term of the core language. A
vocabulary's *model* gives its base types and constants their Lean meaning.
Both are written once, reviewed once and shared by every article that uses
them.

## The core language

`Leanify/Syntax.lean` defines the terms (`Tm`) and types (`Ty`) that
sentences compile to: real numbers, `[0,1]`, propositions, functions, base
types `Ty.base k` supplied by a vocabulary, and a small set of primitives
(`Prim`) with mathlib meanings: real powers, `min`, `max`, Lebesgue measure on
`[0,1]`, Borel measurability, measurable sets, integrability on `[0,1]` and
derivatives within a set. `Leanify/Denote.lean` gives every term its Lean
denotation, relative to a model. Definite descriptions ("the unique $b$ with
…") denote `Classical.epsilon`, and are well defined when the description has
exactly one solution.

## A vocabulary

```lean
structure Vocab where
  types : List Codes        -- names of the base types (for readings)
  consts : List Ty          -- types of the constants `Tm.const i`
  constNames : List Codes   -- their names (for readings)
  nouns : List Noun         -- "distribution function on $[0,1]^2$"
  mods : List Modifier      -- "Borel measurable", "with uniform marginals"
  notions : List Notion     -- "Lebesgue measure on $[0,1]$"
  methods : List Method     -- `z+w` on the complex numbers (below)
  symbols : List Symbol     -- `\mathrm{i}`, `\mathbb{C}`
```

Phrases are written with `phrase!`. Words are matched literally, any formula in
the phrase is matched token for token, and `$v$` marks the variable the phrase
binds:

```lean
def vocab : Vocab where
  consts := [Ty.sq ⟶ .prop, Ty.sq ⟶ .prop, Ty.meas2 ⟶ .prop, Ty.meas2 ⟶ .prop]
  nouns := [
    { sing := phrase!"distribution function on $[0,1]^2$",
      plural := phrase!"distribution functions on $[0,1]^2$", ty := Ty.sq, pred := .const 0 },
    { sing := phrase!"probability measure $v$ on $[0,1]^2$",
      plural := phrase!"probability measures $v$ on $[0,1]^2$", ty := Ty.meas2, pred := .const 2 }]
  mods := [
    { phrase := phrase!"with uniform marginals", prenominal := false, ty := Ty.sq, pred := .const 1 },
    { phrase := phrase!"with uniform marginals", prenominal := false, ty := Ty.meas2, pred := .const 3 }]
```

This is `Leanify.UnitSquare.vocab`. With it, the sentence

> let $\mathcal{D}$ denote the class of standard distribution functions, that is,
> distribution functions on $[0,1]^2$ with uniform marginals.

defines `\mathcal{D}` as the predicate `fun F => DistFn F ∧ UnifMarg F`. The
full list of its phrases is in `Leanify/Library/UnitSquare.lean`.

Vocabularies combine with `++` (`Vocab.core ++ UnitSquare.vocab`): the base
types and constants of the second are renumbered after those of the first.

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
domain). The field `complex` (`Leanify/Library/Complex.lean`, with its model
`ComplexModel.lean`) is such a vocabulary: one base type, interpreted as Mathlib's `ℂ`,
and fifteen constants for its notation. A constant's name says how a reading writes
it: an operator (`+`), `#` for its argument (`\lvert #\rvert`), or nothing (a real
number as a complex one).

## A model

```lean
structure Model where
  base : Nat → Type                -- the base types
  default : (k : Nat) → base k     -- an element of each (for totalized terms)
  consts : List (Val base)         -- each constant: its type and its value
```

The model of the unit-square vocabulary (`Leanify/Library/UnitSquareModel.lean`)
says what the four constants mean in mathlib terms:

```lean
def distFn2 (F : I → I → ℝ) : Prop :=
  ∃ μ : Measure (I × I), IsProbabilityMeasure μ ∧
    ∀ u v : I, F u v = (μ (Set.Iic u ×ˢ Set.Iic v)).toReal

def dfUniformMarginals (F : I → I → ℝ) : Prop :=
  (∀ u : I, F u 1 = u) ∧ ∀ v : I, F 1 v = v
```

Reviewing a vocabulary means checking that each phrase means what its model
says. That review is the only place where words acquire meaning. Everything an
article adds is defined in the article and checked.

## Using a vocabulary

```lean
-- Compiled.lean
#leanify_article Foo "article.tex" "fnv1a64:…" with MyVocab.vocab
-- Article.lean
#leanify_semantics Foo "article.tex" with MyVocab.model
```

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

A phrase belongs in the core vocabulary when it is standard across subjects and
has one established mathlib meaning. Subject vocabularies (measures on the unit
square, …) live in `Leanify/Library/` or in the project that uses
them. A new primitive in `Prim` needs its denotation, its definedness condition
and its readable Lean form (`Leanify/Readable.lean`), and should be rare.
