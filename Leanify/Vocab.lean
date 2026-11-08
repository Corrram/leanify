import Leanify.Math
import Leanify.Syntax

/-! # Vocabularies

A vocabulary supplies the meanings that an article does not define itself:
base types, constants, nouns (`probability measure $\gamma$ on $[0,1]^2$`),
modifiers (`with uniform marginals`) and named notions (`Lebesgue measure on
$[0,1]$`). Each entry pairs a fixed phrase with a closed core term. The phrases
are matched literally; there is no other source of meaning.

A vocabulary is reviewed once, together with its `Model` (the Lean meaning of
its base types and constants), and shared by every article that uses it. The
core vocabulary `Vocab.core` covers real analysis on `[0,1]`; subject
vocabularies extend it (`Vocab.append`).

Notation means what the type of its operands says, as in Python, where `+` calls
the `__add__` of its operands' class: the core reads `+`, `-`, `\cdot`, `/`, `^`,
`\lvert\cdot\rvert`, `\le` and finite sums of real numbers, and a vocabulary that
declares a type of its own says what they mean on it, by its `methods` (the complex
numbers of `Leanify.Library.Complex`). -/

namespace Leanify

/-- An item of a vocabulary phrase: a lower-case word, a fixed formula (matched
token for token), or the variable that the phrase binds (`$x$`). -/
inductive PItem where
  | w (word : Codes)
  | m (toks : List MTok)
  | v
  /-- A formula with arguments (`$C^v$`): the fixed pieces between them. -/
  | f (segs : List (List MTok))
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

abbrev Phrase := List PItem

/-- A noun: a class of objects of one type. `pred` is a closed predicate on `ty`. -/
structure Noun where
  sing : Phrase
  plural : Phrase
  ty : Ty
  pred : Tm
  /-- The field of the vocabulary the noun belongs to (empty: the core). -/
  field : Codes := []
  /-- Its meaning and Mathlib counterpart, for the glossary. -/
  doc : String := ""
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

/-- A modifier restricts a noun of the same type: prenominal adjectives
(`Borel measurable`) and postnominal phrases (`with uniform marginals`). -/
structure Modifier where
  phrase : Phrase
  prenominal : Bool
  ty : Ty
  pred : Tm
  field : Codes := []
  doc : String := ""
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

/-- A named notion, for `NAME is denoted by $S$` and `let $S$ denote NAME`. A notion
with variables in its phrase (`Poisson distribution with mean $v$`) is a function of
them, in order; `doms` are their domains (as for an article's definitions). -/
structure Notion where
  name : Phrase
  value : Tm
  ty : Ty
  doms : List (Option Tm) := []
  field : Codes := []
  doc : String := ""
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

/-- A piece of notation that a vocabulary can give a meaning on one of its types. -/
inductive OpKey where
  /-- A real number as an element of the type, where an element is expected (`1+z`):
  `ℝ → T`. -/
  | ofReal
  /-- `x+y`, `x-y`, `xy`, `x/y`: `T → T → T` (`x/y` is defined for `y ≠ 0`, the image of `0`). -/
  | add | sub | mul | div
  /-- `-x`: `T → T`. -/
  | neg
  /-- `x^n` for a natural number `n`: `T → ℝ → T` (defined for `n ∈ ℕ`). -/
  | pow
  /-- `\lvert x\rvert`: `T → ℝ`. -/
  | abs
  /-- `\sum_{k=a}^{b}` and `\prod_{k=a}^{b}` over the integers from `a` to `b`:
  `ℝ → ℝ → (ℝ → T) → T`. -/
  | sum | prod
  /-- `x\le y`, `x<y` (`x\ge y`, `x>y` with the arguments swapped): `T → T → Prop`. -/
  | le | lt
  /-- A named function of one element (`\exp`, `\Re`, `\operatorname{Re}`): `T → U`. -/
  | fn (name : Codes)
  /-- A decoration of a variable (`\overline{z}`, `\bar z`): `T → U`. -/
  | decor (name : Codes)
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

/-- A method: the notation `op` on elements of `ty` is the constant `const`. -/
structure Method where
  ty : Ty
  op : OpKey
  const : Nat
  /-- Its meaning and Mathlib counterpart, for the glossary. -/
  doc : String := ""
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

/-- A symbol of the vocabulary: a constant (`\mathrm{i}`), or, without one, the set of
all elements of `ty` (`\mathbb{C}`, as a domain: `z\in\mathbb{C}`). -/
structure Symbol where
  sym : Codes
  ty : Ty
  const : Option Nat := none
  field : Codes := []
  doc : String := ""
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

structure Vocab where
  /-- Names of the base types (for readings). -/
  types : List Codes := []
  /-- Types of the constants (`Tm.const i`). -/
  consts : List Ty := []
  /-- Readable names of the constants (for readings). -/
  constNames : List Codes := []
  nouns : List Noun := []
  mods : List Modifier := []
  notions : List Notion := []
  /-- What notation means on the vocabulary's types. -/
  methods : List Method := []
  symbols : List Symbol := []
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

namespace Vocab

/-- Shift base-type indices of a type by `k`. -/
def shiftTy (k : Nat) : Ty → Ty
  | .base i => .base (i + k)
  | .fn a b => .fn (shiftTy k a) (shiftTy k b)
  | t => t

/-- Base-type shifts inside terms (binder annotations). -/
def shiftTm (k : Nat) : Tm → Tm
  | .lam t d b => .lam (shiftTy k t) (shiftTm k d) (shiftTm k b)
  | .all t b => .all (shiftTy k t) (shiftTm k b)
  | .ex t b => .ex (shiftTy k t) (shiftTm k b)
  | .the t b => .the (shiftTy k t) (shiftTm k b)
  | .undef t => .undef (shiftTy k t)
  | .app f x => .app (shiftTm k f) (shiftTm k x)
  | .ofUnit x => .ofUnit (shiftTm k x)
  | .toUnit x => .toUnit (shiftTm k x)
  | .add x y => .add (shiftTm k x) (shiftTm k y)
  | .sub x y => .sub (shiftTm k x) (shiftTm k y)
  | .mul x y => .mul (shiftTm k x) (shiftTm k y)
  | .div x y => .div (shiftTm k x) (shiftTm k y)
  | .neg x => .neg (shiftTm k x)
  | .abs x => .abs (shiftTm k x)
  | .powNat x n => .powNat (shiftTm k x) n
  | .cases p v r => .cases (shiftTm k p) (shiftTm k v) (shiftTm k r)
  | .eq x y => .eq (shiftTm k x) (shiftTm k y)
  | .lt x y => .lt (shiftTm k x) (shiftTm k y)
  | .le x y => .le (shiftTm k x) (shiftTm k y)
  | .not p => .not (shiftTm k p)
  | .and p q => .and (shiftTm k p) (shiftTm k q)
  | .or p q => .or (shiftTm k p) (shiftTm k q)
  | .imp p q => .imp (shiftTm k p) (shiftTm k q)
  | .iff p q => .iff (shiftTm k p) (shiftTm k q)
  | .integral b => .integral (shiftTm k b)
  | .guard p e => .guard (shiftTm k p) (shiftTm k e)
  | t => t

/-- `V ++ W`: the entries of `W` follow those of `V`; its base types and
constants are renumbered. -/
def append (V W : Vocab) : Vocab :=
  let kt := V.types.length
  let kc := V.consts.length
  let tm (t : Tm) : Tm := (shiftTm kt t).shiftConst kc
  { types := V.types ++ W.types
    consts := V.consts ++ W.consts.map (shiftTy kt)
    constNames := V.constNames ++ W.constNames
    nouns := V.nouns ++ W.nouns.map fun n => { n with ty := shiftTy kt n.ty, pred := tm n.pred }
    mods := V.mods ++ W.mods.map fun m => { m with ty := shiftTy kt m.ty, pred := tm m.pred }
    notions := V.notions ++ W.notions.map fun n =>
      { n with ty := shiftTy kt n.ty, value := tm n.value, doms := n.doms.map (·.map tm) }
    methods := V.methods ++ W.methods.map fun m => { m with ty := shiftTy kt m.ty, const := m.const + kc }
    symbols := V.symbols ++ W.symbols.map fun s =>
      { s with ty := shiftTy kt s.ty, const := s.const.map (· + kc) } }

instance : Append Vocab := ⟨append⟩

/-- A reading with the names of the vocabulary's types (`\mathsf{T}_{k}` is the `k`-th). -/
def texTypes (V : Vocab) (s : String) : String :=
  V.types.zipIdx.foldl (fun s (n, k) => s.replace s!"\\mathsf\{T}_\{{k}}" (Codes.toString n)) s

/-- The entries of `V`, as the field `f`. -/
def tag (f : Codes) (V : Vocab) : Vocab :=
  -- an entry's own sense (`natural number`, `with 0`) is kept after the field
  let t (g : Codes) : Codes := if g.isEmpty then f else f ++ [32, 40] ++ g ++ [41]
  { V with nouns := V.nouns.map (fun n => { n with field := t n.field }),
           mods := V.mods.map (fun m => { m with field := t m.field }),
           notions := V.notions.map (fun n => { n with field := t n.field }),
           symbols := V.symbols.map (fun s => { s with field := t s.field }) }

end Vocab

/-! ## Writing phrases

`phrase!"probability measure $v$ on $[0,1]^2$"` is the phrase literal: words are
lower-cased, `$v$` is the bound variable and any other formula is fixed. The
lexer runs when the vocabulary is elaborated, so that the kernel never lexes
vocabulary phrases. -/

open Lean Elab Term Meta in
/-- The phrase items of a string (run by the elaborator of `phrase!`). -/
def phraseOf (s : String) : Except String Phrase := do
  let some toks := lex [] (Codes.ofString s) | throw s!"cannot lex phrase {s}"
  let rec go : Nat → List PTok → Phrase → Except String Phrase
    | 0, _, _ => throw "phrase too long"
    | _ + 1, [], acc => pure acc.reverse
    | f + 1, t :: ts, acc =>
      match t.tok with
      | .word w => go f ts (.w (w.map fun x => if 65 ≤ x && x ≤ 90 then x + 32 else x) :: acc)
      | .mopen =>
        let body := ts.takeWhile (fun p => p.tok != .mclose)
        let rest := ts.drop (body.length + 1)
        match Math.simplify (body.length + 1) body with
        | some [.id [118]] => go f rest (.v :: acc)
        | some ms =>
          if ms.contains (.id [118]) then
            -- split at the arguments `v`
            let segs := ms.foldl (fun (acc : List (List MTok)) t =>
              if t == .id [118] then [] :: acc
              else match acc with
                | cur :: more => (cur ++ [t]) :: more
                | [] => [[t]]) [[]]
            go f rest (.f segs.reverse :: acc)
          else go f rest (.m ms :: acc)
        | none => throw s!"cannot read the formula in phrase {s}"
      | .punct 39 => go f ts acc
      | _ => throw s!"unexpected token in phrase {s}"
  go (toks.length + 1) toks []

syntax:max "phrase!" str : term

open Lean Elab Term Meta in
elab_rules : term
  | `(phrase! $s:str) => do
    match phraseOf s.getString with
    | .ok p => pure (toExpr p)
    | .error e => throwError e

/-! ## The core vocabulary

Real analysis on `[0,1]`: functions and maps with a signature, Borel
measurability and Lebesgue measure. -/

namespace Vocab

def core : Vocab where
  mods := [
    { phrase := phrase!"Borel measurable", prenominal := true, ty := Ty.self,
      pred := .lam Ty.self .tt (.app (.prim .borel) (.loc 0)),
      doc := "a Borel measurable map of `[0,1]` (Mathlib `Measurable`)" }]
  notions := [
    { name := phrase!"Lebesgue measure on $[0,1]$", value := .prim .leb, ty := Ty.set1 ⟶ .real,
      doc := "the Lebesgue measure of a subset of `[0,1]` (Mathlib `volume`)" }]

end Vocab

end Leanify
