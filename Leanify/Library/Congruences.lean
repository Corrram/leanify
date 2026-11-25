import Leanify.Library.Arithmetic

/-! # Vocabulary: congruences

Arithmetic modulo `n`: congruent and coprime integers, units, quadratic residues and the
Legendre symbol, primitive roots, and inverses modulo `n`.

* adjectives, each with its numbers: `congruent to $b$ modulo $n$`, `coprime to $n$`,
  `divisible by $d$`, `invertible modulo $n$`, `quadratic residue modulo $n$`,
  `quadratic nonresidue modulo $n$`, `primitive root modulo $n$` (`$a$ is congruent
  to $b$ modulo $n$`, `every integer $a$ coprime to $n$`);
* notions: the Legendre symbol, the inverse of `a` modulo `n`, the least primitive root
  modulo `n`, the numbers of quadratic residues and of primitive roots modulo `n`, and the
  set of units modulo `n`.

Congruence, coprimality and divisibility are terms of the core language; the others are
constants, interpreted by `Leanify/Library/CongruencesModel.lean` through Mathlib's
`ZMod n`. Primes and the greatest common divisor are in the field `numbers`, Euler's
totient function and multiplicative orders in `arithmetic`. -/

namespace Leanify.Congruences
open Build Core

/-- The constants, in the order of their indices: `(type, TeX name, Lean name)`. -/
def table : List (Ty × Codes × Codes) := [
  (.real ⟶ .real ⟶ .real, w!"\\left(\\frac{#1}{#2}\\right)", w!"Leanify.Congruences.legendre"),       -- 0
  (.real ⟶ .real ⟶ .prop, w!"\\operatorname{QR}_{#2}(#1)", w!"Leanify.Congruences.QuadraticResidue"), -- 1
  (.real ⟶ .real ⟶ .prop, w!"\\operatorname{PrimitiveRoot}_{#2}(#1)", w!"Leanify.Congruences.PrimitiveRoot"), -- 2
  (.real ⟶ .real ⟶ .real, w!"#1^{-1}\\bmod #2", w!"Leanify.Congruences.inverse"),                     -- 3
  (.real ⟶ .real, w!"\\operatorname{g}", w!"Leanify.Congruences.leastPrimitiveRoot"),                 -- 4
  (.real ⟶ .real, w!"\\operatorname{\\#QR}", w!"Leanify.Congruences.numResidues"),                    -- 5
  (.real ⟶ .real, w!"\\operatorname{\\#PR}", w!"Leanify.Congruences.numPrimitiveRoots"),              -- 6
  (.real ⟶ .prop, w!"\\operatorname{HasPrimitiveRoot}", w!"Leanify.Congruences.HasPrimitiveRoot")]    -- 7

def posInt' (n : B) : B := and (isInt n) (lt (num 0) n)
def coprime := Arithmetic.coprime
/-- `n ∣ a - b`. -/
def congruent (a b n : B) : B := and (and (isInt a) (isInt b)) (and (posInt' n) (divides n (sub a b)))

/-- A property of an integer with a modulus (`P n a`, the modulus first). -/
def modN (p : Phrase) (body : B → B → B) (doc : String) : Modifier :=
  { phrase := p, prenominal := false, ty := .real, doc, pred := close <| lamR fun n => lamR fun a => body n a }

def unit (n a : B) : B := and (and (isInt a) (posInt' n)) (coprime a n)
def qr (n a : B) : B := and (unit n a) (app2 (const 1) a n)
def odd (p : B) : B := and (Numbers.isPrime p) (lt (num 2) p)

def vocab : Vocab where
  consts := table.map (·.1)
  constNames := table.map (·.2.1)
  constLean := table.map (·.2.2)
  modules := [w!"Leanify.Library.CongruencesModel"]
  mods := [
    { phrase := phrase!"congruent to $v$ modulo $v$", prenominal := false, ty := .real,
      pred := close <| lamR fun b => lamR fun n => lamR fun a => congruent a b n,
      doc := "`n ∣ a - b`, for integers `a`, `b` and `n ≥ 1` (Mathlib `Int.ModEq`)" },
    modN phrase!"coprime to $v$" (fun n a => and (and (isInt a) (isInt n)) (coprime a n)) "no common divisor but `±1` (Mathlib `IsCoprime`)",
    modN phrase!"relatively prime to $v$" (fun n a => and (and (isInt a) (isInt n)) (coprime a n)) "(Mathlib `IsCoprime`)",
    modN phrase!"divisible by $v$" (fun n a => and (and (isInt a) (isInt n)) (divides n a)) "`d ∣ a`",
    modN phrase!"not divisible by $v$" (fun n a => and (and (isInt a) (isInt n)) (not (divides n a))) "`d ∤ a`",
    modN phrase!"invertible modulo $v$" unit "coprime to `n ≥ 1` (Mathlib `IsUnit` in `ZMod n`)",
    modN phrase!"unit modulo $v$" unit "coprime to `n ≥ 1` (Mathlib `IsUnit` in `ZMod n`)",
    modN phrase!"quadratic residue modulo $v$" qr "coprime to `n`, and a square modulo `n` (Mathlib `IsSquare` in `ZMod n`)",
    modN phrase!"quadratic nonresidue modulo $v$" (fun n a => and (unit n a) (not (app2 (const 1) a n)))
      "coprime to `n`, and not a square modulo `n`",
    modN phrase!"primitive root modulo $v$" (fun n a => and (unit n a) (app2 (const 2) a n))
      "its powers are all units modulo `n` (Mathlib `orderOf` in `ZMod n` is `φ(n)`)"]
  notions := [
    { name := phrase!"Legendre symbol of $v$ modulo $v$", ty := .real ⟶ .real ⟶ .real,
      doc := "`1`, `-1` or `0`, for an integer `a` and an odd prime `p` (Mathlib `legendreSym`)",
      value := close <| lamR fun a => lamR fun p => guard (and (isInt a) (odd p)) (app2 (const 0) a p) },
    { name := phrase!"inverse of $v$ modulo $v$", ty := .real ⟶ .real ⟶ .real,
      doc := "the `b` in `[0, n)` with `ab ≡ 1`, for `a` coprime to `n ≥ 1` (Mathlib `ZMod.inv`)",
      value := close <| lamR fun a => lamR fun n => guard (unit n a) (app2 (const 3) a n) },
    { name := phrase!"least primitive root modulo $v$", ty := .real ⟶ .real,
      doc := "for a modulus that has a primitive root",
      value := close <| lamR fun n => guard (and (posInt' n) (app (const 7) n)) (app (const 4) n) },
    { name := phrase!"number of quadratic residues modulo $v$", value := .const 5, ty := .real ⟶ .real,
      doms := [some posInt], doc := "among the units modulo `n`" },
    { name := phrase!"number of primitive roots modulo $v$", value := .const 6, ty := .real ⟶ .real,
      doms := [some posInt], doc := "in `[0, n)`" },
    { name := phrase!"set of units modulo $v$", ty := .real ⟶ .real ⟶ .prop, doms := [some posInt],
      value := close <| lamR fun n => lamR fun a => and (and (le (num 0) a) (lt a n)) (unit n a),
      doc := "the integers in `[0, n)` coprime to `n` (Mathlib `(ZMod n)ˣ`)" }]

end Leanify.Congruences
