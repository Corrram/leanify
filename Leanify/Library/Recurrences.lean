import Leanify.Library.Core

/-! # Vocabulary: progressions and recurrences

Sequences defined by a recurrence, with their terms as the values of a real function at
the natural numbers (`a(n)`, as in the fields `series` and `iteration`): arithmetic and
geometric progressions, the Fibonacci recurrence, linear recurrences of order two, and the
closed forms of the progressions.

* adjectives of sequences: `arithmetic progression with difference $d$`
  (`a(n+1) = a(n) + d`), `geometric progression with ratio $q$` (`a(n+1) = q a(n)`),
  `arithmetic progression`, `geometric progression`, `satisfying the Fibonacci recurrence`
  (`a(n+2) = a(n+1) + a(n)`, also `solution of the Fibonacci recurrence`), `solution of
  the linear recurrence with coefficients $p$ and $q$` (`a(n+2) = p a(n+1) + q a(n)`);
* notions: the `n`th term and the sum of the first `n` terms of the arithmetic progression
  with first term `a` and difference `d`, and of the geometric progression with first term
  `a` and ratio `q` (the sums `∑_{k=0}^{n-1}` of the terms); the larger and the smaller real
  root of the characteristic polynomial `x² - px - q` (where it has one). The closed forms of
  the sums (`n a + n(n-1)d/2`, `a(1 - qⁿ)/(1 - q)` for `q ≠ 1`) and of the roots
  (`(p ± √(p² + 4q))/2`) are theorems, not definitions.

Every meaning is a term of the core language. -/

namespace Leanify.Recurrences
open Build Core

abbrev F : Ty := Ty.rfun

def nat (n : B) : B := and (isInt n) (le (num 0) n)
def posInt (n : B) : B := and (isInt n) (lt (num 0) n)
def forNat (body : B → B) : B := allR fun n => imp (nat n) (body n)
def zpow (x k : B) : B := app2 (prim .zpow) x k
def sqrt (x : B) : B := app2 (prim .rpow) x (div (num 1) (num 2))
def at1 (a n : B) : B := app a (add n (num 1))
def at2 (a n : B) : B := app a (add n (num 2))
def arith (d a : B) : B := forNat fun n => eq (at1 a n) (add (app a n) d)
def geom (q a : B) : B := forNat fun n => eq (at1 a n) (mul q (app a n))
def disc (p q : B) : B := add (mul p p) (mul (num 4) q)
def finSum (a b : B) (body : B → B) : B := app (app (app (prim .finSum) a) b) (lamR body)
/-- `x` is a root of the characteristic polynomial `x² - px - q`. -/
def charRoot (p q x : B) : B := eq (mul x x) (add (mul p x) q)
def hasCharRoot (p q : B) : B := exR fun x => charRoot p q x

/-- A property of a sequence with an argument (`P v a`). -/
def withArg (p : Phrase) (body : B → B → B) (doc : String) : Modifier :=
  { phrase := p, prenominal := false, ty := F, doc, pred := close <| lamR fun v => lamT F (fun _ => tt) fun a => body v a }
def plain (p : Phrase) (pre : Bool) (body : B → B) (doc : String) : Modifier :=
  { phrase := p, prenominal := pre, ty := F, doc, pred := close <| lamT F (fun _ => tt) body }

def vocab : Vocab where
  mods := [
    withArg phrase!"arithmetic progression with difference $v$" arith "`a(n+1) = a(n) + d` for every `n ≥ 0`",
    withArg phrase!"geometric progression with ratio $v$" geom "`a(n+1) = q a(n)` for every `n ≥ 0`",
    plain phrase!"arithmetic progression" false (fun a => exR fun d => arith d a) "with some difference",
    plain phrase!"geometric progression" false (fun a => exR fun q => geom q a) "with some ratio",
    plain phrase!"satisfying the Fibonacci recurrence" false (fun a => forNat fun n => eq (at2 a n) (add (at1 a n) (app a n)))
      "`a(n+2) = a(n+1) + a(n)`",
    plain phrase!"solution of the Fibonacci recurrence" false (fun a => forNat fun n => eq (at2 a n) (add (at1 a n) (app a n)))
      "`a(n+2) = a(n+1) + a(n)`",
    { phrase := phrase!"solution of the linear recurrence with coefficients $v$ and $v$", prenominal := false, ty := F,
      pred := close <| lamR fun p => lamR fun q => lamT F (fun _ => tt) fun a =>
        forNat fun n => eq (at2 a n) (add (mul p (at1 a n)) (mul q (app a n))),
      doc := "`a(n+2) = p a(n+1) + q a(n)`" }]
  notions := [
    { name := phrase!"$v$th term of the arithmetic progression with first term $v$ and difference $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real, doms := [dom1 .real nat], doc := "`a + nd`",
      value := close <| lamT .real nat fun n => lamR fun a => lamR fun d => add a (mul n d) },
    { name := phrase!"sum of the first $v$ terms of the arithmetic progression with first term $v$ and difference $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real, doms := [dom1 .real nat], doc := "`∑_{k=0}^{n-1} (a + kd)` (`n a + n(n-1)d/2`)",
      value := close <| lamT .real nat fun n => lamR fun a => lamR fun d =>
        finSum (num 0) (sub n (num 1)) fun k => add a (mul k d) },
    { name := phrase!"$v$th term of the geometric progression with first term $v$ and ratio $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real, doms := [dom1 .real nat], doc := "`a qⁿ`",
      value := close <| lamT .real nat fun n => lamR fun a => lamR fun q => mul a (zpow q n) },
    { name := phrase!"sum of the first $v$ terms of the geometric progression with first term $v$ and ratio $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real, doms := [dom1 .real nat],
      doc := "`∑_{k=0}^{n-1} a q^k` (`a(1 - qⁿ)/(1 - q)` for `q ≠ 1`)",
      value := close <| lamT .real nat fun n => lamR fun a => lamR fun q =>
        finSum (num 0) (sub n (num 1)) fun k => mul a (zpow q k) },
    { name := phrase!"larger characteristic root of the recurrence with coefficients $v$ and $v$",
      ty := .real ⟶ .real ⟶ .real, doms := [none, dom2 .real fun p q => hasCharRoot p q],
      doc := "the greatest real root of `x² - px - q`, where it has one (`(p + √(p² + 4q))/2`)",
      value := close <| lamR fun p => lamT .real (fun q => hasCharRoot p q) fun q =>
        theR fun x => and (charRoot p q x) (allR fun y => imp (charRoot p q y) (le y x)) },
    { name := phrase!"smaller characteristic root of the recurrence with coefficients $v$ and $v$",
      ty := .real ⟶ .real ⟶ .real, doms := [none, dom2 .real fun p q => hasCharRoot p q],
      doc := "the least real root of `x² - px - q`, where it has one (`(p - √(p² + 4q))/2`)",
      value := close <| lamR fun p => lamT .real (fun q => hasCharRoot p q) fun q =>
        theR fun x => and (charRoot p q x) (allR fun y => imp (charRoot p q y) (le x y)) }]

end Leanify.Recurrences
