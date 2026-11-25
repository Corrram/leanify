import Leanify.Library.Core

/-! # Vocabulary: summability methods and sequences

Summation methods for series that may diverge, and properties of sequences of real numbers
`a_0, a_1, …` (the values of a real function at the natural numbers, as in the field
`series`): `$a$ is Cesàro summable to $s$`, `the $n$th Cesàro mean of $a$`.

* adjectives of sequences: `Cesàro summable to $s$` (the means of the partial sums tend to
  `s`), `Abel summable to $s$` (`∑ a_k r^k → s` as `r → 1⁻`), `convergent to $l$` (`a_n → l`),
  `null` (`a_n → 0`), `eventually nondecreasing`, `of bounded
  variation` (`∑ |a_{k+1} - a_k| < ∞`), `Cauchy` (`|a_m - a_n| → 0`), `subadditive sequence`
  (`a_{m+n} ≤ a_m + a_n`, as in Fekete's lemma), `log-concave sequence` (`a_k² ≥ a_{k-1} a_{k+1}`);
* notions: the `n`th Cesàro mean of the partial sums, the `n`th arithmetic mean of the
  terms (`(a_0 + … + a_{n-1})/n`), the Abel sum, the `n`th forward difference
  (`Δ^n a_0 = ∑ (-1)^{n-k} \binom{n}{k} a_k`).

Every meaning is a term of the core language. -/

namespace Leanify.Summability
open Build Core

abbrev F : Ty := Ty.rfun

def nat (n : B) : B := and (isInt n) (le (num 0) n)
def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def finSum (a b : B) (body : B → B) : B := app (app (app (prim .finSum) a) b) (lamR body)
def zpow (x k : B) : B := app2 (prim .zpow) x k
def binom (n k : B) : B := app2 (prim .binom) n k
def partialSum (a n : B) : B := finSum (num 0) n fun k => app a k
/-- `σ_n = (s_0 + … + s_{n-1})/n`, the mean of the first `n` partial sums. -/
def cesaro (a n : B) : B := div (finSum (num 0) (sub n (num 1)) fun j => partialSum a j) n
def tendsTo (a l : B) : B :=
  allR fun e => imp (lt (num 0) e) (exR fun n0 => allR fun n => imp (and (nat n) (le n0 n)) (lt (abs (sub (app a n) l)) e))
def tendsToPos (a l : B) : B :=
  allR fun e => imp (lt (num 0) e) (exR fun n0 => allR fun n => imp (and (posInt n) (le n0 n)) (lt (abs (sub (app a n) l)) e))
def eventually (p : B → B) : B := exR fun n0 => allR fun n => imp (and (nat n) (le n0 n)) (p n)
def powerSum (a r : B) : B := app2 (prim .series) (num 0) (lamR fun k => mul (app a k) (zpow r k))
def powerConv (a r : B) : B := app2 (prim .seriesConv) (num 0) (lamR fun k => mul (app a k) (zpow r k))
def unitOpen : B := lamR fun r => and (lt (num 0) r) (lt r (num 1))
def abelSum (a : B) : B := app (app2 (prim .limAt) (num 1) unitOpen) (lamR fun r => powerSum a r)
def abel (a s : B) : B :=
  and (allR fun r => imp (and (lt (num 0) r) (lt r (num 1))) (powerConv a r))
    (and (app (app2 (prim .limAtConv) (num 1) unitOpen) (lamR fun r => powerSum a r)) (eq (abelSum a) s))
def fPred (p : B → B) : Tm := close <| lamT F (fun _ => tt) p
def adj (p : Phrase) (pre : Bool) (body : B → B) (doc : String) : Modifier :=
  { phrase := p, prenominal := pre, ty := F, pred := fPred body, doc }
def withArg (p : Phrase) (body : B → B → B) (doc : String) : Modifier :=
  { phrase := p, prenominal := false, ty := F, pred := close <| lamR fun s => lamT F (fun _ => tt) fun a => body s a, doc }

def vocab : Vocab where
  mods := [
    withArg phrase!"Cesàro summable to $v$" (fun s a => tendsToPos (lamR fun n => cesaro a n) s)
      "`(s_0 + … + s_{n-1})/n → s` for the partial sums `s_j = a_0 + … + a_j`",
    withArg phrase!"Cesaro summable to $v$" (fun s a => tendsToPos (lamR fun n => cesaro a n) s) "Cesàro summable",
    withArg phrase!"Abel summable to $v$" (fun s a => abel a s) "`∑ a_k r^k` converges for `0 < r < 1` and tends to `s` as `r → 1⁻`",
    withArg phrase!"convergent to $v$" (fun l a => tendsTo a l) "`a_n → l` (Mathlib `Filter.Tendsto`)",
    adj phrase!"null" true (fun a => tendsTo a (num 0)) "`a_n → 0`",
    adj phrase!"eventually nondecreasing" true (fun a => eventually fun n => le (app a n) (app a (add n (num 1))))
      "`a_n ≤ a_{n+1}` for all large `n`",
    adj phrase!"of bounded variation" false
      (fun a => app2 (prim .seriesConv) (num 0) (lamR fun k => abs (sub (app a (add k (num 1))) (app a k))))
      "`∑ |a_{k+1} - a_k|` converges",
    adj phrase!"Cauchy" true (fun a => allR fun e => imp (lt (num 0) e) (exR fun n0 => allR fun m => allR fun n =>
        imp (and (and (nat m) (nat n)) (and (le n0 m) (le n0 n))) (lt (abs (sub (app a m) (app a n))) e)))
      "`|a_m - a_n| < ε` for all large `m`, `n`",
    adj phrase!"subadditive sequence" false (fun a => allR fun m => allR fun n => imp (and (posInt m) (posInt n))
        (le (app a (add m n)) (add (app a m) (app a n))))
      "`a_{m+n} ≤ a_m + a_n` for `m, n ≥ 1` (Fekete)",
    adj phrase!"log-concave sequence" false (fun a => allR fun k => imp (posInt k)
        (le (mul (app a (sub k (num 1))) (app a (add k (num 1)))) (mul (app a k) (app a k))))
      "`a_{k-1} a_{k+1} ≤ a_k²` for `k ≥ 1`"]
  notions := [
    { name := phrase!"$v$th Cesàro mean of $v$", ty := .real ⟶ F ⟶ .real, doms := [dom1 .real posInt, none],
      doc := "`(s_0 + … + s_{n-1})/n` for the partial sums `s_j`",
      value := close <| lamT .real posInt fun n => lamT F (fun _ => tt) fun a => cesaro a n },
    { name := phrase!"$v$th arithmetic mean of the terms of $v$", ty := .real ⟶ F ⟶ .real, doms := [dom1 .real posInt, none],
      doc := "`(a_0 + … + a_{n-1})/n`",
      value := close <| lamT .real posInt fun n => lamT F (fun _ => tt) fun a => div (finSum (num 0) (sub n (num 1)) fun k => app a k) n },
    { name := phrase!"Abel sum of $v$", ty := F ⟶ .real, doms := [dom1 F fun a => exR fun s => abel a s],
      doc := "`lim_{r→1⁻} ∑ a_k r^k`, where it exists",
      value := close <| lamT F (fun a => exR fun s => abel a s) abelSum },
    { name := phrase!"$v$th forward difference of $v$ at $v$", ty := .real ⟶ F ⟶ .real ⟶ .real,
      doms := [dom1 .real nat, none, none],
      doc := "`Δ^n a_m = ∑_{k=0}^{n} (-1)^{n-k} \\binom{n}{k} a_{m+k}`",
      value := close <| lamT .real nat fun n => lamT F (fun _ => tt) fun a => lamR fun m =>
        finSum (num 0) n fun k => mul (mul (zpow (neg (num 1)) (sub n k)) (binom n k)) (app a (add m k)) }]

end Leanify.Summability
