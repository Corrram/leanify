import Leanify.Library.Core

/-! # Vocabulary: sequences and series of real numbers

The terms of a sequence or a series are the values at the natural numbers of a real
function (`a(k)`, as in the core's `\sum_{k=0}^{\infty}` and `\lim_{n\to\infty}`), so that
an article writes `Let $a:\mathbb{R}\to\mathbb{R}$ be a function.` and speaks of the
series with terms `a`.

* adjectives of a sequence of terms: `summable` (`∑ a_k` converges), `absolutely summable`,
  `conditionally summable`, `square-summable`, `alternating`;
* notions: the sum of the series with terms `a` (where it converges), its `n`th partial
  sum, the Cauchy product of two sequences, the sum of the power series with coefficients
  `a` at `x` (where it converges) and its radius of convergence (where it is finite), the
  sums of the geometric series, and the limit, the limit superior and the limit inferior of
  a sequence (where they exist).

Every meaning is a term of the core language: a series is the limit of its partial sums
(`series`, `seriesConv`), and a limit of a sequence is a description, defined where it
exists. -/

namespace Leanify.Series
open Build Core

abbrev F : Ty := Ty.rfun

def nat (n : B) : B := and (isInt n) (le (num 0) n)
def converges (a : B) : B := app2 (prim .seriesConv) (num 0) a
def sum (a : B) : B := app2 (prim .series) (num 0) a
def finSum (a b : B) (body : B → B) : B := app (app (app (prim .finSum) a) b) (lamR body)
def zpow (x k : B) : B := app2 (prim .zpow) x k
def absTerms (a : B) : B := lamR fun k => abs (app a k)
def powTerms (a x : B) : B := lamR fun k => mul (app a k) (zpow x k)
/-- `a_n → l` over the natural numbers. -/
def tendsTo (a l : B) : B :=
  allR fun e => imp (lt (num 0) e) (exR fun n0 => allR fun n => imp (and (nat n) (le n0 n)) (lt (abs (sub (app a n) l)) e))
/-- `l` is the limit superior: for every `ε > 0`, `a_n < l + ε` eventually and `a_n > l - ε`
infinitely often. -/
def isLimsup (a l : B) : B :=
  allR fun e => imp (lt (num 0) e)
    (and (exR fun n0 => allR fun n => imp (and (nat n) (le n0 n)) (lt (app a n) (add l e)))
      (allR fun n0 => exR fun n => and (and (nat n) (le n0 n)) (lt (sub l e) (app a n))))
def isLiminf (a l : B) : B :=
  allR fun e => imp (lt (num 0) e)
    (and (exR fun n0 => allR fun n => imp (and (nat n) (le n0 n)) (lt (sub l e) (app a n)))
      (allR fun n0 => exR fun n => and (and (nat n) (le n0 n)) (lt (app a n) (add l e))))
def exUnique (p : B → B) : B := exR fun m => and (p m) (allR fun m' => imp (p m') (eq m' m))
/-- The terms `a_k s^k` are bounded. -/
def boundedAt (a s : B) : B := exR fun m => allR fun k => imp (nat k) (le (abs (mul (app a k) (zpow s k))) m)
/-- `r ≥ 0` separates the radii where the terms are bounded from those where they are not. -/
def isRadius (a r : B) : B :=
  and (le (num 0) r) (and (allR fun s => imp (and (le (num 0) s) (lt s r)) (boundedAt a s))
    (allR fun s => imp (lt r s) (not (boundedAt a s))))

def fPred (p : B → B) : Tm := close <| lamT F (fun _ => tt) p
def adj (p : Phrase) (pre : Bool) (body : B → B) (doc : String) : Modifier :=
  { phrase := p, prenominal := pre, ty := F, pred := fPred body, doc }
/-- A notion of a sequence, defined where `d` holds. -/
def ofSeq (name : Phrase) (d : B → B) (body : B → B) (doc : String) : Notion :=
  { name, ty := F ⟶ .real, doms := [dom1 F d], doc, value := close <| lamT F d body }

/-- A sequence of real numbers: a real function whose values at the natural numbers are its
terms, `0` elsewhere (so that its supremum, boundedness and limit are those of its terms). -/
def seqPred (p : Option (B → B)) : Tm := close <| lamT F (fun _ => tt) fun a =>
  let zero := allR fun x => imp (not (nat x)) (eq (app a x) (num 0))
  match p with
  | some p => and zero (allR fun n => imp (nat n) (p (app a n)))
  | none => zero

def seqNoun (sing plural : Phrase) (p : Option (B → B)) (doc : String) : Noun :=
  { sing, plural, ty := F, pred := seqPred p, doc, seq := true }

def vocab : Vocab where
  nouns := [
    seqNoun phrase!"sequence of real numbers" phrase!"sequences of real numbers" none
      "`a_0, a_1, …`: a function of the natural numbers (Mathlib `ℕ → ℝ`)",
    seqNoun phrase!"real sequence" phrase!"real sequences" none "(Mathlib `ℕ → ℝ`)",
    seqNoun phrase!"sequence" phrase!"sequences" none "a sequence of real numbers (Mathlib `ℕ → ℝ`)",
    seqNoun phrase!"sequence of positive real numbers" phrase!"sequences of positive real numbers" (some fun x => lt (num 0) x)
      "`a_n > 0`",
    seqNoun phrase!"sequence of nonnegative real numbers" phrase!"sequences of nonnegative real numbers" (some fun x => le (num 0) x)
      "`a_n ≥ 0`",
    seqNoun phrase!"sequence of integers" phrase!"sequences of integers" (some fun x => isInt x) "(Mathlib `ℕ → ℤ`)",
    { seqNoun phrase!"subsequence" phrase!"subsequences" none
        "`n ↦ a_{φ(n)}` for a strictly increasing `φ : ℕ → ℕ` (Mathlib `StrictMono`, `a ∘ φ`)" with
      arg := some ([w!"of"], F, close <| lamT F (fun _ => tt) fun a => lamT F (fun _ => tt) fun b =>
        exT F fun p => and (allR fun n => imp (nat n) (nat (app p n)))
          (and (allR fun n => imp (nat n) (lt (app p n) (app p (add n (num 1)))))
            (allR fun n => imp (nat n) (eq (app b n) (app a (app p n)))))) }]
  mods := [
    { phrase := phrase!"converging to $v$", prenominal := false, ty := F,
      pred := close <| lamR fun l => lamT F (fun _ => tt) fun a => tendsTo a l, doc := "`a_n → l` (Mathlib `Filter.Tendsto`)" },
    { phrase := phrase!"convergent", prenominal := true, ty := F,
      pred := close <| lamT F (fun _ => tt) fun a => exR fun l => tendsTo a l, doc := "`a_n → l` for some `l`" },
    { phrase := phrase!"divergent", prenominal := true, ty := F,
      pred := close <| lamT F (fun _ => tt) fun a => not (exR fun l => tendsTo a l), doc := "convergent to no number" },
    -- (Bolzano–Weierstrass: `$(a_n)$ has a convergent subsequence`)
    adj phrase!"with a convergent subsequence" false (fun a => exT F fun p =>
        and (allR fun n => imp (nat n) (nat (app p n)))
          (and (allR fun n => imp (nat n) (lt (app p n) (app p (add n (num 1)))))
            (exR fun l => tendsTo (lamR fun n => app a (app p n)) l)))
      "`a_{φ(n)} → l` for some strictly increasing `φ : ℕ → ℕ` and some `l`",
    adj phrase!"summable" true converges "`∑_{k=0}^∞ a_k` converges (Mathlib `Summable`, for absolute summability)",
    adj phrase!"absolutely summable" true (fun a => converges (absTerms a)) "`∑ |a_k|` converges (Mathlib `Summable`)",
    adj phrase!"conditionally summable" true (fun a => and (converges a) (not (converges (absTerms a))))
      "`∑ a_k` converges, `∑ |a_k|` does not",
    adj phrase!"square-summable" true (fun a => converges (lamR fun k => mul (app a k) (app a k)))
      "`∑ a_k²` converges (`ℓ²`)",
    adj phrase!"alternating" true (fun a => allR fun k => imp (nat k) (le (mul (app a k) (app a (add k (num 1)))) (num 0)))
      "consecutive terms have opposite signs or vanish: `a_k a_{k+1} ≤ 0`"]
  notions := [
    ofSeq phrase!"sum of the series with terms $v$" converges sum "`∑_{k=0}^∞ a_k`, where it converges (Mathlib `tsum`)",
    { name := phrase!"$v$th partial sum of the series with terms $v$", ty := .real ⟶ F ⟶ .real,
      doms := [dom1 .real nat, none], doc := "`∑_{k=0}^{n} a_k`",
      value := close <| lamT .real nat fun n => lamT F (fun _ => tt) fun a => finSum (num 0) n fun k => app a k },
    { name := phrase!"Cauchy product of $v$ and $v$", ty := F ⟶ F ⟶ F, doc := "`n ↦ ∑_{k=0}^{n} a_k b_{n-k}`",
      value := close <| lamT F (fun _ => tt) fun a => lamT F (fun _ => tt) fun b => lamR fun n =>
        finSum (num 0) n fun k => mul (app a k) (app b (sub n k)) },
    { name := phrase!"sum of the power series with coefficients $v$ at $v$", ty := F ⟶ .real ⟶ .real,
      doms := [none, dom2 .real fun a x => converges (powTerms a x)],
      doc := "`∑_{k=0}^∞ a_k x^k`, where it converges (Mathlib `FormalMultilinearSeries.sum`)",
      value := close <| lamT F (fun _ => tt) fun a => lamT .real (fun x => converges (powTerms a x)) fun x => sum (powTerms a x) },
    ofSeq phrase!"radius of convergence of the power series with coefficients $v$"
      (fun a => exUnique fun r => isRadius a r) (fun a => theR fun r => isRadius a r)
      "the `R ≥ 0` with `a_k s^k` bounded for `s < R` and unbounded for `s > R`, where it is finite (Mathlib `FormalMultilinearSeries.radius`)",
    { name := phrase!"sum of the geometric series with ratio $v$", ty := .real ⟶ .real,
      doms := [dom1 .real fun q => lt (abs q) (num 1)], doc := "`1/(1-q)`, `|q| < 1`",
      value := close <| lamT .real (fun q => lt (abs q) (num 1)) fun q => div (num 1) (sub (num 1) q) },
    { name := phrase!"sum of the geometric series with first term $v$ and ratio $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [none, dom1 .real fun q => lt (abs q) (num 1)], doc := "`a/(1-q)`, `|q| < 1`",
      value := close <| lamR fun a => lamT .real (fun q => lt (abs q) (num 1)) fun q => div a (sub (num 1) q) },
    ofSeq phrase!"limit of the sequence $v$" (fun a => exR fun l => tendsTo a l) (fun a => theR fun l => tendsTo a l)
      "`lim_{n→∞} a_n`, where the sequence converges (Mathlib `Filter.Tendsto … atTop`)",
    ofSeq phrase!"limit superior of the sequence $v$" (fun a => exUnique fun l => isLimsup a l) (fun a => theR fun l => isLimsup a l)
      "`limsup a_n`, where it is finite (Mathlib `Filter.limsup`)",
    ofSeq phrase!"limit inferior of the sequence $v$" (fun a => exUnique fun l => isLiminf a l) (fun a => theR fun l => isLiminf a l)
      "`liminf a_n`, where it is finite (Mathlib `Filter.liminf`)"]

end Leanify.Series
