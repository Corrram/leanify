import Leanify.Library.Core

/-! # Vocabulary: continued fractions and Diophantine approximation

The regular continued fraction of an irrational number `x`: its complete quotients
`x_0 = x`, `x_{k+1} = 1/(x_k - ⌊x_k⌋)`, partial quotients `a_k = ⌊x_k⌋` and convergents
`p_n/q_n` (`p_n = a_n p_{n-1} + p_{n-2}`, `q_n = a_n q_{n-1} + q_{n-2}`), the value of a finite
continued fraction `[a_0; a_1, …, a_n]`, and the classes of numbers of Diophantine
approximation (`We write $p_n/q_n$ …`, `Let $x$ be a badly approximable number.`).

* notions: the `n`th complete quotient, partial quotient and convergent of an irrational
  `x`; the numerator and the denominator of the `n`th convergent; the value of the
  continued fraction with partial quotients `a` up to `n` (with `a_k > 0` for `k ≥ 1`);
* adjectives of numbers: `badly approximable` (irrational, and `|x - p/q| ≥ c/q²` for some
  `c > 0`), `Liouville number` (irrational, and for every `n` some `p/q`, `q ≥ 2`, with
  `0 < |x - p/q| < q^{-n}`), `quadratic irrational` (an irrational root of `ax² + bx + c`
  with integers `a ≠ 0`, `b`, `c`), `best approximation of $x$` (a rational `p/q`, `q ≥ 1`,
  with `|qx - p| < |q'x - p'|` for every other `p'/q'` with `1 ≤ q' ≤ q`).

The sequences are existential witnesses of their recursions: each quantity is the unique
value they give, a term of the core language. -/

namespace Leanify.ContinuedFractions
open Build Core

abbrev F : Ty := Ty.rfun

def natP (k : B) : B := and (isInt k) (le (num 0) k)
def forNat (body : B → B) : B := allR fun k => imp (natP k) (body k)
def irrational (x : B) : B := not (exInt fun p => exInt fun q => and (ne q (num 0)) (eq x (div p q)))
def complete (x xs : B) : B :=
  and (eq (app xs (num 0)) x) (forNat fun k => eq (app xs (add k (num 1))) (div (num 1) (sub (app xs k) (floor (app xs k)))))
/-- `P`, `Q` are the numerators and denominators of the convergents of the quotients `a`. -/
def convs (a ps qs : B) : B :=
  and (and (eq (app ps (num 0)) (app a (num 0))) (eq (app qs (num 0)) (num 1)))
    (and (and (eq (app ps (num 1)) (add (mul (app a (num 1)) (app a (num 0))) (num 1))) (eq (app qs (num 1)) (app a (num 1))))
      (forNat fun k => and
        (eq (app ps (add k (num 2))) (add (mul (app a (add k (num 2))) (app ps (add k (num 1)))) (app ps k)))
        (eq (app qs (add k (num 2))) (add (mul (app a (add k (num 2))) (app qs (add k (num 1)))) (app qs k)))))
def quotientsOf (xs : B) : B := lamR fun k => floor (app xs k)
/-- The value `v` that the sequences of `x` give at `n`, by `pick xs ps qs`. -/
def ofX (x : B) (pick : B → B → B → B) : B :=
  theR fun v => exT F fun xs => exT F fun ps => exT F fun qs =>
    and (complete x xs) (and (convs (quotientsOf xs) ps qs) (eq (pick xs ps qs) v))
def posQuotients (a n : B) : B := allR fun k => imp (and (isInt k) (and (le (num 1) k) (le k n))) (lt (num 0) (app a k))
def ofA (a : B) (pick : B → B → B) : B :=
  theR fun v => exT F fun ps => exT F fun qs => and (convs a ps qs) (eq (pick ps qs) v)
def rpow (x y : B) : B := app2 (prim .rpow) x y
def ofNx (name : Phrase) (pick : B → B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real natP, dom1 .real irrational], doc,
    value := close <| lamT .real natP fun n => lamT .real irrational fun x => ofX x (pick n) }

def liouville : Tm := predR fun x => and (irrational x) (allR fun n => imp (natP n) (exInt fun p => exInt fun q =>
  and (le (num 2) q) (and (lt (num 0) (abs (sub x (div p q)))) (lt (abs (sub x (div p q))) (div (num 1) (rpow q n))))))
def quadIrr : Tm := predR fun x => and (irrational x) (exInt fun a => exInt fun b => exInt fun c =>
  and (ne a (num 0)) (eq (add (add (mul a (mul x x)) (mul b x)) c) (num 0)))

def vocab : Vocab where
  nouns := [
    noun phrase!"Liouville number" phrase!"Liouville numbers" liouville "a Liouville number (as the adjective)",
    noun phrase!"quadratic irrational" phrase!"quadratic irrationals" quadIrr "a quadratic irrational (as the adjective)"]
  mods := [
    { phrase := phrase!"badly approximable", prenominal := true, ty := .real,
      pred := predR fun x => and (irrational x) (exR fun c => and (lt (num 0) c)
        (allInt fun p => allInt fun q => imp (le (num 1) q) (le (div c (mul q q)) (abs (sub x (div p q)))))),
      doc := "irrational, and `|x - p/q| ≥ c/q²` for all integers `p`, `q ≥ 1`, for some `c > 0`" },
    { phrase := phrase!"Liouville number", prenominal := false, ty := .real,
      pred := liouville,
      doc := "irrational, and for every `n` there are `p`, `q ≥ 2` with `0 < |x - p/q| < q^{-n}` (Mathlib `Liouville`)" },
    { phrase := phrase!"quadratic irrational", prenominal := false, ty := .real,
      pred := quadIrr,
      doc := "irrational, and `ax² + bx + c = 0` for integers `a ≠ 0`, `b`, `c`" },
    { phrase := phrase!"best approximation of $v$", prenominal := false, ty := .real,
      pred := close <| lamR fun x => lamR fun r => exInt fun p => exInt fun q => and (le (num 1) q) (and (eq r (div p q))
        (allInt fun p' => allInt fun q' => imp (and (le (num 1) q') (and (le q' q) (ne (div p' q') r)))
          (lt (abs (sub (mul q x) p)) (abs (sub (mul q' x) p'))))),
      doc := "a rational `p/q`, `q ≥ 1`, with `|qx - p| < |q'x - p'|` for every other `p'/q'` with `1 ≤ q' ≤ q` (of the second kind)" }]
  notions := [
    ofNx phrase!"$v$th complete quotient of $v$" (fun n xs _ _ => app xs n) "`x_n`: `x_0 = x`, `x_{k+1} = 1/(x_k - ⌊x_k⌋)`, of an irrational `x`",
    ofNx phrase!"$v$th partial quotient of $v$" (fun n xs _ _ => floor (app xs n)) "`a_n = ⌊x_n⌋`, of an irrational `x`",
    ofNx phrase!"$v$th convergent of $v$" (fun n _ ps qs => div (app ps n) (app qs n)) "`p_n/q_n`, of an irrational `x`",
    ofNx phrase!"numerator of the $v$th convergent of $v$" (fun n _ ps _ => app ps n) "`p_n`",
    ofNx phrase!"denominator of the $v$th convergent of $v$" (fun n _ _ qs => app qs n) "`q_n`",
    { name := phrase!"value of the continued fraction with partial quotients $v$ up to $v$", ty := F ⟶ .real ⟶ .real,
      doms := [none, dom2 .real fun a n => and (natP n) (posQuotients a n)],
      doc := "`[a_0; a_1, …, a_n] = p_n/q_n`, for `a_k > 0` (`1 ≤ k ≤ n`)",
      value := close <| lamT F (fun _ => tt) fun a => lamT .real (fun n => and (natP n) (posQuotients a n)) fun n =>
        ofA a fun ps qs => div (app ps n) (app qs n) }]

end Leanify.ContinuedFractions
