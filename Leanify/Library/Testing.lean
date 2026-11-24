import Leanify.Library.Core

/-! # Vocabulary: tests and confidence intervals

The statistics of the classical tests for a sample `x_1, …, x_n` (the first `n` terms of a
sequence, as in the field `samples`), their p-values, and the quantiles they use.

* notions: the z-statistic of the first `n` terms for the mean `μ₀` and the standard
  deviation `σ > 0` (`√n (x̄ - μ₀)/σ`), the t-statistic for the mean `μ₀` (`√n (x̄ - μ₀)/s`,
  `n ≥ 2`, the terms not all equal), the one-sided and two-sided p-values of a z value
  (`1 - Φ(z)`, `2(1 - Φ(|z|))`), the standard normal quantile of order `α ∈ (0,1)`, the
  margin of error at confidence level `γ` for `n` observations with standard deviation `σ`
  (`z_{(1+γ)/2} σ/√n`), and Pearson's chi-squared statistic of observed counts `o` against
  expected counts `e` over `k` cells (`∑ (o_i - e_i)²/e_i`, `e_i > 0`).

`Φ` is the standard normal distribution function, `∫_{-∞}^x e^{-t²/2}/√(2π) dt`. Every
meaning is a term of the core language; a quantile is a description, defined for every
order in `(0,1)`. -/

namespace Leanify.Testing
open Build Core

abbrev F : Ty := Ty.rfun

def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def atLeast2 (n : B) : B := and (isInt n) (le (num 2) n)
def finSum (a b : B) (body : B → B) : B := app (app (app (prim .finSum) a) b) (lamR body)
def sqrt (x : B) : B := app2 (prim .rpow) x (div (num 1) (num 2))
def exp (x : B) : B := app (prim (.realFn .exp)) x
def pi : B := prim .pi
def phi (x : B) : B :=
  app2 (prim .integralOn) (lamR fun t => le t x) (lamR fun t => div (exp (neg (div (mul t t) (num 2)))) (sqrt (mul (num 2) pi)))
def mean (n x : B) : B := div (finSum (num 1) n fun i => app x i) n
def ssq (n x : B) : B := finSum (num 1) n fun i => mul (sub (app x i) (mean n x)) (sub (app x i) (mean n x))
def sdev (n x : B) : B := sqrt (div (ssq n x) (sub n (num 1)))
def level (a : B) : B := and (lt (num 0) a) (lt a (num 1))
def quantile (a : B) : B := theR fun q => eq (phi q) a

def vocab : Vocab where
  notions := [
    { name := phrase!"z-statistic of the first $v$ terms of $v$ for the mean $v$ and the standard deviation $v$",
      ty := .real ⟶ F ⟶ .real ⟶ .real ⟶ .real, doms := [dom1 .real posInt, none, none, dom1 .real fun s => lt (num 0) s],
      doc := "`√n (x̄ - μ₀)/σ`, `σ > 0`",
      value := close <| lamT .real posInt fun n => lamT F (fun _ => tt) fun x => lamR fun m =>
        lamT .real (fun s => lt (num 0) s) fun s => div (mul (sqrt n) (sub (mean n x) m)) s },
    { name := phrase!"t-statistic of the first $v$ terms of $v$ for the mean $v$", ty := .real ⟶ F ⟶ .real ⟶ .real,
      doms := [dom1 .real atLeast2, dom2 F fun n x => ne (ssq n x) (num 0), none],
      doc := "`√n (x̄ - μ₀)/s` with the sample standard deviation `s`, where the terms are not all equal",
      value := close <| lamT .real atLeast2 fun n => lamT F (fun x => ne (ssq n x) (num 0)) fun x => lamR fun m =>
        div (mul (sqrt n) (sub (mean n x) m)) (sdev n x) },
    { name := phrase!"one-sided p-value of $v$", ty := .real ⟶ .real, doc := "`1 - Φ(z)`",
      value := close <| lamR fun z => sub (num 1) (phi z) },
    { name := phrase!"two-sided p-value of $v$", ty := .real ⟶ .real, doc := "`2(1 - Φ(|z|))`",
      value := close <| lamR fun z => mul (num 2) (sub (num 1) (phi (abs z))) },
    { name := phrase!"standard normal quantile of order $v$", ty := .real ⟶ .real, doms := [dom1 .real level],
      doc := "the `z` with `Φ(z) = α`, `0 < α < 1`",
      value := close <| lamT .real level quantile },
    { name := phrase!"margin of error at confidence level $v$ for $v$ observations with standard deviation $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real, doms := [dom1 .real level, dom1 .real posInt, dom1 .real fun s => lt (num 0) s],
      doc := "`z_{(1+γ)/2} σ/√n`",
      value := close <| lamT .real level fun g => lamT .real posInt fun n => lamT .real (fun s => lt (num 0) s) fun s =>
        div (mul (quantile (div (add (num 1) g) (num 2))) s) (sqrt n) },
    { name := phrase!"chi-squared statistic of $v$ against $v$ over $v$ cells", ty := F ⟶ F ⟶ .real ⟶ .real,
      doms := [none, none, dom3 .real fun _ e k => and (posInt k) (allR fun i => imp (and (isInt i) (and (le (num 1) i) (le i k))) (lt (num 0) (app e i)))],
      doc := "`∑_{i=1}^{k} (o_i - e_i)²/e_i`, `e_i > 0` (Pearson)",
      value := close <| lamT F (fun _ => tt) fun o => lamT F (fun _ => tt) fun e =>
        lamT .real (fun k => and (posInt k) (allR fun i => imp (and (isInt i) (and (le (num 1) i) (le i k))) (lt (num 0) (app e i)))) fun k =>
          finSum (num 1) k fun i => cases (lt (num 0) (app e i)) (div (mul (sub (app o i) (app e i)) (sub (app o i) (app e i))) (app e i)) (num 0) }]

end Leanify.Testing
