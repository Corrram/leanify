import Leanify.Library.Core

/-! # Vocabulary: actuarial mathematics

Survival models and the present values of life contingencies under a constant force of
interest `δ` (`We write $\bar A_x$ for the net single premium of a whole life insurance
with force of mortality $\mu$ and force of interest $\delta$.`).

* notions: the survival function of the Gompertz law with parameters `B` and `c`
  (`t ↦ exp(-B(c^t - 1)/log c)`) and of the Gompertz–Makeham law (with `A`, `+ At`), the force of
  mortality of the Gompertz law (`B c^t`); under a constant force of mortality `μ`: the life
  expectancy `1/μ`, the net single premium of a whole life insurance `μ/(μ+δ)` and of a
  continuous whole life annuity `1/(μ+δ)`; the present value of a continuous annuity-certain for
  `n` years `(1 - e^{-δn})/δ`; for a survival function `S`, the complete expectation of life
  `∫_0^∞ S` (where it converges) and the net single premium of an n-year pure endowment
  `e^{-δn} S(n)`; the equivalence premium of a whole life insurance `δ` under constant force
  (the rate that makes premiums and benefits equal: `μ`).

Every meaning is a term of the core language. -/

namespace Leanify.Actuarial
open Build Core

abbrev F : Ty := Ty.rfun

def exp (x : B) : B := app (prim (.realFn .exp)) x
def log (x : B) : B := app (prim (.realFn .log)) x
def rpow (x y : B) : B := app2 (prim .rpow) x y
def pos (x : B) : B := lt (num 0) x
def nonneg (x : B) : B := le (num 0) x
def gompertzS (b c t : B) : B := exp (neg (div (mul b (sub (rpow c t) (num 1))) (log c)))
def cOk (c : B) : B := lt (num 1) c
def posRay : B := lamR fun t => le (num 0) t
def any (_ : B) : B := tt

def vocab : Vocab where
  notions := [
    { name := phrase!"survival function of the Gompertz law with parameters $v$ and $v$", ty := .real ⟶ .real ⟶ F,
      doms := [dom1 .real pos, dom1 .real cOk], doc := "`t ↦ exp(-B(c^t - 1)/log c)`, `B > 0`, `c > 1`",
      value := close <| lamT .real pos fun b => lamT .real cOk fun c => lamR fun t => gompertzS b c t },
    { name := phrase!"survival function of the Gompertz-Makeham law with parameters $v$, $v$ and $v$", ty := .real ⟶ .real ⟶ .real ⟶ F,
      doms := [dom1 .real nonneg, dom1 .real pos, dom1 .real cOk], doc := "`t ↦ exp(-At - B(c^t - 1)/log c)`",
      value := close <| lamT .real nonneg fun a => lamT .real pos fun b => lamT .real cOk fun c => lamR fun t =>
        mul (exp (neg (mul a t))) (gompertzS b c t) },
    { name := phrase!"force of mortality of the Gompertz law with parameters $v$ and $v$", ty := .real ⟶ .real ⟶ F,
      doms := [dom1 .real pos, dom1 .real cOk], doc := "`t ↦ B c^t`",
      value := close <| lamT .real pos fun b => lamT .real cOk fun c => lamR fun t => mul b (rpow c t) },
    { name := phrase!"life expectancy with force of mortality $v$", ty := .real ⟶ .real, doms := [dom1 .real pos],
      doc := "`1/μ`, constant force", value := close <| lamT .real pos fun m => div (num 1) m },
    { name := phrase!"net single premium of a whole life insurance with force of mortality $v$ and force of interest $v$",
      ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real pos, dom1 .real nonneg], doc := "`μ/(μ+δ)`, constant forces",
      value := close <| lamT .real pos fun m => lamT .real nonneg fun d => div m (add m d) },
    { name := phrase!"present value of a continuous whole life annuity with force of mortality $v$ and force of interest $v$",
      ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real pos, dom1 .real nonneg], doc := "`1/(μ+δ)`, constant forces",
      value := close <| lamT .real pos fun m => lamT .real nonneg fun d => div (num 1) (add m d) },
    { name := phrase!"present value of a continuous annuity-certain for $v$ years with force of interest $v$",
      ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real nonneg, dom1 .real pos], doc := "`(1 - e^{-δn})/δ`",
      value := close <| lamT .real nonneg fun n => lamT .real pos fun d => div (sub (num 1) (exp (neg (mul d n)))) d },
    { name := phrase!"complete expectation of life for the survival function $v$", ty := F ⟶ .real,
      doms := [dom1 F fun s => app2 (prim .integrableOn) s posRay],
      doc := "`∫_0^∞ S(t) dt`, where `S` is integrable",
      value := close <| lamT F (fun s => app2 (prim .integrableOn) s posRay) fun s => app2 (prim .integralOn) posRay s },
    { name := phrase!"net single premium of an $v$-year pure endowment for the survival function $v$ with force of interest $v$",
      ty := .real ⟶ F ⟶ .real ⟶ .real, doms := [dom1 .real nonneg, none, dom1 .real nonneg], doc := "`e^{-δn} S(n)`",
      value := close <| lamT .real nonneg fun n => lamT F any fun s => lamT .real nonneg fun d => mul (exp (neg (mul d n))) (app s n) }]

end Leanify.Actuarial
