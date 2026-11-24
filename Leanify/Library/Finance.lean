import Leanify.Library.Densities

/-! # Vocabulary: elementary financial mathematics

Interest, annuities and the Black–Scholes formulas, with real parameters: a rate `r`, a
time `t` in years, a strike `K`, a maturity `T`, a stock price `S` and a volatility `σ`.

* the standard normal distribution function `Φ(x) = ∫_{-∞}^x e^{-y²/2}/√(2π) dy`;
* `present value of $C$ due in $t$ years at the interest rate $r$` (`C (1+r)^{-t}`),
  `future value of $C$ after $t$ years at the interest rate $r$` (`C (1+r)^t`),
  `continuously compounded value of $C$ after $t$ years at the rate $r$` (`C e^{rt}`),
  `present value of an annuity paying $C$ for $n$ periods at the interest rate $r$`
  (`C (1 - (1+r)^{-n})/r`);
* `Black-Scholes price of a call with strike $K$ and maturity $T$ on a stock with price $S$
  and volatility $\sigma$ at the interest rate $r$` (`S Φ(d₁) - K e^{-rT} Φ(d₂)`), the same
  for a put (`K e^{-rT} Φ(-d₂) - S Φ(-d₁)`), and the delta of the call (`Φ(d₁)`), with
  `d₁ = (log(S/K) + (r + σ²/2)T)/(σ√T)` and `d₂ = d₁ - σ√T`.

A rate of interest is greater than `-1`; a strike, a maturity, a price and a volatility
are positive; a number of periods is a positive integer. Every meaning is a term of the
core language (the standard normal density of the field `densities`, an integral, powers
and logarithms). -/

namespace Leanify.Finance
open Build Core

def exp (x : B) : B := app (prim (.realFn .exp)) x
def log (x : B) : B := app (prim (.realFn .log)) x
def rpow (x p : B) : B := app2 (prim .rpow) x p
def sqrt (x : B) : B := rpow x (div (num 1) (num 2))
/-- `Φ(x)`. -/
def phi (x : B) : B := Densities.integralTo x (lamR fun y => Densities.normal (num 0) (num 1) y)

def posP (x : B) : B := lt (num 0) x
def rateP (r : B) : B := lt (neg (num 1)) r
def posIntP (n : B) : B := and (isInt n) (lt (num 0) n)

def d1 (k t s v r : B) : B :=
  div (add (log (div s k)) (mul (add r (div (mul v v) (num 2))) t)) (mul v (sqrt t))
def d2 (k t s v r : B) : B := sub (d1 k t s v r) (mul v (sqrt t))
def call (k t s v r : B) : B := sub (mul s (phi (d1 k t s v r))) (mul (mul k (exp (neg (mul r t)))) (phi (d2 k t s v r)))
def put (k t s v r : B) : B :=
  sub (mul (mul k (exp (neg (mul r t)))) (phi (neg (d2 k t s v r)))) (mul s (phi (neg (d1 k t s v r))))

/-- A Black–Scholes quantity of a strike, a maturity, a price, a volatility and a rate. -/
def bs (name : Phrase) (body : B → B → B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real, doc,
    doms := [dom1 .real posP, dom1 .real posP, dom1 .real posP, dom1 .real posP, none],
    value := close <| lamT .real posP fun k => lamT .real posP fun t => lamT .real posP fun s =>
      lamT .real posP fun v => lamR fun r => body k t s v r }
/-- A value of an amount `C` after a time `t` at a rate `r` (with the condition `d r`). -/
def amount (name : Phrase) (d : B → B) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real, doc, doms := [none, none, dom1 .real d],
    value := close <| lamR fun c => lamR fun t => lamT .real d fun r => body c t r }

def vocab : Vocab where
  notions := [
    { name := phrase!"standard normal distribution function", ty := Ty.rfun,
      doc := "`Φ(x) = ∫_{-∞}^x e^{-y²/2}/√(2π) dy` (Mathlib `ProbabilityTheory.gaussianReal`)",
      value := close <| lamR fun x => phi x },
    amount phrase!"present value of $v$ due in $v$ years at the interest rate $v$" rateP
      (fun c t r => mul c (rpow (add (num 1) r) (neg t))) "`C (1+r)^{-t}`, `r > -1`",
    amount phrase!"future value of $v$ after $v$ years at the interest rate $v$" rateP
      (fun c t r => mul c (rpow (add (num 1) r) t)) "`C (1+r)^t`, `r > -1`",
    amount phrase!"continuously compounded value of $v$ after $v$ years at the rate $v$" (fun _ => tt)
      (fun c t r => mul c (exp (mul r t))) "`C e^{rt}`",
    { name := phrase!"present value of an annuity paying $v$ for $v$ periods at the interest rate $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real, doc := "`C (1 - (1+r)^{-n})/r`, `n` a positive integer, `r > 0`",
      doms := [none, dom1 .real posIntP, dom1 .real posP],
      value := close <| lamR fun c => lamT .real posIntP fun n => lamT .real posP fun r =>
        div (mul c (sub (num 1) (rpow (add (num 1) r) (neg n)))) r },
    bs phrase!"Black-Scholes price of a call with strike $v$ and maturity $v$ on a stock with price $v$ and volatility $v$ at the interest rate $v$"
      call "`S Φ(d₁) - K e^{-rT} Φ(d₂)`; `K, T, S, σ > 0`",
    bs phrase!"Black-Scholes price of a put with strike $v$ and maturity $v$ on a stock with price $v$ and volatility $v$ at the interest rate $v$"
      put "`K e^{-rT} Φ(-d₂) - S Φ(-d₁)`; `K, T, S, σ > 0`",
    bs phrase!"delta of a call with strike $v$ and maturity $v$ on a stock with price $v$ and volatility $v$ at the interest rate $v$"
      (fun k t s v r => phi (d1 k t s v r)) "`Φ(d₁)`, the derivative of the call price in `S`; `K, T, S, σ > 0`"]

end Leanify.Finance
