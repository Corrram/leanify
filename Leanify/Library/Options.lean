import Leanify.Library.Core

/-! # Vocabulary: options and forwards

Payoffs, parity and the binomial model (`We write $q(r,u,d,t)$ for the risk-neutral probability
of the binomial model with rate $r$, up factor $u$ and down factor $d$ over a step $t$.`). The
Black–Scholes prices are in the field `finance`.

* notions: the payoffs `max(S - K, 0)` of a call and `max(K - S, 0)` of a put; the forward price
  `Se^{rT}`; the put price `C - S + Ke^{-rT}` by put–call parity; the risk-neutral probability
  `(e^{rΔt} - d)/(u - d)` of the binomial model and its Cox–Ross–Rubinstein up factor
  `e^{σ√Δt}`; the one-step binomial price `e^{-rΔt}(q f_u + (1-q) f_d)`.

Every meaning is a term of the core language. -/

namespace Leanify.Options
open Build Core

def pos (x : B) : B := lt (num 0) x
def exp (x : B) : B := app (prim (.realFn .exp)) x
def sqrt (x : B) : B := app2 (prim .rpow) x (div (num 1) (num 2))
def maxR (a b : B) : B := app2 (prim .max) a b
def rnq (r u d t : B) : B := div (sub (exp (mul r t)) d) (sub u d)

def vocab : Vocab where
  notions := [
    { name := phrase!"payoff of a call with strike $v$ at the price $v$", ty := .real ⟶ .real ⟶ .real,
      doc := "`max(S - K, 0)`", value := close <| lamR fun k => lamR fun s => maxR (sub s k) (num 0) },
    { name := phrase!"payoff of a put with strike $v$ at the price $v$", ty := .real ⟶ .real ⟶ .real,
      doc := "`max(K - S, 0)`", value := close <| lamR fun k => lamR fun s => maxR (sub k s) (num 0) },
    { name := phrase!"forward price of a stock with price $v$ for maturity $v$ at the rate $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ t => le (num 0) t, none], doc := "`Se^{rT}`",
      value := close <| lamT .real pos fun s => lamT .real (fun t => le (num 0) t) fun t => lamR fun r => mul s (exp (mul r t)) },
    { name := phrase!"put price by put-call parity for the call price $v$, the stock price $v$, the strike $v$, the maturity $v$ and the rate $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doc := "`C - S + Ke^{-rT}`",
      value := close <| lamR fun c => lamR fun s => lamR fun k => lamR fun t => lamR fun r => add (sub c s) (mul k (exp (neg (mul r t)))) },
    { name := phrase!"risk-neutral probability of the binomial model with rate $v$, up factor $v$ and down factor $v$ over a step $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, none, dom3 .real fun _ u d => and (pos d) (lt d u), dom4 .real fun _ _ _ t => pos t],
      doc := "`(e^{rΔt} - d)/(u - d)`",
      value := close <| lamR fun r => lamR fun u => lamT .real (fun d => and (pos d) (lt d u)) fun d => lamT .real pos fun t => rnq r u d t },
    { name := phrase!"Cox-Ross-Rubinstein up factor for the volatility $v$ over a step $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ t => pos t], doc := "`e^{σ√Δt}`",
      value := close <| lamT .real pos fun s => lamT .real pos fun t => exp (mul s (sqrt t)) },
    { name := phrase!"one-step binomial price with values $v$ and $v$ for the risk-neutral probability $v$, the rate $v$ and the step $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doc := "`e^{-rΔt}(q f_u + (1-q) f_d)`",
      value := close <| lamR fun fu => lamR fun fd => lamR fun q => lamR fun r => lamR fun t =>
        mul (exp (neg (mul r t))) (add (mul q fu) (mul (sub (num 1) q) fd)) }]

end Leanify.Options
