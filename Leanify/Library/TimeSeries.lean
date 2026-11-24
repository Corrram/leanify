import Leanify.Library.Core

/-! # Vocabulary: time series

A time series is a sequence `x(1), x(2), …`, the values of a real function at the positive
integers (as in the field `samples`): its sample autocovariance and autocorrelation at a
lag, moving averages, cumulative sums, differences, and exponential smoothing.

* notions: the sample autocovariance at lag `h` of the first `n` terms
  (`(1/n) ∑_{t=1}^{n-h} (x_t - x̄)(x_{t+h} - x̄)`), the sample autocorrelation at lag `h`
  (where the series is not constant), the moving average of order `k`
  (`t ↦ (1/k) ∑_{i=0}^{k-1} x(t-i)`), the cumulative sum (`t ↦ ∑_{i=1}^{t} x(i)`), the
  difference sequence (`t ↦ x(t) - x(t-1)`), the seasonal difference at lag `s`, and
  simple exponential smoothing with parameter `α` (`∑_{i=0}^{t-1} α(1-α)^i x(t-i) +
  (1-α)^t x(0)`);
* adjectives of sequences: `autoregressive sequence of order one with coefficient $\phi$`
  (`x(t+1) = φ x(t)`, without noise) and `random walk with steps $e$`
  (`x(t+1) = x(t) + e(t+1)`).

Every meaning is a term of the core language (finite sums and integer powers). -/

namespace Leanify.TimeSeries
open Build Core

abbrev F : Ty := Ty.rfun

def natP (n : B) : B := and (isInt n) (le (num 0) n)
def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def finSum (a b : B) (body : B → B) : B := app (app (app (prim .finSum) a) b) (lamR body)
def zpow (x k : B) : B := app2 (prim .zpow) x k
def mean (n x : B) : B := div (finSum (num 1) n fun i => app x i) n
def acov (h n x : B) : B :=
  div (finSum (num 1) (sub n h) fun t => mul (sub (app x t) (mean n x)) (sub (app x (add t h)) (mean n x))) n
def forNat (body : B → B) : B := allR fun t => imp (natP t) (body t)

def vocab : Vocab where
  mods := [
    { phrase := phrase!"autoregressive sequence of order one with coefficient $v$", prenominal := false, ty := F,
      pred := close <| lamR fun p => lamT F (fun _ => tt) fun x => forNat fun t => eq (app x (add t (num 1))) (mul p (app x t)),
      doc := "`x(t+1) = φ x(t)` for every `t ≥ 0`" },
    { phrase := phrase!"random walk with steps $v$", prenominal := false, ty := F,
      pred := close <| lamT F (fun _ => tt) fun e => lamT F (fun _ => tt) fun x =>
        forNat fun t => eq (app x (add t (num 1))) (add (app x t) (app e (add t (num 1)))),
      doc := "`x(t+1) = x(t) + e(t+1)` for every `t ≥ 0`" }]
  notions := [
    { name := phrase!"sample autocovariance at lag $v$ of the first $v$ terms of $v$", ty := .real ⟶ .real ⟶ F ⟶ .real,
      doms := [dom1 .real natP, dom2 .real fun h n => and (posInt n) (lt h n), none],
      doc := "`(1/n) ∑_{t=1}^{n-h} (x_t - x̄)(x_{t+h} - x̄)`, `0 ≤ h < n`",
      value := close <| lamT .real natP fun h => lamT .real (fun n => and (posInt n) (lt h n)) fun n =>
        lamT F (fun _ => tt) fun x => acov h n x },
    { name := phrase!"sample autocorrelation at lag $v$ of the first $v$ terms of $v$", ty := .real ⟶ .real ⟶ F ⟶ .real,
      doms := [dom1 .real natP, dom2 .real fun h n => and (posInt n) (lt h n), dom3 F fun _ n x => ne (acov (num 0) n x) (num 0)],
      doc := "the autocovariance at lag `h` over that at lag `0`, where the terms are not all equal",
      value := close <| lamT .real natP fun h => lamT .real (fun n => and (posInt n) (lt h n)) fun n =>
        lamT F (fun x => ne (acov (num 0) n x) (num 0)) fun x => div (acov h n x) (acov (num 0) n x) },
    { name := phrase!"moving average of order $v$ of $v$", ty := .real ⟶ F ⟶ F, doms := [dom1 .real posInt, none],
      doc := "`t ↦ (1/k) ∑_{i=0}^{k-1} x(t-i)`",
      value := close <| lamT .real posInt fun k => lamT F (fun _ => tt) fun x => lamR fun t =>
        div (finSum (num 0) (sub k (num 1)) fun i => app x (sub t i)) k },
    { name := phrase!"cumulative sum of $v$", ty := F ⟶ F, doc := "`t ↦ ∑_{i=1}^{t} x(i)`",
      value := close <| lamT F (fun _ => tt) fun x => lamR fun t => finSum (num 1) t fun i => app x i },
    { name := phrase!"difference sequence of $v$", ty := F ⟶ F, doc := "`t ↦ x(t) - x(t-1)`",
      value := close <| lamT F (fun _ => tt) fun x => lamR fun t => sub (app x t) (app x (sub t (num 1))) },
    { name := phrase!"seasonal difference at lag $v$ of $v$", ty := .real ⟶ F ⟶ F, doms := [dom1 .real posInt, none],
      doc := "`t ↦ x(t) - x(t-s)`",
      value := close <| lamT .real posInt fun s => lamT F (fun _ => tt) fun x => lamR fun t => sub (app x t) (app x (sub t s)) },
    { name := phrase!"exponential smoothing of $v$ with parameter $v$", ty := F ⟶ .real ⟶ F,
      doms := [none, dom1 .real fun a => and (lt (num 0) a) (le a (num 1))],
      doc := "`t ↦ ∑_{i=0}^{t-1} α(1-α)^i x(t-i) + (1-α)^t x(0)`: `s_t = α x_t + (1-α) s_{t-1}`, `s_0 = x_0`; `0 < α ≤ 1`",
      value := close <| lamT F (fun _ => tt) fun x => lamT .real (fun a => and (lt (num 0) a) (le a (num 1))) fun a => lamR fun t =>
        add (finSum (num 0) (sub t (num 1)) fun i => mul (mul a (zpow (sub (num 1) a) i)) (app x (sub t i)))
          (mul (zpow (sub (num 1) a) t) (app x (num 0))) }]

end Leanify.TimeSeries
