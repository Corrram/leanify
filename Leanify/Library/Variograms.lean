import Leanify.Library.Core

/-! # Vocabulary: variogram models

The standard isotropic variogram and covariance models of geostatistics, as functions of the
lag (`We write $\gamma$ for the exponential variogram with sill $c$ and range $a$.`).

* notions: the spherical variogram `c(3h/(2a) - h³/(2a³))` for `h ≤ a` and `c` beyond; the
  exponential variogram `c(1 - e^{-h/a})`; the Gaussian variogram `c(1 - e^{-h²/a²})`; the power
  variogram `c h^α`; the variogram with a nugget `c₀` (`c₀ + γ(h)` for `h > 0`, `0` at `0`); the
  exponential covariance `c e^{-h/a}`; the practical range `3a` of the exponential model.

Every meaning is a term of the core language. -/

namespace Leanify.Variograms
open Build Core

abbrev F : Ty := Ty.rfun

def pos (x : B) : B := lt (num 0) x
def exp (x : B) : B := app (prim (.realFn .exp)) x
def rpow (x s : B) : B := app2 (prim .rpow) x s
def lag (h : B) : B := abs h
def model (name : Phrase) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ F, doms := [dom1 .real pos, dom2 .real fun _ a => pos a], doc,
    value := close <| lamT .real pos fun c => lamT .real pos fun a => lamR fun h => body c a (lag h) }

def vocab : Vocab where
  notions := [
    model phrase!"spherical variogram with sill $v$ and range $v$"
      (fun c a h => cases (le h a) (mul c (sub (div (mul (num 3) h) (mul (num 2) a)) (div (mul h (mul h h)) (mul (num 2) (mul a (mul a a)))))) c)
      "`h ↦ c(3h/(2a) - h³/(2a³))` for `|h| ≤ a`, `c` beyond",
    model phrase!"exponential variogram with sill $v$ and range $v$" (fun c a h => mul c (sub (num 1) (exp (neg (div h a)))))
      "`h ↦ c(1 - e^{-|h|/a})`",
    model phrase!"Gaussian variogram with sill $v$ and range $v$" (fun c a h => mul c (sub (num 1) (exp (neg (div (mul h h) (mul a a))))))
      "`h ↦ c(1 - e^{-h²/a²})`",
    model phrase!"exponential covariance with sill $v$ and range $v$" (fun c a h => mul c (exp (neg (div h a)))) "`h ↦ c e^{-|h|/a}`",
    { name := phrase!"power variogram with coefficient $v$ and exponent $v$", ty := .real ⟶ .real ⟶ F,
      doms := [dom1 .real pos, dom2 .real fun _ a => and (pos a) (lt a (num 2))], doc := "`h ↦ c|h|^α`, `0 < α < 2`",
      value := close <| lamT .real pos fun c => lamT .real (fun a => and (pos a) (lt a (num 2))) fun a => lamR fun h => mul c (rpow (abs h) a) },
    { name := phrase!"variogram $v$ with nugget $v$", ty := F ⟶ .real ⟶ F,
      doms := [none, dom2 .real fun _ n => le (num 0) n], doc := "`h ↦ c₀ + γ(h)` for `h ≠ 0`, `0` at `0`",
      value := close <| lamT F (fun _ => tt) fun g => lamT .real (fun n => le (num 0) n) fun n => lamR fun h =>
        cases (eq h (num 0)) (num 0) (add n (app g h)) },
    { name := phrase!"practical range of the exponential variogram with range $v$", ty := .real ⟶ .real, doms := [dom1 .real pos],
      doc := "`3a`: the lag where it reaches 95% of the sill", value := close <| lamT .real pos fun a => mul (num 3) a }]

end Leanify.Variograms
