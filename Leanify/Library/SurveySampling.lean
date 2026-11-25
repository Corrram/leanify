import Leanify.Library.Core

/-! # Vocabulary: survey sampling

Sample sizes, corrections and design effects of finite-population sampling (`We write
$n(z,p,e)$ for the sample size for a proportion $p$ with margin of error $e$ at critical value
$z$.`). Concentration bounds for sample sizes are in the field `concentration`.

* notions: the sample sizes `z²p(1-p)/e²` for a proportion and `(zσ/e)²` for a mean (before
  rounding up), and the sample size `n₀/(1 + (n₀ - 1)/N)` after the finite population correction;
  the finite population correction factor `√((N-n)/(N-1))`; the margin of error `z√(p(1-p)/n)`;
  the design effect `1 + (m-1)ρ` of clusters of size `m` with intraclass correlation `ρ` and the
  effective sample size `n/deff`; the sampling fraction `n/N`.

Every meaning is a term of the core language. -/

namespace Leanify.SurveySampling
open Build Core

def pos (x : B) : B := lt (num 0) x
def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def sqrt (x : B) : B := app2 (prim .rpow) x (div (num 1) (num 2))
def prob (p : B) : B := and (lt (num 0) p) (lt p (num 1))

def vocab : Vocab where
  notions := [
    { name := phrase!"sample size for a proportion $v$ with margin of error $v$ at critical value $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real prob, dom2 .real fun _ e => pos e, dom3 .real fun _ _ z => pos z], doc := "`z²p(1-p)/e²`",
      value := close <| lamT .real prob fun p => lamT .real pos fun e => lamT .real pos fun z =>
        div (mul (mul z z) (mul p (sub (num 1) p))) (mul e e) },
    { name := phrase!"sample size for a mean with standard deviation $v$ and margin of error $v$ at critical value $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ e => pos e, dom3 .real fun _ _ z => pos z], doc := "`(zσ/e)²`",
      value := close <| lamT .real pos fun s => lamT .real pos fun e => lamT .real pos fun z => mul (div (mul z s) e) (div (mul z s) e) },
    { name := phrase!"sample size $v$ corrected for a population of $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun n => le (num 1) n, dom2 .real fun _ m => posInt m], doc := "`n₀/(1 + (n₀ - 1)/N)`",
      value := close <| lamT .real (fun n => le (num 1) n) fun n => lamT .real posInt fun m => div n (add (num 1) (div (sub n (num 1)) m)) },
    { name := phrase!"finite population correction for a sample of $v$ from a population of $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real posInt, dom2 .real fun n m => and (and (isInt m) (le (num 2) m)) (le n m)], doc := "`√((N-n)/(N-1))`",
      value := close <| lamT .real posInt fun n => lamT .real (fun m => and (and (isInt m) (le (num 2) m)) (le n m)) fun m =>
        sqrt (div (sub m n) (sub m (num 1))) },
    { name := phrase!"margin of error for a proportion $v$ with sample size $v$ at critical value $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun p => and (le (num 0) p) (le p (num 1)), dom2 .real fun _ n => pos n, dom3 .real fun _ _ z => pos z],
      doc := "`z√(p(1-p)/n)`",
      value := close <| lamT .real (fun p => and (le (num 0) p) (le p (num 1))) fun p => lamT .real pos fun n => lamT .real pos fun z =>
        mul z (sqrt (div (mul p (sub (num 1) p)) n)) },
    { name := phrase!"design effect of clusters of size $v$ with intraclass correlation $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real posInt, dom2 .real fun _ r => and (le (neg (num 1)) r) (le r (num 1))], doc := "`1 + (m-1)ρ`",
      value := close <| lamT .real posInt fun m => lamT .real (fun r => and (le (neg (num 1)) r) (le r (num 1))) fun r =>
        add (num 1) (mul (sub m (num 1)) r) },
    { name := phrase!"effective sample size of $v$ observations with design effect $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun n => le (num 0) n, dom2 .real fun _ d => pos d], doc := "`n/deff`",
      value := close <| lamT .real (fun n => le (num 0) n) fun n => lamT .real pos fun d => div n d },
    { name := phrase!"sampling fraction of a sample of $v$ from a population of $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun n => le (num 0) n, dom2 .real fun _ m => pos m], doc := "`n/N`",
      value := close <| lamT .real (fun n => le (num 0) n) fun n => lamT .real pos fun m => div n m }]

end Leanify.SurveySampling
