import Leanify.Library.Topologies

/-! # Vocabulary: metrics on the real line

Metric topology on the set `ℝ`: a metric is a real function of two real numbers, so that an
article compares the usual metric with others, and speaks of balls, Cauchy sequences,
completeness, isometries and contractions (`Let $d$ be a metric on $\mathbb{R}$.`, `$a$ is
Cauchy with respect to $d$`). The field includes `topologies`: the topology induced by a
metric is a topology of that field, with its open, compact and dense sets.

* nouns: `metric on $\mathbb{R}$`, `pseudometric on $\mathbb{R}$`, `ultrametric on
  $\mathbb{R}$` (and `metric`, `pseudometric`, `ultrametric`);
* adjectives of metrics: `complete` (every Cauchy sequence converges), `bounded`,
  `translation-invariant`, `strongly equivalent to $d'$` (`c d ≤ d' ≤ C d`), `equivalent to
  $d'$` (the same induced topology);
* adjectives of sequences (functions of the natural numbers), with the metric: `Cauchy with
  respect to $d$`, `convergent to $l$ with respect to $d$`, `convergent with respect to $d$`,
  `bounded with respect to $d$`;
* adjectives of real functions: `isometry of $d$`, `contraction with respect to $d$`,
  `Lipschitz with respect to $d$`;
* notions: the Euclidean and the discrete metric on `ℝ`, the standard bounded metric
  `min(d, 1)`, the topology induced by a metric, the open and closed balls, the diameter
  of a set and the distance from a point to a set with respect to a metric.

Every meaning is a term of the core language (with the constants of `topologies`); the
diameter is a supremum and the distance an infimum, defined where they exist. -/

namespace Leanify.MetricSpaces
open Build Core
open Leanify.Topologies (S T F isTop)

/-- Metrics: real functions of two real numbers. -/
abbrev D : Ty := .real ⟶ .real ⟶ .real

def d2 (d x y : B) : B := app2 d x y
def pseudo (d : B) : B :=
  and (allR fun x => eq (d2 d x x) (num 0))
    (and (allR fun x => allR fun y => eq (d2 d x y) (d2 d y x))
      (allR fun x => allR fun y => allR fun z => le (d2 d x z) (add (d2 d x y) (d2 d y z))))
def metric (d : B) : B :=
  and (pseudo d) (allR fun x => allR fun y => imp (eq (d2 d x y) (num 0)) (eq x y))
def ultra (d : B) : B :=
  and (metric d) (allR fun x => allR fun y => allR fun z => le (d2 d x z) (app2 (prim .max) (d2 d x y) (d2 d y z)))

/-- `a_m`, `a_n` close for all large natural `m`, `n`. -/
def cauchy (d a : B) : B :=
  allR fun e => imp (lt (num 0) e) (exR fun n0 => allR fun m => allR fun n =>
    imp (and (and (isNat m) (isNat n)) (and (le n0 m) (le n0 n))) (lt (d2 d (app a m) (app a n)) e))
def converges (d a l : B) : B :=
  allR fun e => imp (lt (num 0) e) (exR fun n0 => allR fun n =>
    imp (and (isNat n) (le n0 n)) (lt (d2 d (app a n) l) e))
def complete (d : B) : B := allT F fun a => imp (cauchy d a) (exR fun l => converges d a l)
/-- The topology of `d`: every point of `U` has a ball around it in `U`. -/
def induced (d : B) : B := lamT S (fun _ => tt) fun u => allR fun x => imp (app u x)
  (exR fun e => and (lt (num 0) e) (allR fun y => imp (lt (d2 d x y) e) (app u y)))
def lipschitzD (d f l : B) : B := allR fun x => allR fun y => le (d2 d (app f x) (app f y)) (mul l (d2 d x y))

def dPred (body : B → B) : Tm := close <| lamT D (fun _ => tt) body
/-- A property of the subject (of type `ty`) with a metric (`P d x`). -/
def withD (p : Phrase) (ty : Ty) (body : B → B → B) (doc : String) : Modifier :=
  { phrase := p, prenominal := false, ty, doc,
    pred := close <| lamT D (fun _ => tt) fun d => lamT ty (fun _ => tt) fun x => body d x }
def nounD (sing plural : Phrase) (p : B → B) (doc : String) : Noun :=
  { sing, plural, ty := D, pred := dPred p, doc }
/-- The `d`-diameter of `U`, of a nonempty set with bounded distances. -/
def diamDom (u d : B) : B :=
  and (exR fun x => app u x) (exR fun m => allR fun x => allR fun y => imp (and (app u x) (app u y)) (le (d2 d x y) m))
def distDom (u : B) : B := exR fun x => app u x

/-- The words of the field itself. -/
def own : Vocab := {
  nouns := [
    nounD phrase!"metric $v$ on $\\mathbb{R}$" phrase!"metrics $v$ on $\\mathbb{R}$" metric
      "`d(x,x) = 0`, symmetric, the triangle inequality, `d(x,y) = 0 → x = y` (Mathlib `MetricSpace`)",
    nounD phrase!"metric on $\\mathbb{R}$" phrase!"metrics on $\\mathbb{R}$" metric "(after `is`)",
    nounD phrase!"metric" phrase!"metrics" metric "a metric on `ℝ`",
    nounD phrase!"pseudometric $v$ on $\\mathbb{R}$" phrase!"pseudometrics $v$ on $\\mathbb{R}$" pseudo
      "a metric that may vanish between distinct points (Mathlib `PseudoMetricSpace`)",
    nounD phrase!"pseudometric" phrase!"pseudometrics" pseudo "a pseudometric on `ℝ`",
    nounD phrase!"ultrametric $v$ on $\\mathbb{R}$" phrase!"ultrametrics $v$ on $\\mathbb{R}$" ultra
      "a metric with `d(x,z) ≤ max(d(x,y), d(y,z))` (Mathlib `IsUltrametricDist`)",
    nounD phrase!"ultrametric" phrase!"ultrametrics" ultra "an ultrametric on `ℝ`"]
  mods := [
    { phrase := phrase!"complete", prenominal := true, ty := D, pred := dPred complete,
      doc := "every Cauchy sequence converges (Mathlib `CompleteSpace`)" },
    { phrase := phrase!"bounded", prenominal := true, ty := D,
      pred := dPred fun d => exR fun m => allR fun x => allR fun y => le (d2 d x y) m,
      doc := "`d(x,y) ≤ M` for all `x`, `y` (Mathlib `BoundedSpace`)" },
    { phrase := phrase!"translation-invariant", prenominal := true, ty := D,
      pred := dPred fun d => allR fun x => allR fun y => allR fun z => eq (d2 d (add x z) (add y z)) (d2 d x y),
      doc := "`d(x+z, y+z) = d(x,y)`" },
    withD phrase!"strongly equivalent to $v$" D
      (fun d' d => exR fun c => exR fun c' => and (and (lt (num 0) c) (lt (num 0) c'))
        (allR fun x => allR fun y => and (le (mul c (d2 d x y)) (d2 d' x y)) (le (d2 d' x y) (mul c' (d2 d x y)))))
      "`c d ≤ d' ≤ C d` for some `c, C > 0`",
    withD phrase!"equivalent to $v$" D (fun d' d => allT S fun u => iff (app (induced d) u) (app (induced d') u))
      "the same open sets",
    withD phrase!"Cauchy with respect to $v$" F cauchy
      "`d(a_m, a_n) < ε` for all large natural `m`, `n` (Mathlib `CauchySeq`)",
    { phrase := phrase!"convergent to $v$ with respect to $v$", prenominal := false, ty := F,
      doc := "`d(a_n, l) → 0`, `n ∈ ℕ` (Mathlib `Filter.Tendsto`)",
      pred := close <| lamR fun l => lamT D (fun _ => tt) fun d => lamT F (fun _ => tt) fun a => converges d a l },
    withD phrase!"convergent with respect to $v$" F (fun d a => exR fun l => converges d a l) "`d(a_n, l) → 0` for some `l`",
    withD phrase!"bounded with respect to $v$" F
      (fun d a => exR fun m => allR fun n => imp (isNat n) (le (d2 d (app a n) (app a (num 0))) m))
      "the terms `a_n`, `n ∈ ℕ`, lie in a ball",
    withD phrase!"isometry of $v$" F (fun d f => allR fun x => allR fun y => eq (d2 d (app f x) (app f y)) (d2 d x y))
      "`d(f(x), f(y)) = d(x,y)` (Mathlib `Isometry`)",
    withD phrase!"contraction with respect to $v$" F
      (fun d f => exR fun l => and (and (le (num 0) l) (lt l (num 1))) (lipschitzD d f l))
      "`d(f(x), f(y)) ≤ L d(x,y)` for some `L < 1` (Mathlib `ContractingWith`)",
    withD phrase!"Lipschitz with respect to $v$" F (fun d f => exR fun l => lipschitzD d f l)
      "`d(f(x), f(y)) ≤ L d(x,y)` for some `L` (Mathlib `LipschitzWith`)"]
  notions := [
    { name := phrase!"Euclidean metric on $\\mathbb{R}$", ty := D, doc := "`|x - y|` (Mathlib `dist`)",
      value := close <| lamR fun x => lamR fun y => abs (sub x y) },
    { name := phrase!"usual metric on $\\mathbb{R}$", ty := D, doc := "`|x - y|`",
      value := close <| lamR fun x => lamR fun y => abs (sub x y) },
    { name := phrase!"discrete metric on $\\mathbb{R}$", ty := D, doc := "`0` if `x = y`, `1` else",
      value := close <| lamR fun x => lamR fun y => cases (eq x y) (num 0) (num 1) },
    { name := phrase!"standard bounded metric of $v$", ty := D ⟶ D, doc := "`min(d(x,y), 1)`",
      value := close <| lamT D (fun _ => tt) fun d => lamR fun x => lamR fun y => app2 (prim .min) (d2 d x y) (num 1) },
    { name := phrase!"topology induced by $v$", ty := D ⟶ T,
      doc := "the sets with a ball around each of their points (Mathlib `PseudoMetricSpace.toUniformSpace`)",
      value := close <| lamT D (fun _ => tt) fun d => induced d },
    { name := phrase!"open ball of radius $v$ about $v$ with respect to $v$", ty := .real ⟶ .real ⟶ D ⟶ S,
      doc := "`{y : d(x,y) < r}` (Mathlib `Metric.ball`)",
      value := close <| lamR fun r => lamR fun x => lamT D (fun _ => tt) fun d => lamR fun y => lt (d2 d x y) r },
    { name := phrase!"closed ball of radius $v$ about $v$ with respect to $v$", ty := .real ⟶ .real ⟶ D ⟶ S,
      doc := "`{y : d(x,y) ≤ r}` (Mathlib `Metric.closedBall`)",
      value := close <| lamR fun r => lamR fun x => lamT D (fun _ => tt) fun d => lamR fun y => le (d2 d x y) r },
    { name := phrase!"diameter of $v$ with respect to $v$", ty := S ⟶ D ⟶ .real,
      doms := [none, dom2 D diamDom],
      doc := "`sup {d(x,y) : x, y ∈ U}`, of a nonempty set with bounded distances (Mathlib `Metric.diam`)",
      value := close <| lamT S (fun _ => tt) fun u => lamT D (fun d => diamDom u d) fun d =>
        theR fun m => and (allR fun x => allR fun y => imp (and (app u x) (app u y)) (le (d2 d x y) m))
          (allR fun e => imp (lt (num 0) e) (exR fun x => exR fun y => and (and (app u x) (app u y)) (lt (sub m e) (d2 d x y)))) },
    { name := phrase!"distance from $v$ to $v$ with respect to $v$", ty := .real ⟶ S ⟶ D ⟶ .real,
      doms := [none, dom1 S distDom, none],
      doc := "`inf {d(x,y) : y ∈ U}`, of a nonempty set (Mathlib `Metric.infDist`)",
      value := close <| lamR fun x => lamT S distDom fun u => lamT D (fun _ => tt) fun d =>
        theR fun m => and (allR fun y => imp (app u y) (le m (d2 d x y)))
          (allR fun e => imp (lt (num 0) e) (exR fun y => and (app u y) (lt (d2 d x y) (add m e)))) }] }

/-- `topologies` with the words of metrics (each entry tagged with its field). -/
def vocab : Vocab := Vocab.tag w!"topologies" Topologies.vocab ++ Vocab.tag w!"metricspaces" own

end Leanify.MetricSpaces
