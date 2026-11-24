import Leanify.Library.Distributions

/-! # Vocabulary: branching processes

Galton–Watson branching processes through their offspring distribution, a probability
distribution `p` on `ℕ₀` as in the field `distributions` (its weights `p(k)`):
`We write $q(p)$ for the extinction probability of the branching process with offspring
distribution $p$.`

* notions: the offspring mean `m = ∑ k p(k)`, the offspring generating function
  `s ↦ ∑ p(k) s^k`, the expected size `m^n` of generation `n` (from one ancestor), the
  extinction probability (the least fixed point of the generating function in `[0,1]`);
* adjectives of offspring distributions: `subcritical` (`m < 1`), `critical` (`m = 1`),
  `supercritical` (`m > 1`), each with a finite mean.

Every meaning is a term of the core language (series). -/

namespace Leanify.Branching
open Build Core

abbrev F : Ty := Ty.rfun

def natP (k : B) : B := and (isInt k) (le (num 0) k)
def zpow (x k : B) : B := app2 (prim .zpow) x k
def isDist (p : B) : B := app (fun _ => Distributions.isDistribution) p
def series0 (body : B → B) : B := app2 (prim .series) (num 0) (lamT .real natP body)
def conv0 (body : B → B) : B := app2 (prim .seriesConv) (num 0) (lamT .real natP body)
def meanOf (p : B) : B := series0 fun k => mul k (app p k)
def finiteMean (p : B) : B := and (isDist p) (conv0 fun k => mul k (app p k))
def pgf (p s : B) : B := series0 fun k => mul (app p k) (zpow s k)
def unitI (s : B) : B := and (le (num 0) s) (le s (num 1))
def extinction (p : B) : B :=
  theR fun q => and (unitI q) (and (eq (pgf p q) q) (allR fun s => imp (and (unitI s) (eq (pgf p s) s)) (le q s)))
def fPred (p : B → B) : Tm := close <| lamT F (fun _ => tt) p
def adj (ph : Phrase) (body : B → B) (doc : String) : Modifier :=
  { phrase := ph, prenominal := true, ty := F, pred := fPred body, doc }

def vocab : Vocab where
  mods := [
    adj phrase!"subcritical" (fun p => and (finiteMean p) (lt (meanOf p) (num 1))) "a distribution on `ℕ₀` with mean `m < 1`",
    adj phrase!"critical" (fun p => and (finiteMean p) (eq (meanOf p) (num 1))) "a distribution on `ℕ₀` with mean `m = 1`",
    adj phrase!"supercritical" (fun p => and (finiteMean p) (lt (num 1) (meanOf p))) "a distribution on `ℕ₀` with finite mean `m > 1`"]
  notions := [
    { name := phrase!"offspring mean of $v$", ty := F ⟶ .real, doms := [dom1 F finiteMean],
      doc := "`m = ∑_k k p(k)`, of a distribution on `ℕ₀` with finite mean",
      value := close <| lamT F finiteMean meanOf },
    { name := phrase!"offspring generating function of $v$", ty := F ⟶ F, doms := [dom1 F isDist],
      doc := "`s ↦ ∑_k p(k) s^k` (on `[-1,1]`, where the series converges)",
      value := close <| lamT F isDist fun p => lamR fun s => pgf p s },
    { name := phrase!"expected size of generation $v$ of the branching process with offspring distribution $v$",
      ty := .real ⟶ F ⟶ .real, doms := [dom1 .real natP, dom1 F finiteMean],
      doc := "`m^n`, from one ancestor",
      value := close <| lamT .real natP fun n => lamT F finiteMean fun p => zpow (meanOf p) n },
    { name := phrase!"extinction probability of the branching process with offspring distribution $v$",
      ty := F ⟶ .real, doms := [dom1 F isDist],
      doc := "the least `q ∈ [0,1]` with `G(q) = q` for the offspring generating function `G`",
      value := close <| lamT F isDist extinction }]

end Leanify.Branching
