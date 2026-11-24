import Leanify.Library.Core

/-! # Vocabulary: integration of real functions

Lebesgue integrability and `L^p` norms of real functions on the line, improper integrals,
and integrals over sets. The functions are those of the field `realfunctions` (`Let $f$ be a
continuous function.`), the sets those of `realsets`.

* adjectives of functions: `$p$-integrable` (`|f|^p` is integrable, `p ≥ 1`),
  `locally integrable`, `essentially bounded`, `improperly integrable from $a$ to infinity`;
* notions: the `L^p` norm of `f` (`(∫|f|^p)^{1/p}`), the essential supremum of `|f|`, the
  Hölder conjugate of `p`, the improper integrals of `f` from `a` to infinity, from minus
  infinity to `a` and over the line (as limits of integrals over bounded intervals, where the
  limits exist), and the integral of `f` on a set `S` (where `f` is integrable on `S`).

Every meaning is a term of the core language (`integralOn`, `intervalIntegral`, `ae`). -/

namespace Leanify.Integration
open Build Core

abbrev F : Ty := Ty.rfun
abbrev S : Ty := .real ⟶ .prop

def line : B := lamR fun _ => tt
def rpow (x p : B) : B := app2 (prim .rpow) x p
def integral (s g : B) : B := app2 (prim .integralOn) s g
def integrable (s g : B) : B := app2 (prim .integrableOn) g s
def integ (a b g : B) : B := app (app (app (prim .intervalIntegral) a) b) g
def intervalIntegrable (g a b : B) : B := app2 (app (prim .intervalIntegrable) g) a b
def ae (p : B → B) : B := app (prim .ae) (lamR p)
def absPow (f p : B) : B := lamR fun x => rpow (abs (app f x)) p
def pIntegrable (p f : B) : B := and (le (num 1) p) (integrable line (absPow f p))
/-- `∫_a^b f → l` as `b → ∞`. -/
def toInfinity (f a l : B) : B :=
  allR fun e => imp (lt (num 0) e) (exR fun m => allR fun b => imp (le m b) (lt (abs (sub (integ a b f) l)) e))
def fromMinusInfinity (f b l : B) : B :=
  allR fun e => imp (lt (num 0) e) (exR fun m => allR fun a => imp (le a m) (lt (abs (sub (integ a b f) l)) e))
def overLine (f l : B) : B :=
  allR fun e => imp (lt (num 0) e) (exR fun m => allR fun a => allR fun b =>
    imp (and (le a (neg m)) (le m b)) (lt (abs (sub (integ a b f) l)) e))
def locInt (f : B) : B := allR fun a => allR fun b => intervalIntegrable f a b
def essBounded (f : B) : B := exR fun m => ae fun x => le (abs (app f x)) m
def isEssSup (f m : B) : B :=
  and (ae fun x => le (abs (app f x)) m) (allR fun e => imp (lt (num 0) e) (not (ae fun x => le (abs (app f x)) (sub m e))))

def fPred (p : B → B) : Tm := close <| lamT F (fun _ => tt) p

def vocab : Vocab where
  mods := [
    { phrase := phrase!"$v$-integrable", prenominal := true, ty := F,
      pred := close <| lamR fun p => lamT F (fun _ => tt) fun f => pIntegrable p f,
      doc := "`p ≥ 1` and `|f|^p` is integrable on the line (Mathlib `MeasureTheory.Memℒp`)" },
    { phrase := phrase!"locally integrable", prenominal := true, ty := F, pred := fPred locInt,
      doc := "integrable on every bounded interval (Mathlib `LocallyIntegrable`)" },
    { phrase := phrase!"essentially bounded", prenominal := true, ty := F, pred := fPred essBounded,
      doc := "`|f| ≤ M` almost everywhere (Mathlib `MeasureTheory.Memℒp f ∞`)" },
    { phrase := phrase!"improperly integrable from $v$ to infinity", prenominal := false, ty := F,
      pred := close <| lamR fun a => lamT F (fun _ => tt) fun f => and (locInt f) (exR fun l => toInfinity f a l),
      doc := "locally integrable, and `∫_a^b f` has a limit as `b → ∞`" }]
  notions := [
    { name := phrase!"$L^v$ norm of $v$", ty := .real ⟶ F ⟶ .real,
      doms := [dom1 .real fun p => le (num 1) p, dom2 F pIntegrable],
      doc := "`(∫|f|^p)^{1/p}`, `p ≥ 1`, of a `p`-integrable function (Mathlib `MeasureTheory.eLpNorm`)",
      value := close <| lamT .real (fun p => le (num 1) p) fun p => lamT F (fun f => pIntegrable p f) fun f =>
        rpow (integral line (absPow f p)) (div (num 1) p) },
    { name := phrase!"essential supremum of $v$", ty := F ⟶ .real,
      doms := [dom1 F essBounded], doc := "the least `M` with `|f| ≤ M` almost everywhere, of an essentially bounded function (Mathlib `essSup`)",
      value := close <| lamT F essBounded fun f => theR fun m => isEssSup f m },
    { name := phrase!"Hölder conjugate of $v$", ty := .real ⟶ .real,
      doms := [dom1 .real fun p => lt (num 1) p], doc := "`p/(p-1)`, `p > 1` (Mathlib `Real.conjExponent`)",
      value := close <| lamT .real (fun p => lt (num 1) p) fun p => div p (sub p (num 1)) },
    { name := phrase!"Holder conjugate of $v$", ty := .real ⟶ .real,
      doms := [dom1 .real fun p => lt (num 1) p], doc := "`p/(p-1)`, `p > 1`",
      value := close <| lamT .real (fun p => lt (num 1) p) fun p => div p (sub p (num 1)) },
    { name := phrase!"improper integral of $v$ from $v$ to infinity", ty := F ⟶ .real ⟶ .real,
      doms := [dom1 F locInt, dom2 .real fun f a => exR fun l => toInfinity f a l],
      doc := "`lim_{b→∞} ∫_a^b f`, of a locally integrable function where the limit exists",
      value := close <| lamT F locInt fun f => lamT .real (fun a => exR fun l => toInfinity f a l) fun a =>
        theR fun l => toInfinity f a l },
    { name := phrase!"improper integral of $v$ from minus infinity to $v$", ty := F ⟶ .real ⟶ .real,
      doms := [dom1 F locInt, dom2 .real fun f b => exR fun l => fromMinusInfinity f b l],
      doc := "`lim_{a→-∞} ∫_a^b f`, where the limit exists",
      value := close <| lamT F locInt fun f => lamT .real (fun b => exR fun l => fromMinusInfinity f b l) fun b =>
        theR fun l => fromMinusInfinity f b l },
    { name := phrase!"improper integral of $v$ over the real line", ty := F ⟶ .real,
      doms := [dom1 F fun f => and (locInt f) (exR fun l => overLine f l)],
      doc := "`lim ∫_a^b f` as `a → -∞` and `b → ∞` independently, where the limit exists",
      value := close <| lamT F (fun f => and (locInt f) (exR fun l => overLine f l)) fun f => theR fun l => overLine f l },
    { name := phrase!"integral of $v$ on the set $v$", ty := F ⟶ S ⟶ .real,
      doms := [none, dom2 S fun f s => integrable s f],
      doc := "`∫_S f`, where `f` is integrable on `S` (Mathlib `MeasureTheory.integral` on `S`)",
      value := close <| lamT F (fun _ => tt) fun f => lamT S (fun s => integrable s f) fun s => integral s f }]

end Leanify.Integration
