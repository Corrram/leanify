import Leanify.Library.Core

/-! # Vocabulary: real functions (the field `realfunctions`)

Functions of a real variable by their noun, with the properties of real analysis. A
function is a real function on the whole line, so that an article writes `Let $f$ be a
continuous function.` or `every bounded increasing function $f$`.

* nouns: `function`, `real function`, `bijection`;
* adjectives: `continuous`, `uniformly continuous`, `Lipschitz`, `$L$-Lipschitz`,
  `differentiable`, `continuously differentiable`, `smooth`, `analytic`, `bounded`,
  `increasing` and `nondecreasing`, `decreasing` and `nonincreasing`, `strictly
  increasing`, `strictly decreasing`, `monotone`, `convex`, `concave`, `strictly convex`,
  `even`, `odd`, `periodic`, `$T$-periodic`, `injective`, `surjective`, `bijective`,
  `constant`, `measurable`, `integrable`, `of bounded variation on $[a,b]$`,
  `Hölder continuous with exponent $\alpha$`;
* notions: the derivative, the supremum norm, the Lipschitz constant, the total variation
  on an interval, the integral over the line, the inverse and the composition, the range,
  the sets of zeros, of fixed points and of critical points.

The properties that the core language has (continuity, monotonicity, convexity, …) are
its terms, on the whole line; the others are constants, interpreted by
`Leanify/Library/AnalysisModel.lean`. -/

namespace Leanify.Analysis
open Build Core

abbrev F : Ty := Ty.rfun

/-- The constants, in the order of their indices: `(type, TeX name, Lean name)`. -/
def table : List (Ty × Codes × Codes) := [
  (F ⟶ .prop, w!"\\operatorname{UniformlyContinuous}", w!"Leanify.Analysis.UniformlyContinuous"), -- 0
  (F ⟶ .prop, w!"\\operatorname{Smooth}", w!"Leanify.Analysis.Smooth"),                          -- 1
  (F ⟶ .prop, w!"\\operatorname{Analytic}", w!"Leanify.Analysis.Analytic"),                      -- 2
  (F ⟶ .prop, w!"\\operatorname{Measurable}", w!"Leanify.Analysis.IsMeasurable"),                -- 3
  (F ⟶ .prop, w!"\\operatorname{Integrable}", w!"Leanify.Analysis.IsIntegrable"),                -- 4
  (.real ⟶ .real ⟶ F ⟶ .prop, w!"\\operatorname{BV}", w!"Leanify.Analysis.BoundedVariation"),    -- 5
  (.real ⟶ F ⟶ .prop, w!"\\operatorname{Hölder}", w!"Leanify.Analysis.Holder"),                  -- 6
  (F ⟶ F, w!"#'", w!"Leanify.Analysis.derivative"),                                               -- 7
  (F ⟶ .real, w!"\\lVert #\\rVert_\\infty", w!"Leanify.Analysis.supNorm"),                        -- 8
  (F ⟶ .real, w!"\\operatorname{Lip}", w!"Leanify.Analysis.lipschitzConstant"),                  -- 9
  (F ⟶ .real ⟶ .real ⟶ .real, w!"\\operatorname{V}", w!"Leanify.Analysis.totalVariation"),       -- 10
  (F ⟶ .real, w!"\\int_{\\mathbb{R}}", w!"Leanify.Analysis.integral"),                            -- 11
  (F ⟶ F, w!"#^{-1}", w!"Leanify.Analysis.inverse"),                                              -- 12
  (F ⟶ .prop, w!"\\operatorname{C^1}", w!"Leanify.Analysis.ContinuouslyDifferentiable")]         -- 13

def all : B := lamR fun _ => tt
def fPred (p : B → B) : Tm := close <| lamT F (fun _ => tt) p
def onLine (p : Prim) : Tm := fPred fun f => app2 (prim p) f all
def fnP (k : FnProp) : Tm := onLine (.fnProp k)
def c1 (i : Nat) (f : B) : B := app (const i) f

def injective (f : B) : B := allR fun x => allR fun y => imp (eq (app f x) (app f y)) (eq x y)
def surjective (f : B) : B := allR fun y => exR fun x => eq (app f x) y
def bounded (f : B) : B := exR fun m => allR fun x => le (abs (app f x)) m
def differentiable : Tm := fnP .differentiable
def lipschitzWith (l f : B) : B :=
  and (le (num 0) l) (allR fun x => allR fun y => le (abs (sub (app f x) (app f y))) (mul l (abs (sub x y))))
def lipschitz (f : B) : B := exR fun l => lipschitzWith l f

def mod (p : Phrase) (pre : Bool) (pred : Tm) (doc : String) : Modifier :=
  { phrase := p, prenominal := pre, ty := F, pred, doc }
def nounF (sing plural : Phrase) (pred : Tm) (doc : String) : Noun := { sing, plural, ty := F, pred, doc }
def ofF (name : Phrase) (value : Tm) (ty : Ty) (dom : Option Tm) (doc : String) : Notion :=
  { name, value, ty, doms := [dom], doc }

def vocab : Vocab where
  consts := table.map (·.1)
  constNames := table.map (·.2.1)
  constLean := table.map (·.2.2)
  modules := [w!"Leanify.Library.AnalysisModel"]
  nouns := [
    nounF phrase!"function" phrase!"functions" (fPred fun _ => tt) "a real function on the line (`ℝ → ℝ`)",
    nounF phrase!"real function" phrase!"real functions" (fPred fun _ => tt) "`ℝ → ℝ`",
    nounF phrase!"bijection" phrase!"bijections" (fPred fun f => and (injective f) (surjective f))
      "of the line (Mathlib `Function.Bijective`)"]
  mods := [
    mod phrase!"continuous" true (onLine .continuousOn) "(Mathlib `Continuous`)",
    mod phrase!"uniformly continuous" true (.const 0) "(Mathlib `UniformContinuous`)",
    mod phrase!"Lipschitz" true (fPred fun f => lipschitz f) "`|f(x) - f(y)| ≤ L|x - y|` for some `L` (Mathlib `LipschitzWith`)",
    mod phrase!"Lipschitz continuous" true (fPred fun f => lipschitz f) "(Mathlib `LipschitzWith`)",
    mod phrase!"$v$-Lipschitz" true (close <| lamR fun l => lamT F (fun _ => tt) fun f => lipschitzWith l f)
      "`|f(x) - f(y)| ≤ L|x - y|` (Mathlib `LipschitzWith`)",
    mod phrase!"differentiable" true differentiable "at every point (Mathlib `Differentiable`)",
    mod phrase!"continuously differentiable" true (.const 13) "(Mathlib `ContDiff ℝ 1`)",
    mod phrase!"smooth" true (.const 1) "infinitely differentiable (Mathlib `ContDiff ℝ ⊤`)",
    mod phrase!"infinitely differentiable" true (.const 1) "(Mathlib `ContDiff ℝ ⊤`)",
    mod phrase!"analytic" true (.const 2) "real analytic at every point (Mathlib `AnalyticOnNhd`)",
    mod phrase!"bounded" true (fPred fun f => bounded f) "`|f| ≤ M` for some `M`",
    mod phrase!"increasing" true (fnP .monotone) "`x ≤ y → f(x) ≤ f(y)` (Mathlib `Monotone`)",
    mod phrase!"nondecreasing" true (fnP .monotone) "(Mathlib `Monotone`)",
    mod phrase!"decreasing" true (fnP .antitone) "`x ≤ y → f(y) ≤ f(x)` (Mathlib `Antitone`)",
    mod phrase!"nonincreasing" true (fnP .antitone) "(Mathlib `Antitone`)",
    mod phrase!"strictly increasing" true (onLine .strictMonoOn) "(Mathlib `StrictMono`)",
    mod phrase!"strictly decreasing" true (fnP .strictAnti) "(Mathlib `StrictAnti`)",
    mod phrase!"monotone" true (fPred fun f => or (app2 (prim (.fnProp .monotone)) f all) (app2 (prim (.fnProp .antitone)) f all))
      "increasing or decreasing",
    mod phrase!"convex" true (fnP .convex) "(Mathlib `ConvexOn`)",
    mod phrase!"concave" true (onLine .concaveOn) "(Mathlib `ConcaveOn`)",
    mod phrase!"strictly convex" true (fnP .strictConvex) "(Mathlib `StrictConvexOn`)",
    mod phrase!"strictly concave" true (fnP .strictConcave) "(Mathlib `StrictConcaveOn`)",
    mod phrase!"even" true (fPred fun f => allR fun x => eq (app f (neg x)) (app f x)) "`f(-x) = f(x)`",
    mod phrase!"odd" true (fPred fun f => allR fun x => eq (app f (neg x)) (neg (app f x))) "`f(-x) = -f(x)`",
    mod phrase!"periodic" true (fPred fun f => exR fun t => and (lt (num 0) t) (allR fun x => eq (app f (add x t)) (app f x)))
      "`f(x + T) = f(x)` for some `T > 0` (Mathlib `Function.Periodic`)",
    mod phrase!"$v$-periodic" true (close <| lamR fun t => lamT F (fun _ => tt) fun f => allR fun x => eq (app f (add x t)) (app f x))
      "`f(x + T) = f(x)` (Mathlib `Function.Periodic`)",
    mod phrase!"injective" true (fPred fun f => injective f) "(Mathlib `Function.Injective`)",
    mod phrase!"surjective" true (fPred fun f => surjective f) "onto `ℝ` (Mathlib `Function.Surjective`)",
    mod phrase!"bijective" true (fPred fun f => and (injective f) (surjective f)) "(Mathlib `Function.Bijective`)",
    mod phrase!"constant" true (fPred fun f => allR fun x => allR fun y => eq (app f x) (app f y)) "`f(x) = f(y)`",
    mod phrase!"measurable" true (.const 3) "(Mathlib `Measurable`)",
    mod phrase!"integrable" true (.const 4) "Lebesgue integrable on the line (Mathlib `MeasureTheory.Integrable`)",
    mod phrase!"of bounded variation on $[v,v]$" false (.const 5) "(Mathlib `BoundedVariationOn`)",
    mod phrase!"Hölder continuous with exponent $v$" false (.const 6) "`|f(x) - f(y)| ≤ C|x - y|^α` (Mathlib `HolderWith`)",
    mod phrase!"Holder continuous with exponent $v$" false (.const 6) "(Mathlib `HolderWith`)"]
  notions := [
    ofF phrase!"derivative of $v$" (.const 7) (F ⟶ F) (some differentiable) "of a differentiable function (Mathlib `deriv`)",
    ofF phrase!"supremum norm of $v$" (.const 8) (F ⟶ .real) (some (fPred fun f => bounded f))
      "`sup |f|`, of a bounded function",
    ofF phrase!"Lipschitz constant of $v$" (.const 9) (F ⟶ .real) (some (fPred fun f => lipschitz f))
      "the least `L`, of a Lipschitz function",
    { name := phrase!"total variation of $v$ on $[v,v]$", ty := F ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, none, dom3 .real fun f a b => app (app (app (const 5) a) b) f],
      doc := "of a function of bounded variation there (Mathlib `eVariationOn`)",
      value := close <| lamT F (fun _ => tt) fun f => lamR fun a => lamR fun b =>
        guard (app (app (app (const 5) a) b) f) (app (app (app (const 10) f) a) b) },
    ofF phrase!"integral of $v$ over $\\mathbb{R}$" (.const 11) (F ⟶ .real) (some (.const 4))
      "of an integrable function (Mathlib `MeasureTheory.integral`)",
    ofF phrase!"inverse of $v$" (.const 12) (F ⟶ F) (some (fPred fun f => and (injective f) (surjective f)))
      "of a bijection (Mathlib `Function.invFun`)",
    { name := phrase!"composition of $v$ and $v$", ty := F ⟶ F ⟶ F, doc := "`f ∘ g`",
      value := close <| lamT F (fun _ => tt) fun f => lamT F (fun _ => tt) fun g => lamR fun x => app f (app g x) },
    ofF phrase!"range of $v$" (close <| lamT F (fun _ => tt) fun f => lamR fun y => exR fun x => eq (app f x) y)
      (F ⟶ .real ⟶ .prop) none "`f(ℝ)` (Mathlib `Set.range`)",
    ofF phrase!"image of $v$" (close <| lamT F (fun _ => tt) fun f => lamR fun y => exR fun x => eq (app f x) y)
      (F ⟶ .real ⟶ .prop) none "`f(ℝ)` (Mathlib `Set.range`)",
    ofF phrase!"set of zeros of $v$" (close <| lamT F (fun _ => tt) fun f => lamR fun x => eq (app f x) (num 0))
      (F ⟶ .real ⟶ .prop) none "`{x : f(x) = 0}`",
    ofF phrase!"set of fixed points of $v$" (close <| lamT F (fun _ => tt) fun f => lamR fun x => eq (app f x) x)
      (F ⟶ .real ⟶ .prop) none "`{x : f(x) = x}`",
    ofF phrase!"set of critical points of $v$"
      (close <| lamT F (fun _ => tt) fun f => lamR fun x => eq (app (app (const 7) f) x) (num 0))
      (F ⟶ .real ⟶ .prop) (some differentiable) "`{x : f'(x) = 0}`, of a differentiable function"]

end Leanify.Analysis
