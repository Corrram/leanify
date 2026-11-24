import Leanify.Library.Core

/-! # Vocabulary: calculus of one real variable

Higher derivatives, Taylor polynomials, antiderivatives, and the quantities of a first
course in integration: arc length, average value, the area between two graphs and the
volume of a solid of revolution. The functions are those of the field `realfunctions` (`Let $f$
be a twice differentiable function.`).

* adjectives of functions: `$n$ times differentiable`, `twice differentiable`, `$n$ times
  continuously differentiable`, `twice continuously differentiable`;
* adjectives of functions, with another function: `antiderivative of $f$`, `primitive of
  $f$` (`F' = f`);
* adjectives of points, with the function: `critical point of $f$` (`f'(x) = 0`),
  `inflection point of $f$` (`f` is convex on one side of `x` and concave on the other);
* notions: the `n`th, second and third derivative, the Taylor polynomial of degree `n` of
  `f` at `a`, the arc length of the graph of `f` on `[a,b]`, the average value of `f` on
  `[a,b]`, the area between the graphs of `f` and `g` on `[a,b]`, and the volume of the
  solid of revolution of `f` on `[a,b]`.

The higher derivatives are constants, Mathlib's `iteratedDeriv` and `ContDiff`
(`Leanify/Library/CalculusModel.lean`), for a natural number `n` given as a real number.
A derivative of order `n` is defined for a function that is `n` times differentiable, an
arc length for a continuously differentiable function, and an integral where its
integrand is integrable on `[a,b]`. -/

namespace Leanify.Calculus
open Build Core

abbrev F : Ty := Ty.rfun

/-- The `n`th derivative of `f`. -/
def nth (n f : B) : B := app2 (const 0) n f
def contDiffN (n f : B) : B := app2 (const 1) n f
def diffN (n f : B) : B := app2 (const 2) n f

def line : B := lamR fun _ => tt
def hasDeriv (f x d : B) : B := app2 (app2 (prim .hasDerivWithin) f line) x d
def natP (n : B) : B := and (isInt n) (le (num 0) n)
def sqrt (x : B) : B := app2 (prim .rpow) x (div (num 1) (num 2))
def pi : B := prim .pi
/-- `∫_a^b g`. -/
def integ (a b g : B) : B := app (app (app (prim .intervalIntegral) a) b) g
/-- `g` is integrable on `[a,b]`. -/
def integrable (g a b : B) : B := app2 (app (prim .intervalIntegrable) g) a b

def convexOn (f s : B) : B := app2 (prim (.fnProp .convex)) f s
def concaveOn (f s : B) : B := app2 (prim .concaveOn) f s
/-- `(x-d, x]` and `[x, x+d)`. -/
def leftOf (x d : B) : B := lamR fun y => and (lt (sub x d) y) (le y x)
def rightOf (x d : B) : B := lamR fun y => and (le x y) (lt y (add x d))
def inflection (f x : B) : B :=
  exR fun d => and (lt (num 0) d)
    (or (and (convexOn f (leftOf x d)) (concaveOn f (rightOf x d)))
      (and (concaveOn f (leftOf x d)) (convexOn f (rightOf x d))))

/-- `∑_{k=0}^{n} f^{(k)}(a)/k! (x-a)^k`. -/
def taylor (n f a x : B) : B :=
  app (app (app (prim .finSum) (num 0)) n) (lamR fun k =>
    mul (div (app (nth k f) a) (app (prim .factorial) k)) (app2 (prim .zpow) (sub x a) k))

def fPred (p : B → B) : Tm := close <| lamT F (fun _ => tt) p
def adj (p : Phrase) (pred : Tm) (doc : String) : Modifier := { phrase := p, prenominal := true, ty := F, pred, doc }
/-- A property of a point `x` with the function (`P f x`, the function first). -/
def ofFn (p : Phrase) (body : B → B → B) (doc : String) : Modifier :=
  { phrase := p, prenominal := false, ty := .real, doc, pred := close <| lamT F (fun _ => tt) fun f => lamR fun x => body f x }
/-- A property of a function `g` with another function `f` (`P f g`). -/
def ofFnF (p : Phrase) (body : B → B → B) (doc : String) : Modifier :=
  { phrase := p, prenominal := false, ty := F, doc,
    pred := close <| lamT F (fun _ => tt) fun f => lamT F (fun _ => tt) fun g => body f g }
/-- A derivative of a fixed order `k`. -/
def derivK (name : Phrase) (k : Nat) (doc : String) : Notion :=
  { name, ty := F ⟶ F, doms := [dom1 F fun f => diffN (num k) f], doc,
    value := close <| lamT F (fun f => diffN (num k) f) fun f => nth (num k) f }
/-- A quantity of a function on `[a,b]`, with the condition `d f a b`. -/
def onAB (name : Phrase) (d : B → B → B → B) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty := F ⟶ .real ⟶ .real ⟶ .real, doms := [none, none, dom3 .real d], doc,
    value := close <| lamT F (fun _ => tt) fun f => lamR fun a => lamT .real (fun b => d f a b) fun b => body f a b }

def vocab : Vocab where
  consts := [.real ⟶ F ⟶ F, .real ⟶ F ⟶ .prop, .real ⟶ F ⟶ .prop]
  constNames := [w!"#2^{(#1)}", w!"#2\\in C^{#1}", w!"#2\\in \\mathcal{D}^{#1}"]
  constLean := [w!"Leanify.Calculus.nthDeriv", w!"Leanify.Calculus.TimesContDiff", w!"Leanify.Calculus.TimesDiff"]
  modules := [w!"Leanify.Library.CalculusModel"]
  mods := [
    adj phrase!"$v$ times differentiable" (close <| lamR fun n => lamT F (fun _ => tt) fun f => diffN n f)
      "the derivatives of order `k < n` are differentiable (Mathlib `iteratedDeriv`)",
    adj phrase!"twice differentiable" (fPred fun f => diffN (num 2) f) "`f` and `f'` are differentiable",
    adj phrase!"$v$ times continuously differentiable" (close <| lamR fun n => lamT F (fun _ => tt) fun f => contDiffN n f)
      "of class `C^n` (Mathlib `ContDiff ℝ n`)",
    adj phrase!"twice continuously differentiable" (fPred fun f => contDiffN (num 2) f) "of class `C²` (Mathlib `ContDiff ℝ 2`)",
    ofFnF phrase!"antiderivative of $v$" (fun f g => allR fun x => hasDeriv g x (app f x))
      "`F'(x) = f(x)` for every `x` (Mathlib `HasDerivAt`)",
    ofFnF phrase!"primitive of $v$" (fun f g => allR fun x => hasDeriv g x (app f x)) "`F'(x) = f(x)` for every `x`",
    ofFn phrase!"critical point of $v$" (fun f x => hasDeriv f x (num 0)) "`f'(x) = 0`",
    ofFn phrase!"inflection point of $v$" inflection
      "`f` is convex on `(x-δ, x]` and concave on `[x, x+δ)`, or the other way round, for some `δ > 0`"]
  notions := [
    { name := phrase!"$v$th derivative of $v$", ty := .real ⟶ F ⟶ F,
      doms := [dom1 .real natP, dom2 F fun n f => diffN n f],
      doc := "`f^{(n)}`, of an `n` times differentiable function (Mathlib `iteratedDeriv`)",
      value := close <| lamT .real natP fun n => lamT F (fun f => diffN n f) fun f => nth n f },
    derivK phrase!"second derivative of $v$" 2 "`f''`, of a twice differentiable function",
    derivK phrase!"third derivative of $v$" 3 "`f'''`, of a three times differentiable function",
    { name := phrase!"Taylor polynomial of degree $v$ of $v$ at $v$", ty := .real ⟶ F ⟶ .real ⟶ F,
      doms := [dom1 .real natP, dom2 F fun n f => diffN n f, none],
      doc := "`x ↦ ∑_{k=0}^{n} f^{(k)}(a)/k! (x-a)^k` (Mathlib `taylorWithinEval`)",
      value := close <| lamT .real natP fun n => lamT F (fun f => diffN n f) fun f => lamR fun a =>
        lamR fun x => taylor n f a x },
    { name := phrase!"arc length of the graph of $v$ on $[v,v]$", ty := F ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 F fun f => contDiffN (num 1) f, none, dom2 .real fun a b => le a b],
      doc := "`∫_a^b √(1 + f'(x)²) dx`, `a ≤ b`, of a continuously differentiable function",
      value := close <| lamT F (fun f => contDiffN (num 1) f) fun f => lamR fun a => lamT .real (fun b => le a b) fun b =>
        integ a b (lamR fun x => sqrt (add (num 1) (mul (app (nth (num 1) f) x) (app (nth (num 1) f) x)))) },
    onAB phrase!"average value of $v$ on $[v,v]$" (fun f a b => and (lt a b) (integrable f a b))
      (fun f a b => div (integ a b f) (sub b a))
      "`(1/(b-a)) ∫_a^b f`, `a < b`, of a function integrable on `[a,b]`",
    { name := phrase!"area between the graphs of $v$ and $v$ on $[v,v]$", ty := F ⟶ F ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, none, none, dom4 .real fun f g a b => and (le a b) (integrable (lamR fun x => abs (sub (app f x) (app g x))) a b)],
      doc := "`∫_a^b |f - g|`, `a ≤ b`, where `|f - g|` is integrable on `[a,b]`",
      value := close <| lamT F (fun _ => tt) fun f => lamT F (fun _ => tt) fun g => lamR fun a =>
        lamT .real (fun b => and (le a b) (integrable (lamR fun x => abs (sub (app f x) (app g x))) a b)) fun b =>
          integ a b (lamR fun x => abs (sub (app f x) (app g x))) },
    onAB phrase!"volume of the solid of revolution of $v$ on $[v,v]$"
      (fun f a b => and (le a b) (integrable (lamR fun x => mul (app f x) (app f x)) a b))
      (fun f a b => mul pi (integ a b (lamR fun x => mul (app f x) (app f x))))
      "`π ∫_a^b f²`, `a ≤ b`, where `f²` is integrable on `[a,b]`"]

end Leanify.Calculus
