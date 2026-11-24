import Leanify.Library.Core

/-! # Vocabulary: expected utility and risk aversion

Utility functions on the line and the quantities of decision theory under risk for a
lottery with two outcomes (`Let $u$ be a risk averse utility function.`, `We write
$A_u(x)$ for the Arrow-Pratt coefficient of absolute risk aversion of $u$ at $x$.`).

* nouns: `utility function`, `Bernoulli utility function` (real functions);
* adjectives of utility functions: `risk averse` (concave), `strictly risk averse`
  (strictly concave), `risk seeking` (convex), `risk neutral` (affine), `with decreasing
  absolute risk aversion` (`-u''/u'` nonincreasing, for a twice differentiable `u` with
  `u' > 0`);
* notions: the Arrow–Pratt coefficients of absolute (`-u''(x)/u'(x)`) and relative
  (`-x u''(x)/u'(x)`) risk aversion; the exponential (CARA) utility with risk aversion
  `a > 0` (`(1 - e^{-ax})/a`) and the power (CRRA) utility with relative risk aversion
  `γ > 0`, `γ ≠ 1` (`x^{1-γ}/(1-γ)`); for the lottery paying `x` with probability `p` and
  `y` otherwise, the expected value, the expected utility `p u(x) + (1-p) u(y)`, the
  certainty equivalent (the `c` with `u(c)` the expected utility, for a continuous
  strictly increasing `u`) and the risk premium (expected value minus certainty
  equivalent).

Every meaning is a term of the core language. -/

namespace Leanify.Utility
open Build Core

abbrev F : Ty := Ty.rfun

def line : B := lamR fun _ => tt
def hasDeriv (f x d : B) : B := app2 (app2 (prim .hasDerivWithin) f line) x d
def deriv (f x : B) : B := theR fun d => hasDeriv f x d
def diffAt (f x : B) : B := exR fun d => hasDeriv f x d
def d1 (u : B) : B := lamR fun y => deriv u y
def twice (u x : B) : B := and (allR fun y => diffAt u y) (diffAt (d1 u) x)
def d2 (u x : B) : B := deriv (d1 u) x
def ara (u x : B) : B := neg (div (d2 u x) (deriv u x))
def araDom (u x : B) : B := and (twice u x) (ne (deriv u x) (num 0))
def exp (x : B) : B := app (prim (.realFn .exp)) x
def rpow (x y : B) : B := app2 (prim .rpow) x y
def prob (p : B) : B := and (le (num 0) p) (le p (num 1))
def eu (u x p y : B) : B := add (mul p (app u x)) (mul (sub (num 1) p) (app u y))
def ev (x p y : B) : B := add (mul p x) (mul (sub (num 1) p) y)
def regular (u : B) : B := and (app2 (prim .continuousOn) u line) (app2 (prim .strictMonoOn) u line)
def ce (u x p y : B) : B := theR fun c => eq (app u c) (eu u x p y)
def fPred (p : B → B) : Tm := close <| lamT F (fun _ => tt) p
def adj (p : Phrase) (pre : Bool) (body : B → B) (doc : String) : Modifier :=
  { phrase := p, prenominal := pre, ty := F, pred := fPred body, doc }
def uNoun (s pl : Phrase) (doc : String) : Noun :=
  { sing := s, plural := pl, ty := F, pred := fPred fun _ => tt, doc }
/-- A lottery notion of `u`, `x`, `p`, `y`: `p ∈ [0,1]`, and `dom u` of `u`. -/
def lottery (name : Phrase) (d : B → B) (body : B → B → B → B → B) (doc : String) : Notion :=
  { name, ty := F ⟶ .real ⟶ .real ⟶ .real ⟶ .real, doms := [dom1 F d, none, dom1 .real prob, none], doc,
    value := close <| lamT F d fun u => lamR fun x => lamT .real prob fun p => lamR fun y => body u x p y }

def vocab : Vocab where
  nouns := [
    uNoun phrase!"utility function" phrase!"utility functions" "a real function on the line",
    uNoun phrase!"Bernoulli utility function" phrase!"Bernoulli utility functions" "a real function on the line"]
  mods := [
    adj phrase!"risk averse" true (fun u => app2 (prim .concaveOn) u line) "concave (Mathlib `ConcaveOn`)",
    adj phrase!"strictly risk averse" true (fun u => app2 (prim (.fnProp .strictConcave)) u line) "strictly concave",
    adj phrase!"risk seeking" true (fun u => app2 (prim (.fnProp .convex)) u line) "convex",
    adj phrase!"risk neutral" true (fun u => exR fun a => exR fun b => allR fun x => eq (app u x) (add a (mul b x))) "affine: `u(x) = a + bx`",
    adj phrase!"with decreasing absolute risk aversion" false
      (fun u => and (allR fun x => and (twice u x) (lt (num 0) (deriv u x)))
        (allR fun x => allR fun y => imp (le x y) (le (ara u y) (ara u x))))
      "twice differentiable, `u' > 0`, and `-u''/u'` nonincreasing (DARA)"]
  notions := [
    { name := phrase!"Arrow-Pratt coefficient of absolute risk aversion of $v$ at $v$", ty := F ⟶ .real ⟶ .real,
      doms := [none, dom2 .real araDom],
      doc := "`-u''(x)/u'(x)`, where `u` is twice differentiable at `x` and `u'(x) ≠ 0`",
      value := close <| lamT F (fun _ => tt) fun u => lamT .real (fun x => araDom u x) fun x => ara u x },
    { name := phrase!"coefficient of relative risk aversion of $v$ at $v$", ty := F ⟶ .real ⟶ .real,
      doms := [none, dom2 .real araDom],
      doc := "`-x u''(x)/u'(x)`",
      value := close <| lamT F (fun _ => tt) fun u => lamT .real (fun x => araDom u x) fun x => mul x (ara u x) },
    { name := phrase!"exponential utility with risk aversion $v$", ty := .real ⟶ F, doms := [dom1 .real fun a => lt (num 0) a],
      doc := "`x ↦ (1 - e^{-ax})/a`, `a > 0` (CARA)",
      value := close <| lamT .real (fun a => lt (num 0) a) fun a => lamR fun x => div (sub (num 1) (exp (neg (mul a x)))) a },
    { name := phrase!"power utility with relative risk aversion $v$", ty := .real ⟶ F,
      doms := [dom1 .real fun g => and (lt (num 0) g) (ne g (num 1))],
      doc := "`x ↦ x^{1-γ}/(1-γ)` (for `x > 0`), `γ > 0`, `γ ≠ 1` (CRRA)",
      value := close <| lamT .real (fun g => and (lt (num 0) g) (ne g (num 1))) fun g => lamR fun x =>
        div (rpow x (sub (num 1) g)) (sub (num 1) g) },
    lottery phrase!"expected utility under $v$ of the lottery paying $v$ with probability $v$ and $v$ otherwise"
      (fun _ => tt) eu "`p u(x) + (1-p) u(y)`",
    { name := phrase!"expected value of the lottery paying $v$ with probability $v$ and $v$ otherwise",
      ty := .real ⟶ .real ⟶ .real ⟶ .real, doms := [none, dom1 .real prob, none], doc := "`p x + (1-p) y`",
      value := close <| lamR fun x => lamT .real prob fun p => lamR fun y => ev x p y },
    lottery phrase!"certainty equivalent under $v$ of the lottery paying $v$ with probability $v$ and $v$ otherwise"
      regular ce "the `c` with `u(c) = p u(x) + (1-p) u(y)`, for a continuous strictly increasing `u`",
    lottery phrase!"risk premium under $v$ of the lottery paying $v$ with probability $v$ and $v$ otherwise"
      regular (fun u x p y => sub (ev x p y) (ce u x p y)) "`p x + (1-p) y` minus the certainty equivalent"]

end Leanify.Utility
