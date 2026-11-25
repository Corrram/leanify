import Leanify.Library.Core

/-! # Vocabulary: microeconomics and inequality

Elasticities and marginal quantities of a real function, production functions, and the
Lorenz curve and Gini coefficient (`We write $\varepsilon_D(p)$ for the price elasticity of $D$
at $p$.`, `Let $L$ be a Lorenz curve.`).

* notions: the elasticity of `f` at `x` (`x f'(x)/f(x)`), the marginal value `f'(x)`, the
  average value `f(x)/x`, the Cobb–Douglas function with exponents `α`, `β`
  (`(K,L) ↦ K^α L^β`), the CES function with parameter `ρ` and weight `a`
  (`(K,L) ↦ (a K^ρ + (1-a) L^ρ)^{1/ρ}`), the Gini coefficient of a Lorenz curve
  (`1 - 2 ∫_0^1 L`), the consumer surplus at price `p` for a demand `D` up to the choke price
  `P` (`∫_p^P D`);
* adjectives: `Lorenz curve` (`L(0) = 0`, `L(1) = 1`, nondecreasing and convex on `[0,1]`),
  `elastic at $x$` (`|elasticity| > 1`), `inelastic at $x$`, `with constant returns to scale`
  (of a function of two variables: `F(tK, tL) = t F(K,L)` for `t > 0`), `linearly homogeneous`.

Derivatives are descriptions; every meaning is a term of the core language. -/

namespace Leanify.Economics
open Build Core

abbrev F : Ty := Ty.rfun
abbrev F2 : Ty := .real ⟶ .real ⟶ .real

def line : B := lamR fun _ => tt
def hasDeriv (f x d : B) : B := app2 (app2 (prim .hasDerivWithin) f line) x d
def deriv (f x : B) : B := theR fun d => hasDeriv f x d
def diffAt (f x : B) : B := exR fun d => hasDeriv f x d
def rpow (x y : B) : B := app2 (prim .rpow) x y
def integral (a b g : B) : B := app (app (app (prim .intervalIntegral) a) b) g
def integrable (g a b : B) : B := app2 (app (prim .intervalIntegrable) g) a b
def unitI : B := lamR fun x => and (le (num 0) x) (le x (num 1))
def any (_ : B) : B := tt
def elasticity (f x : B) : B := div (mul x (deriv f x)) (app f x)
def elDom (f x : B) : B := and (diffAt f x) (ne (app f x) (num 0))
def lorenz (l : B) : B :=
  and (and (eq (app l (num 0)) (num 0)) (eq (app l (num 1)) (num 1)))
    (and (app2 (prim (.fnProp .monotone)) l unitI) (app2 (prim (.fnProp .convex)) l unitI))
def elastAdj (p : Phrase) (cmp : B → B) (doc : String) : Modifier :=
  { phrase := p, prenominal := false, ty := F, doc,
    pred := close <| lamR fun x => lamT F any fun f => and (elDom f x) (cmp (abs (elasticity f x))) }

def vocab : Vocab where
  mods := [
    { phrase := phrase!"Lorenz curve", prenominal := false, ty := F, pred := close <| lamT F any lorenz,
      doc := "`L(0) = 0`, `L(1) = 1`, nondecreasing and convex on `[0,1]`" },
    elastAdj phrase!"elastic at $v$" (fun e => lt (num 1) e) "`|x f'(x)/f(x)| > 1`",
    elastAdj phrase!"inelastic at $v$" (fun e => lt e (num 1)) "`|x f'(x)/f(x)| < 1`",
    elastAdj phrase!"unit elastic at $v$" (fun e => eq e (num 1)) "`|x f'(x)/f(x)| = 1`",
    { phrase := phrase!"linearly homogeneous", prenominal := true, ty := F2,
      pred := close <| lamT F2 any fun g => allR fun t => imp (lt (num 0) t) (allR fun k => allR fun l =>
        eq (app2 g (mul t k) (mul t l)) (mul t (app2 g k l))),
      doc := "`F(tK, tL) = t F(K,L)` for `t > 0` (constant returns to scale)" },
    { phrase := phrase!"with constant returns to scale", prenominal := false, ty := F2,
      pred := close <| lamT F2 any fun g => allR fun t => imp (lt (num 0) t) (allR fun k => allR fun l =>
        eq (app2 g (mul t k) (mul t l)) (mul t (app2 g k l))),
      doc := "`F(tK, tL) = t F(K,L)` for `t > 0`" }]
  notions := [
    { name := phrase!"elasticity of $v$ at $v$", ty := F ⟶ .real ⟶ .real, doms := [none, dom2 .real elDom],
      doc := "`x f'(x)/f(x)`", value := close <| lamT F any fun f => lamT .real (fun x => elDom f x) fun x => elasticity f x },
    { name := phrase!"price elasticity of $v$ at $v$", ty := F ⟶ .real ⟶ .real, doms := [none, dom2 .real elDom],
      doc := "`p D'(p)/D(p)`", value := close <| lamT F any fun f => lamT .real (fun x => elDom f x) fun x => elasticity f x },
    { name := phrase!"marginal value of $v$ at $v$", ty := F ⟶ .real ⟶ .real, doms := [none, dom2 .real diffAt],
      doc := "`f'(x)`", value := close <| lamT F any fun f => lamT .real (fun x => diffAt f x) fun x => deriv f x },
    { name := phrase!"average value of $v$ at $v$", ty := F ⟶ .real ⟶ .real, doms := [none, dom1 .real fun x => ne x (num 0)],
      doc := "`f(x)/x`", value := close <| lamT F any fun f => lamT .real (fun x => ne x (num 0)) fun x => div (app f x) x },
    { name := phrase!"Cobb-Douglas function with exponents $v$ and $v$", ty := .real ⟶ .real ⟶ F2,
      doms := [dom1 .real fun a => lt (num 0) a, dom1 .real fun b => lt (num 0) b],
      doc := "`(K,L) ↦ K^α L^β` (for `K, L ≥ 0`)",
      value := close <| lamT .real (fun a => lt (num 0) a) fun a => lamT .real (fun b => lt (num 0) b) fun b =>
        lamR fun k => lamR fun l => mul (rpow k a) (rpow l b) },
    { name := phrase!"CES function with parameter $v$ and weight $v$", ty := .real ⟶ .real ⟶ F2,
      doms := [dom1 .real fun r => ne r (num 0), dom1 .real fun a => and (lt (num 0) a) (lt a (num 1))],
      doc := "`(K,L) ↦ (a K^ρ + (1-a) L^ρ)^{1/ρ}`, `ρ ≠ 0`, `0 < a < 1`",
      value := close <| lamT .real (fun r => ne r (num 0)) fun r => lamT .real (fun a => and (lt (num 0) a) (lt a (num 1))) fun a =>
        lamR fun k => lamR fun l => rpow (add (mul a (rpow k r)) (mul (sub (num 1) a) (rpow l r))) (div (num 1) r) },
    { name := phrase!"Gini coefficient of $v$", ty := F ⟶ .real,
      doms := [dom1 F fun l => and (lorenz l) (integrable l (num 0) (num 1))],
      doc := "`1 - 2 ∫_0^1 L`, of a Lorenz curve",
      value := close <| lamT F (fun l => and (lorenz l) (integrable l (num 0) (num 1))) fun l =>
        sub (num 1) (mul (num 2) (integral (num 0) (num 1) l)) },
    { name := phrase!"consumer surplus for the demand $v$ at price $v$ up to $v$", ty := F ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, none, dom3 .real fun d p q => and (le p q) (integrable d p q)],
      doc := "`∫_p^P D`, up to the choke price `P`",
      value := close <| lamT F any fun d => lamR fun p => lamT .real (fun q => and (le p q) (integrable d p q)) fun q => integral p q d }]

end Leanify.Economics
