import Leanify.Library.Markov

/-! # Vocabulary: copula families and measures of dependence

The copulas of the field `unitsquare` by name, the measures of concordance and dependence
of a copula, and its dependence properties. The field includes `markov` (and so
`hilbert` and `unitsquare`): `Let $C$ be a copula.` binds a copula, a function of two
points of `[0,1]`.

* copulas: the independence copula `Π(u,v) = uv`, the comonotonicity copula `M = min(u,v)`
  (also `upper Fréchet–Hoeffding bound`), the countermonotonicity copula
  `W = max(u+v-1, 0)` (`lower Fréchet–Hoeffding bound`), and the Clayton (`θ > 0`),
  Gumbel (`θ ≥ 1`), Frank (`θ ≠ 0`), Farlie–Gumbel–Morgenstern (`|θ| ≤ 1`),
  Ali–Mikhail–Haq (`-1 ≤ θ < 1`), Cuadras–Augé (`0 ≤ θ ≤ 1`), Marshall–Olkin
  (`α, β ∈ [0,1]`) and Gaussian (`|ρ| < 1`) copulas with their parameters;
* measures of a copula: Spearman's rho `12∫∫C - 3`, Kendall's tau `4∫C dC - 1`,
  Blomqvist's beta `4C(1/2,1/2) - 1`, Spearman's footrule `6∫C(t,t)dt - 2`, Gini's gamma
  `4∫(C(t,t) + C(t,1-t))dt - 2`, Chatterjee's xi `6∫∫(∂₁C)² - 2`, and the lower and upper
  tail dependence coefficients (where the limits exist);
* adjectives of copulas: `positively quadrant dependent` (`C ≥ Π`), `negatively quadrant
  dependent`, `radially symmetric`, `left tail decreasing`, `max-stable` (an extreme-value
  copula); `more concordant than $D$` (`C ≥ D` pointwise).

Every meaning is a term of the core language with the constants of `unitsquare`: the
points of `[0,1]` and their numbers, the integral over `[0,1]`, the integral against the
measure of a copula, the conditional distribution function `∂₁C` and the standard normal
quantile function. -/

namespace Leanify.Copulas
open Build Core
open Leanify.UnitSquare (I01 sq isCopula)

def val (u : B) : B := app (const UnitSquare.val) u
def pt (x : B) : B := app (const UnitSquare.point) x
def int1 (g : B → B) : B := app (const UnitSquare.integral) (lamT I01 (fun _ => tt) g)
def against (f c : B) : B := app2 (const UnitSquare.integral2) f c
def condDF (c : B) : B := app (const UnitSquare.condDF) c
def normalQ (u : B) : B := app (const UnitSquare.normalQ) u
def copula (c : B) : B := app (lift isCopula) c

def exp (x : B) : B := app (prim (.realFn .exp)) x
def log (x : B) : B := app (prim (.realFn .log)) x
def rpow (x p : B) : B := app2 (prim .rpow) x p
def min (x y : B) : B := app2 (prim .min) x y
def max (x y : B) : B := app2 (prim .max) x y
def pi : B := prim .pi
def sqrt (x : B) : B := rpow x (div (num 1) (num 2))
def half : B := div (num 1) (num 2)

/-- A copula given by its values at the numbers `u, v ∈ [0,1]`. -/
def fam (body : B → B → B) : B := lamT I01 (fun _ => tt) fun u => lamT I01 (fun _ => tt) fun v => body (val u) (val v)
def interior (u v : B) : B := and (lt (num 0) u) (lt (num 0) v)
def clayton (t u v : B) : B :=
  cases (interior u v) (rpow (sub (add (rpow u (neg t)) (rpow v (neg t))) (num 1)) (neg (div (num 1) t))) (num 0)
def gumbel (t u v : B) : B :=
  cases (interior u v) (exp (neg (rpow (add (rpow (neg (log u)) t) (rpow (neg (log v)) t)) (div (num 1) t)))) (num 0)
def frank (t u v : B) : B :=
  neg (div (log (add (num 1) (div (mul (sub (exp (neg (mul t u))) (num 1)) (sub (exp (neg (mul t v))) (num 1)))
    (sub (exp (neg t)) (num 1))))) t)
def fgm (t u v : B) : B := mul (mul u v) (add (num 1) (mul t (mul (sub (num 1) u) (sub (num 1) v))))
def amh (t u v : B) : B := div (mul u v) (sub (num 1) (mul t (mul (sub (num 1) u) (sub (num 1) v))))
def cuadras (t u v : B) : B := mul (rpow (min u v) t) (rpow (mul u v) (sub (num 1) t))
def marshall (a b u v : B) : B := min (mul (rpow u (sub (num 1) a)) v) (mul u (rpow v (sub (num 1) b)))
/-- The bivariate normal density with correlation `ρ`. -/
def phi2 (r s t : B) : B :=
  div (exp (neg (div (add (sub (mul s s) (mul (mul (num 2) r) (mul s t))) (mul t t)) (mul (num 2) (sub (num 1) (mul r r))))))
    (mul (mul (num 2) pi) (sqrt (sub (num 1) (mul r r))))
def below (q : B) : B := lamR fun x => le x q
def gaussian (r : B) : B :=
  lamT I01 (fun _ => tt) fun u => lamT I01 (fun _ => tt) fun v =>
    cases (or (eq (val u) (num 0)) (eq (val v) (num 0))) (num 0)
      (cases (eq (val u) (num 1)) (val v)
        (cases (eq (val v) (num 1)) (val u)
          (app2 (prim .integralOn) (below (normalQ u)) (lamR fun s =>
            app2 (prim .integralOn) (below (normalQ v)) (lamR fun t => phi2 r s t)))))

def inI (t : B) : B := and (le (num 0) t) (le t (num 1))
/-- A family with one parameter in the domain `d`. -/
def fam1 (name : Phrase) (d : B → B) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ sq, doms := [dom1 .real d], doc, value := close <| lamT .real d fun t => fam (body t) }
def fixed (name : Phrase) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := sq, doc, value := close <| fam body }

/-- `C` at the points with numbers `x` and `y`. -/
def at2 (c x y : B) : B := app2 c (pt x) (pt y)
def spearman (c : B) : B := sub (mul (num 12) (int1 fun u => int1 fun v => app2 c u v)) (num 3)
def kendall (c : B) : B := sub (mul (num 4) (against c c)) (num 1)
def blomqvist (c : B) : B := sub (mul (num 4) (at2 c half half)) (num 1)
def footrule (c : B) : B := sub (mul (num 6) (int1 fun t => app2 c t t)) (num 2)
def gini (c : B) : B :=
  sub (mul (num 4) (int1 fun t => add (app2 c t t) (app2 c t (pt (sub (num 1) (val t)))))) (num 2)
def chatterjee (c : B) : B :=
  sub (mul (num 6) (int1 fun u => int1 fun v => mul (app2 (condDF c) u v) (app2 (condDF c) u v))) (num 2)
def openUnit : B := lamR fun x => and (lt (num 0) x) (lt x (num 1))
def lowerRatio (c : B) : B := lamR fun t => div (at2 c t t) t
def upperRatio (c : B) : B := lamR fun t => div (add (sub (num 1) (mul (num 2) t)) (at2 c t t)) (sub (num 1) t)
def limAt (a d f : B) : B := app (app2 (prim .limAt) a d) f
def limAtConv (a d f : B) : B := app (app2 (prim .limAtConv) a d) f

def measure (name : Phrase) (body : B → B) (doc : String) : Notion :=
  { name, ty := sq ⟶ .real, doms := [dom1 sq copula], doc, value := close <| lamT sq copula body }
def measureD (name : Phrase) (d : B → B) (body : B → B) (doc : String) : Notion :=
  { name, ty := sq ⟶ .real, doms := [dom1 sq fun c => and (copula c) (d c)], doc,
    value := close <| lamT sq (fun c => and (copula c) (d c)) body }

def forPts (body : B → B → B) : B := allT I01 fun u => allT I01 fun v => body u v
def sqPred (body : B → B) : Tm := close <| lamT sq (fun _ => tt) body

/-- The words of the field itself. -/
def own : Vocab where
  mods := [
    { phrase := phrase!"positively quadrant dependent", prenominal := true, ty := sq,
      pred := sqPred fun c => forPts fun u v => le (mul (val u) (val v)) (app2 c u v), doc := "`C(u,v) ≥ uv` (PQD)" },
    { phrase := phrase!"negatively quadrant dependent", prenominal := true, ty := sq,
      pred := sqPred fun c => forPts fun u v => le (app2 c u v) (mul (val u) (val v)), doc := "`C(u,v) ≤ uv` (NQD)" },
    { phrase := phrase!"radially symmetric", prenominal := true, ty := sq,
      pred := sqPred fun c => forPts fun u v =>
        eq (app2 c u v) (add (sub (add (val u) (val v)) (num 1)) (at2 c (sub (num 1) (val u)) (sub (num 1) (val v)))),
      doc := "`C(u,v) = u + v - 1 + C(1-u,1-v)`: `(U,V)` and `(1-U,1-V)` have the same law" },
    { phrase := phrase!"left tail decreasing", prenominal := true, ty := sq,
      pred := sqPred fun c => forPts fun u u' => allT I01 fun v =>
        imp (le (val u) (val u')) (le (mul (val u) (app2 c u' v)) (mul (val u') (app2 c u v))),
      doc := "`C(u,v)/u` is nonincreasing in `u` (LTD in the first coordinate)" },
    { phrase := phrase!"max-stable", prenominal := true, ty := sq,
      pred := sqPred fun c => allR fun t => imp (lt (num 0) t) (forPts fun u v =>
        eq (at2 c (rpow (val u) t) (rpow (val v) t)) (rpow (app2 c u v) t)),
      doc := "`C(u^t, v^t) = C(u,v)^t` for every `t > 0`: an extreme-value copula" },
    { phrase := phrase!"more concordant than $v$", prenominal := false, ty := sq,
      pred := close <| lamT sq (fun _ => tt) fun d => lamT sq (fun _ => tt) fun c => forPts fun u v => le (app2 d u v) (app2 c u v),
      doc := "`C(u,v) ≥ D(u,v)` for all `u`, `v` (the concordance order)" }]
  notions := [
    fixed phrase!"independence copula" (fun u v => mul u v) "`Π(u,v) = uv`",
    fixed phrase!"product copula" (fun u v => mul u v) "`Π(u,v) = uv`",
    fixed phrase!"comonotonicity copula" min "`M(u,v) = min(u,v)`",
    fixed phrase!"upper Fréchet-Hoeffding bound" min "`M(u,v) = min(u,v)`",
    fixed phrase!"upper Frechet-Hoeffding bound" min "`M(u,v) = min(u,v)`",
    fixed phrase!"countermonotonicity copula" (fun u v => max (sub (add u v) (num 1)) (num 0)) "`W(u,v) = max(u+v-1, 0)`",
    fixed phrase!"lower Fréchet-Hoeffding bound" (fun u v => max (sub (add u v) (num 1)) (num 0)) "`W(u,v) = max(u+v-1, 0)`",
    fixed phrase!"lower Frechet-Hoeffding bound" (fun u v => max (sub (add u v) (num 1)) (num 0)) "`W(u,v) = max(u+v-1, 0)`",
    fam1 phrase!"Clayton copula with parameter $v$" (fun t => lt (num 0) t) clayton "`(u^{-θ} + v^{-θ} - 1)^{-1/θ}`, `θ > 0`",
    fam1 phrase!"Gumbel copula with parameter $v$" (fun t => le (num 1) t) gumbel
      "`exp(-((-log u)^θ + (-log v)^θ)^{1/θ})`, `θ ≥ 1`",
    fam1 phrase!"Frank copula with parameter $v$" (fun t => ne t (num 0)) frank
      "`-(1/θ) log(1 + (e^{-θu} - 1)(e^{-θv} - 1)/(e^{-θ} - 1))`, `θ ≠ 0`",
    fam1 phrase!"Farlie-Gumbel-Morgenstern copula with parameter $v$" (fun t => le (abs t) (num 1)) fgm
      "`uv(1 + θ(1-u)(1-v))`, `|θ| ≤ 1`",
    fam1 phrase!"FGM copula with parameter $v$" (fun t => le (abs t) (num 1)) fgm "the Farlie–Gumbel–Morgenstern copula",
    fam1 phrase!"Ali-Mikhail-Haq copula with parameter $v$" (fun t => and (le (neg (num 1)) t) (lt t (num 1))) amh
      "`uv/(1 - θ(1-u)(1-v))`, `-1 ≤ θ < 1`",
    fam1 phrase!"Cuadras-Augé copula with parameter $v$" inI cuadras "`min(u,v)^θ (uv)^{1-θ}`, `0 ≤ θ ≤ 1`",
    fam1 phrase!"Cuadras-Auge copula with parameter $v$" inI cuadras "the Cuadras–Augé copula",
    { name := phrase!"Marshall-Olkin copula with parameters $v$ and $v$", ty := .real ⟶ .real ⟶ sq,
      doms := [dom1 .real inI, dom1 .real inI], doc := "`min(u^{1-α} v, u v^{1-β})`, `α, β ∈ [0,1]`",
      value := close <| lamT .real inI fun a => lamT .real inI fun b => fam (marshall a b) },
    { name := phrase!"Gaussian copula with correlation $v$", ty := .real ⟶ sq,
      doms := [dom1 .real fun r => lt (abs r) (num 1)],
      doc := "`Φ_ρ(Φ⁻¹(u), Φ⁻¹(v))`, the bivariate normal distribution function with correlation `ρ`, `|ρ| < 1`",
      value := close <| lamT .real (fun r => lt (abs r) (num 1)) gaussian },
    measure phrase!"Spearman's rho of $v$" spearman "`12∫∫C(u,v) du dv - 3`",
    measure phrase!"Kendall's tau of $v$" kendall "`4∫C dC - 1`",
    measure phrase!"Blomqvist's beta of $v$" blomqvist "`4C(1/2,1/2) - 1`",
    measure phrase!"Spearman's footrule of $v$" footrule "`6∫C(t,t)dt - 2`",
    measure phrase!"Gini's gamma of $v$" gini "`4∫(C(t,t) + C(t,1-t))dt - 2`",
    measure phrase!"Chatterjee's xi of $v$" chatterjee "`6∫∫(∂₁C(u,v))² du dv - 2`",
    measureD phrase!"lower tail dependence coefficient of $v$" (fun c => limAtConv (num 0) openUnit (lowerRatio c))
      (fun c => limAt (num 0) openUnit (lowerRatio c)) "`lim_{t→0⁺} C(t,t)/t`, where it exists",
    measureD phrase!"upper tail dependence coefficient of $v$" (fun c => limAtConv (num 1) openUnit (upperRatio c))
      (fun c => limAt (num 1) openUnit (upperRatio c)) "`lim_{t→1⁻} (1 - 2t + C(t,t))/(1-t)`, where it exists"]

/-- `markov` (with `hilbert` and `unitsquare`) and these words: one vocabulary, so that the
words of this field use the type and the constants of `unitsquare` as they are numbered
there. -/
def vocab : Vocab :=
  let K := Markov.vocab
  let O := Vocab.tag w!"copulas" own
  { K with mods := K.mods ++ O.mods, notions := K.notions ++ O.notions }

end Leanify.Copulas
