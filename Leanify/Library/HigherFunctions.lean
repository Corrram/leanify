import Leanify.Library.Core

/-! # Vocabulary: higher transcendental functions

Special functions beyond those of the field `special`, each by its series or integral:
the error functions, Bessel functions of integer order, the lower incomplete gamma
function, the Lambert W function, the dilogarithm, the sine integral, the Fresnel
integrals and Dawson's function (`We write $\operatorname{erf}(x)$ for the error function at
$x$.`).

* notions: `erf x = (2/√π) ∫_0^x e^{-t²} dt` and `erfc = 1 - erf`; `J_n(x) = ∑_{m≥0}
  (-1)^m (x/2)^{2m+n}/(m!(m+n)!)` and `I_n(x)` (without the sign), `n ∈ ℕ₀`; `γ(s,x) = ∫_0^x
  t^{s-1} e^{-t} dt`, `s > 0`, `x ≥ 0`; `W(x)`, the `w ≥ -1` with `w e^w = x`, `x ≥ -1/e`;
  `Li₂(x) = ∑_{k≥1} x^k/k²`, `|x| ≤ 1`; `Si(x) = ∫_0^x (sin t)/t dt`; `S(x) = ∫_0^x sin(t²) dt`,
  `C(x) = ∫_0^x cos(t²) dt`; `D(x) = e^{-x²} ∫_0^x e^{t²} dt`.

Every meaning is a term of the core language. -/

namespace Leanify.HigherFunctions
open Build Core

abbrev F : Ty := Ty.rfun

def natP (k : B) : B := and (isInt k) (le (num 0) k)
def rpow (x y : B) : B := app2 (prim .rpow) x y
def zpow (x k : B) : B := app2 (prim .zpow) x k
def fact (n : B) : B := app (prim .factorial) n
def exp (x : B) : B := app (prim (.realFn .exp)) x
def sin (x : B) : B := app (prim (.realFn .sin)) x
def cos (x : B) : B := app (prim (.realFn .cos)) x
def pi : B := prim .pi
def integral (a b g : B) : B := app (app (app (prim .intervalIntegral) a) b) g
def series (a : B) (body : B → B) : B := app2 (prim .series) a (lamT .real natP body)
def erf (x : B) : B := mul (div (num 2) (rpow pi (div (num 1) (num 2)))) (integral (num 0) x (lamR fun t => exp (neg (mul t t))))
def bessel (sign : Bool) (n x : B) : B :=
  series (num 0) fun m => div (mul (if sign then zpow (neg (num 1)) m else num 1) (zpow (div x (num 2)) (add (mul (num 2) m) n)))
    (mul (fact m) (fact (add m n)))
def fn1 (name : Phrase) (d : Option (B → B)) (body : B → B) (doc : String) : Notion :=
  match d with
  | some d => { name, ty := .real ⟶ .real, doms := [dom1 .real d], doc, value := close <| lamT .real d body }
  | none => { name, ty := .real ⟶ .real, doc, value := close <| lamR body }

def vocab : Vocab where
  notions := [
    fn1 phrase!"error function at $v$" none erf "`(2/√π) ∫_0^x e^{-t²} dt`",
    fn1 phrase!"complementary error function at $v$" none (fun x => sub (num 1) (erf x)) "`1 - erf x`",
    { name := phrase!"Bessel function of the first kind of order $v$", ty := .real ⟶ F, doms := [dom1 .real natP],
      doc := "`J_n(x) = ∑_{m≥0} (-1)^m (x/2)^{2m+n}/(m!(m+n)!)`, integer order `n ≥ 0`",
      value := close <| lamT .real natP fun n => lamR fun x => bessel true n x },
    { name := phrase!"modified Bessel function of the first kind of order $v$", ty := .real ⟶ F, doms := [dom1 .real natP],
      doc := "`I_n(x) = ∑_{m≥0} (x/2)^{2m+n}/(m!(m+n)!)`",
      value := close <| lamT .real natP fun n => lamR fun x => bessel false n x },
    { name := phrase!"lower incomplete gamma function at $v$ and $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun s => lt (num 0) s, dom1 .real fun x => le (num 0) x],
      doc := "`γ(s,x) = ∫_0^x t^{s-1} e^{-t} dt`, `s > 0`, `x ≥ 0`",
      value := close <| lamT .real (fun s => lt (num 0) s) fun s => lamT .real (fun x => le (num 0) x) fun x =>
        integral (num 0) x (lamR fun t => mul (rpow t (sub s (num 1))) (exp (neg t))) },
    fn1 phrase!"Lambert W function at $v$" (some fun x => le (neg (div (num 1) (exp (num 1)))) x)
      (fun x => theR fun w => and (le (neg (num 1)) w) (eq (mul w (exp w)) x))
      "the principal branch: the `w ≥ -1` with `w e^w = x`, for `x ≥ -1/e`",
    fn1 phrase!"dilogarithm of $v$" (some fun x => le (abs x) (num 1))
      (fun x => app2 (prim .series) (num 1) (lamT .real (fun k => and (isInt k) (le (num 1) k)) fun k => div (zpow x k) (mul k k))) "`Li₂(x) = ∑_{k≥1} x^k/k²`, `|x| ≤ 1`",
    fn1 phrase!"sine integral of $v$" none (fun x => integral (num 0) x (lamR fun t => div (sin t) t))
      "`Si(x) = ∫_0^x (sin t)/t dt`",
    fn1 phrase!"Fresnel sine integral of $v$" none (fun x => integral (num 0) x (lamR fun t => sin (mul t t))) "`S(x) = ∫_0^x sin(t²) dt`",
    fn1 phrase!"Fresnel cosine integral of $v$" none (fun x => integral (num 0) x (lamR fun t => cos (mul t t))) "`C(x) = ∫_0^x cos(t²) dt`",
    fn1 phrase!"Dawson function at $v$" none
      (fun x => mul (exp (neg (mul x x))) (integral (num 0) x (lamR fun t => exp (mul t t)))) "`D(x) = e^{-x²} ∫_0^x e^{t²} dt`"]

end Leanify.HigherFunctions
