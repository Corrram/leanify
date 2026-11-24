import Leanify.Library.Core

/-! # Vocabulary: Fourier series and transforms

The real Fourier analysis of a real function: the Fourier coefficients of a function on
`[-π, π]` (of a `2π`-periodic one), the partial sums of its Fourier series and their Fejér
means, the Dirichlet and Fejér kernels, and the Fourier cosine and sine transforms of an
integrable function on the line. The functions are those of the field `realfunctions`
(`Let $f$ be a $2\pi$-periodic continuous function.`); an article fixes its notation itself
(`We write $a_n(f)$ for the $n$th Fourier cosine coefficient of $f$.`).

* `a_n(f) = (1/π) ∫_{-π}^{π} f(x) cos(nx) dx` and `b_n(f) = (1/π) ∫_{-π}^{π} f(x) sin(nx) dx`,
  for a nonnegative integer `n` and a function that is integrable on `[-π, π]`;
* `S_N f(x) = a_0/2 + ∑_{n=1}^{N} (a_n cos(nx) + b_n sin(nx))`, and the Fejér mean
  `σ_N f = (S_0 f + … + S_N f)/(N + 1)`;
* `D_N(x) = 1/2 + ∑_{n=1}^{N} cos(nx)` and `F_N(x) = (D_0(x) + … + D_N(x))/(N + 1)` (with
  these normalizations, `S_N f(x) = (1/π) ∫_{-π}^{π} f(t) D_N(x - t) dt`);
* `ξ ↦ ∫ f(x) cos(ξx) dx` and `ξ ↦ ∫ f(x) sin(ξx) dx`, for a function integrable on the line;
* `trigonometric polynomial`: a function `x ↦ ∑_{n=0}^{N} (a_n cos(nx) + b_n sin(nx))`.

Every meaning is a term of the core language (integrals, sums, `\cos`, `\sin`, `\pi`): the
field has no constants and no model. -/

namespace Leanify.Fourier
open Build Core

abbrev F : Ty := Ty.rfun

def cos (x : B) : B := app (prim (.realFn .cos)) x
def sin (x : B) : B := app (prim (.realFn .sin)) x
def pi : B := prim .pi
def finSum (a b : B) (body : B → B) : B := app (app (app (prim .finSum) a) b) (lamR body)
def line : B := lamR fun _ => tt

/-- `f` is integrable on `[-π, π]`. -/
def onCircle (f : B) : B := app2 (app (prim .intervalIntegrable) f) (neg pi) pi
/-- `(1/π) ∫_{-π}^{π} f(x) w(nx) dx`. -/
def coeff (w : B → B) (n f : B) : B :=
  div (app (app (app (prim .intervalIntegral) (neg pi)) pi) (lamR fun x => mul (app f x) (w (mul n x)))) pi
def cosC (n f : B) : B := coeff cos n f
def sinC (n f : B) : B := coeff sin n f
/-- `S_N f(x)`. -/
def partialSum (nn f x : B) : B :=
  add (div (cosC (num 0) f) (num 2))
    (finSum (num 1) nn fun n => add (mul (cosC n f) (cos (mul n x))) (mul (sinC n f) (sin (mul n x))))
def dirichlet (nn x : B) : B := add (div (num 1) (num 2)) (finSum (num 1) nn fun n => cos (mul n x))

def natP (n : B) : B := and (isInt n) (le (num 0) n)
def lineP (f : B) : B := app2 (prim .integrableOn) f line

/-- Of a nonnegative integer and a function integrable on `[-π, π]`. -/
def ofNF (name : Phrase) (ty : Ty) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ F ⟶ ty, doms := [dom1 .real natP, dom1 F onCircle], doc,
    value := close <| lamT .real natP fun n => lamT F onCircle fun f => body n f }
/-- Of a function integrable on the line. -/
def ofF (name : Phrase) (body : B → B) (doc : String) : Notion :=
  { name, ty := F ⟶ F, doms := [dom1 F lineP], doc, value := close <| lamT F lineP body }
/-- Of a nonnegative integer. -/
def ofN (name : Phrase) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ F, doms := [dom1 .real natP], doc, value := close <| lamT .real natP fun n => lamR fun x => body n x }

def vocab : Vocab where
  nouns := [
    { sing := phrase!"trigonometric polynomial", plural := phrase!"trigonometric polynomials", ty := F,
      pred := close <| lamT F (fun _ => tt) fun f => exR fun nn => and (and (isInt nn) (le (num 0) nn))
        (exT F fun a => exT F fun b => allR fun x =>
          eq (app f x) (finSum (num 0) nn fun n => add (mul (app a n) (cos (mul n x))) (mul (app b n) (sin (mul n x))))),
      doc := "`x ↦ ∑_{n=0}^{N} (a_n cos(nx) + b_n sin(nx))` for some `N` and coefficients" }]
  notions := [
    ofNF phrase!"$v$th Fourier cosine coefficient of $v$" .real cosC
      "`(1/π) ∫_{-π}^{π} f(x) cos(nx) dx`, of a function integrable on `[-π, π]` (Mathlib `fourierCoeff`, in real form)",
    ofNF phrase!"$v$th Fourier sine coefficient of $v$" .real sinC
      "`(1/π) ∫_{-π}^{π} f(x) sin(nx) dx`, of a function integrable on `[-π, π]`",
    ofNF phrase!"$v$th partial sum of the Fourier series of $v$" F (fun nn f => lamR fun x => partialSum nn f x)
      "`a_0/2 + ∑_{n=1}^{N} (a_n cos(nx) + b_n sin(nx))`",
    ofNF phrase!"$v$th Fejér mean of $v$" F
      (fun nn f => lamR fun x => div (finSum (num 0) nn fun k => partialSum k f x) (add nn (num 1)))
      "`(S_0 f + … + S_N f)/(N + 1)`",
    ofNF phrase!"$v$th Fejer mean of $v$" F
      (fun nn f => lamR fun x => div (finSum (num 0) nn fun k => partialSum k f x) (add nn (num 1)))
      "`(S_0 f + … + S_N f)/(N + 1)`",
    ofN phrase!"Dirichlet kernel of order $v$" dirichlet "`1/2 + ∑_{n=1}^{N} cos(nx)`",
    ofN phrase!"Fejér kernel of order $v$"
      (fun nn x => div (finSum (num 0) nn fun k => dirichlet k x) (add nn (num 1))) "`(D_0 + … + D_N)/(N + 1)`",
    ofN phrase!"Fejer kernel of order $v$"
      (fun nn x => div (finSum (num 0) nn fun k => dirichlet k x) (add nn (num 1))) "`(D_0 + … + D_N)/(N + 1)`",
    ofF phrase!"Fourier cosine transform of $v$"
      (fun f => lamR fun t => app2 (prim .integralOn) line (lamR fun x => mul (app f x) (cos (mul t x))))
      "`ξ ↦ ∫ f(x) cos(ξx) dx`, of a function integrable on the line",
    ofF phrase!"Fourier sine transform of $v$"
      (fun f => lamR fun t => app2 (prim .integralOn) line (lamR fun x => mul (app f x) (sin (mul t x))))
      "`ξ ↦ ∫ f(x) sin(ξx) dx`, of a function integrable on the line"]

end Leanify.Fourier
