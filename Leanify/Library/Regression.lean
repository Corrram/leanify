import Leanify.Library.Core

/-! # Vocabulary: simple linear regression

The least-squares line of `y` on `x` for the first `n` observations `(x_i, y_i)` (as in the
field `samples`, where the slope and intercept are), its fitted values and residuals, the
sums of squares, the coefficient of determination and the standard errors (`We write
$R^2_n(y,x)$ for the coefficient of determination of the regression of $y$ on $x$ for the first
$n$ terms.`).

* notions, for `n ≥ 3` and `x` not constant on the first `n` terms: the fitted value at `t`
  (`b̂₀ + b̂₁ t`), the `i`th residual (`y_i - ŷ_i`), the residual, total and explained sums of
  squares, the coefficient of determination `1 - RSS/TSS` (where `y` is not constant), the
  adjusted coefficient `1 - (1 - R²)(n-1)/(n-2)`, the residual standard error `√(RSS/(n-2))`
  and the standard error of the slope `√(RSS/(n-2)) / √(∑ (x_i - x̄)²)`.

Every meaning is a term of the core language. -/

namespace Leanify.Regression
open Build Core

abbrev F : Ty := Ty.rfun

def finSum (a b : B) (body : B → B) : B := app (app (app (prim .finSum) a) b) (lamR body)
def sum (n : B) (body : B → B) : B := finSum (num 1) n body
def sqrt (x : B) : B := app2 (prim .rpow) x (div (num 1) (num 2))
def mean (n x : B) : B := div (sum n fun i => app x i) n
def sxx (n x : B) : B := sum n fun i => mul (sub (app x i) (mean n x)) (sub (app x i) (mean n x))
def sxy (n x y : B) : B := sum n fun i => mul (sub (app x i) (mean n x)) (sub (app y i) (mean n y))
def slope (n x y : B) : B := div (sxy n x y) (sxx n x)
def icpt (n x y : B) : B := sub (mean n y) (mul (slope n x y) (mean n x))
def fitted (n x y t : B) : B := add (icpt n x y) (mul (slope n x y) t)
def resid (n x y i : B) : B := sub (app y i) (fitted n x y (app x i))
def rss (n x y : B) : B := sum n fun i => mul (resid n x y i) (resid n x y i)
def tss (n y : B) : B := sxx n y
def ess (n x y : B) : B := sum n fun i => mul (sub (fitted n x y (app x i)) (mean n y)) (sub (fitted n x y (app x i)) (mean n y))
def r2 (n x y : B) : B := sub (num 1) (div (rss n x y) (tss n y))
def ok (n x : B) : B := and (and (isInt n) (le (num 3) n)) (ne (sxx n x) (num 0))
def okY (n x y : B) : B := and (ok n x) (ne (sxx n y) (num 0))
/-- A quantity of the regression of `y` on `x` for the first `n` terms. -/
def reg (name : Phrase) (needY : Bool) (body : B → B → B → B) (doc : String) : Notion :=
  let d (y x n : B) : B := if needY then okY n x y else ok n x
  { name, ty := F ⟶ F ⟶ .real ⟶ .real, doms := [none, none, dom3 .real d], doc,
    value := close <| lamT F (fun _ => tt) fun y => lamT F (fun _ => tt) fun x => lamT .real (fun n => d y x n) fun n => body y x n }

def vocab : Vocab where
  notions := [
    { name := phrase!"fitted value at $v$ of the regression of $v$ on $v$ for the first $v$ terms",
      ty := .real ⟶ F ⟶ F ⟶ .real ⟶ .real, doms := [none, none, none, dom4 .real fun _ _ x n => ok n x],
      doc := "`b̂₀ + b̂₁ t` for the least-squares line",
      value := close <| lamR fun t => lamT F (fun _ => tt) fun y => lamT F (fun _ => tt) fun x =>
        lamT .real (fun n => ok n x) fun n => fitted n x y t },
    { name := phrase!"$v$th residual of the regression of $v$ on $v$ for the first $v$ terms",
      ty := .real ⟶ F ⟶ F ⟶ .real ⟶ .real, doms := [none, none, none, dom4 .real fun _ _ x n => ok n x],
      doc := "`y_i - ŷ_i`",
      value := close <| lamR fun i => lamT F (fun _ => tt) fun y => lamT F (fun _ => tt) fun x =>
        lamT .real (fun n => ok n x) fun n => resid n x y i },
    reg phrase!"residual sum of squares of the regression of $v$ on $v$ for the first $v$ terms" false
      (fun y x n => rss n x y) "`∑ (y_i - ŷ_i)²`",
    reg phrase!"total sum of squares of the regression of $v$ on $v$ for the first $v$ terms" false
      (fun y _ n => tss n y) "`∑ (y_i - ȳ)²`",
    reg phrase!"explained sum of squares of the regression of $v$ on $v$ for the first $v$ terms" false
      (fun y x n => ess n x y) "`∑ (ŷ_i - ȳ)²`",
    reg phrase!"coefficient of determination of the regression of $v$ on $v$ for the first $v$ terms" true
      (fun y x n => r2 n x y) "`R² = 1 - RSS/TSS`",
    reg phrase!"adjusted coefficient of determination of the regression of $v$ on $v$ for the first $v$ terms" true
      (fun y x n => sub (num 1) (div (mul (sub (num 1) (r2 n x y)) (sub n (num 1))) (sub n (num 2))))
      "`1 - (1 - R²)(n-1)/(n-2)`",
    reg phrase!"residual standard error of the regression of $v$ on $v$ for the first $v$ terms" false
      (fun y x n => sqrt (div (rss n x y) (sub n (num 2)))) "`√(RSS/(n-2))`",
    reg phrase!"standard error of the slope of the regression of $v$ on $v$ for the first $v$ terms" false
      (fun y x n => div (sqrt (div (rss n x y) (sub n (num 2)))) (sqrt (sxx n x))) "`√(RSS/(n-2)) / √(∑ (x_i - x̄)²)`"]

end Leanify.Regression
