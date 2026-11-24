import Leanify.Library.Core

/-! # Vocabulary: means of two numbers

The classical means of two numbers, as notions with their arguments (`the logarithmic mean
of $x$ and $y$`); an article fixes its notation itself (`We write $L(x,y)$ for the
logarithmic mean of $x$ and $y$.`).

* the arithmetic, geometric, harmonic, quadratic (root mean square), contraharmonic,
  Heronian and centroidal means;
* the logarithmic and the identric mean, with their value `x` where `x = y`;
* the power mean of order `p` (the geometric mean for `p = 0`) and the Lehmer mean of
  order `p`.

A mean is defined where its formula is: the geometric and the Heronian mean for
nonnegative numbers, the others (but the arithmetic and the quadratic mean) for positive
numbers. Every meaning is a term of the core language: the field has no constants and no
model. -/

namespace Leanify.Means
open Build Core

def sqrt (x : B) : B := app2 (prim .rpow) x (div (num 1) (num 2))
def rpow (x p : B) : B := app2 (prim .rpow) x p
def log (x : B) : B := app (prim (.realFn .log)) x
def exp (x : B) : B := app (prim (.realFn .exp)) x

def posP (x : B) : B := lt (num 0) x
def nonnegP (x : B) : B := le (num 0) x

/-- A mean of two numbers, each in its domain `d` (in the value and at each use). -/
def mean2 (name : Phrase) (d : Option (B → B)) (body : B → B → B) (doc : String) : Notion :=
  let dm := d.bind (dom1 .real)
  let lam := fun (b : B → B) => match d with | some p => lamT .real p b | none => lamR b
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dm, dm], doc,
    value := close <| lam fun x => lam fun y => body x y }

/-- A mean of order `p` of two positive numbers (the order first). -/
def meanP (name : Phrase) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real, doms := [none, dom1 .real posP, dom1 .real posP], doc,
    value := close <| lamR fun p => lamT .real posP fun x => lamT .real posP fun y => body p x y }

def arithmetic (x y : B) : B := div (add x y) (num 2)
def geometric (x y : B) : B := sqrt (mul x y)

def vocab : Vocab where
  notions := [
    mean2 phrase!"arithmetic mean of $v$ and $v$" none arithmetic "`(x + y)/2`",
    mean2 phrase!"geometric mean of $v$ and $v$" (some nonnegP) geometric "`√(xy)`, for `x, y ≥ 0`",
    mean2 phrase!"harmonic mean of $v$ and $v$" (some posP) (fun x y => div (mul (num 2) (mul x y)) (add x y))
      "`2xy/(x + y)`, for `x, y > 0`",
    mean2 phrase!"quadratic mean of $v$ and $v$" none (fun x y => sqrt (div (add (mul x x) (mul y y)) (num 2)))
      "`√((x² + y²)/2)`",
    mean2 phrase!"root mean square of $v$ and $v$" none (fun x y => sqrt (div (add (mul x x) (mul y y)) (num 2)))
      "`√((x² + y²)/2)`",
    mean2 phrase!"contraharmonic mean of $v$ and $v$" (some posP) (fun x y => div (add (mul x x) (mul y y)) (add x y))
      "`(x² + y²)/(x + y)`, for `x, y > 0`",
    mean2 phrase!"Heronian mean of $v$ and $v$" (some nonnegP) (fun x y => div (add (add x (geometric x y)) y) (num 3))
      "`(x + √(xy) + y)/3`, for `x, y ≥ 0`",
    mean2 phrase!"centroidal mean of $v$ and $v$" (some posP)
      (fun x y => div (mul (num 2) (add (add (mul x x) (mul x y)) (mul y y))) (mul (num 3) (add x y)))
      "`2(x² + xy + y²)/(3(x + y))`, for `x, y > 0`",
    mean2 phrase!"logarithmic mean of $v$ and $v$" (some posP)
      (fun x y => cases (eq x y) x (div (sub x y) (sub (log x) (log y))))
      "`(x - y)/(log x - log y)`, and `x` for `x = y`; for `x, y > 0`",
    mean2 phrase!"identric mean of $v$ and $v$" (some posP)
      (fun x y => cases (eq x y) x (exp (sub (div (sub (mul x (log x)) (mul y (log y))) (sub x y)) (num 1))))
      "`e^{-1} (x^x / y^y)^{1/(x - y)}`, and `x` for `x = y`; for `x, y > 0`",
    meanP phrase!"power mean of order $v$ of $v$ and $v$"
      (fun p x y => cases (eq p (num 0)) (geometric x y)
        (rpow (div (add (rpow x p) (rpow y p)) (num 2)) (div (num 1) p)))
      "`((x^p + y^p)/2)^{1/p}`, and `√(xy)` for `p = 0`; for `x, y > 0`",
    meanP phrase!"Lehmer mean of order $v$ of $v$ and $v$"
      (fun p x y => div (add (rpow x p) (rpow y p)) (add (rpow x (sub p (num 1))) (rpow y (sub p (num 1)))))
      "`(x^p + y^p)/(x^{p-1} + y^{p-1})`, for `x, y > 0`"]

end Leanify.Means
