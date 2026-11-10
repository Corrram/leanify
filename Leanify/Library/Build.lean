import Leanify.Vocab

/-! # Writing vocabulary terms with named binders

Vocabulary meanings are closed terms with de Bruijn indices. `B` is a term
waiting for the number of binders around it, so that binders can be written with
Lean functions: `allR fun x => (isInt x).imp (le (num 0) (mul x x))` is
`∀ x : ℝ, x ∈ ℤ → 0 ≤ x·x`. `B.close` gives the closed term. -/

namespace Leanify.Build

/-- A term under `n` binders, given `n`. -/
abbrev B := Nat → Tm

/-- The variable bound at depth `lvl`. -/
def var (lvl : Nat) : B := fun n => .loc (n - 1 - lvl)

def close (b : B) : Tm := b 0
def lift (t : Tm) : B := fun _ => t

def binder (k : Tm → Tm) (body : B → B) : B := fun n => k (body (var n) (n + 1))
def allT (t : Ty) (body : B → B) : B := binder (.all t) body
def exT (t : Ty) (body : B → B) : B := binder (.ex t) body
def theT (t : Ty) (body : B → B) : B := binder (.the t) body
/-- `x ↦ body`, defined where `dom` holds. -/
def lamT (t : Ty) (dom body : B → B) : B := fun n => .lam t (dom (var n) (n + 1)) (body (var n) (n + 1))

def allR := allT .real
def exR := exT .real
def theR := theT .real
def lamR (body : B → B) : B := lamT .real (fun _ => fun _ => .tt) body

def num (k : Nat) : B := lift (.num k)
def tt : B := lift .tt
def app (f x : B) : B := fun n => .app (f n) (x n)
def app2 (f x y : B) : B := app (app f x) y
def add (x y : B) : B := fun n => .add (x n) (y n)
def sub (x y : B) : B := fun n => .sub (x n) (y n)
def mul (x y : B) : B := fun n => .mul (x n) (y n)
def div (x y : B) : B := fun n => .div (x n) (y n)
def neg (x : B) : B := fun n => .neg (x n)
def abs (x : B) : B := fun n => .abs (x n)
def eq (x y : B) : B := fun n => .eq (x n) (y n)
def lt (x y : B) : B := fun n => .lt (x n) (y n)
def le (x y : B) : B := fun n => .le (x n) (y n)
def not (p : B) : B := fun n => .not (p n)
def and (p q : B) : B := fun n => .and (p n) (q n)
def or (p q : B) : B := fun n => .or (p n) (q n)
def imp (p q : B) : B := fun n => .imp (p n) (q n)
def iff (p q : B) : B := fun n => .iff (p n) (q n)
def guard (c e : B) : B := fun n => .guard (c n) (e n)
def cases (c v r : B) : B := fun n => .cases (c n) (v n) (r n)
def prim (p : Prim) : B := lift (.prim p)
def const (i : Nat) : B := lift (.const i)

def isInt (x : B) : B := app (prim .isInt) x
def isNat (x : B) : B := app (prim .isNat) x
def floor (x : B) : B := app (prim .floor) x
def ne (x y : B) : B := not (eq x y)

/-- `∀ x ∈ ℤ, body`. -/
def allInt (body : B → B) : B := allR fun x => imp (isInt x) (body x)
/-- `∃ x ∈ ℤ, body`. -/
def exInt (body : B → B) : B := exR fun x => and (isInt x) (body x)

/-- `a` divides `b` (in the integers). -/
def divides (a b : B) : B := exInt fun k => eq b (mul a k)

/-- A predicate on real numbers. -/
def predR (p : B → B) : Tm := close (lamR p)

end Leanify.Build
