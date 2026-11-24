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

/-! ### The domains of a notion's arguments

A notion's `doms` are read by `Elab.applyAllD`: the domain of an argument is a predicate
of it, in which the arguments before it are free (the one just before at `loc 2` inside
the predicate, the one before that at `loc 3`). The same condition belongs in the value,
as the domain of the argument's `lamT`, so that a definition made from the notion (`We
write $H(x,y)$ for …`) is well defined there, and each use of it asks for it. -/

/-- The domain of an argument of type `t` that speaks about the argument alone. -/
def dom1 (t : Ty) (p : B → B) : Option Tm := some (close (lamT t (fun _ => tt) p))

/-- The domain of an argument of type `t` that also speaks about the argument before it:
`p prev self`. -/
def dom2 (t : Ty) (p : B → B → B) : Option Tm :=
  match close (lamR fun prev => lamR fun _ => lamT t (fun _ => tt) fun self => p prev self) with
  | .lam _ _ (.lam _ _ inner) => some inner
  | _ => none

/-- The domain of an argument that speaks about the two arguments before it:
`p first second self`. -/
def dom3 (t : Ty) (p : B → B → B → B) : Option Tm :=
  match close (lamR fun a => lamR fun b => lamR fun _ =>
      lamT t (fun _ => tt) fun self => p a b self) with
  | .lam _ _ (.lam _ _ (.lam _ _ inner)) => some inner
  | _ => none

/-- The domain of an argument that speaks about the three arguments before it:
`p first second third self`. -/
def dom4 (t : Ty) (p : B → B → B → B → B) : Option Tm :=
  match close (lamR fun a => lamR fun b => lamR fun c => lamR fun _ =>
      lamT t (fun _ => tt) fun self => p a b c self) with
  | .lam _ _ (.lam _ _ (.lam _ _ (.lam _ _ inner))) => some inner
  | _ => none

end Leanify.Build
