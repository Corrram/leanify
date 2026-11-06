import Lean

/-! # Typed core terms

Every symbol that an article introduces is a *global definition*: its value is
the denotation of the article's own defining formula. Two further sources of
meaning exist, both fixed before the article is read:

* the core prelude (`Prim`): real powers, `min`/`max`, Lebesgue measure on
  `[0,1]`, Borel measurability, measurable sets, integrability on `[0,1]` and
  derivatives, with their usual mathlib meaning;
* the vocabulary of the article (`Vocab`, `Model`): base types and constants
  supplied by a downstream library, each with a Lean meaning that is reviewed
  once and shared by every article that uses the vocabulary.

Partial operations are total (as in mathlib), but every compiled term also has a
syntactic *definedness condition* (`Tm.defined`). A compiled claim means
`defined ∧ claim`, so a formula such as `1/0 = 0` or a real power of a negative
number cannot become true for a conventional reason.

This module is purely syntactic and does not depend on mathlib: the compiler
(lexing, parsing and elaboration) only manipulates these terms. Their meaning is
given in `Leanify.Denote`. -/

namespace Leanify

inductive Ty where
  | real | unit | prop
  | fn (a b : Ty)
  /-- The `k`-th base type declared by the vocabulary. -/
  | base (k : Nat)
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

infixr:60 " ⟶ " => Ty.fn

/-- Subsets of the unit square, read as two-place predicates. -/
abbrev Ty.set2 : Ty := .unit ⟶ .unit ⟶ .prop
abbrev Ty.set1 : Ty := .unit ⟶ .prop
/-- Set functions on the unit square (laws of random pairs). -/
abbrev Ty.meas2 : Ty := Ty.set2 ⟶ .real
/-- Functions on the unit square, such as distribution functions. -/
abbrev Ty.sq : Ty := .unit ⟶ .unit ⟶ .real
abbrev Ty.self : Ty := .unit ⟶ .unit
abbrev Ty.rfun : Ty := .real ⟶ .real

/-- Standard properties of a real function on a domain (`Leanify.Prelude`). -/
inductive FnProp where
  | convex | strictConvex | strictConcave | strictAnti | monotone | antitone
  | bounded | nonneg | pos | differentiable | contDiff | injective
  | lowerSemicont | upperSemicont | lipschitz
  deriving DecidableEq, Repr, Lean.ToExpr

/-- Standard properties of a set of points of the plane. -/
inductive SetProp where
  | closed | isOpen | bounded | connected
  deriving DecidableEq, Repr, Lean.ToExpr

/-- Properties of a quantity of functions on the unit square (of a copula, say) on a
class of them: convexity, and semicontinuity and continuity for uniform convergence. -/
inductive SqProp where
  | convex | concave | lowerUniform | upperUniform | contUniform
  deriving DecidableEq, Repr, Lean.ToExpr

/-- Properties of a class of functions on the unit square: convexity, and
compactness and closedness for uniform convergence. -/
inductive ClassProp where
  | convex | compactUniform | closedUniform
  deriving DecidableEq, Repr, Lean.ToExpr

/-- Standard functions of a real variable, with their mathlib meaning. `\log` and
`\tan` are applied only inside their domains (the compiler adds the condition). -/
inductive RealFn where
  | exp | log | sin | cos | tan
  deriving DecidableEq, Repr, Lean.ToExpr

/-- The core prelude: standard notions of real analysis with their usual mathlib
meaning (`Leanify.Prelude`). -/
inductive Prim where
  | rpow | min | max
  /-- Lebesgue measure of a subset of `[0,1]`. -/
  | leb
  /-- Borel measurability of a map `[0,1] → [0,1]`. -/
  | borel
  | measurableSet1 | measurableSet2
  /-- Lebesgue integrability on `[0,1]`. -/
  | integrable
  /-- `hasDerivWithin f S x d`: `f` has derivative `d` at `x` within `S`. -/
  | hasDerivWithin
  /-- `intervalIntegral a b f`: the oriented integral `∫_a^b f`. -/
  | intervalIntegral
  /-- `intervalIntegrable f a b`: `f` is integrable between `a` and `b`. -/
  | intervalIntegrable
  /-- Shapes of a set of points of the plane: compact, convex, symmetric about the origin. -/
  | compact2 | convex2 | symm2
  /-- Properties of a real function on a domain: continuous, concave, strictly increasing. -/
  | continuousOn | concaveOn | strictMonoOn
  /-- Further properties of a real function on a domain. -/
  | fnProp (k : FnProp)
  /-- Further properties of a set of points of the plane. -/
  | setProp (k : SetProp)
  /-- Properties of a quantity of functions on the unit square, on a class. -/
  | sqProp (k : SqProp)
  /-- Properties of a class of functions on the unit square. -/
  | classProp (k : ClassProp)
  /-- `\exp`, `\log`, `\sin`, `\cos`, `\tan`. -/
  | realFn (k : RealFn)
  /-- The number `π`. -/
  | pi
  /-- Integers and natural numbers (`0,1,2,…`) among the real numbers. -/
  | isInt | isNat
  /-- `\lfloor x\rfloor` and `\lceil x\rceil`, as real numbers. -/
  | floor | ceil
  /-- `finSum a b f`: `∑_{k=a}^{b} f(k)` over the integers between `a` and `b` (`finProd`: the product). -/
  | finSum | finProd
  /-- `series a f`: `∑_{k=a}^{∞} f(k)`, the limit of the partial sums; `seriesConv a f`:
  the partial sums converge. -/
  | series | seriesConv
  /-- `limAt a D f`: `\lim_{x\to a} f(x)` for `x ∈ D`, `x ≠ a`; `limAtConv a D f`: it exists
  and `a` is a limit point of `D`. -/
  | limAt | limAtConv
  /-- `limTop D f`: `\lim_{x\to\infty} f(x)` for `x ∈ D`; `limTopConv D f`: it exists and `D`
  is unbounded above. A sequence `\lim_{n\to\infty} a_n` is the limit within the natural
  numbers. -/
  | limTop | limTopConv
  /-- `n!` and `\binom{n}{k}` for natural numbers. -/
  | factorial | binom
  /-- `zpow x k`: `x^k` for an integer `k`. -/
  | zpow
  deriving DecidableEq, Repr, Lean.ToExpr

def Prim.ty : Prim → Ty
  | .rpow | .min | .max => .real ⟶ .real ⟶ .real
  | .leb => Ty.set1 ⟶ .real
  | .borel => Ty.self ⟶ .prop
  | .measurableSet1 => Ty.set1 ⟶ .prop
  | .measurableSet2 => Ty.set2 ⟶ .prop
  | .integrable => (.unit ⟶ .real) ⟶ .prop
  | .hasDerivWithin => Ty.rfun ⟶ (.real ⟶ .prop) ⟶ .real ⟶ .real ⟶ .prop
  | .intervalIntegral => .real ⟶ .real ⟶ Ty.rfun ⟶ .real
  | .intervalIntegrable => Ty.rfun ⟶ .real ⟶ .real ⟶ .prop
  | .compact2 | .convex2 | .symm2 => (.real ⟶ .real ⟶ .prop) ⟶ .prop
  | .continuousOn | .concaveOn | .strictMonoOn | .fnProp _ => Ty.rfun ⟶ (.real ⟶ .prop) ⟶ .prop
  | .setProp _ => (.real ⟶ .real ⟶ .prop) ⟶ .prop
  | .sqProp _ => (Ty.sq ⟶ .real) ⟶ (Ty.sq ⟶ .prop) ⟶ .prop
  | .classProp _ => (Ty.sq ⟶ .prop) ⟶ .prop
  | .realFn _ => .real ⟶ .real
  | .pi => .real
  | .isInt | .isNat => .real ⟶ .prop
  | .floor | .ceil => .real ⟶ .real
  | .finSum | .finProd => .real ⟶ .real ⟶ Ty.rfun ⟶ .real
  | .series => .real ⟶ Ty.rfun ⟶ .real
  | .seriesConv => .real ⟶ Ty.rfun ⟶ .prop
  | .limAt => .real ⟶ (.real ⟶ .prop) ⟶ Ty.rfun ⟶ .real
  | .limAtConv => .real ⟶ (.real ⟶ .prop) ⟶ Ty.rfun ⟶ .prop
  | .limTop => (.real ⟶ .prop) ⟶ Ty.rfun ⟶ .real
  | .limTopConv => (.real ⟶ .prop) ⟶ Ty.rfun ⟶ .prop
  | .factorial => .real ⟶ .real
  | .binom | .zpow => .real ⟶ .real ⟶ .real

/-- Untyped core terms with de Bruijn locals, indexed article definitions
(`glob`) and vocabulary constants (`const`). Types are checked by `typeOf`;
ill-typed terms have no denotation. -/
inductive Tm where
  | glob (i : Nat)
  | loc (i : Nat)
  | prim (p : Prim)
  | const (i : Nat)
  | app (f x : Tm)
  /-- `lam t dom body`: a function on `t`; `dom` (a proposition about the bound
  variable) is its declared domain, used only for definedness. -/
  | lam (t : Ty) (dom body : Tm)
  | num (n : Nat)
  | ofUnit (x : Tm)
  /-- A real number used as a point of `[0,1]`; defined only inside `[0,1]`. -/
  | toUnit (x : Tm)
  | add (x y : Tm) | sub (x y : Tm) | mul (x y : Tm) | div (x y : Tm)
  | neg (x : Tm) | abs (x : Tm)
  | powNat (x : Tm) (n : Nat)
  /-- `cases c v rest`: the first branch whose condition holds. -/
  | cases (c v rest : Tm)
  | undef (t : Ty)
  | eq (x y : Tm) | lt (x y : Tm) | le (x y : Tm)
  | tt
  | not (p : Tm) | and (p q : Tm) | or (p q : Tm) | imp (p q : Tm) | iff (p q : Tm)
  | all (t : Ty) (body : Tm) | ex (t : Ty) (body : Tm)
  /-- Integral over `[0,1]` of a body in one new local of type `[0,1]`. -/
  | integral (body : Tm)
  /-- Semantically transparent; contributes the condition to definedness. -/
  | guard (c e : Tm)
  /-- The definite description `the x : t such that body`. It is defined only
  when exactly one such `x` exists. -/
  | the (t : Ty) (body : Tm)
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

/-- The type of a term, given the types of vocabulary constants (`cs`), article
definitions (`gs`) and locals (`ls`). -/
def typeOf (cs gs : List Ty) (ls : List Ty) : Tm → Option Ty
  | .glob i => gs[i]?
  | .loc i => ls[i]?
  | .prim p => some p.ty
  | .const i => cs[i]?
  | .app f x =>
    match typeOf cs gs ls f, typeOf cs gs ls x with
    | some (.fn a b), some a' => if a' = a then some b else none
    | _, _ => none
  | .lam t _ body =>
    match typeOf cs gs (t :: ls) body with
    | some b => some (.fn t b)
    | none => none
  | .num _ => some .real
  | .ofUnit x =>
    match typeOf cs gs ls x with
    | some .unit => some .real
    | _ => none
  | .toUnit x =>
    match typeOf cs gs ls x with
    | some .real => some .unit
    | _ => none
  | .add x y | .sub x y | .mul x y | .div x y =>
    match typeOf cs gs ls x, typeOf cs gs ls y with
    | some .real, some .real => some .real
    | _, _ => none
  | .neg x | .abs x | .powNat x _ =>
    match typeOf cs gs ls x with
    | some .real => some .real
    | _ => none
  | .cases _ v _ => typeOf cs gs ls v
  | .undef t => some t
  | .eq _ _ | .lt _ _ | .le _ _ | .tt | .not _ | .and _ _ | .or _ _ | .imp _ _ | .iff _ _
  | .all _ _ | .ex _ _ => some .prop
  | .integral _ => some .real
  | .guard _ e => typeOf cs gs ls e
  | .the t _ => some t

namespace Tm

/-- Shift free local indices `≥ c` by `k` (for moving terms under binders). -/
def shift (k : Nat) : Nat → Tm → Tm
  | c, .loc i => if i < c then .loc i else .loc (i + k)
  | c, .app f x => .app (shift k c f) (shift k c x)
  | c, .lam t d b => .lam t (shift k (c + 1) d) (shift k (c + 1) b)
  | c, .ofUnit x => .ofUnit (shift k c x)
  | c, .toUnit x => .toUnit (shift k c x)
  | c, .add x y => .add (shift k c x) (shift k c y)
  | c, .sub x y => .sub (shift k c x) (shift k c y)
  | c, .mul x y => .mul (shift k c x) (shift k c y)
  | c, .div x y => .div (shift k c x) (shift k c y)
  | c, .neg x => .neg (shift k c x)
  | c, .abs x => .abs (shift k c x)
  | c, .powNat x n => .powNat (shift k c x) n
  | c, .cases p v r => .cases (shift k c p) (shift k c v) (shift k c r)
  | c, .eq x y => .eq (shift k c x) (shift k c y)
  | c, .lt x y => .lt (shift k c x) (shift k c y)
  | c, .le x y => .le (shift k c x) (shift k c y)
  | c, .not p => .not (shift k c p)
  | c, .and p q => .and (shift k c p) (shift k c q)
  | c, .or p q => .or (shift k c p) (shift k c q)
  | c, .imp p q => .imp (shift k c p) (shift k c q)
  | c, .iff p q => .iff (shift k c p) (shift k c q)
  | c, .all t b => .all t (shift k (c + 1) b)
  | c, .ex t b => .ex t (shift k (c + 1) b)
  | c, .integral b => .integral (shift k (c + 1) b)
  | c, .guard p e => .guard (shift k c p) (shift k c e)
  | c, .the t b => .the t (shift k (c + 1) b)
  | _, t => t

/-- Replace the local `loc j` (at binder depth `j` of the term) by `s`, lowering
the locals above it (the substitution of β-reduction; `s` is closed under the
binders it is moved under by `shift`). -/
def subst (s : Tm) : Nat → Tm → Tm
  | j, .loc i => if i < j then .loc i else if i == j then shift j 0 s else .loc (i - 1)
  | j, .app f x => .app (subst s j f) (subst s j x)
  | j, .lam t d b => .lam t (subst s (j + 1) d) (subst s (j + 1) b)
  | j, .ofUnit x => .ofUnit (subst s j x)
  | j, .toUnit x => .toUnit (subst s j x)
  | j, .add x y => .add (subst s j x) (subst s j y)
  | j, .sub x y => .sub (subst s j x) (subst s j y)
  | j, .mul x y => .mul (subst s j x) (subst s j y)
  | j, .div x y => .div (subst s j x) (subst s j y)
  | j, .neg x => .neg (subst s j x)
  | j, .abs x => .abs (subst s j x)
  | j, .powNat x n => .powNat (subst s j x) n
  | j, .cases p v r => .cases (subst s j p) (subst s j v) (subst s j r)
  | j, .eq x y => .eq (subst s j x) (subst s j y)
  | j, .lt x y => .lt (subst s j x) (subst s j y)
  | j, .le x y => .le (subst s j x) (subst s j y)
  | j, .not p => .not (subst s j p)
  | j, .and p q => .and (subst s j p) (subst s j q)
  | j, .or p q => .or (subst s j p) (subst s j q)
  | j, .imp p q => .imp (subst s j p) (subst s j q)
  | j, .iff p q => .iff (subst s j p) (subst s j q)
  | j, .all t b => .all t (subst s (j + 1) b)
  | j, .ex t b => .ex t (subst s (j + 1) b)
  | j, .integral b => .integral (subst s (j + 1) b)
  | j, .guard p e => .guard (subst s j p) (subst s j e)
  | j, .the t b => .the t (subst s (j + 1) b)
  | _, t => t

/-- Shift vocabulary constant indices by `k` (for appending vocabularies). -/
def shiftConst (k : Nat) : Tm → Tm
  | .const i => .const (i + k)
  | .app f x => .app (shiftConst k f) (shiftConst k x)
  | .lam t d b => .lam t (shiftConst k d) (shiftConst k b)
  | .ofUnit x => .ofUnit (shiftConst k x)
  | .toUnit x => .toUnit (shiftConst k x)
  | .add x y => .add (shiftConst k x) (shiftConst k y)
  | .sub x y => .sub (shiftConst k x) (shiftConst k y)
  | .mul x y => .mul (shiftConst k x) (shiftConst k y)
  | .div x y => .div (shiftConst k x) (shiftConst k y)
  | .neg x => .neg (shiftConst k x)
  | .abs x => .abs (shiftConst k x)
  | .powNat x n => .powNat (shiftConst k x) n
  | .cases p v r => .cases (shiftConst k p) (shiftConst k v) (shiftConst k r)
  | .eq x y => .eq (shiftConst k x) (shiftConst k y)
  | .lt x y => .lt (shiftConst k x) (shiftConst k y)
  | .le x y => .le (shiftConst k x) (shiftConst k y)
  | .not p => .not (shiftConst k p)
  | .and p q => .and (shiftConst k p) (shiftConst k q)
  | .or p q => .or (shiftConst k p) (shiftConst k q)
  | .imp p q => .imp (shiftConst k p) (shiftConst k q)
  | .iff p q => .iff (shiftConst k p) (shiftConst k q)
  | .all t b => .all t (shiftConst k b)
  | .ex t b => .ex t (shiftConst k b)
  | .integral b => .integral (shiftConst k b)
  | .guard p e => .guard (shiftConst k p) (shiftConst k e)
  | .the t b => .the t (shiftConst k b)
  | t => t

/-- Conjunction, implication and universal closure that omit trivial parts.
(`defined` is a definition; omitting `True` keeps it readable.) -/
def mkAnd : Tm → Tm → Tm
  | .tt, q => q
  | p, .tt => p
  | p, q => .and p q

def mkImp : Tm → Tm → Tm
  | _, .tt => .tt
  | .tt, q => q
  | p, q => .imp p q

def mkAll (t : Ty) : Tm → Tm
  | .tt => .tt
  | b => .all t b

/-- `∃! x : t, body`, as `∃ x, body ∧ ∀ y, body[y] → y = x`. -/
def existsUnique (t : Ty) (body : Tm) : Tm :=
  .ex t (.and body (.all t (.imp (shift 1 1 body) (.eq (.loc 0) (.loc 1)))))

/-- The syntactic definedness condition of a term (left-to-right, as for TCCs). -/
def defined : Tm → Tm
  | .glob _ | .loc _ | .prim _ | .const _ | .num _ | .tt => .tt
  | .undef _ => .not .tt
  | .app f x => mkAnd (defined f) (defined x)
  | .lam t dom body => mkAll t (mkImp dom (defined body))
  | .ofUnit x | .neg x | .abs x | .powNat x _ | .not x => defined x
  | .toUnit x => mkAnd (defined x) (.and (.le (.num 0) x) (.le x (.num 1)))
  | .add x y | .sub x y | .mul x y | .eq x y | .lt x y | .le x y | .iff x y =>
      mkAnd (defined x) (defined y)
  | .div x y => mkAnd (defined x) (mkAnd (defined y) (.not (.eq y (.num 0))))
  | .cases c v rest =>
      mkAnd (defined c) (mkAnd (mkImp c (mkAnd (defined v) (agreesDefined rest v)))
        (mkImp (.not c) (defined rest)))
  | .and p q | .imp p q => mkAnd (defined p) (mkImp p (defined q))
  | .or p q => mkAnd (defined p) (mkImp (.not p) (defined q))
  | .all t body | .ex t body => mkAll t (defined body)
  | .integral body => mkAnd (mkAll .unit (defined body))
      (.app (.prim .integrable) (.lam .unit .tt body))
  -- a guard's condition must hold (e.g. an argument lies in the function's domain)
  | .guard c e => mkAnd (defined c) (mkAnd c (defined e))
  -- a description denotes only if exactly one object satisfies it
  | .the t body => mkAnd (mkAll t (defined body)) (existsUnique t body)
where
  /-- Later branches that also apply must be defined and agree. -/
  agreesDefined : Tm → Tm → Tm
    | .cases c w rest, v => mkAnd (mkImp c (mkAnd (defined w) (.eq w v))) (agreesDefined rest v)
    | _, _ => .tt

/-- What a compiled claim asserts: it is meaningful, and it holds. -/
def sound (p : Tm) : Tm := .and (defined p) p

end Tm

end Leanify
