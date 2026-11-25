import Leanify.Denote
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Order.Lattice
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Algebra.Group.Conj
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # The meaning of the field `structures`

Groups, rings, fields, vector spaces, topological and metric spaces and ordered sets, with
their elements: `Let $G$ be a group and $g,h\in G$. Then $(gh)^{-1}=h^{-1}g^{-1}$.`

**Elements.** Leanify's language is simply typed, so the elements of all structures have
one type, `El`. An element is a point (`Pt`, a set of real numbers) together with the
operations of its structure (`Ops`): `gh` is the product of the structure that `g` belongs
to, `x+y` its sum, `1` its identity. A numeral (`El.num r`) takes its meaning from the
element it meets: `g=1` says that `g` is the identity of its group, `2x=x+x`.

**Structures.** A structure is the set of its elements, `El → Prop`: its points, all with the
same operations. A subgroup, a subring or an open subset is a subset with the same
operations. A noun says which operations the structure uses and what they satisfy, in
Mathlib's terms: `IsGroup S` asks for a Mathlib `Group` on the points of `S` whose
product, identity and inverse are those of `S`. Such an instance is unique where it
exists, so a property of Mathlib's (`IsSimpleGroup`, `ringChar`, `T2Space`) is a property
of the structure.

**Size.** The points are sets of real numbers, so a structure has at most `2^𝔠` elements:
`for every group` ranges over the groups of at most that many elements (every group of
analysis and algebra in practice). A statement about every group follows from Mathlib's
statement about every group.

**Maps.** A map between structures is a function `El → El`; `φ\colon G\to H` asks that it
maps `G` into `H`, and its values elsewhere are not used. -/

namespace Leanify.Structures

noncomputable section
open Classical

/-- The points on which structures are built. -/
abbrev Pt : Type := Set ℝ

/-- The operations of a ring: those of the scalars of a module. `real` embeds the real
numbers, where the ring has them (`ℝ`, a real algebra): a number `r` is then `real r`, not
only a rational multiple of `1`. -/
structure ROps where
  add : Pt → Pt → Pt
  zero : Pt
  neg : Pt → Pt
  mul : Pt → Pt → Pt
  one : Pt
  inv : Pt → Pt
  real : Option (ℝ → Pt)

instance : Inhabited ROps := ⟨⟨fun a _ => a, ∅, id, fun a _ => a, ∅, id, none⟩⟩

/-- The operations of a structure. Every structure has all of them; its noun says which it
uses. -/
structure Ops where
  add : Pt → Pt → Pt
  zero : Pt
  neg : Pt → Pt
  mul : Pt → Pt → Pt
  one : Pt
  inv : Pt → Pt
  /-- The real numbers in the structure, where it has them. -/
  real : Option (ℝ → Pt)
  /-- The scalars of a module (the points of its ring of scalars), their ring operations and
  their action. A ring acts on itself by its product. -/
  scalars : Set Pt
  sops : ROps
  smul : Pt → Pt → Pt
  /-- An order. -/
  le : Pt → Pt → Prop
  /-- A topology: its open sets. -/
  opens : Set (Set Pt)
  /-- A distance, a norm and an inner product. -/
  dist : Pt → Pt → ℝ
  norm : Pt → ℝ
  inner : Pt → Pt → ℝ

instance : Inhabited Ops :=
  ⟨⟨fun a _ => a, ∅, id, fun a _ => a, ∅, id, none, ∅, default, fun _ a => a, fun _ _ => False, ∅,
    fun _ _ => 0, fun _ => 0, fun _ _ => 0⟩⟩

/-- An element: a point with the operations of its structure, or a numeral, whose meaning
is given by the element it meets. -/
inductive El where
  | el (o : Ops) (x : Pt)
  | num (r : ℝ)

instance : Inhabited El := ⟨.num 0⟩

/-- An element of every structure's type (the base type's default). -/
def elDefault : El := .num 0

/-! ## Numerals -/

/-- `n` as `1 + ⋯ + 1`. -/
def natIn (add : Pt → Pt → Pt) (zero one : Pt) : ℕ → Pt
  | 0 => zero
  | n + 1 => if n = 0 then one else add (natIn add zero one n) one

def intIn (add : Pt → Pt → Pt) (zero one : Pt) (neg : Pt → Pt) (k : ℤ) : Pt :=
  if 0 ≤ k then natIn add zero one k.toNat else neg (natIn add zero one k.natAbs)

/-- A real number in a ring: by its embedding of the reals, if it has one; otherwise an
integer `k` is `k·1`, a rational number `p/q` is `(p·1)(q·1)⁻¹`, and others have no meaning
(the zero). -/
def numeralIn (add : Pt → Pt → Pt) (zero one : Pt) (neg : Pt → Pt) (mul : Pt → Pt → Pt) (inv : Pt → Pt)
    (real : Option (ℝ → Pt)) (r : ℝ) : Pt :=
  match real with
  | some e => e r
  | none =>
    if h : ∃ q : ℚ, (q : ℝ) = r then
      let q := Classical.choose h
      if q.den = 1 then intIn add zero one neg q.num
      else mul (intIn add zero one neg q.num) (inv (intIn add zero one neg q.den))
    else zero

def Ops.numeral (o : Ops) (r : ℝ) : Pt := numeralIn o.add o.zero o.one o.neg o.mul o.inv o.real r
def ROps.numeral (o : ROps) (r : ℝ) : Pt := numeralIn o.add o.zero o.one o.neg o.mul o.inv o.real r

/-- The ring operations of a structure. -/
def Ops.ring (o : Ops) : ROps := ⟨o.add, o.zero, o.neg, o.mul, o.one, o.inv, o.real⟩
/-- A ring's operations as those of a structure. -/
def ROps.lift (r : ROps) : Ops :=
  { (default : Ops) with add := r.add, zero := r.zero, neg := r.neg, mul := r.mul, one := r.one, inv := r.inv, real := r.real }

/-- `x ^ n` for a natural number `n`. -/
def Ops.npow (o : Ops) (x : Pt) : ℕ → Pt
  | 0 => o.one
  | n + 1 => o.mul (o.npow x n) x

/-! ## Operations on elements -/

def ofReal (r : ℝ) : El := .num r

/-- A binary operation: on two elements of a structure its operation, a numeral as an
element of the structure, two numerals as real numbers. -/
def lift2 (f : Ops → Pt → Pt → Pt) (g : ℝ → ℝ → ℝ) : El → El → El
  | .el o x, .el _ y => .el o (f o x y)
  | .el o x, .num s => .el o (f o x (o.numeral s))
  | .num r, .el o y => .el o (f o (o.numeral r) y)
  | .num r, .num s => .num (g r s)

def add : El → El → El := lift2 Ops.add (· + ·)
def sub : El → El → El := lift2 (fun o x y => o.add x (o.neg y)) (· - ·)
def div : El → El → El := lift2 (fun o x y => o.mul x (o.inv y)) (· / ·)

/-- `xy`: the product of a structure, or a scalar times an element of a module (`cv`, the
scalar `c` an element of another structure); a number times an element is the number as a
scalar (in a ring, a multiple of `1`; in a real vector space, the real number). -/
def mul : El → El → El
  | .el o x, .el o' y => if o = o' then .el o (o.mul x y) else .el o' (o'.smul x y)
  | .num r, .el o y => .el o (o.smul (o.sops.numeral r) y)
  | .el o x, .num s => .el o (o.smul (o.sops.numeral s) x)
  | .num r, .num s => .num (r * s)

def neg : El → El
  | .el o x => .el o (o.neg x)
  | .num r => .num (-r)

/-- `x ^ n` for an integer `n` (`x^{-1}` is the inverse). -/
def pow : El → ℝ → El
  | .el o x, n =>
    if h : ∃ k : ℤ, (k : ℝ) = n then
      let k := Classical.choose h
      if 0 ≤ k then .el o (o.npow x k.toNat) else .el o (o.inv (o.npow x k.natAbs))
    else .el o o.zero
  | .num r, n => .num (r ^ n)

/-- `x^{-1}`. -/
def inv (a : El) : El := pow a (-1)

/-- Equality of elements: of the same structure and point, a numeral as an element of the
structure of the other side. -/
def eqv : El → El → Prop
  | .el o x, .el o' y => o = o' ∧ x = y
  | .el o x, .num s => x = o.numeral s
  | .num r, .el o y => o.numeral r = y
  | .num r, .num s => r = s

def le : El → El → Prop
  | .el o x, .el o' y => o = o' ∧ o.le x y
  | .el o x, .num s => o.le x (o.numeral s)
  | .num r, .el o y => o.le (o.numeral r) y
  | .num r, .num s => r ≤ s

def lt (a b : El) : Prop := le a b ∧ ¬ eqv a b

/-- An element with an inverse in its operations (every element of a group, a nonzero
element of a field, a unit of a ring): where `x/y` and `y^{-1}` are meant. -/
def Invertible : El → Prop
  | .el o y => ∃ z, o.mul y z = o.one ∧ o.mul z y = o.one
  | .num r => r ≠ 0

/-- The norm of an element of a normed space, the inner product of two elements of an inner
product space. -/
def norm : El → ℝ
  | .el o x => o.norm x
  | .num r => |r|
def inner : El → El → ℝ
  | .el o x, .el _ y => o.inner x y
  | _, _ => 0

/-- The distance between two elements of a metric space. -/
def dist : El → El → ℝ
  | .el o x, .el _ y => o.dist x y
  | _, _ => 0

/-! ## Structures -/

/-- The operations of a structure (those of one of its elements). -/
def opsOf (S : El → Prop) : Ops := if h : ∃ o x, S (.el o x) then Classical.choose h else default

/-- The points of a structure. -/
def carrier (S : El → Prop) : Set Pt := {x | S (.el (opsOf S) x)}

/-- The elements of `S` are points with the same operations. -/
def Uniform (S : El → Prop) : Prop := ∀ a, S a → ∃ x, a = .el (opsOf S) x

/-- The element of `S` at a point. -/
def at' (S : El → Prop) (x : Pt) : El := .el (opsOf S) x

/-! ### Groups -/

/-- A group on the points of `S` with the product, identity and inverse of `S`. -/
def GroupOn (S : El → Prop) (G : Group (carrier S)) : Prop :=
  letI := G
  ((1 : carrier S) : Pt) = (opsOf S).one ∧
  ∀ a b : carrier S, ((a * b : carrier S) : Pt) = (opsOf S).mul a b ∧ ((a⁻¹ : carrier S) : Pt) = (opsOf S).inv a

/-- The additive and the multiplicative notation of `S` are the same operations (a group
may be written either way). -/
def OneNotation (S : El → Prop) : Prop :=
  let o := opsOf S
  o.zero = o.one ∧ ∀ a ∈ carrier S, o.neg a = o.inv a ∧ ∀ b ∈ carrier S, o.add a b = o.mul a b

/-- `S` is a group (Mathlib `Group`), written multiplicatively or additively. -/
def IsGroup (S : El → Prop) : Prop := Uniform S ∧ OneNotation S ∧ ∃ G, GroupOn S G

/-- A property of Mathlib's groups, of the group `S`. -/
def groupHas (P : (α : Type) → Group α → Prop) (S : El → Prop) : Prop :=
  Uniform S ∧ OneNotation S ∧ ∃ G, GroupOn S G ∧ P (carrier S) G

def Abelian : (El → Prop) → Prop := groupHas fun α G => letI := G; ∀ a b : α, a * b = b * a
def Cyclic : (El → Prop) → Prop := groupHas fun α G => letI := G; IsCyclic α
def SimpleGroup : (El → Prop) → Prop := groupHas fun α G => letI := G; IsSimpleGroup α
def Solvable : (El → Prop) → Prop := groupHas fun α G => letI := G; Group.IsSolvable α
def Nilpotent : (El → Prop) → Prop := groupHas fun α G => letI := G; Group.IsNilpotent α
/-- A `p`-group: the order of every element is a power of `p` (Mathlib `IsPGroup`). -/
def PGroup (p : ℝ) : (El → Prop) → Prop := groupHas fun α G => letI := G; IsPGroup ⌊p⌋₊ α

/-- `H` is a subgroup of `G`: a group, with the operations of `G`, inside `G`. -/
def SubgroupOf (G H : El → Prop) : Prop := IsGroup H ∧ ∀ a, H a → G a
/-- `N` is a normal subgroup of `G` (Mathlib `Subgroup.Normal`). -/
def NormalIn (G N : El → Prop) : Prop :=
  SubgroupOf G N ∧ IsGroup G ∧ ∀ g n, G g → N n → N (mul (mul g n) (pow g (-1)))

/-- The number of elements, `0` for an infinite structure (Mathlib `Nat.card`). -/
def card (S : El → Prop) : ℝ := Nat.card (carrier S)
def Finite (S : El → Prop) : Prop := (carrier S).Finite
def Countable (S : El → Prop) : Prop := (carrier S).Countable

/-- The order of an element: the least `n ≥ 1` with `g^n = 1`, `0` if there is none
(Mathlib `orderOf`). -/
def orderEl : El → ℝ
  | .el o x => if h : ∃ n : ℕ, 0 < n ∧ o.npow x n = o.one then (Nat.find h : ℝ) else 0
  | .num _ => 0

/-- The index `[G : H]` (Mathlib `Subgroup.index`): the number of cosets `gH`, `0` if
infinite. -/
def index (G H : El → Prop) : ℝ :=
  Nat.card {c : Set Pt // ∃ g ∈ carrier G, c = {x | ∃ h ∈ carrier H, x = (opsOf G).mul g h}}

/-- The centre: the elements that commute with every element. -/
def center (G : El → Prop) : El → Prop := fun a => G a ∧ ∀ b, G b → eqv (mul a b) (mul b a)

/-- The exponent (Mathlib `Monoid.exponent`). -/
def exponent (G : El → Prop) : ℝ :=
  if h : ∃ G' : Group (carrier G), GroupOn G G' then
    (@Monoid.exponent (carrier G) (Classical.choose h).toMonoid : ℝ) else 0

/-- The number of Sylow `p`-subgroups (Mathlib `Sylow`). -/
def numSylow (p : ℝ) (G : El → Prop) : ℝ :=
  if h : ∃ G' : Group (carrier G), GroupOn G G' then
    (@Nat.card (@Sylow ⌊p⌋₊ (carrier G) (Classical.choose h)) : ℝ) else 0

/-- The identity element (the zero, in additive notation). -/
def identity (S : El → Prop) : El := .el (opsOf S) (opsOf S).one
def zero (S : El → Prop) : El := .el (opsOf S) (opsOf S).zero

/-- A number as an element of the structure `S` (`φ(1)` for `φ\colon G\to H`). -/
def ofRealIn (S : El → Prop) (r : ℝ) : El := .el (opsOf S) ((opsOf S).numeral r)

/-- The subgroup generated by an element: its integer powers. -/
def cyclicSub (g : El) : El → Prop := fun a => ∃ k : ℤ, eqv a (pow g k)

/-! ### Homomorphisms -/

/-- `f` is a homomorphism of groups (or monoids) on `G`: `f(ab) = f(a)f(b)`. -/
def HomOn (G : El → Prop) (f : El → El) : Prop :=
  ∀ a b, G a → G b → eqv (f (mul a b)) (mul (f a) (f b))

/-- `f` is a homomorphism of rings on `R`: sums, products and the identity. -/
def RingHomOn (R : El → Prop) (f : El → El) : Prop :=
  HomOn R f ∧ (∀ a b, R a → R b → eqv (f (add a b)) (add (f a) (f b))) ∧ eqv (f (identity R)) (.num 1)

def InjOn (S : El → Prop) (f : El → El) : Prop := ∀ a b, S a → S b → eqv (f a) (f b) → eqv a b

/-- The kernel of a homomorphism on `G`: the elements mapped to the identity (the zero; in a
group, written either way, they are the same). -/
def kernel (G : El → Prop) (f : El → El) : El → Prop := fun a => G a ∧ eqv (f a) (.num 0)
/-- The image of `S` under `f`. -/
def image (S : El → Prop) (f : El → El) : El → Prop := fun b => ∃ a, S a ∧ eqv b (f a)

/-- `G` and `H` are isomorphic: there is a bijective homomorphism (Mathlib `MulEquiv`). -/
def Isomorphic (G H : El → Prop) : Prop :=
  ∃ f : El → El, HomOn G f ∧ InjOn G f ∧ (∀ a, G a → H (f a)) ∧ ∀ b, H b → ∃ a, G a ∧ eqv (f a) b

/-! ### Rings and fields -/

/-- A ring on the points of `S` with the sum, product, zero, identity and negation of `S`. -/
def RingOn (S : El → Prop) (R : Ring (carrier S)) : Prop :=
  letI := R
  ((0 : carrier S) : Pt) = (opsOf S).zero ∧ ((1 : carrier S) : Pt) = (opsOf S).one ∧
  ∀ a b : carrier S, ((a + b : carrier S) : Pt) = (opsOf S).add a b ∧
    ((a * b : carrier S) : Pt) = (opsOf S).mul a b ∧ ((-a : carrier S) : Pt) = (opsOf S).neg a

/-- The inverse of `S` is the inverse of the nonzero elements of the ring `R`. -/
def InvOn (S : El → Prop) (R : Ring (carrier S)) : Prop :=
  letI := R
  ∀ a b : carrier S, a * b = 1 → ((b : carrier S) : Pt) = (opsOf S).inv a

/-- A ring is its own ring of scalars, acting by its product (so that `2x` is `(1+1)x`). -/
def SelfScalars (S : El → Prop) : Prop :=
  (opsOf S).sops = (opsOf S).ring ∧ ∀ a ∈ carrier S, ∀ b ∈ carrier S, (opsOf S).smul a b = (opsOf S).mul a b

def IsRing (S : El → Prop) : Prop := Uniform S ∧ SelfScalars S ∧ ∃ R, RingOn S R ∧ InvOn S R

def ringHas (P : (α : Type) → Ring α → Prop) (S : El → Prop) : Prop :=
  Uniform S ∧ SelfScalars S ∧ ∃ R, RingOn S R ∧ InvOn S R ∧ P (carrier S) R

def CommRing' : (El → Prop) → Prop := ringHas fun α R => letI := R; ∀ a b : α, a * b = b * a
def Domain : (El → Prop) → Prop := ringHas fun α R => letI := R; (∀ a b : α, a * b = b * a) ∧ IsDomain α
def IsFieldS : (El → Prop) → Prop := ringHas fun α R => letI := R; IsField α
def DivisionRing' : (El → Prop) → Prop := ringHas fun α R => letI := R; Nontrivial α ∧ ∀ a : α, a ≠ 0 → ∃ b, a * b = 1
def Noetherian : (El → Prop) → Prop := ringHas fun α R => letI := R; IsNoetherianRing α
def PID : (El → Prop) → Prop :=
  ringHas fun α R => letI := R; (∀ a b : α, a * b = b * a) ∧ IsDomain α ∧ IsPrincipalIdealRing α
def UFD : (El → Prop) → Prop :=
  ringHas fun α R => letI := R; ∃ h : (∀ a b : α, a * b = b * a),
    letI : CommRing α := { R with mul_comm := h }; IsDomain α ∧ UniqueFactorizationMonoid α
def LocalRing' : (El → Prop) → Prop :=
  ringHas fun α R => letI := R; (∀ a b : α, a * b = b * a) ∧ IsLocalRing α
def Reduced : (El → Prop) → Prop := ringHas fun α R => letI := R; IsReduced α

/-- The characteristic (Mathlib `ringChar`). -/
def char (S : El → Prop) : ℝ :=
  if h : ∃ R : Ring (carrier S), RingOn S R then (@ringChar (carrier S) (Classical.choose h).toNonAssocRing.toNonAssocSemiring : ℝ) else 0

/-- The perfection `K^{p^∞}` of a field of characteristic `p`: the elements that are
`p^n`-th powers in `K` for every `n` (`⋂ₙ K^{pⁿ}`). -/
def perfectionS (K : El → Prop) : El → Prop := fun x =>
  K x ∧ ∀ n : ℕ, ∃ y, K y ∧ eqv (pow y ((char K) ^ n)) x

def AlgClosed : (El → Prop) → Prop :=
  ringHas fun α R => letI := R; ∃ h : IsField α, letI := h.toField; IsAlgClosed α
def Perfect : (El → Prop) → Prop :=
  ringHas fun α R => letI := R; ∃ h : IsField α, letI := h.toField; PerfectField α

/-- `I` is an ideal of the ring `R` (a two-sided ideal). -/
def IdealOf (R I : El → Prop) : Prop :=
  IsRing R ∧ (∀ a, I a → R a) ∧ I (zero R) ∧
  (∀ a b, I a → I b → I (add a b)) ∧ (∀ r a, R r → I a → I (mul r a) ∧ I (mul a r))
def ProperIdealOf (R I : El → Prop) : Prop := IdealOf R I ∧ ¬ I (identity R)
/-- A prime ideal of a commutative ring: proper, and `ab ∈ I` gives `a ∈ I` or `b ∈ I`. -/
def PrimeIdealOf (R I : El → Prop) : Prop :=
  ProperIdealOf R I ∧ ∀ a b, R a → R b → I (mul a b) → I a ∨ I b
/-- A maximal ideal: proper, and contained in no other proper ideal. -/
def MaximalIdealOf (R I : El → Prop) : Prop :=
  ProperIdealOf R I ∧ ∀ J, ProperIdealOf R J → (∀ a, I a → J a) → ∀ a, J a → I a
def PrincipalIdealOf (R I : El → Prop) : Prop :=
  IdealOf R I ∧ ∃ g, R g ∧ ∀ a, I a ↔ ∃ r, R r ∧ eqv a (mul r g)

/-- A unit of a ring: an element with an inverse. -/
def UnitIn (R : El → Prop) (a : El) : Prop := R a ∧ ∃ b, R b ∧ eqv (mul a b) (.num 1) ∧ eqv (mul b a) (.num 1)
def ZeroDivisorIn (R : El → Prop) (a : El) : Prop := R a ∧ ∃ b, R b ∧ ¬ eqv b (.num 0) ∧ eqv (mul a b) (.num 0)
def NilpotentIn (R : El → Prop) (a : El) : Prop := R a ∧ ∃ n : ℕ, eqv (pow a n) (.num 0)

/-- `K` is a subfield of `L`. -/
def SubfieldOf (L K : El → Prop) : Prop := IsFieldS K ∧ IsFieldS L ∧ ∀ a, K a → L a
def SubringOf (R S : El → Prop) : Prop := IsRing S ∧ IsRing R ∧ ∀ a, S a → R a

/-! ### Modules and vector spaces -/

/-- An additive commutative group on the points of `S` with its sum, zero and negation. -/
def AddOn (S : El → Prop) (A : AddCommGroup (carrier S)) : Prop :=
  letI := A
  ((0 : carrier S) : Pt) = (opsOf S).zero ∧
  ∀ a b : carrier S, ((a + b : carrier S) : Pt) = (opsOf S).add a b ∧ ((-a : carrier S) : Pt) = (opsOf S).neg a

/-- `V` is a module over the ring `R`: an additive group whose scalars are the points of
`R`, acting by the scalar multiplication of `V` (Mathlib `Module`). -/
def ModuleOver (R V : El → Prop) : Prop :=
  Uniform V ∧ Uniform R ∧ (opsOf V).scalars = carrier R ∧ (opsOf V).sops = (opsOf R).ring ∧
  ∃ (Rr : Ring (carrier R)) (A : AddCommGroup (carrier V)), RingOn R Rr ∧ AddOn V A ∧
    ∃ M : @Module (carrier R) (carrier V) Rr.toSemiring A.toAddCommMonoid,
      ∀ (c : carrier R) (v : carrier V), ((@HSMul.hSMul _ _ _ (@instHSMul _ _ M.toSMul) c v : carrier V) : Pt) =
        (opsOf V).smul c v

def VectorSpaceOver (K V : El → Prop) : Prop := IsFieldS K ∧ ModuleOver K V

/-- A property of Mathlib's modules, of the module `V` over `R`. -/
def moduleHas (P : (α β : Type) → (Rr : Ring α) → (A : AddCommGroup β) →
    @Module α β Rr.toSemiring A.toAddCommMonoid → Prop) (R V : El → Prop) : Prop :=
  ModuleOver R V ∧ ∃ (Rr : Ring (carrier R)) (A : AddCommGroup (carrier V)), RingOn R Rr ∧ AddOn V A ∧
    ∃ M : @Module (carrier R) (carrier V) Rr.toSemiring A.toAddCommMonoid,
      (∀ (c : carrier R) (v : carrier V), ((@HSMul.hSMul _ _ _ (@instHSMul _ _ M.toSMul) c v : carrier V) : Pt) =
        (opsOf V).smul c v) ∧ P _ _ Rr A M

/-- `W` is a subspace (a submodule): nonempty, closed under sums and under the scalars of
its operations. -/
def Subspace (W : El → Prop) : Prop :=
  Uniform W ∧ (∃ a, W a) ∧ (∀ a b, W a → W b → W (add a b)) ∧
  ∀ c ∈ (opsOf W).scalars, ∀ a, W a → W (.el (opsOf W) ((opsOf W).smul c (match a with | .el _ x => x | .num _ => ∅)))
def SubspaceOf (V W : El → Prop) : Prop := Subspace W ∧ ∀ a, W a → V a

/-- The dimension of `V` over `K` (Mathlib `Module.finrank`; `0` if infinite). -/
def dim (K V : El → Prop) : ℝ :=
  if h : ∃ (Rr : Ring (carrier K)) (A : AddCommGroup (carrier V)), RingOn K Rr ∧ AddOn V A ∧
      ∃ M : @Module (carrier K) (carrier V) Rr.toSemiring A.toAddCommMonoid,
        ∀ (c : carrier K) (v : carrier V), ((@HSMul.hSMul _ _ _ (@instHSMul _ _ M.toSMul) c v : carrier V) : Pt) =
          (opsOf V).smul c v then
    let Rr := Classical.choose h
    let h2 := Classical.choose_spec h
    let A := Classical.choose h2
    let M := Classical.choose (Classical.choose_spec h2).2.2
    (@Module.finrank (carrier K) (carrier V) Rr.toSemiring A.toAddCommMonoid M : ℝ)
  else 0

def FiniteDim (K V : El → Prop) : Prop :=
  moduleHas (fun α β Rr A M => @Module.Finite α β Rr.toSemiring A.toAddCommMonoid M) K V

/-- `f` is linear on `V`: sums, and the scalars of `V`. -/
def LinearOn (V : El → Prop) (f : El → El) : Prop :=
  (∀ a b, V a → V b → eqv (f (add a b)) (add (f a) (f b))) ∧
  ∀ c ∈ (opsOf V).scalars, ∀ x ∈ carrier V,
    eqv (f (.el (opsOf V) ((opsOf V).smul c x)))
      (match f (.el (opsOf V) x) with | .el o y => .el o (o.smul c y) | a => a)

/-- The ring of scalars of a module, as a structure: its points, with its ring operations. -/
def scal (V : El → Prop) : El → Prop :=
  fun a => ∃ x ∈ (opsOf V).scalars, a = .el (opsOf V).sops.lift x

/-- The dimension of `V` over its own scalars (Mathlib `Module.finrank`). -/
def dimS (V : El → Prop) : ℝ := dim (scal V) V
def FiniteDimS (V : El → Prop) : Prop := FiniteDim (scal V) V

/-- A linear combination `c₁x₁ + ⋯ + cₙxₙ`, with the operations `o`. -/
def lincomb (o : Ops) (l : List (Pt × Pt)) : Pt := l.foldr (fun p acc => o.add (o.smul p.1 p.2) acc) o.zero

/-- `B` is linearly independent: a linear combination of distinct elements of `B` with
scalars of its module is zero only with zero scalars (Mathlib `LinearIndependent`). -/
def LinIndep (B : El → Prop) : Prop :=
  Uniform B ∧ ∀ l : List (Pt × Pt), (l.map Prod.snd).Nodup → (∀ p ∈ l, p.2 ∈ carrier B ∧ p.1 ∈ (opsOf B).scalars) →
    lincomb (opsOf B) l = (opsOf B).zero → ∀ p ∈ l, p.1 = (opsOf B).sops.zero

/-- The span of `B`: the smallest subspace with its operations that contains it (Mathlib
`Submodule.span`). -/
def span (B : El → Prop) : El → Prop :=
  fun a => ∀ W, Subspace W → opsOf W = opsOf B → (∀ b, B b → W b) → W a

/-- `B` is a basis of `V`: linearly independent and spanning `V` (Mathlib `Basis`). -/
def BasisOf (V B : El → Prop) : Prop := (∀ a, B a → V a) ∧ LinIndep B ∧ ∀ a, V a ↔ span B a

/-- `B` spans `V`. -/
def SpansOf (V B : El → Prop) : Prop := (∀ a, B a → V a) ∧ ∀ a, V a ↔ span B a

/-! ### Maps with a codomain -/

/-- `f` maps `X` onto `Y`. -/
def SurjOnto (X Y : El → Prop) (f : El → El) : Prop := ∀ b, Y b → ∃ a, X a ∧ eqv (f a) b
def BijOnto (X Y : El → Prop) (f : El → El) : Prop := InjOn X f ∧ SurjOnto X Y f
/-- An isomorphism of `X` onto `Y`: a bijective homomorphism of groups (or rings, or a
bijective linear map of modules), whatever operations they have (Mathlib `MulEquiv`). -/
def IsoOnto (X Y : El → Prop) (f : El → El) : Prop :=
  BijOnto X Y f ∧ HomOn X f ∧ ∀ a b, X a → X b → eqv (f (add a b)) (add (f a) (f b))

/-! ### Topological and metric spaces -/

/-- The topology on the points of `S` that the open sets of its operations induce: the open
sets of `S` are the traces `V ∩ S` of open sets `V` (for a space, its open sets; for a subset
of a space, its subspace topology, Mathlib `TopologicalSpace.induced`). -/
def TopOn (S : El → Prop) (t : TopologicalSpace (carrier S)) : Prop :=
  ∀ U : Set (carrier S), t.IsOpen U ↔ ∃ V ∈ (opsOf S).opens, Subtype.val '' U = V ∩ carrier S

def IsTopSpace (S : El → Prop) : Prop := Uniform S ∧ ∃ t, TopOn S t

def topHas (P : (α : Type) → TopologicalSpace α → Prop) (S : El → Prop) : Prop :=
  Uniform S ∧ ∃ t, TopOn S t ∧ P (carrier S) t

def Hausdorff : (El → Prop) → Prop := topHas fun α t => letI := t; T2Space α
def T1 : (El → Prop) → Prop := topHas fun α t => letI := t; T1Space α
def RegularS : (El → Prop) → Prop := topHas fun α t => letI := t; RegularSpace α
def NormalS : (El → Prop) → Prop := topHas fun α t => letI := t; NormalSpace α
def CompactS : (El → Prop) → Prop := topHas fun α t => letI := t; CompactSpace α
def ConnectedS : (El → Prop) → Prop := topHas fun α t => letI := t; ConnectedSpace α
def PathConnectedS : (El → Prop) → Prop := topHas fun α t => letI := t; PathConnectedSpace α
def LocallyCompactS : (El → Prop) → Prop := topHas fun α t => letI := t; LocallyCompactSpace α
def SecondCountableS : (El → Prop) → Prop := topHas fun α t => letI := t; SecondCountableTopology α
def SeparableS : (El → Prop) → Prop := topHas fun α t => letI := t; TopologicalSpace.SeparableSpace α
def MetrizableS : (El → Prop) → Prop := topHas fun α t => letI := t; TopologicalSpace.MetrizableSpace α
def DiscreteS : (El → Prop) → Prop := topHas fun α t => letI := t; DiscreteTopology α

/-- A subset of a space is open: its points are an open set of the space's topology. -/
def OpenS (U : El → Prop) : Prop := Uniform U ∧ carrier U ∈ (opsOf U).opens
/-- `F` is closed in `X`: its complement in `X` is open in `X`. -/
def ClosedIn (X F : El → Prop) : Prop :=
  (∀ a, F a → X a) ∧ ∃ V ∈ (opsOf X).opens, {x | x ∈ carrier X ∧ x ∉ carrier F} = V ∩ carrier X
/-- `D` is dense in `X`: it meets every nonempty open set of `X`. -/
def DenseIn (X D : El → Prop) : Prop :=
  (∀ a, D a → X a) ∧ ∀ U ∈ (opsOf X).opens, (∃ x ∈ U, x ∈ carrier X) → ∃ x ∈ U, x ∈ carrier D
/-- `N` is a neighbourhood of `a`: it contains an open set that contains `a`. -/
def NbhdOf (a : El) (N : El → Prop) : Prop :=
  ∃ x, a = .el (opsOf N) x ∧ ∃ U ∈ (opsOf N).opens, x ∈ U ∧ U ⊆ carrier N ∧ Uniform N

/-- `f` is continuous on `X` into the spaces of its values: the preimage of an open set is
open in `X` (relative to `X`). -/
def ContinuousOn' (X : El → Prop) (f : El → El) : Prop :=
  ∀ (o : Ops), ∀ U ∈ o.opens, ∃ V ∈ (opsOf X).opens,
    ∀ x ∈ carrier X, (x ∈ V ↔ ∃ y ∈ U, eqv (f (.el (opsOf X) x)) (.el o y))

/-- `f` is a homeomorphism of `X` onto its image: continuous, with a continuous inverse. -/
def HomeoOn (X : El → Prop) (f : El → El) : Prop :=
  ContinuousOn' X f ∧ ∃ g : El → El, ContinuousOn' (image X f) g ∧
    (∀ a, X a → eqv (g (f a)) a) ∧ ∀ b, image X f b → eqv (f (g b)) b

/-- A metric on the points of `S` whose distance and open sets are those of `S`. -/
def MetricOn (S : El → Prop) (m : MetricSpace (carrier S)) : Prop :=
  (∀ a b : carrier S, @Dist.dist _ m.toDist a b = (opsOf S).dist a b) ∧ TopOn S m.toUniformSpace.toTopologicalSpace

def IsMetricSpace (S : El → Prop) : Prop := Uniform S ∧ ∃ m, MetricOn S m

def metricHas (P : (α : Type) → MetricSpace α → Prop) (S : El → Prop) : Prop :=
  Uniform S ∧ ∃ m, MetricOn S m ∧ P (carrier S) m

def CompleteS : (El → Prop) → Prop := metricHas fun α m => letI := m; CompleteSpace α
def TotallyBoundedS : (El → Prop) → Prop := metricHas fun α m => letI := m; TotallyBounded (Set.univ : Set α)
def BoundedS : (El → Prop) → Prop := metricHas fun α m => letI := m; Bornology.IsBounded (Set.univ : Set α)

/-- A real function on `X` is continuous (Mathlib `ContinuousOn`). -/
def ContinuousReal (X : El → Prop) (f : El → ℝ) : Prop :=
  ∀ U : Set ℝ, IsOpen U → ∃ V ∈ (opsOf X).opens, ∀ x ∈ carrier X, (x ∈ V ↔ f (.el (opsOf X) x) ∈ U)

/-- The operations of an element (a numeral has none). -/
def opsEl : El → Ops
  | .el o _ => o
  | .num _ => default
def ptEl : El → Pt
  | .el _ x => x
  | .num _ => ∅

/-- A sequence `s` (a function of the natural numbers) converges to `l`, in the topology of
the space that `l` belongs to (Mathlib `Filter.Tendsto … atTop (nhds l)`). -/
def ConvergesTo (s : ℝ → El) (l : El) : Prop :=
  (∃ x, l = .el (opsEl l) x) ∧ ∀ U ∈ (opsEl l).opens, ptEl l ∈ U →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ y ∈ U, s n = .el (opsEl l) y

/-- A Cauchy sequence of a metric space: `d(s_m, s_n) < ε` for large `m`, `n`. -/
def CauchySeq' (s : ℝ → El) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n → dist (s m) (s n) < ε

/-- `f` is an isometry on `X`. -/
def IsometryOn (X : El → Prop) (f : El → El) : Prop := ∀ a b, X a → X b → dist (f a) (f b) = dist a b
def LipschitzOn (L : ℝ) (X : El → Prop) (f : El → El) : Prop := ∀ a b, X a → X b → dist (f a) (f b) ≤ L * dist a b

/-! ### Normed and inner product spaces

A real normed space: the scalars are the real numbers (its ring of scalars embeds them). -/

/-- The scalars of `S` are the real numbers, by an embedding of `ℝ`. -/
def RealScalars (S : El → Prop) : Prop :=
  ∃ e : ℝ → Pt, (opsOf S).sops.real = some e ∧ Function.Injective e ∧ (opsOf S).scalars = Set.range e ∧
    (opsOf S).sops.add = (fun a b => e ((Classical.epsilon fun r => e r = a) + (Classical.epsilon fun r => e r = b))) ∧
    (opsOf S).sops.mul = (fun a b => e ((Classical.epsilon fun r => e r = a) * (Classical.epsilon fun r => e r = b)))

/-- `V` is a real vector space: a vector space over a field whose elements are the real
numbers, with their sum and product. -/
def RealVectorSpace (V : El → Prop) : Prop := RealScalars V ∧ ∃ K, VectorSpaceOver K V

/-- A normed real vector space on the points of `S` with its sum, zero, negation, norm,
distance, open sets and real scalars. -/
def NormedOn (S : El → Prop) (N : NormedAddCommGroup (carrier S)) (M : @NormedSpace ℝ (carrier S) _ N.toSeminormedAddCommGroup) : Prop :=
  letI := N
  ((0 : carrier S) : Pt) = (opsOf S).zero ∧
  (∀ a b : carrier S, ((a + b : carrier S) : Pt) = (opsOf S).add a b ∧ ((-a : carrier S) : Pt) = (opsOf S).neg a ∧
    ‖a‖ = (opsOf S).norm a ∧ Dist.dist a b = (opsOf S).dist a b) ∧
  TopOn S N.toUniformSpace.toTopologicalSpace ∧
  ∃ e : ℝ → Pt, (opsOf S).sops.real = some e ∧
    ∀ (r : ℝ) (a : carrier S), ((@HSMul.hSMul _ _ _ (@instHSMul _ _ M.toModule.toDistribMulAction.toSMul) r a : carrier S) : Pt) = (opsOf S).smul (e r) a

def IsNormedSpace (S : El → Prop) : Prop := Uniform S ∧ RealScalars S ∧ ∃ N M, NormedOn S N M

def normedHas (P : (α : Type) → (N : NormedAddCommGroup α) → @NormedSpace ℝ α _ N.toSeminormedAddCommGroup → Prop)
    (S : El → Prop) : Prop :=
  Uniform S ∧ RealScalars S ∧ ∃ N M, NormedOn S N M ∧ P (carrier S) N M

/-- A Banach space: a complete normed space (Mathlib `CompleteSpace`). -/
def Banach : (El → Prop) → Prop := normedHas fun α N _ => letI := N; CompleteSpace α

/-- A real inner product space: a normed space whose norm comes from the inner product of `S`
(Mathlib `InnerProductSpace ℝ`). -/
def IsInnerProductSpace (S : El → Prop) : Prop :=
  IsNormedSpace S ∧ (∀ a ∈ carrier S, (opsOf S).norm a = Real.sqrt ((opsOf S).inner a a)) ∧
  (∀ a ∈ carrier S, ∀ b ∈ carrier S, (opsOf S).inner a b = (opsOf S).inner b a) ∧
  (∀ a ∈ carrier S, ∀ b ∈ carrier S, ∀ c ∈ carrier S, (opsOf S).inner ((opsOf S).add a b) c =
    (opsOf S).inner a c + (opsOf S).inner b c) ∧
  ∀ (r : ℝ) (e : ℝ → Pt), (opsOf S).sops.real = some e → ∀ a ∈ carrier S, ∀ b ∈ carrier S,
    (opsOf S).inner ((opsOf S).smul (e r) a) b = r * (opsOf S).inner a b

/-- A Hilbert space: a complete inner product space. -/
def Hilbert (S : El → Prop) : Prop := IsInnerProductSpace S ∧ Banach S

/-- Orthogonal elements: their inner product is zero. -/
def Orthogonal (a b : El) : Prop := inner a b = 0

/-- `f` is a bounded linear map on the normed space `X`: linear, with `‖f(x)‖ ≤ C‖x‖`
(Mathlib `ContinuousLinearMap`). -/
def BoundedLinearOn (X : El → Prop) (f : El → El) : Prop :=
  LinearOn X f ∧ ∃ C : ℝ, ∀ a, X a → norm (f a) ≤ C * norm a

/-- The operator norm of a bounded linear map on `X` (Mathlib `ContinuousLinearMap.opNorm`):
the least `C ≥ 0` with `‖f(x)‖ ≤ C‖x‖`. -/
def opNorm (X : El → Prop) (f : El → El) : ℝ :=
  sInf {C : ℝ | 0 ≤ C ∧ ∀ a, X a → norm (f a) ≤ C * norm a}

/-! ### Monoids, finite generation, field extensions -/

/-- A monoid (Mathlib `Monoid`) and a semigroup (Mathlib `Semigroup`) with the product of `S`. -/
def IsMonoid (S : El → Prop) : Prop :=
  Uniform S ∧ ∃ M : Monoid (carrier S), letI := M; ((1 : carrier S) : Pt) = (opsOf S).one ∧
    ∀ a b : carrier S, ((a * b : carrier S) : Pt) = (opsOf S).mul a b
def IsSemigroup (S : El → Prop) : Prop :=
  Uniform S ∧ ∃ M : Semigroup (carrier S), letI := M; ∀ a b : carrier S, ((a * b : carrier S) : Pt) = (opsOf S).mul a b

/-- A finitely generated group (Mathlib `Group.FG`). -/
def FGGroup : (El → Prop) → Prop := groupHas fun α G => letI := G; Group.FG α
/-- A finitely generated module (Mathlib `Module.Finite`). -/
def FGModule (R V : El → Prop) : Prop :=
  moduleHas (fun α β Rr A M => @Module.Finite α β Rr.toSemiring A.toAddCommMonoid M) R V

/-- The subfield of `L` generated by `T`: the smallest subfield with the operations of `L`
that contains `T`. -/
def genField (L T : El → Prop) : El → Prop :=
  fun a => ∀ M, IsFieldS M → opsOf M = opsOf L → (∀ b, T b → M b) → M a

/-- `L` is a finitely generated extension of `K`: generated over `K` by finitely many
elements (Mathlib `IntermediateField.FG`). -/
def FGExtension (K L : El → Prop) : Prop :=
  SubfieldOf L K ∧ ∃ F : List El, (∀ b ∈ F, L b) ∧ ∀ a, L a ↔ genField L (fun b => K b ∨ b ∈ F) a

/-- The degree `[L : K]` (Mathlib `Module.finrank K L`). -/
def degree (L K : El → Prop) : ℝ := dim K L

/-- The value of the polynomial with coefficients `c₀, c₁, …` at `a`, by Horner's rule. -/
def polyEval (cs : List El) (a : El) : El := cs.foldr (fun c acc => add c (mul a acc)) (.num 0)

/-- `a` is algebraic over `K`: a root of a nonzero polynomial with coefficients in `K`
(Mathlib `IsAlgebraic`). -/
def AlgebraicEl (K : El → Prop) (a : El) : Prop :=
  ∃ cs : List El, (∀ c ∈ cs, K c) ∧ (∃ c ∈ cs, ¬ eqv c (.num 0)) ∧ eqv (polyEval cs a) (.num 0)
/-- `L` is algebraic over `K` (Mathlib `Algebra.IsAlgebraic`). -/
def AlgebraicExt (K L : El → Prop) : Prop := SubfieldOf L K ∧ ∀ a, L a → AlgebraicEl K a
/-- `L` is a finite extension of `K` (Mathlib `FiniteDimensional K L`). -/
def FiniteExt (K L : El → Prop) : Prop := SubfieldOf L K ∧ FiniteDim K L

/-! ### More topology -/

/-- The closure of `A` in `X` (Mathlib `closure`): the points of `X` every open neighbourhood
of which meets `A`. -/
def closureIn (A X : El → Prop) : El → Prop :=
  fun a => X a ∧ ∀ V ∈ (opsOf X).opens, (match a with | .el _ x => x ∈ V | .num _ => False) →
    ∃ b, A b ∧ (match b with | .el _ y => y ∈ V | .num _ => False)
/-- The interior of `A` in `X` (Mathlib `interior`). -/
def interiorIn (A X : El → Prop) : El → Prop :=
  fun a => A a ∧ ∃ V ∈ (opsOf X).opens, (match a with | .el _ x => x ∈ V | .num _ => False) ∧
    ∀ y ∈ V, y ∈ carrier X → A (.el (opsOf X) y)
/-- The boundary of `A` in `X` (Mathlib `frontier`). -/
def boundaryIn (A X : El → Prop) : El → Prop := fun a => closureIn A X a ∧ ¬ interiorIn A X a

/-- `a` is a limit point of `A` (Mathlib `AccPt`): every open set containing `a` meets `A`
in another point. -/
def LimitPointOf (A : El → Prop) (a : El) : Prop :=
  ∃ x, a = .el (opsOf A) x ∧ ∀ V ∈ (opsOf A).opens, x ∈ V → ∃ y ∈ V, y ≠ x ∧ y ∈ carrier A
def IsolatedPointOf (A : El → Prop) (a : El) : Prop := A a ∧ ¬ LimitPointOf A a

def FirstCountableS : (El → Prop) → Prop := topHas fun α t => letI := t; FirstCountableTopology α
def TotallyDisconnectedS : (El → Prop) → Prop := topHas fun α t => letI := t; TotallyDisconnectedSpace α
def SigmaCompactS : (El → Prop) → Prop := topHas fun α t => letI := t; SigmaCompactSpace α
def LindelofS : (El → Prop) → Prop := topHas fun α t => letI := t; LindelofSpace α
def T0 : (El → Prop) → Prop := topHas fun α t => letI := t; T0Space α
def PerfectSpace' : (El → Prop) → Prop := topHas fun α t => letI := t; ∀ x : α, (nhdsWithin x {x}ᶜ).NeBot

/-- The diameter of a set of a metric space: the supremum of the distances (Mathlib
`Metric.diam`). -/
def diam (A : El → Prop) : ℝ := sSup {d | ∃ a b, A a ∧ A b ∧ d = dist a b}
/-- A bounded set of a metric space: its distances are bounded. -/
def BoundedSet (A : El → Prop) : Prop := ∃ C : ℝ, ∀ a b, A a → A b → dist a b ≤ C

/-! ### Counting -/

def numSubgroups (G : El → Prop) : ℝ := Nat.card {H : El → Prop // SubgroupOf G H}
def numNormalSubgroups (G : El → Prop) : ℝ := Nat.card {H : El → Prop // NormalIn G H}
/-- The number of conjugacy classes (Mathlib `ConjClasses`). -/
def numConjClasses (G : El → Prop) : ℝ :=
  if h : ∃ G' : Group (carrier G), GroupOn G G' then
    (@Nat.card (@ConjClasses (carrier G) (Classical.choose h).toMonoid) : ℝ) else 0
def numOfOrder (d : ℝ) (G : El → Prop) : ℝ := Nat.card {a : El // G a ∧ orderEl a = d}
def centerOrder (G : El → Prop) : ℝ := card (center G)

/-! ### Named structures

A group of Mathlib on a finite type, as a structure: its elements numbered by
`Fintype.equivFin`, the point of `k` being `{k}`. -/

def ptNat (k : ℕ) : Pt := {(k : ℝ)}

def encF (α : Type) [Fintype α] (a : α) : Pt := ptNat (Fintype.equivFin α a)
def decF (α : Type) [Fintype α] [Nonempty α] (x : Pt) : α :=
  if h : ∃ a, encF α a = x then Classical.choose h else Classical.arbitrary α

/-- The operations of a finite group, in both notations. -/
def opsOfGroup (α : Type) [Group α] [Fintype α] : Ops :=
  letI : Nonempty α := ⟨1⟩
  { (default : Ops) with
    mul := fun x y => encF α (decF α x * decF α y), one := encF α 1, inv := fun x => encF α (decF α x)⁻¹,
    add := fun x y => encF α (decF α x * decF α y), zero := encF α 1, neg := fun x => encF α (decF α x)⁻¹ }

def ofGroup (α : Type) [Group α] [Fintype α] : El → Prop :=
  fun a => ∃ g : α, a = .el (opsOfGroup α) (encF α g)

def trivialGroup : El → Prop := ofGroup Unit
/-- The cyclic group of order `n` (Mathlib `Multiplicative (ZMod n)`). -/
def cyclicGroup (n : ℝ) : El → Prop :=
  if h : ⌊n⌋₊ = 0 then trivialGroup else haveI : NeZero ⌊n⌋₊ := ⟨h⟩; ofGroup (Multiplicative (ZMod ⌊n⌋₊))
def symmetricGroup (n : ℝ) : El → Prop := ofGroup (Equiv.Perm (Fin ⌊n⌋₊))
def alternatingGroup' (n : ℝ) : El → Prop := ofGroup (alternatingGroup (Fin ⌊n⌋₊))
/-- The dihedral group of order `m = 2n` (Mathlib `DihedralGroup n`). -/
def dihedralGroup (m : ℝ) : El → Prop :=
  if h : ⌊m⌋₊ / 2 = 0 then trivialGroup else haveI : NeZero (⌊m⌋₊ / 2) := ⟨h⟩; ofGroup (DihedralGroup (⌊m⌋₊ / 2))
def kleinFour : El → Prop := ofGroup (Multiplicative (ZMod 2 × ZMod 2))

/-! The direct product of two structures: pairs of points, encoded as one point, with the
operations taken in each factor. -/

def pair (x y : Pt) : Pt := (Real.exp '' x) ∪ ((fun t => -Real.exp t) '' y)
def fst (z : Pt) : Pt := {t | Real.exp t ∈ z}
def snd (z : Pt) : Pt := {t | -Real.exp t ∈ z}

def prodOps (o p : Ops) : Ops :=
  { (default : Ops) with
    add := fun a b => pair (o.add (fst a) (fst b)) (p.add (snd a) (snd b)), zero := pair o.zero p.zero,
    neg := fun a => pair (o.neg (fst a)) (p.neg (snd a)),
    mul := fun a b => pair (o.mul (fst a) (fst b)) (p.mul (snd a) (snd b)), one := pair o.one p.one,
    inv := fun a => pair (o.inv (fst a)) (p.inv (snd a)) }

def prod (G H : El → Prop) : El → Prop :=
  fun a => ∃ x y, G (.el (opsOf G) x) ∧ H (.el (opsOf H) y) ∧ a = .el (prodOps (opsOf G) (opsOf H)) (pair x y)

/-! ### Orders -/

def PosetOn (S : El → Prop) (P : PartialOrder (carrier S)) : Prop :=
  ∀ a b : carrier S, @LE.le _ P.toLE a b ↔ (opsOf S).le a b

def IsPoset (S : El → Prop) : Prop := Uniform S ∧ ∃ P, PosetOn S P
def posetHas (Q : (α : Type) → PartialOrder α → Prop) (S : El → Prop) : Prop :=
  Uniform S ∧ ∃ P, PosetOn S P ∧ Q (carrier S) P

def TotalS : (El → Prop) → Prop := posetHas fun _ P => ∀ a b, @LE.le _ P.toLE a b ∨ @LE.le _ P.toLE b a
def LatticeS : (El → Prop) → Prop := posetHas fun α P =>
  (∀ a b : α, ∃ s, @IsLUB α P.toPreorder.toLE {a, b} s) ∧ ∀ a b : α, ∃ s, @IsGLB α P.toPreorder.toLE {a, b} s
def WellOrderedS : (El → Prop) → Prop := posetHas fun α P =>
  (∀ a b, @LE.le _ P.toLE a b ∨ @LE.le _ P.toLE b a) ∧ WellFounded (@LT.lt α P.toLT)

/-- `b` is an upper bound of `A`, `b` is the supremum of `A`. -/
def UpperBound (A : El → Prop) (b : El) : Prop := ∀ a, A a → le a b
def LowerBound (A : El → Prop) (b : El) : Prop := ∀ a, A a → le b a
def MaximalIn (S : El → Prop) (m : El) : Prop := S m ∧ ∀ a, S a → le m a → eqv a m
def MinimalIn (S : El → Prop) (m : El) : Prop := S m ∧ ∀ a, S a → le a m → eqv a m
def GreatestIn (S : El → Prop) (m : El) : Prop := S m ∧ ∀ a, S a → le a m
def LeastIn (S : El → Prop) (m : El) : Prop := S m ∧ ∀ a, S a → le m a
def MonotoneOn' (S : El → Prop) (f : El → El) : Prop := ∀ a b, S a → S b → le a b → le (f a) (f b)

/-! ### Maps

A map between structures with its domain and codomain, as Mathlib's bundled maps
(`G →* H`, `V →ₗ[K] W`): `φ(g)` is its value, a number its value at that element of the
domain (`φ(1)` at the identity of `G`), and its properties are about its domain. -/

structure Map where
  dom : El → Prop
  cod : El → Prop
  fn : El → El

instance : Inhabited Map := ⟨⟨fun _ => False, fun _ => False, id⟩⟩
def mapDefault : Map := default

/-- `φ(a)`. -/
def apply (φ : Map) : El → El
  | .num r => φ.fn (ofRealIn φ.dom r)
  | a => φ.fn a

/-- `φ\colon G\to H`: the domain is `G`, the codomain `H`, and `φ` maps `G` into `H`. -/
def MapSig (G H : El → Prop) (φ : Map) : Prop :=
  (∀ a, φ.dom a ↔ G a) ∧ (∀ a, φ.cod a ↔ H a) ∧ ∀ a, G a → H (apply φ a)

/-- `ψ ∘ φ`. -/
def compose (ψ φ : Map) : Map := ⟨φ.dom, ψ.cod, fun a => apply ψ (apply φ a)⟩
/-- Two maps are equal: the same domain and codomain, the same values on the domain. -/
def mapEq (φ ψ : Map) : Prop :=
  (∀ a, φ.dom a ↔ ψ.dom a) ∧ (∀ a, φ.cod a ↔ ψ.cod a) ∧ ∀ a, φ.dom a → eqv (apply φ a) (apply ψ a)
/-- The identity map of `S`. -/
def idMap (S : El → Prop) : Map := ⟨S, S, id⟩

def mDom (φ : Map) : El → Prop := φ.dom
def mCod (φ : Map) : El → Prop := φ.cod

def IsHomM (φ : Map) : Prop := HomOn φ.dom (apply φ)
def IsRingHomM (φ : Map) : Prop := RingHomOn φ.dom (apply φ)
def LinearM (φ : Map) : Prop := LinearOn φ.dom (apply φ)
def ContinuousM (φ : Map) : Prop := ContinuousOn' φ.dom (apply φ)
def HomeoM (φ : Map) : Prop := HomeoOn φ.dom (apply φ) ∧ SurjOnto φ.dom φ.cod (apply φ)
def IsometryM (φ : Map) : Prop := IsometryOn φ.dom (apply φ)
def MonotoneM (φ : Map) : Prop := MonotoneOn' φ.dom (apply φ)
def BoundedLinearM (φ : Map) : Prop := BoundedLinearOn φ.dom (apply φ)
def InjectiveM (φ : Map) : Prop := InjOn φ.dom (apply φ)
def SurjectiveM (φ : Map) : Prop := SurjOnto φ.dom φ.cod (apply φ)
def BijectiveM (φ : Map) : Prop := BijOnto φ.dom φ.cod (apply φ)
def IsoM (φ : Map) : Prop := IsoOnto φ.dom φ.cod (apply φ)
/-- An isomorphism of a structure onto itself. -/
def AutoM (φ : Map) : Prop := IsoM φ ∧ ∀ a, φ.dom a ↔ φ.cod a
/-- A map of a structure into itself. -/
def EndoM (φ : Map) : Prop := ∀ a, φ.dom a ↔ φ.cod a
def LipschitzM (L : ℝ) (φ : Map) : Prop := LipschitzOn L φ.dom (apply φ)
/-- A contraction: Lipschitz with a constant less than `1`. -/
def ContractionM (φ : Map) : Prop := ∃ L : ℝ, 0 ≤ L ∧ L < 1 ∧ LipschitzOn L φ.dom (apply φ)

/-- The kernel: the elements of the domain mapped to the identity (the zero). -/
def kernelM (φ : Map) : El → Prop := kernel φ.dom (apply φ)
/-- The image of the domain. -/
def imageM (φ : Map) : El → Prop := image φ.dom (apply φ)
/-- `φ(K)`: the image of the elements of `K` in the domain. -/
def imageSetM (φ : Map) (K : El → Prop) : El → Prop := image (fun a => φ.dom a ∧ K a) (apply φ)
/-- The rank and the nullity of a linear map (Mathlib `LinearMap.rank`). -/
def rankM (φ : Map) : ℝ := dimS (imageM φ)
def nullityM (φ : Map) : ℝ := dimS (kernelM φ)
/-- The operator norm. -/
def opNormM (φ : Map) : ℝ := opNorm φ.dom (apply φ)
/-- `c` is an eigenvalue of `T`: `Tv = cv` for some nonzero `v` of the domain. -/
def EigenvalueOf (T : Map) (c : El) : Prop :=
  ∃ v, T.dom v ∧ ¬ eqv v (.num 0) ∧ eqv (apply T v) (mul c v)
/-- `v` is an eigenvector of `T`: nonzero, and `Tv = cv` for a scalar `c` of its space. -/
def EigenvectorOf (T : Map) (v : El) : Prop :=
  T.dom v ∧ ¬ eqv v (.num 0) ∧ ∃ c ∈ (opsEl v).scalars, eqv (apply T v) (.el (opsEl v) ((opsEl v).smul c (ptEl v)))
/-- `a` is a fixed point of `φ`. -/
def FixedPointOf (φ : Map) (a : El) : Prop := φ.dom a ∧ eqv (apply φ a) a

end

end Leanify.Structures
