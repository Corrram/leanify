import Leanify.Library.Hilbert
import Leanify.Library.UnitSquareModel
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-! # The meaning of the vocabulary of square-integrable functions

Functions on `[0,1]` and kernels are functions, as everywhere in Leanify; the statements of the
field `hilbert` are about them as elements of `L^2` (classes of functions that agree almost
everywhere) through the norm: an operator that is `c` times the identity on a class `A` sends
each `g` of `A` to a function `h` with `\lVert h-cg\rVert=0`.

* `memL2 f`: `f` is measurable with an integrable square on `[0,1]` (Mathlib `MemLp f 2`);
  `memL20 f`: moreover `∫ f = 0`;
* `inner1 f g = ∫ f g` and `norm1 f = (∫ f^2)^{1/2}` on `[0,1]`;
* for kernels (functions of a sequence in `[0,1]` that depend on finitely many of its terms):
  `innerSeq F G` and `normSeq F` against the law `uniformLaw` of independent uniform terms;
* `opNormOn T A`: the least `c ≥ 0` with `\lVert Tg\rVert ≤ c\lVert g\rVert` for all `g` of `A`
  (the norm of `T` on `A`; `0` when there is no such `c`); `opNormOnSeq` for operators on
  kernels;
* `tensorPow T m`: `T` applied to each of the terms `1, …, m` of the sequence, one after the
  other (`T` acting on the function of that term with the others fixed);
* `hoeffding F S`: the component of `F` for a finite set `S` of positive integers,
  `\sum_{A\subseteq S}(-1)^{|S\setminus A|}\,\mathbb{E}[F\mid\text{terms in }A]`, the conditional
  expectation replacing the terms outside `A` by independent uniform ones; `hoeffSpace S G`:
  `G` is a kernel with `\lVert G-G_S\rVert=0`;
* `dependsFirst F m`: `m` is a natural number and `F` depends only on the terms `1, …, m`;
* `subsetSum m f = \sum_{S\subseteq\{1,\dots,m\}} f(S)` for a natural number `m` (else `0`). -/

namespace Leanify.Hilbert.Model
open MeasureTheory UnitSquare
open scoped unitInterval

/-- `f` is square-integrable on `[0,1]`. -/
def memL2 (f : I → ℝ) : Prop := MemLp f 2 (volume : Measure I)

/-- `f` is square-integrable on `[0,1]` with integral zero. -/
def memL20 (f : I → ℝ) : Prop := memL2 f ∧ ∫ x, f x = 0

/-- The inner product of `L^2([0,1])`. -/
noncomputable def inner1 (f g : I → ℝ) : ℝ := ∫ x, f x * g x

/-- The norm of `L^2([0,1])`. -/
noncomputable def norm1 (f : I → ℝ) : ℝ := Real.sqrt (∫ x, f x ^ 2)

/-- The inner product of kernels, for independent uniform terms. -/
noncomputable def innerSeq (F G : (ℝ → I) → ℝ) : ℝ := ∫ s, F (seqOf s) * G (seqOf s) ∂uniformLaw

/-- The norm of a kernel, for independent uniform terms. -/
noncomputable def normSeq (F : (ℝ → I) → ℝ) : ℝ := Real.sqrt (∫ s, F (seqOf s) ^ 2 ∂uniformLaw)

/-- The norm of an operator on a class of functions. -/
noncomputable def opNormOn (T : (I → ℝ) → (I → ℝ)) (A : (I → ℝ) → Prop) : ℝ :=
  sInf {c : ℝ | 0 ≤ c ∧ ∀ g, A g → norm1 (T g) ≤ c * norm1 g}

/-- The norm of an operator on a class of kernels. -/
noncomputable def opNormOnSeq (T : ((ℝ → I) → ℝ) → ((ℝ → I) → ℝ)) (A : ((ℝ → I) → ℝ) → Prop) : ℝ :=
  sInf {c : ℝ | 0 ≤ c ∧ ∀ G, A G → normSeq (T G) ≤ c * normSeq G}

/-- `T` applied to the term `i` of a sequence, the other terms fixed. -/
noncomputable def applyAt (T : (I → ℝ) → (I → ℝ)) (i : ℕ) (F : (ℝ → I) → ℝ) : (ℝ → I) → ℝ :=
  fun x => T (fun u => F (Function.update x (i : ℝ) u)) (x (i : ℝ))

/-- `T` applied to the terms `1, …, n` of a sequence (the last term first). -/
noncomputable def applyUpTo (T : (I → ℝ) → (I → ℝ)) : ℕ → ((ℝ → I) → ℝ) → ((ℝ → I) → ℝ)
  | 0, F => F
  | n + 1, F => applyUpTo T n (applyAt T (n + 1) F)

/-- The tensor power `T^{\otimes m}`: `T` applied to each of the terms `1, …, m`. -/
noncomputable def tensorPow (T : (I → ℝ) → (I → ℝ)) (m : ℝ) (F : (ℝ → I) → ℝ) : (ℝ → I) → ℝ :=
  applyUpTo T (Nat.floor m) F

/-- The conditional expectation of a kernel given the terms of a set `A` of indices: the
other terms are replaced by independent uniform ones. -/
noncomputable def condOn (A : ℝ → Prop) (F : (ℝ → I) → ℝ) : (ℝ → I) → ℝ := by
  classical
  exact fun x => ∫ s, F (fun t => if A t then x t else seqOf s t) ∂uniformLaw

/-- The component `F_S` of a kernel for a finite set `S` (of positive integers): the
alternating sum of the conditional expectations given the subsets of `S`. -/
noncomputable def hoeffding (F : (ℝ → I) → ℝ) (S : ℝ → Prop) : (ℝ → I) → ℝ := by
  classical
  exact if h : {t : ℝ | S t}.Finite then
    fun x => ∑ A ∈ h.toFinset.powerset,
      (-1 : ℝ) ^ (h.toFinset.card - A.card) * condOn (fun t => t ∈ A) F x
  else fun _ => 0

/-- The subspace of the components for `S`: the kernels `G` with `\lVert G-G_S\rVert=0`. -/
def hoeffSpace (S : ℝ → Prop) (G : (ℝ → I) → ℝ) : Prop :=
  isKernel G ∧ normSeq (fun x => G x - hoeffding G S x) = 0

/-- `F` depends only on the terms `1, …, m` of a sequence (`m` a natural number). -/
def dependsFirst (F : (ℝ → I) → ℝ) (m : ℝ) : Prop :=
  ∃ n : ℕ, (n : ℝ) = m ∧ ∀ x y : ℝ → I, (∀ i : ℕ, 1 ≤ i → i ≤ n → x i = y i) → F x = F y

/-- `\sum_{S\subseteq\{1,\dots,m\}} f(S)` for a natural number `m` (else `0`). -/
noncomputable def subsetSum (m : ℝ) (f : (ℝ → Prop) → ℝ) : ℝ := by
  classical
  exact if ∃ n : ℕ, (n : ℝ) = m then
    ∑ A ∈ (Finset.Icc 1 (Nat.floor m)).powerset, f (fun t => ∃ i ∈ A, (i : ℝ) = t)
  else 0

end Leanify.Hilbert.Model
