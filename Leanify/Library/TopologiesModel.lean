import Leanify.Denote
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Bases
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Compactness.SigmaCompact

/-! # The meaning of the field `topologies`

A topology on `ℝ` is a family of sets of real numbers (`(ℝ → Prop) → Prop`) that contains
`ℝ` and is closed under finite intersections and arbitrary unions, as the field states it
in the core language (`IsTopology`). `space τ` is the Mathlib topological space with these
open sets (and `⊥`, a junk value, if `τ` is not a topology), so that every notion of the
field is Mathlib's for that space. -/

namespace Leanify.Topologies

/-- `τ` contains `ℝ` and is closed under finite intersections and arbitrary unions. -/
def IsTopology (τ : (ℝ → Prop) → Prop) : Prop :=
  τ (fun _ => True) ∧ (∀ U V, τ U → τ V → τ (fun x => U x ∧ V x)) ∧
    ∀ 𝓕 : (ℝ → Prop) → Prop, (∀ U, 𝓕 U → τ U) → τ (fun x => ∃ U, 𝓕 U ∧ U x)

set_option warn.classDefReducibility false in
/-- The topological space on `ℝ` whose open sets are those of `τ` (a value, not an instance:
every use names it). -/
noncomputable def space (τ : (ℝ → Prop) → Prop) : TopologicalSpace ℝ := by
  classical
  exact if h : IsTopology τ then
    { IsOpen := τ
      isOpen_univ := h.1
      isOpen_inter := fun s t hs ht => h.2.1 s t hs ht
      isOpen_sUnion := fun s hs => h.2.2 (fun U => U ∈ s) hs }
  else ⊥

def CompactIn (τ : (ℝ → Prop) → Prop) (U : ℝ → Prop) : Prop := @IsCompact ℝ (space τ) U
def ConnectedIn (τ : (ℝ → Prop) → Prop) (U : ℝ → Prop) : Prop := @IsConnected ℝ (space τ) U
def DenseIn (τ : (ℝ → Prop) → Prop) (U : ℝ → Prop) : Prop := @Dense ℝ (space τ) U
def Hausdorff (τ : (ℝ → Prop) → Prop) : Prop := @T2Space ℝ (space τ)
def SecondCountable (τ : (ℝ → Prop) → Prop) : Prop := @SecondCountableTopology ℝ (space τ)
def Separable (τ : (ℝ → Prop) → Prop) : Prop := @TopologicalSpace.SeparableSpace ℝ (space τ)
def Metrizable (τ : (ℝ → Prop) → Prop) : Prop := @TopologicalSpace.MetrizableSpace ℝ (space τ)
def CompactSpaceOf (τ : (ℝ → Prop) → Prop) : Prop := @CompactSpace ℝ (space τ)
def ConnectedSpaceOf (τ : (ℝ → Prop) → Prop) : Prop := @ConnectedSpace ℝ (space τ)
/-- `f` is continuous from `(ℝ, τ)` to `(ℝ, σ)`. -/
def ContinuousFor (τ σ : (ℝ → Prop) → Prop) (f : ℝ → ℝ) : Prop :=
  @Continuous ℝ ℝ (space τ) (space σ) f
noncomputable def closureIn (τ : (ℝ → Prop) → Prop) (U : ℝ → Prop) : ℝ → Prop := @closure ℝ (space τ) U
noncomputable def interiorIn (τ : (ℝ → Prop) → Prop) (U : ℝ → Prop) : ℝ → Prop := @interior ℝ (space τ) U
/-- The sequence `n ↦ a n` (`n ∈ ℕ`) converges to `l` in `(ℝ, τ)`. -/
def ConvergesIn (τ : (ℝ → Prop) → Prop) (a : ℝ → ℝ) (l : ℝ) : Prop :=
  @Filter.Tendsto ℕ ℝ (fun n => a n) Filter.atTop (@nhds ℝ (space τ) l)

end Leanify.Topologies
