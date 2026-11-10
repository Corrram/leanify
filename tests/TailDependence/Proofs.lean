import TailDependence.Article

/-! # Proofs of the definitions and claims of `article.tex`

* `definedI : wellDefinedI`: definition `I` makes sense (no division by zero, every
  argument in its domain). `definedness [h₁, …]` proves most of these; give it the
  facts it cannot find.
* `proofK : obligationK`: claim `K` holds. `intro_premises` introduces
  `cJ : claimJ` for each premise `J` (in a proof, the earlier steps and the cited
  results). A claim the text derives (a proof step, or a result with a compiled
  proof) may use only its premises, Mathlib and the article: `#leanify_certify`
  audits this.
* `refuteK : meaningfulK ∧ ¬ claimK` instead records that claim `K` is false as
  stated; readers and the PDF margin then mark it.
* `satisfiedK : satisfiableK`: the hypotheses of claim `K` can hold together.

A proof that still uses `sorry` leaves its claim unverified, and `lake build`
certifies the others. -/

namespace TailDependence.Proofs
open TailDependence
open scoped unitInterval

/-! ## Two facts about copulas

A copula of the model is the distribution function of a probability measure on
`[0,1]^2` with uniform marginals. It vanishes on the left edge of the square, and
its value on the right edge is the second coordinate. -/

theorem copula_zero_left {C : I → I → ℝ} (hC : copulas C) (v : I) : C 0 v = 0 := by
  obtain ⟨⟨μ, hμ, hF⟩, hu, -⟩ := hC
  have h01 : C 0 1 = 0 := by simpa using hu 0
  have hmono : μ (Set.Iic 0 ×ˢ Set.Iic v) ≤ μ (Set.Iic 0 ×ˢ Set.Iic 1) :=
    MeasureTheory.measure_mono (Set.prod_mono le_rfl (Set.Iic_subset_Iic.mpr unitInterval.le_one'))
  have hle := ENNReal.toReal_mono (MeasureTheory.measure_ne_top μ _) hmono
  rw [hF] at h01 ⊢
  linarith [ENNReal.toReal_nonneg (a := μ (Set.Iic 0 ×ˢ Set.Iic v))]

theorem copula_one_left {C : I → I → ℝ} (hC : copulas C) (v : I) : C 1 v = v := hC.2.2 v

theorem projIcc_one : Set.projIcc (0 : ℝ) 1 zero_le_one 1 = (1 : I) := by
  rw [Set.projIcc_right]; rfl

theorem projIcc_zero : Set.projIcc (0 : ℝ) 1 zero_le_one 0 = (0 : I) := by
  rw [Set.projIcc_left]; rfl

theorem projIcc_coe (u : I) : Set.projIcc (0 : ℝ) 1 zero_le_one u = u := Set.projIcc_val zero_le_one u

/-! ## Definitions -/

theorem defined0 : wellDefined0 := by
  unfold wellDefined0
  definedness []

theorem defined1 : wellDefined1 := by
  unfold wellDefined1
  definedness []

theorem defined2 : wellDefined2 := by
  unfold wellDefined2
  definedness []

theorem defined3 : wellDefined3 := by
  unfold wellDefined3
  definedness []

/-! ## Proposition 1: every LTD copula is PQD -/

/-- `If $u=0$, then $C(u,v)=0=uv$.` -/
theorem proof1 : obligation1 := by
  intro_premises
  refine ⟨by unfold meaningful1; definedness [], fun C ⟨hC, _⟩ u v hu => ?_⟩
  have h : u = 0 := Subtype.ext hu
  subst h
  exact ⟨copula_zero_left hC v, by simp⟩

/-- `If $u>0$, then $\frac{C(u,v)}{u}\ge C(1,v)=v$ by \eqref{eq:ltd}.` -/
theorem proof2 : obligation2 := by
  intro_premises
  refine ⟨by unfold meaningful2; definedness [], fun C ⟨hC, hL⟩ u v hu => ?_⟩
  have h := hL v u ⟨hu, u.2.2⟩ 1 ⟨one_pos, le_rfl⟩ u.2.2
  rw [projIcc_one, projIcc_coe, div_one] at h
  rw [projIcc_one]
  exact ⟨h, copula_one_left hC v⟩

/-- `Hence $C(u,v)\ge uv$.` -/
theorem proof3 : obligation3 := by
  intro_premises
  refine ⟨by unfold meaningful3; definedness [], fun C hCL u v => ?_⟩
  rcases (unitInterval.nonneg u).eq_or_lt with h0 | hpos
  · obtain ⟨h1, h2⟩ := c1 C hCL u v h0.symm
    linarith
  · obtain ⟨h1, h2⟩ := c2 C hCL u v hpos
    rw [h2, le_div_iff₀ hpos] at h1
    linarith

/-- Proposition 1, from its proof. -/
theorem proof0 : obligation0 := by
  intro_premises
  exact ⟨by unfold meaningful0; definedness [], fun C hCL u v => c3 C hCL u v⟩

/-! ## Proposition 2: every RTI copula is PQD -/

/-- `If $u=1$, then $C(u,v)=v=uv$.` -/
theorem proof5 : obligation5 := by
  intro_premises
  refine ⟨by unfold meaningful5; definedness [], fun C ⟨hC, _⟩ u v hu => ?_⟩
  have h : u = 1 := Subtype.ext hu
  subst h
  exact ⟨copula_one_left hC v, by simp⟩

/-- `If $u<1$, then $\frac{1-u-v+C(u,v)}{1-u}\ge1-v+C(0,v)=1-v$ by \eqref{eq:rti}.` -/
theorem proof6 : obligation6 := by
  intro_premises
  refine ⟨by unfold meaningful6; definedness [], fun C ⟨hC, hR⟩ u v hu => ?_⟩
  have h := hR v 0 ⟨le_rfl, one_pos⟩ u ⟨u.2.1, hu⟩ u.2.1
  rw [projIcc_zero, projIcc_coe, sub_zero, div_one] at h
  rw [projIcc_zero, copula_zero_left hC v]
  rw [copula_zero_left hC v] at h
  exact ⟨by linarith, by ring⟩

/-- `Hence $C(u,v)\ge uv$.` -/
theorem proof7 : obligation7 := by
  intro_premises
  refine ⟨by unfold meaningful7; definedness [], fun C hCR u v => ?_⟩
  rcases (unitInterval.le_one u).eq_or_lt with h1 | hlt
  · obtain ⟨h, h'⟩ := c5 C hCR u v h1
    linarith
  · obtain ⟨h, h'⟩ := c6 C hCR u v hlt
    rw [h', le_div_iff₀ (by linarith)] at h
    nlinarith

/-- Proposition 2, from its proof. -/
theorem proof4 : obligation4 := by
  intro_premises
  exact ⟨by unfold meaningful4; definedness [], fun C hCR u v => c7 C hCR u v⟩

/-! ## The hypotheses can be met

The independence copula `Π(u,v) = uv`, the distribution function of Lebesgue measure on
the square, is a copula, and it is left-tail decreasing and right-tail increasing (the
two maps are constant). So no step of the proofs above holds for an empty reason. -/

/-- The independence copula `Π(u,v) = uv`. -/
def indep : I → I → ℝ := fun u v => (u : ℝ) * v

theorem indep_copula : copulas indep := by
  refine ⟨⟨(MeasureTheory.volume : MeasureTheory.Measure I).prod MeasureTheory.volume, inferInstance, fun u v => ?_⟩, fun u => ?_, fun v => ?_⟩
  · rw [MeasureTheory.Measure.prod_prod, unitInterval.volume_Iic, unitInterval.volume_Iic,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal u.2.1, ENNReal.toReal_ofReal v.2.1]
    rfl
  · simp [indep]
  · simp [indep]

theorem coe_projIcc {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    ((Set.projIcc (0 : ℝ) 1 zero_le_one x : I) : ℝ) = x := by
  rw [Set.projIcc_of_mem zero_le_one ⟨h0, h1⟩]

theorem indep_ltd : leftTailDecreasing indep := by
  intro v a ha b hb _
  simp only [indep, coe_projIcc ha.1.le ha.2, coe_projIcc hb.1.le hb.2]
  rw [mul_div_cancel_left₀ _ hb.1.ne', mul_div_cancel_left₀ _ ha.1.ne']

theorem indep_rti : rightTailIncreasing indep := by
  intro v a ha b hb _
  simp only [indep, coe_projIcc ha.1 ha.2.le, coe_projIcc hb.1 hb.2.le]
  have h1 : (1 - a - (v : ℝ) + a * v) / (1 - a) = 1 - v := by
    rw [div_eq_iff (by linarith)]; ring
  have h2 : (1 - b - (v : ℝ) + b * v) / (1 - b) = 1 - v := by
    rw [div_eq_iff (by linarith)]; ring
  rw [h1, h2]

theorem satisfied0 : satisfiable0 := ⟨indep, indep_copula, indep_ltd⟩
theorem satisfied1 : satisfiable1 := ⟨indep, ⟨indep_copula, indep_ltd⟩, 0, 0, rfl⟩
theorem satisfied2 : satisfiable2 := ⟨indep, ⟨indep_copula, indep_ltd⟩, 1, 1, by norm_num⟩
theorem satisfied4 : satisfiable4 := ⟨indep, indep_copula, indep_rti⟩
theorem satisfied5 : satisfiable5 := ⟨indep, ⟨indep_copula, indep_rti⟩, 1, 1, rfl⟩
theorem satisfied6 : satisfiable6 := ⟨indep, ⟨indep_copula, indep_rti⟩, 0, 0, by norm_num⟩
end TailDependence.Proofs
