import Arguments.Article

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
* `satisfiedK : satisfiableK`: the hypotheses of statement `K` can hold together (give
  values for its variables). A statement whose hypotheses cannot all hold is true for
  an empty reason; the report says for which statements this is shown.

`leanify_step` is the standard tactic for a whole obligation. The certificate reports
which claims that the text derives it closes.

A proof that still uses `sorry` leaves its claim unverified, and `lake build`
certifies the others. -/

namespace Arguments.Proofs
open Arguments

/-- Claim 0, statement (lemma at line 18; premises: claim 1, claim 2, claim 3):
`\forall x\in \mathbb{R},\ 1<x\Rightarrow x<{x}^{2}` -/
theorem proof0 : obligation0 := by
  leanify_step

/-- The hypotheses of claim 0 can hold together:
`\exists x\in \mathbb{R},\ 1<x` -/
theorem satisfied0 : satisfiable0 := by
  leanify_values 2

/-- Claim 1, proof step (proof at line 22; no premises):
`\forall x\in \mathbb{R},\ 1<x\Rightarrow 0<x-1` -/
theorem proof1 : obligation1 := by
  leanify_step

/-- Claim 2, proof step (proof at line 22; premises: claim 1):
`\forall x\in \mathbb{R},\ 1<x\Rightarrow 0<x` -/
theorem proof2 : obligation2 := by
  leanify_step

/-- Claim 3, proof step (proof at line 23; premises: claim 1, claim 2):
`\forall x\in \mathbb{R},\ 1<x\Rightarrow {x}^{2}-x=x\,(x-1)\land 0<x\,(x-1)` -/
theorem proof3 : obligation3 := by
  leanify_step

/-- Claim 4, statement (lemma at line 27; premises: claim 5, claim 6):
`\forall x\in \mathbb{R},\ \forall y\in \mathbb{R},\ 0<x\land x<y\Rightarrow {x}^{2}<{y}^{2}` -/
theorem proof4 : obligation4 := by
  leanify_step

/-- The hypotheses of claim 4 can hold together:
`\exists x\in \mathbb{R},\ \exists y\in \mathbb{R},\ 0<x\land x<y` -/
theorem satisfied4 : satisfiable4 := by
  leanify_values 1 2

/-- Claim 5, proof step (proof at line 33; no premises):
`\forall x\in \mathbb{R},\ \forall y\in \mathbb{R},\ 0<x\Rightarrow x<y\Rightarrow 0<y-x` -/
theorem proof5 : obligation5 := by
  leanify_step

/-- Claim 6, proof step (proof at line 35; premises: claim 5):
`\forall x\in \mathbb{R},\ \forall y\in \mathbb{R},\ 0<x\Rightarrow x<y\Rightarrow 0<y+x\Rightarrow {y}^{2}-{x}^{2}=(y-x)\,(y+x)\land 0<(y-x)\,(y+x)` -/
theorem proof6 : obligation6 := by
  leanify_step

/-- Claim 7, statement (lemma at line 41; no premises):
`\forall x\in \mathbb{R},\ x\in \mathbb{Z}\Rightarrow (\exists z\in \mathbb{R},\ z\in \mathbb{Z}\land x=2\,z)\Rightarrow (\exists z\in \mathbb{R},\ z\in \mathbb{Z}\land {x}^{2}=2\,z)` -/
theorem proof7 : obligation7 := by
  intro_premises
  refine ⟨by unfold meaningful7; definedness [], ?_⟩
  rintro x - ⟨z, ⟨n, rfl⟩, rfl⟩
  exact ⟨2 * (n : ℝ) ^ 2, ⟨2 * n ^ 2, by push_cast; ring⟩, by ring⟩

/-- The hypotheses of claim 7 can hold together:
`\exists x\in \mathbb{R},\ x\in \mathbb{Z}\land (\exists z\in \mathbb{R},\ z\in \mathbb{Z}\land x=2\,z)` -/
theorem satisfied7 : satisfiable7 := by
  leanify_values 0

/-- Claim 8, statement (lemma at line 47; no premises):
`\forall x\in \mathbb{R},\ 0<x\Rightarrow (\forall y\in \mathbb{R},\ 0<{y}^{2}+x)` -/
theorem proof8 : obligation8 := by
  leanify_step

/-- The hypotheses of claim 8 can hold together:
`\exists x\in \mathbb{R},\ 0<x` -/
theorem satisfied8 : satisfiable8 := by
  leanify_values 1

/-- Claim 9, statement (lemma at line 53; premises: claim 10, claim 11, claim 12, claim 13):
`\forall x\in \mathbb{R},\ x\le \lvert x\rvert` -/
theorem proof9 : obligation9 := by
  leanify_step

/-- Claim 10, proof step (proof at line 60; no premises):
`\forall x\in \mathbb{R},\ 0\le x\Rightarrow \lvert x\rvert=x` -/
theorem proof10 : obligation10 := by
  leanify_step

/-- Claim 11, proof step (proof at line 61; premises: claim 10):
`\forall x\in \mathbb{R},\ x<0\Rightarrow \lvert x\rvert=-x` -/
theorem proof11 : obligation11 := by
  leanify_step

/-- Claim 12, proof step (proof at line 62; premises: claim 10, claim 11):
`\forall x\in \mathbb{R},\ x<0\Rightarrow x<0\land 0<\lvert x\rvert` -/
theorem proof12 : obligation12 := by
  leanify_step

/-- Claim 13, proof step (proof at line 64; premises: claim 10, claim 11, claim 12):
`\forall x\in \mathbb{R},\ x\le \lvert x\rvert` -/
theorem proof13 : obligation13 := by
  leanify_step

/-- Claim 14, statement (lemma at line 70; premises: claim 15, claim 16, claim 17):
`\forall x\in \mathbb{R},\ {x}^{2}<1\Rightarrow x<1` -/
theorem proof14 : obligation14 := by
  leanify_step

/-- The hypotheses of claim 14 can hold together:
`\exists x\in \mathbb{R},\ {x}^{2}<1` -/
theorem satisfied14 : satisfiable14 := by
  leanify_values 0

/-- Claim 15, proof step (proof at line 77; no premises):
`\forall x\in \mathbb{R},\ {x}^{2}<1\Rightarrow 1\le x\Rightarrow x\le {x}^{2}\land 1\le x` -/
theorem proof15 : obligation15 := by
  leanify_step

/-- Claim 16, proof step (proof at line 78; premises: claim 15):
`\forall x\in \mathbb{R},\ {x}^{2}<1\Rightarrow 1\le x\Rightarrow \bot` -/
theorem proof16 : obligation16 := by
  leanify_step

/-- Claim 17, proof step (proof at line 79; premises: claim 15, claim 16):
`\forall x\in \mathbb{R},\ {x}^{2}<1\Rightarrow x<1` -/
theorem proof17 : obligation17 := by
  leanify_step

/-- Claim 18, statement (lemma at line 83; premises: claim 19, claim 20, claim 21):
`\forall x\in \mathbb{R},\ \neg ({x}^{2}=-1)` -/
theorem proof18 : obligation18 := by
  leanify_step

/-- Claim 19, proof step (proof at line 89; no premises):
`\forall x\in \mathbb{R},\ {x}^{2}=-1\Rightarrow 0\le {x}^{2}\land {x}^{2}<0` -/
theorem proof19 : obligation19 := by
  leanify_step

/-- Claim 20, proof step (proof at line 89; premises: claim 19):
`\forall x\in \mathbb{R},\ {x}^{2}=-1\Rightarrow \bot` -/
theorem proof20 : obligation20 := by
  leanify_step

/-- Claim 21, proof step (proof at line 90; premises: claim 19, claim 20):
`\forall x\in \mathbb{R},\ \neg ({x}^{2}=-1)` -/
theorem proof21 : obligation21 := by
  leanify_step

/-- Claim 22, statement (lemma at line 98; no premises):
`\forall x\in \mathbb{R},\ 0\le {x}^{2}` -/
theorem proof22 : obligation22 := by
  leanify_step

/-- Claim 23, proof step (proof at line 104; no premises):
`\forall x\in \mathbb{R},\ 0\le x\Rightarrow {x}^{2}=x\,x\land 0\le x\,x` -/
theorem proof23 : obligation23 := by
  leanify_step

/-- Claim 24, statement (lemma at line 114; no premises):
`\forall x\in \mathbb{R},\ 0<x\Rightarrow 0<x+1` -/
theorem proof24 : obligation24 := by
  leanify_step

/-- The hypotheses of claim 24 can hold together:
`\exists x\in \mathbb{R},\ 0<x` -/
theorem satisfied24 : satisfiable24 := by
  leanify_values 1

/-- Claim 25, proof step (proof at line 122; no premises):
`\forall x\in \mathbb{R},\ 0<x\Rightarrow x+1\le 0\Rightarrow x\le -1\land -1<0` -/
theorem proof25 : obligation25 := by
  leanify_step

/-- Claim 26, statement (lemma at line 133; premises: claim 27, claim 28, claim 29):
`\forall x\in \mathbb{R},\ x\in \mathbb{Z}\land 0<x\Rightarrow x\le {x}^{2}` -/
theorem proof26 : obligation26 := by
  intro_premises
  refine ⟨by unfold meaningful26; definedness [], ?_⟩
  -- induction over the positive integers: the base case is claim 27, the step claim 29
  rintro x ⟨⟨k, rfl⟩, hk⟩
  have hk1 : 1 ≤ k := by exact_mod_cast hk
  clear hk
  induction k, hk1 using Int.leInduction with
  | base =>
    have h := c27 1 ⟨⟨1, by norm_num⟩, by norm_num⟩ rfl
    push_cast
    exact h.ge
  | succ m hm ih =>
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    simpa using c29 m ⟨⟨m, rfl⟩, hm0⟩ ih

/-- The hypotheses of claim 26 can hold together:
`\exists x\in \mathbb{R},\ x\in \mathbb{Z}\land 0<x` -/
theorem satisfied26 : satisfiable26 := by
  leanify_values 1

/-- Claim 27, proof step (proof at line 139; no premises):
`\forall x\in \mathbb{R},\ x\in \mathbb{Z}\land 0<x\Rightarrow x=1\Rightarrow {x}^{2}=1` -/
theorem proof27 : obligation27 := by
  leanify_step

/-- Claim 28, proof step (proof at line 141; premises: claim 27):
`\forall x\in \mathbb{R},\ x\in \mathbb{Z}\land 0<x\Rightarrow x\le {x}^{2}\Rightarrow {(x+1)}^{2}={x}^{2}+2\,x+1\land x+2\,x+1\le {x}^{2}+2\,x+1` -/
theorem proof28 : obligation28 := by
  leanify_step

/-- Claim 29, proof step (proof at line 142; premises: claim 27, claim 28):
`\forall x\in \mathbb{R},\ x\in \mathbb{Z}\land 0<x\Rightarrow x\le {x}^{2}\Rightarrow x+1\le {(x+1)}^{2}` -/
theorem proof29 : obligation29 := by
  leanify_step

/-- Claim 30, statement (lemma at line 149; no premises):
`\forall x\in \mathbb{R},\ x\in \mathbb{Z}\land 0<x\Rightarrow x\le {x}^{2}` -/
theorem proof30 : obligation30 := by
  intro_premises
  refine ⟨by unfold meaningful30; definedness [], ?_⟩
  rintro x ⟨⟨k, rfl⟩, hk⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by exact_mod_cast hk : 0 < k)
  nlinarith

/-- The hypotheses of claim 30 can hold together:
`\exists x\in \mathbb{R},\ x\in \mathbb{Z}\land 0<x` -/
theorem satisfied30 : satisfiable30 := by
  leanify_values 1

end Arguments.Proofs
