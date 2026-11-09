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
* `satisfiedK : satisfiableK`: the hypotheses of claim `K` can hold together (give
  values for its variables: `leanify_values 1 2`). A claim whose hypotheses cannot all
  hold is true for an empty reason, and a step of a proof under them was not checked;
  the report says for which claims this is shown. It is asked once for each set of
  hypotheses, and not of the steps of a proof by contradiction.

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

/-- The hypotheses of claim 6 can hold together:
`\exists x\in \mathbb{R},\ \exists y\in \mathbb{R},\ 0<x\land x<y\land 0<y+x` -/
theorem satisfied6 : satisfiable6 := by
  leanify_values 1 2

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

/-- The hypotheses of claim 10 can hold together:
`\exists x\in \mathbb{R},\ 0\le x` -/
theorem satisfied10 : satisfiable10 := by
  leanify_values 1

/-- Claim 11, proof step (proof at line 61; premises: claim 10):
`\forall x\in \mathbb{R},\ x<0\Rightarrow \lvert x\rvert=-x` -/
theorem proof11 : obligation11 := by
  leanify_step

/-- The hypotheses of claim 11 can hold together:
`\exists x\in \mathbb{R},\ x<0` -/
theorem satisfied11 : satisfiable11 := by
  leanify_values (-1)

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

/-- Claim 22, statement (lemma at line 99; premises: claim 23, claim 24, claim 25, claim 26):
`\forall x\in \mathbb{R},\ \forall y\in \mathbb{R},\ 0<x\land x<y\Rightarrow {x}^{2}<{y}^{2}` -/
theorem proof22 : obligation22 := by
  leanify_step

/-- Claim 23, proof step (proof at line 105; no premises):
`\forall x\in \mathbb{R},\ 0<x\Rightarrow 0<2\,x` -/
theorem proof23 : obligation23 := by
  leanify_step

/-- The hypotheses of claim 23 can hold together:
`\exists x\in \mathbb{R},\ 0<x` -/
theorem satisfied23 : satisfiable23 := by
  leanify_values 1

/-- Claim 24, proof step (proof at line 107; premises: claim 23):
`\forall x\in \mathbb{R},\ \forall y\in \mathbb{R},\ 0<x\Rightarrow x<y\Rightarrow 2\,x<y+x` -/
theorem proof24 : obligation24 := by
  leanify_step

/-- Claim 25, proof step (proof at line 107; premises: claim 23, claim 24):
`\forall x\in \mathbb{R},\ \forall y\in \mathbb{R},\ 0<x\Rightarrow x<y\Rightarrow 0<y-x` -/
theorem proof25 : obligation25 := by
  leanify_step

/-- Claim 26, proof step (proof at line 108; premises: claim 23, claim 24, claim 25):
`\forall x\in \mathbb{R},\ \forall y\in \mathbb{R},\ 0<x\Rightarrow x<y\Rightarrow {y}^{2}-{x}^{2}=(y-x)\,(y+x)\land 0<(y-x)\,(y+x)` -/
theorem proof26 : obligation26 := by
  leanify_step

/-- Claim 27, statement (lemma at line 114; premises: claim 28, claim 29, claim 30):
`\forall x\in \mathbb{R},\ 0\le {x}^{2}` -/
theorem proof27 : obligation27 := by
  leanify_step

/-- Claim 28, proof step (proof at line 120; no premises):
`\forall x\in \mathbb{R},\ 0\le x\Rightarrow {x}^{2}=x\,x\land 0\le x\,x` -/
theorem proof28 : obligation28 := by
  leanify_step

/-- Claim 29, proof step (proof at line 122; premises: claim 28):
`\forall x\in \mathbb{R},\ x<0\Rightarrow 0<-x` -/
theorem proof29 : obligation29 := by
  leanify_step

/-- Claim 30, proof step (proof at line 122; premises: claim 28, claim 29):
`\forall x\in \mathbb{R},\ x<0\Rightarrow {x}^{2}=-x\,-x\land 0<-x\,-x` -/
theorem proof30 : obligation30 := by
  leanify_step

/-- Claim 31, statement (lemma at line 128; premises: claim 32, claim 33):
`\forall x\in \mathbb{R},\ \forall y\in \mathbb{R},\ 2\,x\,y\le {x}^{2}+{y}^{2}` -/
theorem proof31 : obligation31 := by
  leanify_step

/-- Claim 32, proof step (proof at line 134; no premises):
`\forall x\in \mathbb{R},\ \forall y\in \mathbb{R},\ y\le x\Rightarrow 0\le x-y` -/
theorem proof32 : obligation32 := by
  leanify_step

/-- The hypotheses of claim 32 can hold together:
`\exists x\in \mathbb{R},\ \exists y\in \mathbb{R},\ y\le x` -/
theorem satisfied32 : satisfiable32 := by
  leanify_values 1

/-- Claim 33, proof step (proof at line 134; premises: claim 32):
`\forall x\in \mathbb{R},\ \forall y\in \mathbb{R},\ y\le x\Rightarrow {x}^{2}+{y}^{2}-2\,x\,y=(x-y)\,(x-y)\land 0\le (x-y)\,(x-y)` -/
theorem proof33 : obligation33 := by
  leanify_step

/-- Claim 34, statement (lemma at line 140; premises: claim 35, claim 36, claim 37):
`\forall x\in \mathbb{R},\ 0<x\Rightarrow 0<x+1` -/
theorem proof34 : obligation34 := by
  leanify_step

/-- Claim 35, proof step (proof at line 147; no premises):
`\forall x\in \mathbb{R},\ 0<x\Rightarrow x+1\le 0\Rightarrow x\le -1\land -1<0` -/
theorem proof35 : obligation35 := by
  leanify_step

/-- Claim 36, proof step (proof at line 148; premises: claim 35):
`\forall x\in \mathbb{R},\ 0<x\Rightarrow x+1\le 0\Rightarrow \bot` -/
theorem proof36 : obligation36 := by
  leanify_step

/-- Claim 37, proof step (proof at line 149; premises: claim 35, claim 36):
`\forall x\in \mathbb{R},\ 0<x\Rightarrow 0<x+1` -/
theorem proof37 : obligation37 := by
  leanify_step

/-- Claim 38, statement (lemma at line 159; premises: claim 39, claim 40, claim 41, claim 42):
`\forall x\in \mathbb{R},\ x\in \mathbb{Z}\land 0<x\Rightarrow x\le {x}^{2}` -/
theorem proof38 : obligation38 := by
  leanify_step

/-- The hypotheses of claim 38 can hold together:
`\exists x\in \mathbb{R},\ x\in \mathbb{Z}\land 0<x` -/
theorem satisfied38 : satisfiable38 := by
  leanify_values 1

/-- Claim 39, proof step (proof at line 165; no premises):
`\forall x\in \mathbb{R},\ x\in \mathbb{Z}\land 0<x\Rightarrow x=1\Rightarrow {x}^{2}=1` -/
theorem proof39 : obligation39 := by
  leanify_step

/-- The hypotheses of claim 39 can hold together:
`\exists x\in \mathbb{R},\ (x\in \mathbb{Z}\land 0<x)\land x=1` -/
theorem satisfied39 : satisfiable39 := by
  leanify_values 1

/-- Claim 40, proof step (proof at line 167; premises: claim 39):
`\forall x\in \mathbb{R},\ x\in \mathbb{Z}\land 0<x\Rightarrow x\le {x}^{2}\Rightarrow {(x+1)}^{2}={x}^{2}+2\,x+1\land x+2\,x+1\le {x}^{2}+2\,x+1` -/
theorem proof40 : obligation40 := by
  leanify_step

/-- The hypotheses of claim 40 can hold together:
`\exists x\in \mathbb{R},\ (x\in \mathbb{Z}\land 0<x)\land x\le {x}^{2}` -/
theorem satisfied40 : satisfiable40 := by
  leanify_values 1

/-- Claim 41, proof step (proof at line 168; premises: claim 39, claim 40):
`\forall x\in \mathbb{R},\ x\in \mathbb{Z}\land 0<x\Rightarrow x\le {x}^{2}\Rightarrow x+1\le {(x+1)}^{2}` -/
theorem proof41 : obligation41 := by
  leanify_step

/-- Claim 42, proof step (proof at line 169; premises: claim 39, claim 40, claim 41):
`\forall x\in \mathbb{R},\ x\in \mathbb{Z}\land 0<x\Rightarrow x\le {x}^{2}\Rightarrow x+1\in \mathbb{Z}\land 0<x+1\Rightarrow x+1\le {(x+1)}^{2}` -/
theorem proof42 : obligation42 := by
  leanify_step

/-- The hypotheses of claim 42 can hold together:
`\exists x\in \mathbb{R},\ (x\in \mathbb{Z}\land 0<x)\land x\le {x}^{2}\land x+1\in \mathbb{Z}\land 0<x+1` -/
theorem satisfied42 : satisfiable42 := by
  leanify_values 1

/-- Claim 43, statement (lemma at line 176; premises: claim 44, claim 45, claim 46, claim 47, claim 48):
`\forall x\in \mathbb{R},\ x\in \mathbb{Z}\land 0<x\Rightarrow 2\,x\le {x}^{2}+1` -/
theorem proof43 : obligation43 := by
  leanify_step

/-- Claim 44, proof step (proof at line 182; no premises):
`\forall x\in \mathbb{R},\ x\in \mathbb{Z}\land 0<x\Rightarrow x=1\Rightarrow 2\,x=2` -/
theorem proof44 : obligation44 := by
  leanify_step

/-- Claim 45, proof step (proof at line 182; premises: claim 44):
`\forall x\in \mathbb{R},\ x\in \mathbb{Z}\land 0<x\Rightarrow x=1\Rightarrow {x}^{2}+1=2` -/
theorem proof45 : obligation45 := by
  leanify_step

/-- Claim 46, proof step (proof at line 184; premises: claim 44, claim 45):
`\forall x\in \mathbb{R},\ x\in \mathbb{Z}\land 0<x\Rightarrow 2\le x\Rightarrow (x-1\in \mathbb{Z}\land 0<x-1\Rightarrow 2\,(x-1)\le {(x-1)}^{2}+1)\Rightarrow 2\,(x-1)\le {(x-1)}^{2}+1` -/
theorem proof46 : obligation46 := by
  leanify_step

/-- The hypotheses of claim 46 can hold together:
`\exists x\in \mathbb{R},\ (x\in \mathbb{Z}\land 0<x)\land 2\le x\land (x-1\in \mathbb{Z}\land 0<x-1\Rightarrow 2\,(x-1)\le {(x-1)}^{2}+1)` -/
theorem satisfied46 : satisfiable46 := by
  leanify_values 2

/-- Claim 47, proof step (proof at line 185; premises: claim 44, claim 45, claim 46):
`\forall x\in \mathbb{R},\ x\in \mathbb{Z}\land 0<x\Rightarrow 2\le x\Rightarrow (x-1\in \mathbb{Z}\land 0<x-1\Rightarrow 2\,(x-1)\le {(x-1)}^{2}+1)\Rightarrow 2\,x\le {(x-1)}^{2}+3` -/
theorem proof47 : obligation47 := by
  leanify_step

/-- Claim 48, proof step (proof at line 185; premises: claim 44, claim 45, claim 46, claim 47):
`\forall x\in \mathbb{R},\ x\in \mathbb{Z}\land 0<x\Rightarrow 2\le x\Rightarrow (x-1\in \mathbb{Z}\land 0<x-1\Rightarrow 2\,(x-1)\le {(x-1)}^{2}+1)\Rightarrow {(x-1)}^{2}+3={x}^{2}-2\,x+4\land {x}^{2}-2\,x+4\le {x}^{2}+1` -/
theorem proof48 : obligation48 := by
  leanify_step

/-- Claim 49, statement (lemma at line 193; premises: claim 50):
`\forall x\in \mathbb{R},\ x\in \mathbb{Z}\land 0<x\Rightarrow 1\le x` -/
theorem proof49 : obligation49 := by
  leanify_step

/-- Claim 50, proof step (proof at line 199; no premises):
`\forall x\in \mathbb{R},\ x\in \mathbb{Z}\land 0<x\Rightarrow (\forall y\in \mathbb{R},\ y<x\Rightarrow y\in \mathbb{Z}\land 0<y\Rightarrow 1\le y)\Rightarrow 1\le x` -/
theorem proof50 : obligation50 := by
  leanify_step

/-- The hypotheses of claim 50 can hold together:
`\exists x\in \mathbb{R},\ (x\in \mathbb{Z}\land 0<x)\land (\forall y\in \mathbb{R},\ y<x\Rightarrow y\in \mathbb{Z}\land 0<y\Rightarrow 1\le y)` -/
theorem satisfied50 : satisfiable50 := by
  unfold satisfiable50
  refine ⟨1, ⟨Leanify.Prelude.isInt_one, by norm_num⟩, fun y _ hy => ?_⟩
  have := Leanify.Prelude.isInt.add_one_le_of_lt Leanify.Prelude.isInt_zero hy.1 hy.2
  linarith

/-- Claim 51, statement (lemma at line 209; no premises):
`\forall x\in \mathbb{R},\ x\in \mathbb{Z}\land 0<x\Rightarrow 2\le x+1` -/
theorem proof51 : obligation51 := by
  leanify_step

end Arguments.Proofs
