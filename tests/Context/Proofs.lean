import Context.Article

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

namespace Context.Proofs
open Context

/-- Claim 0, statement (lemma at line 18; premises: claim 1). -/
theorem proof0 : obligation0 := by
  leanify_step

/-- Claim 1, proof step (proof at line 21; no premises). -/
theorem proof1 : obligation1 := by
  leanify_step

/-- Claim 2, statement (lemma at line 30; no premises). -/
theorem proof2 : obligation2 := by
  leanify_step

/-- Claim 3, proof step (proof at line 33; no premises). -/
theorem proof3 : obligation3 := by
  leanify_step

/-- Claim 4, proof step (proof at line 33; premises: claim 3). -/
theorem proof4 : obligation4 := by
  leanify_step

/-- Claim 5, statement (lemma at line 42; no premises). -/
theorem proof5 : obligation5 := by
  leanify_step

/-- Claim 6, proof step (proof at line 45; no premises). -/
theorem proof6 : obligation6 := by
  leanify_step

/-- Claim 7, proof step (proof at line 45; premises: claim 6). -/
theorem proof7 : obligation7 := by
  leanify_step

/-- Claim 8, statement (lemma at line 53; premises: claim 9, claim 10). -/
theorem proof8 : obligation8 := by
  leanify_step

/-- Claim 9, proof step (proof at line 56; no premises). -/
theorem proof9 : obligation9 := by
  leanify_step

/-- Claim 10, proof step (proof at line 56; no premises). -/
theorem proof10 : obligation10 := by
  leanify_step

/-- The hypothesis of the first case can hold: `x = 1`. -/
theorem satisfied3 : satisfiable3 := by
  leanify_values 1

/-- The hypothesis of the second case can hold: `x = -1`. -/
theorem satisfied10 : satisfiable10 := by
  leanify_values (-1)

end Context.Proofs
