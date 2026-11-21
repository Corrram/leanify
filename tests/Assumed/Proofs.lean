import Assumed.Article

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

namespace Assumed.Proofs
open Assumed

/- Definition 0 (`f`) has no proof `defined0 : wellDefined0` here: the certificate assumes
that it is well defined (the axiom `Assumed.Assumed.wellDefined0`), and the reports say so. -/

/-- Claim 0, statement (lemma at line 14; no premises):
`\forall x\in \mathbb{R},\ 0<x\Rightarrow f(x)=x+\frac{1}{x}` -/
theorem proof0 : obligation0 := by
  intro_premises
  refine ⟨by unfold meaningful0; definedness [], fun x hx => ?_⟩
  simp only [f]

/-- The hypotheses of claim 0 can hold together:
`\exists x\in \mathbb{R},\ 0<x` -/
theorem satisfied0 : satisfiable0 := by
  leanify_values 1

end Assumed.Proofs
