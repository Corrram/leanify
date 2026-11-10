import Undefined.Article

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

namespace Undefined.Proofs
open Undefined

/-- Definition 0: `chi` (`\chi`) is well defined. -/
theorem defined0 : wellDefined0 := by
  unfold wellDefined0
  definedness []

/-- Definition 1: `omega` (`\omega`) is well defined. -/
theorem defined1 : wellDefined1 := by
  unfold wellDefined1
  definedness []

/-- Definition 2: `Delta` (`\Delta`) is well defined. -/
theorem defined2 : wellDefined2 := by
  unfold wellDefined2
  definedness []

/-- Definition 3: `d` is well defined. -/
theorem defined3 : wellDefined3 := by
  unfold wellDefined3
  definedness []

/-- Definition 4: `L` is well defined. -/
theorem defined4 : wellDefined4 := by
  unfold wellDefined4
  definedness []

/- Claim 0, statement (lemma at line 38), is quoted from the literature: the article
assumes it (`Quoted.claim0`), and the certificate names it among its axioms. A theorem
`proof0 : obligation0` here would prove it instead.
`\forall x\in \mathrm{Graph},\ \operatorname{finite}(x)\Rightarrow \omega(x)\le \chi(x)` -/

/- Claim 1, statement (lemma at line 42), is quoted from the literature: the article
assumes it (`Quoted.claim1`), and the certificate names it among its axioms. A theorem
`proof1 : obligation1` here would prove it instead.
`\forall x\in \mathrm{Graph},\ \operatorname{finite}(x)\Rightarrow \chi(x)\le \Delta(x)+1` -/

/-- Claim 2, statement (theorem at line 50; premises: claim 3, claim 4, claim 5, claim 0, claim 1):
`\forall x\in \mathrm{Graph},\ \operatorname{finite}(x)\land \operatorname{connected}(x)\Rightarrow \omega(x)\le \Delta(x)+1` -/
theorem proof2 : obligation2 := by
  leanify_step

/- The hypotheses of claim 2 (a finite connected graph) are not shown to hold together:
nothing is known of a graph, so no graph can be given. The report says so, and the
theorem is marked as argued. -/

/-- Claim 3, proof step (proof at line 53; premises: claim 0):
`\forall x\in \mathrm{Graph},\ \operatorname{finite}(x)\land \operatorname{connected}(x)\Rightarrow \omega(x)\le \chi(x)` -/
theorem proof3 : obligation3 := by
  leanify_step

/-- Claim 4, proof step (proof at line 53; premises: claim 0, claim 1, claim 3):
`\forall x\in \mathrm{Graph},\ \operatorname{finite}(x)\land \operatorname{connected}(x)\Rightarrow \chi(x)\le \Delta(x)+1` -/
theorem proof4 : obligation4 := by
  leanify_step

/-- Claim 5, proof step (proof at line 54; premises: claim 0, claim 1, claim 3, claim 4):
`\forall x\in \mathrm{Graph},\ \operatorname{finite}(x)\land \operatorname{connected}(x)\Rightarrow \omega(x)\le \Delta(x)+1` -/
theorem proof5 : obligation5 := by
  leanify_step

/-- Claim 6, statement (lemma at line 60; no premises):
`\forall x\in \mathrm{Graph},\ \omega(L(x))-\omega(L(x))+\chi(L(x))\le \chi(L(x))` -/
theorem proof6 : obligation6 := by
  leanify_step

/-- Claim 7, statement (lemma at line 64; no premises):
`\forall x\in \mathrm{Graph},\ \forall y\in \mathrm{Graph},\ d(x,y)<d(x,y)+1` -/
theorem proof7 : obligation7 := by
  leanify_step

/-- Claim 8, statement (lemma at line 73; no premises):
`1\le 2` -/
theorem proof8 : obligation8 := by
  leanify_step

/-- Claim 9, statement (lemma at line 84; no premises):
`\exists x\in \mathrm{Graph},\ \chi(x)\le \chi(x)`

A graph must be given, and nothing is known of a graph. What a proof can use is the
element that every kind of object is assumed to have. -/
theorem proof9 : obligation9 := by
  refine ⟨trivial, ?_⟩
  unfold claim9
  exact ⟨Notion.Graph.2, le_refl _⟩

end Undefined.Proofs
