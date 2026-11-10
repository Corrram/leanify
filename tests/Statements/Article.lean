import Statements.Compiled
import Leanify.Readable
import Leanify.Library.ComplexModel

/-! # The definitions and claims of `article.tex` as Lean

The article draws on the fields `numbers` (no constants) and `complex`, whose
constants `Leanify.Complex.model` interprets in Mathlib (`ℂ`). For every definition, a
Lean definition with the symbol's name, and for every claim `K`: `claimK` (what the
sentence says), `meaningfulK` (every term in it is defined) and `obligationK` (its
premises imply both). Each is tied to the compiled document by a kernel-checked `rfl`
theorem. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#leanify_semantics Statements "article.tex"
