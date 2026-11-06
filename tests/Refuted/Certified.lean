import Refuted.Proofs
import Leanify.Certify

/-! # The certified article

The kernel checks `Refuted.certificate`: every verified claim of `article.tex` holds and
every definition is well defined. `Refuted.verifiedK : meaningfulK ∧ claimK` is then
claim `K`, as stated in the text. The command also writes
`article.leanify.json` (for the reader and the diagnostics) and `article.leanify.tex` (for the
margin marks of `leanify.sty`). -/

#leanify_certify Refuted "article.tex" using Refuted.Proofs
