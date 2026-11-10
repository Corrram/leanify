import Undefined.Proofs
import Leanify.Certify

/-! # The certified article

The kernel checks `Undefined.certificate`: every verified claim of `article.tex` holds and
every definition is well defined. `Undefined.verifiedK : meaningfulK ∧ claimK` is then
claim `K`, as stated in the text. The command also writes
`article.leanify.json` (for the reader and the diagnostics) and `article.leanify.tex` (for the
margin marks of `leanify.sty`). -/

#leanify_certify Undefined "article.tex" using Undefined.Proofs
