import Context.Proofs
import Leanify.Certify

/-! # The certified article

The kernel checks `Context.certificate`: every verified claim of `article.tex` holds and
every definition is well defined. `Context.verifiedK : meaningfulK ∧ claimK` is then
claim `K`, as stated in the text. The command also writes
`article.leanify.json` (for the reader and the diagnostics) and `article.leanify.tex` (for the
margin marks of `leanify.sty`). -/

#leanify_certify Context "article.tex" using Context.Proofs
