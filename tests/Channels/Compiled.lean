import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `channels`: binary entropy in bits, capacities of the binary symmetric, erasure, Z and Gaussian channels, and rate-distortion functions. After editing the article, run

    lake exe leanify prepare tests/Channels/article.tex --lean tests/Channels/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `channels`. -/
def Channels.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["channels"]

#leanify_article Channels "article.tex" "fnv1a64:279e8f58aea5960c" with Channels.vocabulary
