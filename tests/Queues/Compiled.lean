import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `queues`: traffic intensity, the M/M/1 queue (mean numbers, sojourn and waiting times, stationary probabilities), the Erlang B and C formulas and the Pollaczek-Khinchine formula. After editing the article, run

    lake exe leanify prepare tests/Queues/article.tex --lean tests/Queues/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `queues`. -/
def Queues.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["queues"]

#leanify_article Queues "article.tex" "fnv1a64:ad4521a297ca6f0b" with Queues.vocabulary
