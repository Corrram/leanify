import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `markovchains`: doubly stochastic, irreducible and primitive matrices, absorbing states, stationary and reversible distributions, transition probabilities. After editing the article, run

    lake exe leanify prepare tests/MarkovChains/article.tex --lean tests/MarkovChains/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `markovchains`. -/
def MarkovChains.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["markovchains"]

#leanify_article MarkovChains "article.tex" "fnv1a64:ef82621e89d9aefb" with MarkovChains.vocabulary
