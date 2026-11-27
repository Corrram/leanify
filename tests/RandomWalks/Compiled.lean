import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `randomwalks`: gambler's ruin probabilities and durations, the distribution of the simple random walk, hitting probabilities, exit times and transition densities of Brownian motion. After editing the article, run

    lake exe leanify prepare tests/RandomWalks/article.tex --lean tests/RandomWalks/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `randomwalks`. -/
def RandomWalks.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["randomwalks"]

#leanify_article RandomWalks "article.tex" "fnv1a64:99a5207e78c96666" with RandomWalks.vocabulary
