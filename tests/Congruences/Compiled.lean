import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `congruences` of the vocabulary: adjectives with numbers after `is` and after a noun (`$a^p$ is congruent to $a$ modulo $p$`, `an integer $a$ coprime to $n$`, `$2$ is a quadratic residue modulo $7$`), the Legendre symbol and primitive roots. After editing the article, run

    lake exe leanify prepare tests/Congruences/article.tex --lean tests/Congruences/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the fields `numbers` and `arithmetic` and `congruences`. -/
def Congruences.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["numbers", "arithmetic", "congruences"]

#leanify_article Congruences "article.tex" "fnv1a64:43ed3c0df1d93512" with Congruences.vocabulary
