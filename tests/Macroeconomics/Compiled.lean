import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `macroeconomics`: the Solow model, Harrod-Domar growth, the Fisher equation, growth rates, multipliers and the Taylor rule. After editing the article, run

    lake exe leanify prepare tests/Macroeconomics/article.tex --lean tests/Macroeconomics/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `macroeconomics`. -/
def Macroeconomics.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["macroeconomics"]

#leanify_article Macroeconomics "article.tex" "fnv1a64:5c38e6e5da59b60e" with Macroeconomics.vocabulary
