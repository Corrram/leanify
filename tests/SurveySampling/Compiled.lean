import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `surveysampling`: sample sizes, finite population corrections, margins of error, design effects and sampling fractions. After editing the article, run

    lake exe leanify prepare tests/SurveySampling/article.tex --lean tests/SurveySampling/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `surveysampling`. -/
def SurveySampling.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["surveysampling"]

#leanify_article SurveySampling "article.tex" "fnv1a64:7bcf4ab6d4499791" with SurveySampling.vocabulary
