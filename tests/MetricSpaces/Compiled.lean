import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `metricspaces`: metrics on `ℝ`, the topology a metric induces, balls, Cauchy sequences, contractions and isometries. After editing the article, run

    lake exe leanify prepare tests/MetricSpaces/article.tex --lean tests/MetricSpaces/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the fields `realfunctions`, `realsets` and `metricspaces`. -/
def MetricSpaces.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["realfunctions", "realsets", "metricspaces"]

#leanify_article MetricSpaces "article.tex" "fnv1a64:5a689c7815e031c8" with MetricSpaces.vocabulary
