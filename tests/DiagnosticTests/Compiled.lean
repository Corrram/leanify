import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `diagnostictests`: predictive values, accuracy, likelihood ratios, the Youden index, post-test odds, odds ratios, relative risks and the number needed to treat. After editing the article, run

    lake exe leanify prepare tests/DiagnosticTests/article.tex --lean tests/DiagnosticTests/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `diagnostictests`. -/
def DiagnosticTests.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["diagnostictests"]

#leanify_article DiagnosticTests "article.tex" "fnv1a64:a705c211e43f86e9" with DiagnosticTests.vocabulary
