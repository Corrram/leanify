import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of the field `timeseries`: sample autocovariance and autocorrelation at a lag, moving averages, cumulative sums, differences, exponential smoothing, AR(1) sequences and random walks. After editing the article, run

    lake exe leanify prepare tests/TimeSeries/article.tex --lean tests/TimeSeries/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the field `timeseries`. -/
def TimeSeries.vocabulary : Leanify.Vocab :=
  Leanify.Fields.select ["timeseries"]

#leanify_article TimeSeries "article.tex" "fnv1a64:14b2a46d2d7202d9" with TimeSeries.vocabulary
