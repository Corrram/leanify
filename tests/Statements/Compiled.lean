import Leanify.Meta
import Leanify.Library.Fields

/-! # `article.tex`, compiled

A test of statement forms found in OpenAI's collection of AI-written manuscripts
(github.com/openai/math): nouns whose first word is also an adjective (`prime
number`, `odd prime`), `there is an integer $Q$ such that`, binders with a noun
and a bound (`for every integer $n\ge1$`), `real` and `fixed`, absolute
constants, conditions written after a display formula (`\qquad\text{for every
integer }k\ge1`, `\qquad(p\in\mathbb Z,\ q\ge Q)`), and the LaTeX that made
whole articles unreadable (`\ref*`, `\cite[…]` before a line break, `\let` with
`\renewcommand`). After editing the article, run

    lake exe leanify prepare tests/Statements/article.tex --lean tests/Statements/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The vocabulary of the article: the core and the fields `numbers` and `complex`. -/
def Statements.vocabulary : Leanify.Vocab := Leanify.Fields.select ["numbers", "complex"]

#leanify_article Statements "article.tex" "fnv1a64:d65b7f8645ce2b80" with Statements.vocabulary
