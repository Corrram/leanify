import Leanify.Meta

/-! # `article.tex`, compiled

A test of claims that follow a sentence which Leanify does not read: a hypothesis of a
statement that is not read, a case and a supposition that an unread sentence of a proof
ends. Each claim is read with the hypotheses of the sentences that are read, so it may
not be the claim of the text. The claims are verified as read, and the reports name them
(`after` in `article.leanify.json`) and count them apart from the verified claims. After
editing the article, run

    lake exe leanify prepare tests/Context/article.tex --lean tests/Context/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#leanify_article Context "article.tex" "fnv1a64:39c2facb4ce5bc84"
