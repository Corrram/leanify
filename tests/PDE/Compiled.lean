import Leanify.Meta

/-! # `article.tex`, compiled

A test of fields on `\mathbb R^3\times[0,1)` (vector and scalar fields, function
spaces, compact sets, supports, norms, energies) and of the Navier–Stokes equations,
in the words of Theorem 1.1 of the Navier–Stokes blowup paper. After editing the
article, run

    lake exe leanify prepare tests/PDE/article.tex --lean tests/PDE/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#leanify_article PDE "article.tex" "fnv1a64:1a5f8489ea5370d5"
