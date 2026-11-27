import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Algebra.Polynomial.Eval.Defs
import Leanify.Denote

/-! # The meaning of the field `graphcounts`

The counts of the standard graphs of Mathlib on `Fin n` (`⊤`, `completeBipartiteGraph`,
`cycleGraph`, `turanGraph`, and the hypercube of words of bits): their edges, their spanning
trees (the subgraphs on all of their vertices that are trees, `SimpleGraph.IsTree`) and their
chromatic polynomials (the polynomial whose value at every natural number `j` is the number of
colourings with `j` colours, `SimpleGraph.Coloring`). Each takes the integer part of its
arguments (Leanify asks that they be nonnegative integers), apart from the point at which a
chromatic polynomial is evaluated. -/

namespace Leanify.GraphCounts

noncomputable section
open SimpleGraph Classical

/-- The hypercube of dimension `n`: the words of `n` bits, two of them adjacent when they differ
in exactly one bit. -/
def hypercube (n : ℕ) : SimpleGraph (Fin n → Bool) where
  Adj x y := (Finset.univ.filter fun i => x i ≠ y i).card = 1
  symm := ⟨fun x y h => by simpa only [ne_comm] using h⟩
  loopless := ⟨fun x h => by simp at h⟩

/-- The number of edges of a graph. -/
def numEdges {V : Type} (G : SimpleGraph V) : ℝ := (Nat.card G.edgeSet : ℝ)

/-- The number of spanning trees of a graph: its subgraphs with all of its vertices that are
trees. -/
def numSpanningTrees {V : Type} (G : SimpleGraph V) : ℝ :=
  (Nat.card {H : SimpleGraph V // H ≤ G ∧ H.IsTree} : ℝ)

/-- The chromatic polynomial of a graph at `k`: the value at `k` of the polynomial whose value at
every natural number `j` is the number of colourings of the graph with `j` colours (`0` if there
is none). -/
def chromaticPolynomialAt {V : Type} (G : SimpleGraph V) (k : ℝ) : ℝ :=
  if h : ∃ P : Polynomial ℝ, ∀ j : ℕ, P.eval (j : ℝ) = (Nat.card (G.Coloring (Fin j)) : ℝ) then
    (Classical.choose h).eval k
  else 0

/-- The number of edges of the complete graph on `n` vertices. -/
def edgesComplete (n : ℝ) : ℝ := numEdges (⊤ : SimpleGraph (Fin ⌊n⌋₊))

/-- The number of edges of the complete bipartite graph with parts of sizes `m` and `n`. -/
def edgesCompleteBipartite (m n : ℝ) : ℝ := numEdges (completeBipartiteGraph (Fin ⌊m⌋₊) (Fin ⌊n⌋₊))

/-- The number of edges of the hypercube of dimension `n`. -/
def edgesHypercube (n : ℝ) : ℝ := numEdges (hypercube ⌊n⌋₊)

/-- The number of labelled graphs on `n` vertices: the simple graphs on `Fin n`. -/
def labelledGraphs (n : ℝ) : ℝ := (Nat.card (SimpleGraph (Fin ⌊n⌋₊)) : ℝ)

/-- The number of spanning trees of the complete graph on `n` vertices. -/
def treesComplete (n : ℝ) : ℝ := numSpanningTrees (⊤ : SimpleGraph (Fin ⌊n⌋₊))

/-- The number of spanning trees of the complete bipartite graph with parts of sizes `m` and `n`. -/
def treesCompleteBipartite (m n : ℝ) : ℝ := numSpanningTrees (completeBipartiteGraph (Fin ⌊m⌋₊) (Fin ⌊n⌋₊))

/-- The number of spanning trees of the cycle on `n` vertices. -/
def treesCycle (n : ℝ) : ℝ := numSpanningTrees (cycleGraph ⌊n⌋₊)

/-- The chromatic polynomial of the complete graph on `n` vertices at `k`. -/
def chromaticComplete (n k : ℝ) : ℝ := chromaticPolynomialAt (⊤ : SimpleGraph (Fin ⌊n⌋₊)) k

/-- The chromatic polynomial of a tree on `n` vertices at `k`: the value at `k` of the chromatic
polynomial that every tree on `n` vertices has (`0` if they do not all have one). -/
def chromaticTree (n k : ℝ) : ℝ :=
  if h : ∃ c : ℝ, ∀ T : SimpleGraph (Fin ⌊n⌋₊), T.IsTree → chromaticPolynomialAt T k = c then
    Classical.choose h
  else 0

/-- The chromatic polynomial of the cycle on `n` vertices at `k`. -/
def chromaticCycle (n k : ℝ) : ℝ := chromaticPolynomialAt (cycleGraph ⌊n⌋₊) k

/-- The number of edges of the Turán graph on `n` vertices with `r` parts. -/
def turanEdges (n r : ℝ) : ℝ := numEdges (turanGraph ⌊n⌋₊ ⌊r⌋₊)

end

end Leanify.GraphCounts
