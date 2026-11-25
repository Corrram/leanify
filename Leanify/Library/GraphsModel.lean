import Leanify.Denote
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Trails

/-! # The meaning of the field `graphs`

A graph is a finite simple graph on `Fin n`, for some `n`; its vertex `i` is the number
`i + 1`, so that the vertices of a graph on `n` vertices are `1, …, n`. -/

namespace Leanify.Graphs
open SimpleGraph

/-- A finite simple graph with the vertices `1, …, n`. -/
def Graph : Type := Σ n : ℕ, SimpleGraph (Fin n)

/-- The graph without vertices. -/
def Graph.empty : Graph := ⟨0, ⊥⟩

noncomputable section
open Classical

/-- `v` is a vertex of `G`: one of `1, …, n`. -/
def IsVertex (G : Graph) (v : ℝ) : Prop := ∃ i : Fin G.1, (i : ℝ) + 1 = v

def numVertices (G : Graph) : ℝ := G.1
def numEdges (G : Graph) : ℝ := Nat.card G.2.edgeSet

/-- The vertices `u` and `v` are adjacent in `G`. -/
def Adjacent (u v : ℝ) (G : Graph) : Prop := ∃ i j : Fin G.1, (i : ℝ) + 1 = u ∧ (j : ℝ) + 1 = v ∧ G.2.Adj i j

/-- The number of neighbours of `v` (`0` if `v` is not a vertex). -/
def degree (v : ℝ) (G : Graph) : ℝ := Nat.card {j : Fin G.1 // Adjacent v ((j : ℝ) + 1) G}

/-- The distance between the vertices `u` and `v` (`0` if they are not connected, or not
vertices). -/
def dist (u v : ℝ) (G : Graph) : ℝ :=
  if h : ∃ i j : Fin G.1, (i : ℝ) + 1 = u ∧ (j : ℝ) + 1 = v then G.2.dist h.choose h.choose_spec.choose else 0

/-- The vertices `u` and `v` are joined by a walk. -/
def Reachable (u v : ℝ) (G : Graph) : Prop :=
  ∃ i j : Fin G.1, (i : ℝ) + 1 = u ∧ (j : ℝ) + 1 = v ∧ G.2.Reachable i j

def minDegree (G : Graph) : ℝ := G.2.minDegree
def maxDegree (G : Graph) : ℝ := G.2.maxDegree
def chromaticNumber (G : Graph) : ℝ := G.2.chromaticNumber.toNat
def cliqueNumber (G : Graph) : ℝ := G.2.cliqueNum
def independenceNumber (G : Graph) : ℝ := G.2.indepNum
def numComponents (G : Graph) : ℝ := Nat.card G.2.ConnectedComponent
def diameter (G : Graph) : ℝ := G.2.diam
def girth (G : Graph) : ℝ := G.2.girth

def Connected (G : Graph) : Prop := G.2.Connected
def Acyclic (G : Graph) : Prop := G.2.IsAcyclic
def IsTree (G : Graph) : Prop := G.2.IsTree
def Bipartite (G : Graph) : Prop := G.2.Colorable 2
def Regular (G : Graph) : Prop := ∃ d, G.2.IsRegularOfDegree d
def Complete (G : Graph) : Prop := G.2 = ⊤
def Hamiltonian (G : Graph) : Prop := G.2.IsHamiltonian

def completeGraph (n : ℝ) : Graph := ⟨⌊n⌋₊, ⊤⟩
def cycleGraph (n : ℝ) : Graph := ⟨⌊n⌋₊, SimpleGraph.cycleGraph ⌊n⌋₊⟩
def pathGraph (n : ℝ) : Graph := ⟨⌊n⌋₊, SimpleGraph.pathGraph ⌊n⌋₊⟩
def emptyGraph (n : ℝ) : Graph := ⟨⌊n⌋₊, ⊥⟩

/-- `K_{m,n}`: the parts `{1, …, m}` and `{m+1, …, m+n}`. -/
def completeBipartite (m n : ℝ) : Graph :=
  ⟨⌊m⌋₊ + ⌊n⌋₊, SimpleGraph.fromRel fun i j => (i : ℕ) < ⌊m⌋₊ ∧ ⌊m⌋₊ ≤ (j : ℕ)⟩

def complement (G : Graph) : Graph := ⟨G.1, G.2ᶜ⟩

/-- `G` is `k`-colorable (Mathlib `SimpleGraph.Colorable`). -/
def Colorable (k : ℝ) (G : Graph) : Prop := ∃ m : ℕ, (m : ℝ) = k ∧ G.2.Colorable m
/-- A closed walk through every edge exactly once (Mathlib `SimpleGraph.Walk.IsEulerian`). -/
def Eulerian (G : Graph) : Prop := ∃ v : Fin G.1, ∃ w : G.2.Walk v v, w.IsEulerian
/-- A walk through every edge exactly once. -/
def EulerTrail (G : Graph) : Prop := ∃ u v : Fin G.1, ∃ w : G.2.Walk u v, w.IsEulerian
/-- A path through every vertex (Mathlib `SimpleGraph.Walk.IsHamiltonian`). -/
def HamiltonianPath (G : Graph) : Prop := ∃ u v : Fin G.1, ∃ w : G.2.Walk u v, w.IsHamiltonian
/-- A cycle of odd length. -/
def OddCycle (G : Graph) : Prop := ∃ v : Fin G.1, ∃ w : G.2.Walk v v, w.IsCycle ∧ Odd w.length
/-- The number of vertices of odd degree. -/
def numOddDegree (G : Graph) : ℝ := Nat.card {i : Fin G.1 // ∃ k : ℕ, degree ((i : ℝ) + 1) G = 2 * k + 1}
/-- The number of vertices of degree `k`. -/
def numOfDegree (k : ℝ) (G : Graph) : ℝ := Nat.card {i : Fin G.1 // degree ((i : ℝ) + 1) G = k}

end

end Leanify.Graphs
