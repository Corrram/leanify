import Leanify.Library.Core

/-! # Vocabulary: counting in graph theory

The counts of the standard graphs and extremal numbers, as numbers of their parameters
(`We write $\tau(n)$ for the number of spanning trees of the complete graph on $n$ vertices.`).
Graphs as objects are in the field `graphs`.

* notions: the numbers of edges of the complete graph, of the complete bipartite graph and of
  the hypercube of dimension `n`; the number of labelled graphs on `n` vertices; the numbers of
  spanning trees of the complete graph, of the complete bipartite graph and of the cycle; the
  chromatic polynomials of the complete graph, of a tree and of the cycle at a number; the
  number of edges of the Turán graph `T(n,r)` (`r` parts), and the bound `\binom{s+t-2}{s-1}` on
  the Ramsey number `R(s,t)` (Erdős–Szekeres).

The counts are constants, interpreted by the declarations of
`Leanify/Library/GraphCountsModel.lean`: the graphs of Mathlib on `Fin n` (`⊤`,
`completeBipartiteGraph`, `cycleGraph`, `turanGraph`, the hypercube of words of bits), the
cardinality of their sets of edges, of their spanning trees (`SimpleGraph.IsTree`), and
their chromatic polynomials (whose value at every natural number `j` is the number of
colourings with `j` colours, `SimpleGraph.Coloring`). Their closed forms (`n^{n-2}`,
Cayley; `k(k-1)^{n-1}`) are theorems, not definitions. The bound on the Ramsey number is the
formula it names. -/

namespace Leanify.GraphCounts
open Build Core

def natP (n : B) : B := and (isInt n) (le (num 0) n)
def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def binom (n k : B) : B := app2 (prim .binom) n k
def two (name : Phrase) (d1 d2 : B → B) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real d1, dom2 .real fun _ y => d2 y], doc,
    value := close <| lamT .real d1 fun x => lamT .real d2 fun y => body x y }
def ge3 (n : B) : B := and (isInt n) (le (num 3) n)

/-! The indices of the constants (apart from the names of their meanings). -/
namespace Const
def edgesComplete : Nat := 0
def edgesCompleteBipartite : Nat := 1
def edgesHypercube : Nat := 2
def labelledGraphs : Nat := 3
def treesComplete : Nat := 4
def treesCompleteBipartite : Nat := 5
def treesCycle : Nat := 6
def chromaticComplete : Nat := 7
def chromaticTree : Nat := 8
def chromaticCycle : Nat := 9
def turanEdges : Nat := 10
end Const

/-- A count of one parameter, the constant `c`. -/
def oneC (name : Phrase) (d : B → B) (c : Nat) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real, doms := [dom1 .real d], doc, value := .const c }
/-- A count of two parameters, the constant `c`. -/
def twoC (name : Phrase) (d1 d2 : B → B) (c : Nat) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real d1, dom2 .real fun _ y => d2 y], doc, value := .const c }

def vocab : Vocab where
  consts := [.real ⟶ .real, .real ⟶ .real ⟶ .real, .real ⟶ .real, .real ⟶ .real, .real ⟶ .real,
    .real ⟶ .real ⟶ .real, .real ⟶ .real, .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real,
    .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real]
  constNames := [w!"\\lvert E(K_{#})\\rvert", w!"\\lvert E(K_{#1,#2})\\rvert", w!"\\lvert E(Q_{#})\\rvert",
    w!"\\operatorname{graphs}", w!"\\tau(K_{#})", w!"\\tau(K_{#1,#2})", w!"\\tau(C_{#})",
    w!"P_{K_{#1}}(#2)", w!"P_{T_{#1}}(#2)", w!"P_{C_{#1}}(#2)", w!"\\lvert E(T(#1,#2))\\rvert"]
  constLean := [w!"Leanify.GraphCounts.edgesComplete", w!"Leanify.GraphCounts.edgesCompleteBipartite",
    w!"Leanify.GraphCounts.edgesHypercube", w!"Leanify.GraphCounts.labelledGraphs",
    w!"Leanify.GraphCounts.treesComplete", w!"Leanify.GraphCounts.treesCompleteBipartite",
    w!"Leanify.GraphCounts.treesCycle", w!"Leanify.GraphCounts.chromaticComplete",
    w!"Leanify.GraphCounts.chromaticTree", w!"Leanify.GraphCounts.chromaticCycle",
    w!"Leanify.GraphCounts.turanEdges"]
  modules := [w!"Leanify.Library.GraphCountsModel"]
  notions := [
    oneC phrase!"number of edges of the complete graph on $v$ vertices" natP Const.edgesComplete
      "the edges of `⊤ : SimpleGraph (Fin n)` (`n(n-1)/2`)",
    twoC phrase!"number of edges of the complete bipartite graph with parts of sizes $v$ and $v$" natP natP
      Const.edgesCompleteBipartite "the edges of Mathlib `completeBipartiteGraph (Fin m) (Fin n)` (`mn`)",
    oneC phrase!"number of edges of the hypercube of dimension $v$" natP Const.edgesHypercube
      "the edges of the graph of the words of `n` bits, adjacent when they differ in one bit (`n2^{n-1}`)",
    oneC phrase!"number of labelled graphs on $v$ vertices" natP Const.labelledGraphs
      "the simple graphs on `Fin n` (Mathlib `SimpleGraph`; `2^{n(n-1)/2}`)",
    oneC phrase!"number of spanning trees of the complete graph on $v$ vertices" posInt Const.treesComplete
      "the subgraphs of `⊤ : SimpleGraph (Fin n)` with all its vertices that are trees (Mathlib `IsTree`; `n^{n-2}`, Cayley)",
    twoC phrase!"number of spanning trees of the complete bipartite graph with parts of sizes $v$ and $v$" posInt posInt
      Const.treesCompleteBipartite "the spanning trees of `completeBipartiteGraph (Fin m) (Fin n)` (`m^{n-1}n^{m-1}`)",
    oneC phrase!"number of spanning trees of the cycle on $v$ vertices" ge3 Const.treesCycle
      "the spanning trees of Mathlib `cycleGraph n` (`n`)",
    twoC phrase!"chromatic polynomial of the complete graph on $v$ vertices at $v$" natP (fun _ => tt)
      Const.chromaticComplete "the polynomial counting the colourings of `⊤ : SimpleGraph (Fin n)` (`k(k-1)⋯(k-n+1)`)",
    twoC phrase!"chromatic polynomial of a tree on $v$ vertices at $v$" posInt (fun _ => tt)
      Const.chromaticTree "the chromatic polynomial that every tree on `Fin n` has (`k(k-1)^{n-1}`)",
    twoC phrase!"chromatic polynomial of the cycle on $v$ vertices at $v$" ge3 (fun _ => tt)
      Const.chromaticCycle "the polynomial counting the colourings of `cycleGraph n` (`(k-1)^n + (-1)^n(k-1)`)",
    twoC phrase!"number of edges of the Turán graph on $v$ vertices with $v$ parts" natP posInt Const.turanEdges
      "the edges of Mathlib `turanGraph n r`: the largest number of edges of a graph on `n` vertices without `K_{r+1}` (Turán)",
    two phrase!"binomial bound on the Ramsey number for $v$ and $v$" posInt posInt
      (fun s t => binom (sub (add s t) (num 2)) (sub s (num 1))) "`\\binom{s+t-2}{s-1}`: `R(s,t)` is at most this"]

end Leanify.GraphCounts
