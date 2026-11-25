import Leanify.Library.Core

/-! # Vocabulary: finite simple graphs

A graph is a finite simple graph whose vertices are the integers `1, …, n` (Mathlib's
`SimpleGraph (Fin n)`, the vertex `i` being `i + 1`): a type of its own, so that an article
binds graphs as it binds numbers (`Let $G$ be a connected graph on $n$ vertices.`) and names
vertices by numbers (`$\deg_G(v)$ for $v\in V(G)$`, `\sum_{v=1}^{n}`).

* nouns: `graph`, `simple graph`, `finite graph`, `tree`, `forest`;
* adjectives: `connected`, `acyclic`, `bipartite`, `regular`, `complete`, `triangle-free`,
  `Hamiltonian`, `on $n$ vertices`, `with $m$ edges`, `$k$-regular`;
* notions: the vertex set, the number of vertices and of edges, the degree of a vertex, the
  neighbours of a vertex, adjacency, the distance between two vertices, the minimum and
  maximum degree, the chromatic, clique and independence numbers, the number of connected
  components, the diameter, the girth; the complete, cycle, path and empty graphs on `n`
  vertices, the complete bipartite graph `K_{m,n}`, and the complement (also
  `\overline{G}`).

Equality of graphs is equality of the labelled graphs (`$G$ is the complete graph on $4$
vertices`). The constants are interpreted by `Leanify/Library/GraphsModel.lean`. -/

namespace Leanify.Graphs
open Build Core

/-- Graphs: the field's base type. -/
abbrev G : Ty := .base 0

namespace Const
def isVertex : Nat := 0
def numVertices : Nat := 1
def numEdges : Nat := 2
def degree : Nat := 3
def adj : Nat := 4
def dist : Nat := 5
def minDegree : Nat := 6
def maxDegree : Nat := 7
def chromatic : Nat := 8
def clique : Nat := 9
def indep : Nat := 10
def components : Nat := 11
def diameter : Nat := 12
def girth : Nat := 13
def connected : Nat := 14
def acyclic : Nat := 15
def isTree : Nat := 16
def bipartite : Nat := 17
def regular : Nat := 18
def complete : Nat := 19
def hamiltonian : Nat := 20
def completeOn : Nat := 21
def cycleOn : Nat := 22
def pathOn : Nat := 23
def emptyOn : Nat := 24
def completeBip : Nat := 25
def compl : Nat := 26
def reachable : Nat := 27
end Const
open Const

def vert (v g : B) : B := app2 (const isVertex) g v
def nv (g : B) : B := app (const numVertices) g

def gPred (p : B → B) : Tm := close <| lamT G (fun _ => tt) p
def anyGraph : Tm := gPred fun _ => tt

def natDom : Option Tm := some nonnegInt

/-- A notion of a graph, a number. -/
def ofG (name : Phrase) (c : Nat) (doc : String) : Notion :=
  { name, value := .const c, ty := G ⟶ .real, doc }

/-- A graph on `n` vertices. -/
def onN (name : Phrase) (c : Nat) (dom : Option Tm) (doc : String) : Notion :=
  { name, value := .const c, ty := .real ⟶ G, doms := [dom], doc }

/-- `v` is a vertex of `g` (with `g` first, as `G ⟶ ℝ ⟶ Prop`). -/
def vertexSet : Tm := close <| lamT G (fun _ => tt) fun g => lamR fun v => vert v g

/-- The degree of `v` in `g`, for a vertex `v`. -/
def degreeIn : Tm := close <| lamR fun v => lamT G (fun _ => tt) fun g =>
  guard (vert v g) (app2 (const degree) v g)

/-- The neighbours of `v` in `g`, for a vertex `v`. -/
def neighbours : Tm := close <| lamR fun v => lamT G (fun _ => tt) fun g =>
  guard (vert v g) (lamR fun u => app (app (app (const adj) u) v) g)

/-- The distance between two vertices of `g` that a walk joins (between vertices of different
components it is not a number). -/
def distIn : Tm := close <| lamR fun u => lamR fun v => lamT G (fun _ => tt) fun g =>
  guard (and (and (vert u g) (vert v g)) (app (app (app (const reachable) u) v) g))
    (app (app (app (const dist) u) v) g)

/-- A graph with at least one vertex. -/
def nonempty : Tm := gPred fun g => le (num 1) (nv g)

def adjacency : Tm := close <| lamT G (fun _ => tt) fun g => lamR fun u => lamR fun v =>
  app (app (app (const adj) u) v) g

def mod (p : Phrase) (pre : Bool) (pred : Tm) (doc : String) : Modifier :=
  { phrase := p, prenominal := pre, ty := G, pred, doc }

def nounG (sing plural : Phrase) (pred : Tm) (doc : String) : Noun :=
  { sing, plural, ty := G, pred, doc }

def vocab : Vocab where
  types := [w!"\\mathrm{Graph}"]
  consts := [G ⟶ .real ⟶ .prop, G ⟶ .real, G ⟶ .real, .real ⟶ G ⟶ .real, .real ⟶ .real ⟶ G ⟶ .prop,
    .real ⟶ .real ⟶ G ⟶ .real, G ⟶ .real, G ⟶ .real, G ⟶ .real, G ⟶ .real, G ⟶ .real, G ⟶ .real,
    G ⟶ .real, G ⟶ .real, G ⟶ .prop, G ⟶ .prop, G ⟶ .prop, G ⟶ .prop, G ⟶ .prop, G ⟶ .prop, G ⟶ .prop,
    .real ⟶ G, .real ⟶ G, .real ⟶ G, .real ⟶ G, .real ⟶ .real ⟶ G, G ⟶ G, .real ⟶ .real ⟶ G ⟶ .prop]
  constNames := [w!"#2\\in V(#1)", w!"\\lvert V(#)\\rvert", w!"\\lvert E(#)\\rvert", w!"\\deg_{#2}(#1)",
    w!"\\operatorname{Adj}", w!"\\operatorname{dist}", w!"\\delta", w!"\\Delta", w!"\\chi", w!"\\omega",
    w!"\\alpha", w!"\\operatorname{c}", w!"\\operatorname{diam}", w!"\\operatorname{girth}",
    w!"\\operatorname{Connected}", w!"\\operatorname{Acyclic}", w!"\\operatorname{Tree}",
    w!"\\operatorname{Bipartite}", w!"\\operatorname{Regular}", w!"\\operatorname{Complete}",
    w!"\\operatorname{Hamiltonian}", w!"K_{#}", w!"C_{#}", w!"P_{#}", w!"\\overline{K_{#}}", w!"K_{#1,#2}",
    w!"\\overline{#}", w!"\\operatorname{Reachable}"]
  constLean := [w!"Leanify.Graphs.IsVertex", w!"Leanify.Graphs.numVertices", w!"Leanify.Graphs.numEdges",
    w!"Leanify.Graphs.degree", w!"Leanify.Graphs.Adjacent", w!"Leanify.Graphs.dist", w!"Leanify.Graphs.minDegree",
    w!"Leanify.Graphs.maxDegree", w!"Leanify.Graphs.chromaticNumber", w!"Leanify.Graphs.cliqueNumber",
    w!"Leanify.Graphs.independenceNumber", w!"Leanify.Graphs.numComponents", w!"Leanify.Graphs.diameter",
    w!"Leanify.Graphs.girth", w!"Leanify.Graphs.Connected", w!"Leanify.Graphs.Acyclic", w!"Leanify.Graphs.IsTree",
    w!"Leanify.Graphs.Bipartite", w!"Leanify.Graphs.Regular", w!"Leanify.Graphs.Complete",
    w!"Leanify.Graphs.Hamiltonian", w!"Leanify.Graphs.completeGraph", w!"Leanify.Graphs.cycleGraph",
    w!"Leanify.Graphs.pathGraph", w!"Leanify.Graphs.emptyGraph", w!"Leanify.Graphs.completeBipartite",
    w!"Leanify.Graphs.complement", w!"Leanify.Graphs.Reachable"]
  typeLean := [(w!"Leanify.Graphs.Graph", w!"Leanify.Graphs.Graph.empty")]
  modules := [w!"Leanify.Library.GraphsModel"]
  nouns := [
    nounG phrase!"graph" phrase!"graphs" anyGraph "a finite simple graph on the vertices `1, …, n` (Mathlib `SimpleGraph (Fin n)`)",
    nounG phrase!"simple graph" phrase!"simple graphs" anyGraph "a finite simple graph (Mathlib `SimpleGraph (Fin n)`)",
    nounG phrase!"finite graph" phrase!"finite graphs" anyGraph "a finite simple graph (Mathlib `SimpleGraph (Fin n)`)",
    nounG phrase!"finite simple graph" phrase!"finite simple graphs" anyGraph "(Mathlib `SimpleGraph (Fin n)`)",
    nounG phrase!"tree" phrase!"trees" (gPred fun g => app (const isTree) g) "connected and acyclic (Mathlib `SimpleGraph.IsTree`)",
    nounG phrase!"forest" phrase!"forests" (gPred fun g => app (const acyclic) g) "acyclic (Mathlib `SimpleGraph.IsAcyclic`)"]
  mods := [
    mod phrase!"connected" true (.const connected) "nonempty, and any two vertices are joined by a walk (Mathlib `SimpleGraph.Connected`)",
    mod phrase!"acyclic" true (.const acyclic) "without cycles (Mathlib `SimpleGraph.IsAcyclic`)",
    mod phrase!"bipartite" true (.const bipartite) "2-colorable (Mathlib `SimpleGraph.Colorable 2`)",
    mod phrase!"regular" true (.const regular) "all vertices have the same degree (Mathlib `SimpleGraph.IsRegularOfDegree`)",
    mod phrase!"complete" true (.const complete) "any two distinct vertices are adjacent (`G = ⊤`)",
    mod phrase!"Hamiltonian" true (.const hamiltonian) "with a cycle through every vertex (Mathlib `SimpleGraph.IsHamiltonian`)",
    mod phrase!"triangle-free" true (gPred fun g => le (app (const clique) g) (num 2))
      "without three pairwise adjacent vertices (Mathlib `SimpleGraph.CliqueFree 3`)",
    mod phrase!"$v$-regular" true (close <| lamR fun k => lamT G (fun _ => tt) fun g =>
        and (app (const regular) g) (allR fun v => imp (vert v g) (eq (app2 (const degree) v g) k)))
      "every vertex has degree `k` (Mathlib `SimpleGraph.IsRegularOfDegree`)",
    mod phrase!"on $v$ vertices" false (close <| lamR fun n => lamT G (fun _ => tt) fun g => eq (nv g) n)
      "with `n` vertices",
    mod phrase!"with $v$ vertices" false (close <| lamR fun n => lamT G (fun _ => tt) fun g => eq (nv g) n)
      "with `n` vertices",
    mod phrase!"with $v$ edges" false (close <| lamR fun m => lamT G (fun _ => tt) fun g => eq (app (const numEdges) g) m)
      "with `m` edges",
    mod phrase!"with $v$ vertices and $v$ edges" false (close <| lamR fun n => lamR fun m => lamT G (fun _ => tt) fun g =>
        and (eq (nv g) n) (eq (app (const numEdges) g) m))
      "with `n` vertices and `m` edges",
    mod phrase!"on $v$ vertices with $v$ edges" false (close <| lamR fun n => lamR fun m => lamT G (fun _ => tt) fun g =>
        and (eq (nv g) n) (eq (app (const numEdges) g) m))
      "with `n` vertices and `m` edges"]
  notions := [
    { name := phrase!"vertex set of $v$", value := vertexSet, ty := G ⟶ .real ⟶ .prop,
      doc := "`{1, …, n}`" },
    ofG phrase!"number of vertices of $v$" numVertices "`n` (Mathlib `Fintype.card (Fin n)`)",
    ofG phrase!"number of edges of $v$" numEdges "(Mathlib `G.edgeSet`)",
    { name := phrase!"degree of $v$ in $v$", value := degreeIn, ty := .real ⟶ G ⟶ .real,
      doc := "the number of neighbours of a vertex (Mathlib `SimpleGraph.degree`)" },
    { name := phrase!"set of neighbours of $v$ in $v$", value := neighbours, ty := .real ⟶ G ⟶ .real ⟶ .prop,
      doc := "the vertices adjacent to a vertex (Mathlib `SimpleGraph.neighborSet`)" },
    { name := phrase!"set of neighbors of $v$ in $v$", value := neighbours, ty := .real ⟶ G ⟶ .real ⟶ .prop,
      doc := "the vertices adjacent to a vertex (Mathlib `SimpleGraph.neighborSet`)" },
    { name := phrase!"adjacency relation of $v$", value := adjacency, ty := G ⟶ .real ⟶ .real ⟶ .prop,
      doc := "`u ∼ v` (Mathlib `SimpleGraph.Adj`)" },
    { name := phrase!"distance between $v$ and $v$ in $v$", value := distIn, ty := .real ⟶ .real ⟶ G ⟶ .real,
      doc := "the length of a shortest walk, between vertices of one component (Mathlib `SimpleGraph.dist`)" },
    { ofG phrase!"minimum degree of $v$" minDegree "of a graph with a vertex (Mathlib `SimpleGraph.minDegree`)" with
      doms := [some nonempty] },
    { ofG phrase!"maximum degree of $v$" maxDegree "of a graph with a vertex (Mathlib `SimpleGraph.maxDegree`)" with
      doms := [some nonempty] },
    ofG phrase!"chromatic number of $v$" chromatic "(Mathlib `SimpleGraph.chromaticNumber`)",
    ofG phrase!"clique number of $v$" clique "(Mathlib `SimpleGraph.cliqueNum`)",
    ofG phrase!"independence number of $v$" indep "(Mathlib `SimpleGraph.indepNum`)",
    ofG phrase!"number of connected components of $v$" components "(Mathlib `SimpleGraph.ConnectedComponent`)",
    ofG phrase!"number of components of $v$" components "(Mathlib `SimpleGraph.ConnectedComponent`)",
    { ofG phrase!"diameter of $v$" diameter "of a connected graph (Mathlib `SimpleGraph.diam`)" with
      doms := [some (.const connected)] },
    { ofG phrase!"girth of $v$" girth "the length of a shortest cycle, of a graph with a cycle (Mathlib `SimpleGraph.girth`)" with
      doms := [some (gPred fun g => not (app (const acyclic) g))] },
    onN phrase!"complete graph on $v$ vertices" completeOn natDom "`K_n` (Mathlib `⊤`)",
    onN phrase!"cycle on $v$ vertices" cycleOn (some (predR fun n => and (isInt n) (le (num 3) n)))
      "`C_n`, for `n ≥ 3` (Mathlib `SimpleGraph.cycleGraph`)",
    onN phrase!"cycle graph on $v$ vertices" cycleOn (some (predR fun n => and (isInt n) (le (num 3) n)))
      "`C_n`, for `n ≥ 3` (Mathlib `SimpleGraph.cycleGraph`)",
    onN phrase!"path on $v$ vertices" pathOn natDom "`P_n` (Mathlib `SimpleGraph.pathGraph`)",
    onN phrase!"path graph on $v$ vertices" pathOn natDom "`P_n` (Mathlib `SimpleGraph.pathGraph`)",
    onN phrase!"empty graph on $v$ vertices" emptyOn natDom "no edges (Mathlib `⊥`)",
    { name := phrase!"complete bipartite graph $K_{v,v}$", value := .const completeBip, ty := .real ⟶ .real ⟶ G,
      doms := [natDom, natDom], doc := "parts `{1, …, m}` and `{m+1, …, m+n}`" },
    { name := phrase!"complement of $v$", value := .const compl, ty := G ⟶ G,
      doc := "the same vertices, the other pairs adjacent (Mathlib `Gᶜ`)" }]
  methods := [
    { ty := G, op := .decor w!"\\overline", const := compl, doc := "the complement `Gᶜ`" }]

end Leanify.Graphs
