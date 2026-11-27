import Leanify.Library.Core

/-! # Vocabulary: polyhedra

Euler's formula and the combinatorics and angles of the Platonic solids by their faces
(`We write $V(p,q)$ for the number of vertices of the Platonic solid with faces of $p$ sides and
$q$ faces at each vertex.`). Volumes are in the field `solids`.

* notions: the Euler characteristic `V - E + F` of a polyhedron; the numbers of vertices,
  edges and faces of the Platonic solid `{p,q}` (faces with `p` sides, `q` at each vertex) and
  its dihedral angle; the angle defect `2π - s` of a vertex with face angles summing to `s`
  (Descartes: the defects of a convex polyhedron add up to `4π`).

The quantities of the Platonic solids are constants, interpreted by the declarations of
`Leanify/Library/PolyhedraModel.lean`: their values for every convex polyhedron of
`EuclideanSpace ℝ (Fin 3)` whose faces are regular polygons with `p` sides, `q` at each vertex
(its faces of dimension `0`, `1`, `2` the exposed subsets of that dimension, Mathlib
`IsExposed`), where there is one. Their formulas (`4p/D`, `2pq/D`, `4q/D` for
`D = 4 - (p-2)(q-2) > 0`, `sin(θ/2) = cos(π/q)/sin(π/p)`) are theorems, not definitions. -/

namespace Leanify.Polyhedra
open Build Core

def ge3 (n : B) : B := and (isInt n) (le (num 3) n)
def sin (x : B) : B := app (prim (.realFn .sin)) x
def cos (x : B) : B := app (prim (.realFn .cos)) x
def pi : B := prim .pi
/-! The indices of the constants (apart from the names of their meanings). -/
namespace Const
def numVertices : Nat := 0
def numEdges : Nat := 1
def numFaces : Nat := 2
def dihedralAngle : Nat := 3
def existsPlatonic : Nat := 4
end Const

/-- A quantity of the Platonic solid `{p,q}`, where there is one: the constant `c`. -/
def platonic (name : Phrase) (c : Nat) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real,
    doms := [dom1 .real ge3, dom2 .real fun p q => and (ge3 q) (app2 (const Const.existsPlatonic) p q)], doc, value := .const c }

def vocab : Vocab where
  consts := [.real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real,
    .real ⟶ .real ⟶ .prop]
  constNames := [w!"V_{\\{#1,#2\\}}", w!"E_{\\{#1,#2\\}}", w!"F_{\\{#1,#2\\}}", w!"\\theta_{\\{#1,#2\\}}",
    w!"\\exists\\{#1,#2\\}"]
  constLean := [w!"Leanify.Polyhedra.numVertices", w!"Leanify.Polyhedra.numEdges", w!"Leanify.Polyhedra.numFaces",
    w!"Leanify.Polyhedra.dihedralAngle", w!"Leanify.Polyhedra.ExistsPlatonic"]
  modules := [w!"Leanify.Library.PolyhedraModel"]
  notions := [
    { name := phrase!"Euler characteristic of a polyhedron with $v$ vertices, $v$ edges and $v$ faces", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doc := "`V - E + F`, which is `2` for a convex polyhedron",
      value := close <| lamR fun v => lamR fun e => lamR fun f => add (sub v e) f },
    platonic phrase!"number of vertices of the Platonic solid with faces of $v$ sides and $v$ faces at each vertex"
      Const.numVertices "its faces of dimension `0` (`4p/(4 - (p-2)(q-2))`)",
    platonic phrase!"number of edges of the Platonic solid with faces of $v$ sides and $v$ faces at each vertex"
      Const.numEdges "its faces of dimension `1` (`2pq/(4 - (p-2)(q-2))`)",
    platonic phrase!"number of faces of the Platonic solid with faces of $v$ sides and $v$ faces at each vertex"
      Const.numFaces "its faces of dimension `2` (`4q/(4 - (p-2)(q-2))`)",
    platonic phrase!"dihedral angle of the Platonic solid with faces of $v$ sides and $v$ faces at each vertex"
      Const.dihedralAngle "the angle between two faces with a common edge (`sin(θ/2) = cos(π/q)/sin(π/p)`)",
    { name := phrase!"angle defect of a vertex with face angles summing to $v$", ty := .real ⟶ .real,
      doms := [dom1 .real fun s => and (lt (num 0) s) (lt s (mul (num 2) pi))],
      doc := "`2π - s`", value := close <| lamT .real (fun s => and (lt (num 0) s) (lt s (mul (num 2) pi))) fun s => sub (mul (num 2) pi) s }]

end Leanify.Polyhedra
