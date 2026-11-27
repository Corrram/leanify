import Leanify.Library.Core

/-! # Vocabulary: volumes and surface areas of solids

The volumes and surface areas of the standard solids, and of balls and spheres in `n`
dimensions (`We write $V_n(r)$ for the volume of the ball of radius $r$ in dimension $n$.`).

* notions: the volume of the ball of radius `r` in `ℝ^n` and the surface area of its boundary
  sphere; the volume and surface area of a cylinder and of a cone; the volume of an ellipsoid
  with semi-axes `a, b, c` and of a torus with radii `R > r`; the volumes of the regular
  tetrahedron, octahedron, dodecahedron and icosahedron with edge `a`; the volume of the
  standard simplex in `ℝ^n`.

The quantities are constants, interpreted by the declarations of
`Leanify/Library/SolidsModel.lean`: the solids are sets of `EuclideanSpace ℝ (Fin n)` (by their
equations, the regular polyhedra as convex hulls of their vertices), a volume is their
Lebesgue measure (Mathlib `volume`), a surface area the Euclidean Hausdorff measure of their
boundary (Mathlib `μHE[d]`). The formulas (`π^{n/2} r^n/Γ(n/2 + 1)`,
`2π r(r + h)`, `a³/(6√2)`, `1/n!`, …) are theorems, not definitions. -/

namespace Leanify.Solids
open Build Core

def pos (x : B) : B := lt (num 0) x
def posInt (n : B) : B := and (isInt n) (le (num 1) n)

/-! The indices of the constants (apart from the names of their meanings). -/
namespace Const
def ballVolume : Nat := 0
def sphereArea : Nat := 1
def cylinderVolume : Nat := 2
def cylinderArea : Nat := 3
def coneVolume : Nat := 4
def coneArea : Nat := 5
def ellipsoidVolume : Nat := 6
def torusVolume : Nat := 7
def tetrahedronVolume : Nat := 8
def octahedronVolume : Nat := 9
def dodecahedronVolume : Nat := 10
def icosahedronVolume : Nat := 11
def simplexVolume : Nat := 12
end Const

/-- A quantity of a radius and a height, the constant `c`. -/
def two (name : Phrase) (c : Nat) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real pos, dom1 .real pos], doc, value := .const c }
/-- A quantity of the edge, the constant `c`. -/
def edge (name : Phrase) (c : Nat) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real, doms := [dom1 .real pos], doc, value := .const c }

def vocab : Vocab where
  consts := [.real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real,
    .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real,
    .real ⟶ .real, .real ⟶ .real, .real ⟶ .real, .real ⟶ .real, .real ⟶ .real]
  constNames := [w!"\\operatorname{vol}(B^{#2}_{#1})", w!"\\operatorname{area}(S^{#2}_{#1})",
    w!"\\operatorname{vol}(\\mathrm{Cyl}_{#1,#2})", w!"\\operatorname{area}(\\mathrm{Cyl}_{#1,#2})",
    w!"\\operatorname{vol}(\\mathrm{Cone}_{#1,#2})", w!"\\operatorname{area}(\\mathrm{Cone}_{#1,#2})",
    w!"\\operatorname{vol}(\\mathrm{Ell}_{#1,#2,#3})", w!"\\operatorname{vol}(\\mathrm{Tor}_{#1,#2})",
    w!"\\operatorname{vol}(\\mathrm{Tet}_{#})", w!"\\operatorname{vol}(\\mathrm{Oct}_{#})",
    w!"\\operatorname{vol}(\\mathrm{Dod}_{#})", w!"\\operatorname{vol}(\\mathrm{Ico}_{#})", w!"\\operatorname{vol}(\\Delta^{#})"]
  constLean := [w!"Leanify.Solids.ballVolume", w!"Leanify.Solids.sphereArea", w!"Leanify.Solids.cylinderVolume",
    w!"Leanify.Solids.cylinderArea", w!"Leanify.Solids.coneVolume", w!"Leanify.Solids.coneArea",
    w!"Leanify.Solids.ellipsoidVolume", w!"Leanify.Solids.torusVolume", w!"Leanify.Solids.tetrahedronVolume",
    w!"Leanify.Solids.octahedronVolume", w!"Leanify.Solids.dodecahedronVolume", w!"Leanify.Solids.icosahedronVolume",
    w!"Leanify.Solids.simplexVolume"]
  modules := [w!"Leanify.Library.SolidsModel"]
  notions := [
    { name := phrase!"volume of the ball of radius $v$ in dimension $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun r => le (num 0) r, dom1 .real posInt],
      doc := "the Lebesgue measure of the ball of `ℝ^n` (`π^{n/2} r^n/Γ(n/2 + 1)`)", value := .const Const.ballVolume },
    { name := phrase!"surface area of the sphere of radius $v$ in dimension $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun r => le (num 0) r, dom1 .real posInt],
      doc := "the `(n-1)`-dimensional Euclidean Hausdorff measure of the sphere in `ℝ^n` (Mathlib `μHE`) (`2π^{n/2} r^{n-1}/Γ(n/2)`)",
      value := .const Const.sphereArea },
    two phrase!"volume of the cylinder with radius $v$ and height $v$" Const.cylinderVolume
      "the Lebesgue measure of `x₁² + x₂² ≤ r²`, `0 ≤ x₃ ≤ h` (`π r² h`)",
    two phrase!"surface area of the cylinder with radius $v$ and height $v$" Const.cylinderArea
      "the area of its boundary, with the two disks (`2π r(r + h)`)",
    two phrase!"volume of the cone with radius $v$ and height $v$" Const.coneVolume "the Lebesgue measure of the solid cone (`π r² h/3`)",
    two phrase!"surface area of the cone with radius $v$ and height $v$" Const.coneArea
      "the area of its boundary, with the base (`π r(r + √(r² + h²))`)",
    { name := phrase!"volume of the ellipsoid with semi-axes $v$, $v$ and $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom1 .real pos, dom1 .real pos],
      doc := "the Lebesgue measure of `(x₁/a)² + (x₂/b)² + (x₃/c)² ≤ 1` (`4π abc/3`)", value := .const Const.ellipsoidVolume },
    { name := phrase!"volume of the torus with radii $v$ and $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun bigR r => and (pos r) (lt r bigR)],
      doc := "the Lebesgue measure of the solid torus, `0 < r < R` (`2π² R r²`)", value := .const Const.torusVolume },
    edge phrase!"volume of the regular tetrahedron with edge $v$" Const.tetrahedronVolume "the Lebesgue measure of the convex hull of its vertices (`a³/(6√2)`)",
    edge phrase!"volume of the regular octahedron with edge $v$" Const.octahedronVolume "the Lebesgue measure of the convex hull of `±(a/√2)eᵢ` (`√2 a³/3`)",
    edge phrase!"volume of the regular dodecahedron with edge $v$" Const.dodecahedronVolume "the Lebesgue measure of the convex hull of its twenty vertices (`(15 + 7√5) a³/4`)",
    edge phrase!"volume of the regular icosahedron with edge $v$" Const.icosahedronVolume "the Lebesgue measure of the convex hull of its twelve vertices (`5(3 + √5) a³/12`)",
    { name := phrase!"volume of the standard simplex in dimension $v$", ty := .real ⟶ .real, doms := [dom1 .real posInt],
      doc := "the Lebesgue measure of the points with nonnegative coordinates of sum at most `1` (`1/n!`)",
      value := .const Const.simplexVolume }]

end Leanify.Solids
