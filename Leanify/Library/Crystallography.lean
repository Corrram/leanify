import Leanify.Library.Core

/-! # Vocabulary: crystallography

Cubic lattices by their lattice constant and Miller indices (`We write $d(a,h,k,l)$ for the
interplanar spacing of the cubic lattice with constant $a$ for the Miller indices $h$, $k$ and
$l$.`).

* notions: the interplanar spacing `a/√(h² + k² + l²)`; the packing fractions `π/6`, `√3π/8` and
  `√2π/6` of the simple, body-centred and face-centred cubic lattices; their coordination numbers
  `6`, `8` and `12`; the numbers of atoms per unit cell `2` and `4` and the nearest-neighbour
  distances `√3a/2` and `a/√2` of the body-centred and face-centred lattices.

Every meaning is a term of the core language. -/

namespace Leanify.Crystallography
open Build Core

def pos (x : B) : B := lt (num 0) x
def sqrt (x : B) : B := app2 (prim .rpow) x (div (num 1) (num 2))
def pi : B := prim .pi
def constant (name : Phrase) (v : B) (doc : String) : Notion := { name, ty := .real, doc, value := close v }
def cubic (name : Phrase) (body : B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real, doms := [dom1 .real pos], doc, value := close <| lamT .real pos body }

def vocab : Vocab where
  notions := [
    { name := phrase!"interplanar spacing of the cubic lattice with constant $v$ for the Miller indices $v$, $v$ and $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ h => isInt h, dom3 .real fun _ _ k => isInt k,
        dom4 .real fun _ h k l => and (isInt l) (lt (num 0) (add (mul h h) (add (mul k k) (mul l l))))],
      doc := "`a/√(h² + k² + l²)`",
      value := close <| lamT .real pos fun a => lamT .real isInt fun h => lamT .real isInt fun k =>
        lamT .real (fun l => and (isInt l) (lt (num 0) (add (mul h h) (add (mul k k) (mul l l))))) fun l =>
          div a (sqrt (add (mul h h) (add (mul k k) (mul l l)))) },
    constant phrase!"packing fraction of the simple cubic lattice" (div pi (num 6)) "`π/6`",
    constant phrase!"packing fraction of the body-centred cubic lattice" (div (mul (sqrt (num 3)) pi) (num 8)) "`√3π/8`",
    constant phrase!"packing fraction of the face-centred cubic lattice" (div (mul (sqrt (num 2)) pi) (num 6)) "`√2π/6`",
    constant phrase!"coordination number of the simple cubic lattice" (num 6) "`6`",
    constant phrase!"coordination number of the body-centred cubic lattice" (num 8) "`8`",
    constant phrase!"coordination number of the face-centred cubic lattice" (num 12) "`12`",
    constant phrase!"number of atoms per unit cell of the body-centred cubic lattice" (num 2) "`2`",
    constant phrase!"number of atoms per unit cell of the face-centred cubic lattice" (num 4) "`4`",
    cubic phrase!"nearest-neighbour distance of the body-centred cubic lattice with constant $v$"
      (fun a => div (mul (sqrt (num 3)) a) (num 2)) "`√3a/2`",
    cubic phrase!"nearest-neighbour distance of the face-centred cubic lattice with constant $v$"
      (fun a => div a (sqrt (num 2))) "`a/√2`"]

end Leanify.Crystallography
