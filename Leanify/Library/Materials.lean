import Leanify.Library.Core

/-! # Vocabulary: mechanics of materials

Stresses, stiffnesses and the classical beam and column formulas, by their parameters (`We write
$\delta(L,F,E,I)$ for the deflection of a cantilever of length $L$ under the end load $F$ with
Young's modulus $E$ and second moment of area $I$.`).

* notions: the stress `F/A` and the strain `ΔL/L`; the axial stiffness `EA/L` of a rod; the
  shear modulus `E/(2(1+ν))` and the bulk modulus `E/(3(1-2ν))` for Young's modulus `E` and
  Poisson's ratio `ν`; the second moments of area `bh³/12` of a rectangle and `πr⁴/4` of a disk;
  the end deflection `FL³/(3EI)` of a cantilever and the midspan deflection `FL³/(48EI)` of a
  simply supported beam under a point load; the Euler buckling load `π²EI/L²` of a pinned column.

Every meaning is a term of the core language. -/

namespace Leanify.Materials
open Build Core

def pos (x : B) : B := lt (num 0) x
def pi : B := prim .pi
def two (name : Phrase) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [none, dom2 .real fun _ y => pos y], doc,
    value := close <| lamR fun x => lamT .real pos fun y => body x y }
def twoPos (name : Phrase) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real pos, dom2 .real fun _ y => pos y], doc,
    value := close <| lamT .real pos fun x => lamT .real pos fun y => body x y }
def poisson (name : Phrase) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real pos, dom2 .real fun _ n => and (lt (num (0)) (add n (num 1))) (lt (mul (num 2) n) (num 1))], doc,
    value := close <| lamT .real pos fun e => lamT .real (fun n => and (lt (num 0) (add n (num 1))) (lt (mul (num 2) n) (num 1))) fun n => body e n }
def beam (name : Phrase) (body : B → B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
    doms := [dom1 .real pos, none, dom3 .real fun _ _ e => pos e, dom4 .real fun _ _ _ i => pos i], doc,
    value := close <| lamT .real pos fun l => lamR fun f => lamT .real pos fun e => lamT .real pos fun i => body l f e i }

def vocab : Vocab where
  notions := [
    two phrase!"stress for the force $v$ on the area $v$" (fun f a => div f a) "`F/A`",
    two phrase!"strain for the extension $v$ of the length $v$" (fun d l => div d l) "`ΔL/L`",
    { name := phrase!"axial stiffness of a rod of length $v$ and cross-section $v$ with Young's modulus $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ a => pos a, dom3 .real fun _ _ e => pos e], doc := "`EA/L`",
      value := close <| lamT .real pos fun l => lamT .real pos fun a => lamT .real pos fun e => div (mul e a) l },
    poisson phrase!"shear modulus for Young's modulus $v$ and Poisson's ratio $v$" (fun e n => div e (mul (num 2) (add (num 1) n)))
      "`E/(2(1+ν))`, for `-1 < ν < 1/2`",
    poisson phrase!"bulk modulus for Young's modulus $v$ and Poisson's ratio $v$" (fun e n => div e (mul (num 3) (sub (num 1) (mul (num 2) n))))
      "`E/(3(1-2ν))`, for `-1 < ν < 1/2`",
    twoPos phrase!"second moment of area of a rectangle of width $v$ and height $v$" (fun b h => div (mul b (mul h (mul h h))) (num 12))
      "`bh³/12`, about the centroidal axis parallel to the width",
    { name := phrase!"second moment of area of a disk of radius $v$", ty := .real ⟶ .real, doms := [dom1 .real pos],
      doc := "`πr⁴/4`, about a diameter", value := close <| lamT .real pos fun r => div (mul pi (mul (mul r r) (mul r r))) (num 4) },
    beam phrase!"deflection of a cantilever of length $v$ under the end load $v$ with Young's modulus $v$ and second moment of area $v$"
      (fun l f e i => div (mul f (mul l (mul l l))) (mul (num 3) (mul e i))) "`FL³/(3EI)`",
    beam phrase!"midspan deflection of a simply supported beam of length $v$ under the central load $v$ with Young's modulus $v$ and second moment of area $v$"
      (fun l f e i => div (mul f (mul l (mul l l))) (mul (num 48) (mul e i))) "`FL³/(48EI)`",
    { name := phrase!"Euler buckling load of a pinned column of length $v$ with Young's modulus $v$ and second moment of area $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ e => pos e, dom3 .real fun _ _ i => pos i], doc := "`π²EI/L²`",
      value := close <| lamT .real pos fun l => lamT .real pos fun e => lamT .real pos fun i => div (mul (mul pi pi) (mul e i)) (mul l l) }]

end Leanify.Materials
