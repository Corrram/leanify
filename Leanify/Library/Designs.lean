import Leanify.Library.Core

/-! # Vocabulary: combinatorial designs

The parameters of balanced incomplete block designs, Steiner triple systems and finite
planes (`We write $r(v,k,\lambda)$ for the replication number of a design with $v$ points,
block size $k$ and index $\lambda$.`).

* modifiers: `admissible for Steiner triple systems` (`v ≡ 1` or `3 (mod 6)`, the orders of
  Steiner triple systems by Kirkman's theorem).
* notions: the replication number `λ(v-1)/(k-1)` and the number of blocks `λv(v-1)/(k(k-1))` of
  a 2-`(v,k,λ)` design; the number `v(v-1)/6` of triples of a Steiner triple system; the
  numbers of points and lines `n² + n + 1` of a projective plane, and of points `n²` and lines
  `n² + n` of an affine plane, of order `n`.

Every meaning is a term of the core language. -/

namespace Leanify.Designs
open Build Core

def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def ge2 (n : B) : B := and (isInt n) (le (num 2) n)
def mod6 (v r : B) : B := isInt (div (sub v r) (num 6))
def design (name : Phrase) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real,
    doms := [dom1 .real ge2, dom2 .real fun v k => and (ge2 k) (lt k v), dom3 .real fun _ _ l => posInt l], doc,
    value := close <| lamT .real ge2 fun v => lamT .real (fun k => and (ge2 k) (lt k v)) fun k => lamT .real posInt fun l => body v k l }
def plane (name : Phrase) (body : B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real, doms := [dom1 .real ge2], doc, value := close <| lamT .real ge2 body }

def vocab : Vocab where
  mods := [
    { phrase := phrase!"admissible for Steiner triple systems", prenominal := false, ty := .real,
      pred := close <| lamR fun v => and (posInt v) (or (mod6 v (num 1)) (mod6 v (num 3))),
      doc := "a positive integer `v ≡ 1` or `3 (mod 6)`: the orders of Steiner triple systems (Kirkman)" }]
  notions := [
    design phrase!"replication number of a design with $v$ points, block size $v$ and index $v$"
      (fun v k l => div (mul l (sub v (num 1))) (sub k (num 1))) "`λ(v-1)/(k-1)`: the blocks through a point of a 2-`(v,k,λ)` design",
    design phrase!"number of blocks of a design with $v$ points, block size $v$ and index $v$"
      (fun v k l => div (mul l (mul v (sub v (num 1)))) (mul k (sub k (num 1)))) "`λv(v-1)/(k(k-1))`",
    { name := phrase!"number of triples of a Steiner triple system of order $v$", ty := .real ⟶ .real, doms := [dom1 .real posInt],
      doc := "`v(v-1)/6`", value := close <| lamT .real posInt fun v => div (mul v (sub v (num 1))) (num 6) },
    plane phrase!"number of points of a projective plane of order $v$" (fun n => add (mul n n) (add n (num 1))) "`n² + n + 1`",
    plane phrase!"number of lines of a projective plane of order $v$" (fun n => add (mul n n) (add n (num 1))) "`n² + n + 1`",
    plane phrase!"number of points of an affine plane of order $v$" (fun n => mul n n) "`n²`",
    plane phrase!"number of lines of an affine plane of order $v$" (fun n => add (mul n n) n) "`n² + n`"]

end Leanify.Designs
