import Leanify.Library.Vectors
import Leanify.Library.Matrices

/-! # Vocabulary: matrices applied to vectors

The fields `vectors` and `matrices` together, which come with this field: `Ax` for a matrix
`A` and a vector `x` with as many coordinates as `A` has columns (Mathlib `Matrix.mulVec`),
a vector with as many coordinates as `A` has rows. With the order of the vectors in every
coordinate, an article states systems of linear inequalities (`Ax\le b`, `A^\top y\ge 0`,
`x\ge 0`), as in Farkas's lemma.

The constants are interpreted by `Leanify/Library/LinearSystemsModel.lean`. -/

namespace Leanify.LinearSystems
open Build Core

/-- The words of the field, where the constants of `vectors` and `matrices` begin at `cv`
and `cm`, their types are `tv` and `tm`, and the constants of the field begin at `co`. -/
def own (tv tm co : Nat) : Vocab :=
  let V : Ty := .base tv
  let M : Ty := .base tm
  { consts := [M ⟶ V ⟶ V, M ⟶ V ⟶ .prop]
    constNames := [w!"\\cdot", w!"\\operatorname{cols}(#1)=\\dim #2"]
    constLean := [w!"Leanify.LinearSystems.mulVec", w!"Leanify.LinearSystems.MulVecable"]
    modules := [w!"Leanify.Library.LinearSystemsModel"]
    notions := [
      { name := phrase!"image of $v$ under $v$", ty := V ⟶ M ⟶ V,
        doc := "`Ax`, for a matrix `A` with as many columns as the vector `x` has coordinates (Mathlib `Matrix.mulVec`)",
        value := close <| lamT V (fun _ => tt) fun x => lamT M (fun a => app2 (const (co + 1)) a x) fun a =>
          app2 (const co) a x }]
    methods := [
      { ty := V, op := .fn w!"@act", const := co, dom := some (.const (co + 1)),
        doc := "`Ax`, for a matrix `A` with as many columns as the vector `x` has coordinates (Mathlib `Matrix.mulVec`)" }] }

/-- The field in a vocabulary of its own: after `vectors` and `matrices`. -/
def vocab : Vocab :=
  let G := Vocab.tag w!"vectors" Vectors.vocab ++ Vocab.tag w!"matrices" Matrices.vocab
  G.join (Vocab.tag w!"linearsystems" (own 0 1 G.consts.length))

end Leanify.LinearSystems
