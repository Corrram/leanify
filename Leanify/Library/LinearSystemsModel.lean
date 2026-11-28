import Leanify.Library.VectorsModel
import Leanify.Library.MatricesModel

/-! # The meaning of the field `linearsystems`

A matrix of `matrices` applied to a vector of `vectors`. -/

namespace Leanify.LinearSystems

noncomputable section

/-- `Ax` is defined: `A` has as many columns as `x` has coordinates. -/
def MulVecable (A : Leanify.Matrices.Mat) (x : Leanify.Vectors.Vec) : Prop := A.2.1 = x.1

/-- `Ax`, the matrix `A` applied to the vector `x` (Mathlib `Matrix.mulVec`). -/
def mulVec (A : Leanify.Matrices.Mat) (x : Leanify.Vectors.Vec) : Leanify.Vectors.Vec :=
  Leanify.Vectors.mk A.1 fun i => ∑ j ∈ Finset.range A.2.1, Leanify.Matrices.at' A i j * Leanify.Vectors.at' x j

end

end Leanify.LinearSystems
