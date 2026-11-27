import Default.Compiled
import Leanify.Readable
import Leanify.Library.AnalysisModel
import Leanify.Library.TopologyModel
import Leanify.Library.CalculusModel
import Leanify.Library.DynamicsModel
import Leanify.Library.SpecialModel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Complex.Trigonometric
import Leanify.Library.ComplexModel
import Leanify.Library.TorusModel
import Leanify.Library.VectorsModel
import Leanify.Library.PolynomialsModel
import Leanify.Library.StructuresModel
import Leanify.Library.TopologiesModel
import Leanify.Library.GeometryModel
import Leanify.Library.RandomVariablesModel
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Leanify.Library.MatricesModel
import Leanify.Library.UnitSquareModel
import Leanify.Library.HilbertModel
import Leanify.Library.MarkovModel
import Leanify.Library.CombinatoricsModel
import Leanify.Library.CountingModel
import Leanify.Library.PermutationsModel
import Leanify.Library.GraphsModel
import Leanify.Library.GraphCountsModel
import Leanify.Library.WordsModel
import Leanify.Library.FiniteFieldsModel
import Leanify.Library.QuadraticsModel
import Leanify.Library.SolidsModel
import Leanify.Library.TrianglesModel
import Leanify.Library.SphericalGeometryModel
import Leanify.Library.PolyhedraModel
import Leanify.Library.LatticePointsModel
import Leanify.Library.DesignsModel
import Leanify.Library.ClassicalProbabilityModel
import Leanify.Library.FractalsModel
import Leanify.Library.ArithmeticModel
import Leanify.Library.CongruencesModel

/-! # The definitions and claims of `article.tex` as Lean

The article names no field and so draws on all of them (`math`), whose constants are interpreted in Mathlib by the
declarations that the vocabulary names. For every definition, a Lean definition with the
symbol's name, and for every claim `K`: `claimK` (what the sentence says), `meaningfulK`
(every term in it is defined) and `obligationK` (its premises imply both). Each is tied to
the compiled document by a kernel-checked `rfl` theorem. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#leanify_semantics Default "article.tex"
