import Leanify.Library.Core

/-! # Vocabulary: vectors

A vector is a real vector of some dimension `n` (Mathlib's `Fin n → ℝ`, with the
Euclidean norm): a type of its own, so that an article binds vectors as it binds numbers
(`Let $x$ and $y$ be vectors in $\mathbb{R}^n$.`) and writes `x+y`, `x-y`, `-x` (of the
same dimension), `cx` for a number `c`, `\lVert x\rVert` (also `\|x\|`) and
`\langle x,y\rangle` (of the same dimension), and `x\le y`, `x<y` for the order in every
coordinate (`x\ge 0`: a number is compared with every coordinate). A real number is the
vector of dimension 1.

* nouns: `vector`, `unit vector`;
* adjectives: `nonzero`, `unit`, `in $\mathbb{R}^n$`, `of dimension $n$`, `orthogonal to
  $y$`, `parallel to $y$`;
* notions: the dimension, the norm, the inner product, the `i`th coordinate, the distance
  and the angle between two vectors, the cross product (in dimension 3), the zero vector
  and the standard basis vectors, the sum of the coordinates, and `$\mathbb{R}^n$` as the
  set of the vectors of dimension `n` (`the set of vectors in $\mathbb{R}^n$`).

The constants are interpreted by `Leanify/Library/VectorsModel.lean`. -/

namespace Leanify.Vectors
open Build Core

/-- Vectors: the field's base type. -/
abbrev V : Ty := .base 0

/-- The constants, in the order of their indices: `(type, TeX name, Lean name)`. -/
def table : List (Ty × Codes × Codes) := [
  (V ⟶ .real, w!"\\dim", w!"Leanify.Vectors.dim"),                                   -- 0
  (.real ⟶ V, w!"", w!"Leanify.Vectors.ofReal"),                                     -- 1
  (V ⟶ V ⟶ .prop, w!"\\dim #1=\\dim #2", w!"Leanify.Vectors.SameDim"),               -- 2
  (V ⟶ V ⟶ .prop, w!"\\operatorname{Scalable}(#1,#2)", w!"Leanify.Vectors.Scalable"), -- 3
  (V ⟶ V ⟶ V, w!"+", w!"Leanify.Vectors.add"),                                       -- 4
  (V ⟶ V ⟶ V, w!"-", w!"Leanify.Vectors.sub"),                                       -- 5
  (V ⟶ V, w!"-", w!"Leanify.Vectors.neg"),                                           -- 6
  (V ⟶ V ⟶ V, w!"\\cdot", w!"Leanify.Vectors.mul"),                                  -- 7
  (V ⟶ .real, w!"\\lVert #\\rVert", w!"Leanify.Vectors.norm"),                       -- 8
  (V ⟶ V ⟶ .real, w!"\\langle #1,#2\\rangle", w!"Leanify.Vectors.inner"),            -- 9
  (.real ⟶ V ⟶ .real, w!"#2_{#1}", w!"Leanify.Vectors.coord"),                       -- 10
  (V ⟶ V ⟶ V, w!"\\times", w!"Leanify.Vectors.cross"),                               -- 11
  (.real ⟶ V, w!"0_{#}", w!"Leanify.Vectors.zero"),                                  -- 12
  (.real ⟶ .real ⟶ V, w!"e_{#1}^{(#2)}", w!"Leanify.Vectors.basis"),                 -- 13
  (V ⟶ V ⟶ .real, w!"\\angle(#1,#2)", w!"Leanify.Vectors.angle"),                    -- 14
  (V ⟶ .real, w!"\\operatorname{sum}", w!"Leanify.Vectors.coordSum"),                -- 15
  (V ⟶ V ⟶ .prop, w!"#1\\parallel #2", w!"Leanify.Vectors.Parallel"),                -- 16
  (V ⟶ V ⟶ .prop, w!"#1\\le #2", w!"Leanify.Vectors.le"),                            -- 17
  (V ⟶ V ⟶ .prop, w!"#1<#2", w!"Leanify.Vectors.lt"),                                 -- 18
  (V ⟶ V ⟶ .prop, w!"\\operatorname{Comparable}(#1,#2)", w!"Leanify.Vectors.Comparable")] -- 19

def vPred (p : B → B) : Tm := close <| lamT V (fun _ => tt) p
def dimOf (x : B) : B := app (const 0) x
def sameDim : Tm := .const 2
def nonzero (x : B) : B := not (eq (app (const 8) x) (num 0))
def inRn : Tm := close <| lamR fun n => lamT V (fun _ => tt) fun x => eq (dimOf x) n
def natDom : Option Tm := some nonnegInt

def mod (p : Phrase) (pre : Bool) (pred : Tm) (doc : String) : Modifier :=
  { phrase := p, prenominal := pre, ty := V, pred, doc }
def nounV (sing plural : Phrase) (pred : Tm) (doc : String) : Noun := { sing, plural, ty := V, pred, doc }
/-- A notion of two vectors of the same dimension. -/
def of2 (name : Phrase) (c : Nat) (ty : Ty) (doc : String) : Notion :=
  { name, ty, doc, value := close <| lamT V (fun _ => tt) fun x => lamT V (fun _ => tt) fun y =>
      guard (app2 (const 2) x y) (app2 (const c) x y) }

def vocab : Vocab where
  types := [w!"\\mathrm{Vec}"]
  consts := table.map (·.1)
  constNames := table.map (·.2.1)
  constLean := table.map (·.2.2)
  typeLean := [(w!"Leanify.Vectors.Vec", w!"Leanify.Vectors.Vec.empty")]
  modules := [w!"Leanify.Library.VectorsModel"]
  nouns := [
    nounV phrase!"vector" phrase!"vectors" (vPred fun _ => tt) "a real vector of some dimension (Mathlib `Fin n → ℝ`)",
    nounV phrase!"unit vector" phrase!"unit vectors" (vPred fun x => eq (app (const 8) x) (num 1)) "of norm 1"]
  mods := [
    mod phrase!"nonzero" true (vPred fun x => nonzero x) "not the zero vector",
    mod phrase!"unit" true (vPred fun x => eq (app (const 8) x) (num 1)) "of norm 1",
    mod phrase!"in $\\mathbb{R}^v$" false inRn "of dimension `n`",
    mod phrase!"in $\\mathbb{R}^{v}$" false inRn "of dimension `n`",
    mod phrase!"of dimension $v$" false inRn "in `ℝⁿ`",
    mod phrase!"orthogonal to $v$" false (close <| lamT V (fun _ => tt) fun y => lamT V (fun _ => tt) fun x =>
        and (app2 (const 2) x y) (eq (app2 (const 9) x y) (num 0))) "of the same dimension, with inner product 0",
    mod phrase!"parallel to $v$" false (close <| lamT V (fun _ => tt) fun y => lamT V (fun _ => tt) fun x =>
        and (app2 (const 2) x y) (app2 (const 16) x y)) "of the same dimension, one a multiple of the other"]
  notions := [
    { name := phrase!"dimension of $v$", value := .const 0, ty := V ⟶ .real, doc := "`n`, for a vector in `ℝⁿ`" },
    { name := phrase!"norm of $v$", value := .const 8, ty := V ⟶ .real, doc := "the Euclidean norm (Mathlib `EuclideanSpace`)" },
    { name := phrase!"length of $v$", value := .const 8, ty := V ⟶ .real, doc := "the Euclidean norm" },
    of2 phrase!"inner product of $v$ and $v$" 9 (V ⟶ V ⟶ .real) "`∑ xᵢyᵢ`, of vectors of the same dimension (Mathlib `inner`)",
    of2 phrase!"dot product of $v$ and $v$" 9 (V ⟶ V ⟶ .real) "`∑ xᵢyᵢ`, of vectors of the same dimension",
    { name := phrase!"$v$th coordinate of $v$", ty := .real ⟶ V ⟶ .real, doc := "`xᵢ`, for `1 ≤ i ≤ n`",
      value := close <| lamR fun i => lamT V (fun _ => tt) fun x =>
        guard (and (isInt i) (and (le (num 1) i) (le i (dimOf x)))) (app2 (const 10) i x) },
    { name := phrase!"distance between $v$ and $v$", ty := V ⟶ V ⟶ .real, doc := "`‖x - y‖`, of vectors of the same dimension",
      value := close <| lamT V (fun _ => tt) fun x => lamT V (fun _ => tt) fun y =>
        guard (app2 (const 2) x y) (app (const 8) (app2 (const 5) x y)) },
    { name := phrase!"angle between $v$ and $v$", ty := V ⟶ V ⟶ .real,
      doc := "in `[0, π]`, of nonzero vectors of the same dimension (Mathlib `InnerProductGeometry.angle`)",
      value := close <| lamT V (fun _ => tt) fun x => lamT V (fun _ => tt) fun y =>
        guard (and (app2 (const 2) x y) (and (nonzero x) (nonzero y))) (app2 (const 14) x y) },
    { name := phrase!"cross product of $v$ and $v$", ty := V ⟶ V ⟶ V, doc := "of vectors of dimension 3 (Mathlib `crossProduct`)",
      value := close <| lamT V (fun _ => tt) fun x => lamT V (fun _ => tt) fun y =>
        guard (and (eq (dimOf x) (num 3)) (eq (dimOf y) (num 3))) (app2 (const 11) x y) },
    { name := phrase!"zero vector of dimension $v$", value := .const 12, ty := .real ⟶ V, doms := [natDom], doc := "`0 ∈ ℝⁿ`" },
    { name := phrase!"zero vector in $\\mathbb{R}^v$", value := .const 12, ty := .real ⟶ V, doms := [natDom], doc := "`0 ∈ ℝⁿ`" },
    { name := phrase!"$v$th standard basis vector of dimension $v$", ty := .real ⟶ .real ⟶ V, doc := "`eᵢ ∈ ℝⁿ`, for `1 ≤ i ≤ n`",
      value := close <| lamR fun i => lamR fun n =>
        guard (and (and (isInt i) (isInt n)) (and (le (num 1) i) (le i n))) (app2 (const 13) i n) },
    { name := phrase!"sum of the coordinates of $v$", value := .const 15, ty := V ⟶ .real, doc := "`∑ xᵢ`" },
    { name := phrase!"set of vectors in $\\mathbb{R}^v$", value := inRn, ty := .real ⟶ V ⟶ .prop, doms := [natDom], doc := "`ℝⁿ`" },
    { name := phrase!"set of vectors of dimension $v$", value := inRn, ty := .real ⟶ V ⟶ .prop, doms := [natDom], doc := "`ℝⁿ`" }]
  methods := [
    { ty := V, op := .ofReal, const := 1, doc := "a real number `c` as the vector `(c)` of dimension 1" },
    { ty := V, op := .add, const := 4, doc := "`x + y`, of the same dimension", dom := some sameDim },
    { ty := V, op := .sub, const := 5, doc := "`x - y`, of the same dimension", dom := some sameDim },
    { ty := V, op := .neg, const := 6, doc := "`-x`" },
    { ty := V, op := .mul, const := 7, doc := "`cx`, for a vector `c` of dimension 1 (a number)", dom := some (.const 3) },
    { ty := V, op := .le, const := 17, dom := some (.const 19),
      doc := "`x\\le y`: in every coordinate, of vectors of the same dimension; a number is compared with every coordinate (`x\\ge 0`)" },
    { ty := V, op := .lt, const := 18, dom := some (.const 19),
      doc := "`x<y`: in every coordinate (`x>0`: every coordinate is positive)" },
    { ty := V, op := .fn w!"@norm", const := 8, doc := "`\\lVert x\\rVert`, `\\|x\\|`: the Euclidean norm" },
    { ty := V, op := .fn w!"@inner", const := 9, doc := "`\\langle x,y\\rangle`: the inner product, of the same dimension",
      dom := some sameDim }]

end Leanify.Vectors
