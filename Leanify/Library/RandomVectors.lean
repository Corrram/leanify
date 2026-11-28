import Leanify.Library.Vectors
import Leanify.Library.Matrices
import Leanify.Library.Complex

/-! # Vocabulary: random vectors

A random vector is a function of the outcome `ω` of one probability space for the whole
article, `[0,1]` with Lebesgue measure, into the real vectors of one dimension: a type of
its own, so that an article binds random vectors by a noun (`Let $X$ and $Y$ be
$d$-dimensional random vectors.`). The field builds on the fields `vectors`, `matrices` and
`complex`, which come with it: an article writes

* `X+Y`, `X-Y`, `-X` (of the same dimension), `cX` for a number `c`, `X+b` for a vector `b`
  (the constant random vector) and `AX` for a matrix `A` with as many columns as `X` has
  coordinates (`AX+b`); `Ab` for a matrix and a vector is of the field `linearsystems`;
* `X\stackrel{d}{=}Y` (also `\overset{d}{=}`, with `d`, `D`, `\mathcal{D}`, `\mathcal{L}` or
  `law` above `=`): the random vectors have the same distribution, that is, the same
  dimension and the same joint distribution function;
* `X\sim F` for a function `F` of vectors: `F` is the joint distribution function of `X`;
* nouns: `random vector`;
* adjectives: `$d$-dimensional`, `in $\mathbb{R}^d$`, `of dimension $d$`, `integrable`
  (every coordinate is), `independent of $Y$` (the joint distribution function of the
  coordinates of both is the product of theirs), `equal in distribution to $Y$`, `with the
  same distribution as $Y$`, `with joint distribution function $F$`, `with characteristic
  function $\varphi$`; and of several (`independent random vectors $X$ and $Y$`, `$X$ and $Y$
  are independent`, `identically distributed`);
* notions: the dimension of a random vector; its characteristic function, the complex
  function `t ↦ E[e^{i⟨t,X⟩}]` of the vectors of its dimension; its joint distribution
  function; its mean vector (expectation, expected value), of an integrable one; and the
  mean of its `i`th coordinate.

An article names the characteristic function by the notion (`For a random vector $X$, let
$\varphi_X$ denote the characteristic function of $X$.`).

The constants of the field are interpreted by `Leanify/Library/RandomVectorsModel.lean`; the
integrability and the means are terms of the core language with them. -/

namespace Leanify.RandomVectors
open Build Core

/-- Where the field stands in a vocabulary: the first constant and the type of `vectors`,
of `matrices`, of `complex`, and of the field itself. -/
structure Offs where
  cv : Nat
  tv : Nat
  cm : Nat
  tm : Nat
  cc : Nat
  tc : Nat
  co : Nat
  to : Nat
  deriving Repr

def any (_ : B) : B := tt
def inRange (i n : B) : B := and (isInt i) (and (le (num 1) i) (le i n))
/-- The outcomes: `[0,1]`. -/
def inOmega (w : B) : B := and (le (num 0) w) (le w (num 1))
/-- `ω ↦ f ω` is integrable, and its expectation. -/
def integ (f : B → B) : B := app2 (prim .integrableOn) (lamR f) (lamR inOmega)
def expect (f : B → B) : B := app2 (prim .integralOn) (lamR inOmega) (lamR f)

/-- The words of the field, with the indices that `o` gives. -/
def own (o : Offs) : Vocab :=
  let V : Ty := .base o.tv
  let M : Ty := .base o.tm
  let C : Ty := .base o.tc
  let RV : Ty := .base o.to
  -- (type, TeX name, Lean name), in the order of the indices after `o.co`
  let table : List (Ty × Codes × Codes) := [
    (RV ⟶ .real ⟶ .real ⟶ .real, w!"{#1}_{#2}(#3)", w!"Leanify.RandomVectors.coord"),          -- 0
    (RV ⟶ .prop, w!"\\operatorname{RVec}", w!"Leanify.RandomVectors.IsRVec"),                  -- 1
    (RV ⟶ .real, w!"\\dim", w!"Leanify.RandomVectors.dim"),                                    -- 2
    (.real ⟶ RV, w!"", w!"Leanify.RandomVectors.ofReal"),                                      -- 3
    (RV ⟶ RV ⟶ .prop, w!"\\dim #1=\\dim #2", w!"Leanify.RandomVectors.SameDim"),               -- 4
    (RV ⟶ RV ⟶ .prop, w!"\\operatorname{Scalable}(#1,#2)", w!"Leanify.RandomVectors.Scalable"), -- 5
    (RV ⟶ RV ⟶ RV, w!"+", w!"Leanify.RandomVectors.add"),                                      -- 6
    (RV ⟶ RV ⟶ RV, w!"-", w!"Leanify.RandomVectors.sub"),                                      -- 7
    (RV ⟶ RV, w!"-", w!"Leanify.RandomVectors.neg"),                                           -- 8
    (RV ⟶ RV ⟶ RV, w!"\\cdot", w!"Leanify.RandomVectors.mul"),                                 -- 9
    (RV ⟶ RV ⟶ .prop, w!"#1\\stackrel{d}{=}#2", w!"Leanify.RandomVectors.EqDist"),             -- 10
    (RV ⟶ RV ⟶ .prop, w!"#1\\perp #2", w!"Leanify.RandomVectors.Indep"),                       -- 11
    (V ⟶ RV, w!"", w!"Leanify.RandomVectors.ofVec"),                                           -- 12
    (M ⟶ RV ⟶ RV, w!"\\cdot", w!"Leanify.RandomVectors.act"),                                  -- 13
    (M ⟶ RV ⟶ .prop, w!"\\operatorname{Actable}(#1,#2)", w!"Leanify.RandomVectors.Actable"),   -- 14
    (RV ⟶ V ⟶ C, w!"\\varphi_{#1}(#2)", w!"Leanify.RandomVectors.charFun"),                    -- 15
    (RV ⟶ V ⟶ .real, w!"F_{#1}(#2)", w!"Leanify.RandomVectors.cdf"),                           -- 16
    (RV ⟶ (V ⟶ .real) ⟶ .prop, w!"#1\\sim #2", w!"Leanify.RandomVectors.HasCdf")]              -- 17
  let c (k : Nat) : B := const (o.co + k)
  let dimOf (x : B) : B := app (c 2) x
  -- `X_i(ω)`: the `i`-th coordinate at the outcome `ω`
  let coord (x i w : B) : B := app (app2 (c 0) x i) w
  -- (constants of `vectors`: the dimension and the `i`-th coordinate of a vector)
  let vdim (t : B) : B := app (const (o.cv + 0)) t
  let vcoord (i t : B) : B := app2 (const (o.cv + 10)) i t
  let coordInt (x i : B) : B := integ fun w => coord x i w
  let integrable (x : B) : B := allR fun i => imp (inRange i (dimOf x)) (coordInt x i)
  let mod (p : Phrase) (pre : Bool) (pred : Tm) (doc : String) : Modifier :=
    { phrase := p, prenominal := pre, ty := RV, pred, doc }
  let ofDim : Tm := close <| lamR fun n => lamT RV any fun x => eq (dimOf x) n
  let rel (p : Phrase) (k : Nat) (doc : String) : Modifier :=
    mod p false (close <| lamT RV any fun y => lamT RV any fun x => app2 (c k) x y) doc
  let coordMean (name : Phrase) : Notion :=
    { name, ty := .real ⟶ RV ⟶ .real,
      doms := [none, dom2 RV fun i x => and (inRange i (dimOf x)) (coordInt x i)],
      doc := "`E[X_i]`, for `1 ≤ i ≤ d` and an integrable coordinate",
      value := close <| lamR fun i => lamT RV (fun x => and (inRange i (dimOf x)) (coordInt x i)) fun x =>
        expect fun w => coord x i w }
  let mean (name : Phrase) : Notion :=
    { name, ty := RV ⟶ V, doms := [dom1 RV integrable],
      doc := "the vector of the expectations of the coordinates, of an integrable random vector",
      value := close <| lamT RV integrable fun x =>
        theT V fun m => and (eq (vdim m) (dimOf x))
          (allR fun i => imp (inRange i (dimOf x)) (eq (vcoord i m) (expect fun w => coord x i w))) }
  -- a function of the vectors of the dimension of the random vector
  let onVec (name : Phrase) (k : Nat) (cod : Ty) (doc : String) : Notion :=
    { name, ty := RV ⟶ V ⟶ cod, doc,
      value := close <| lamT RV any fun x => lamT V (fun t => eq (vdim t) (dimOf x)) fun t => app2 (c k) x t }
  { types := [w!"\\mathrm{RVec}"]
    consts := table.map (·.1)
    constNames := table.map (·.2.1)
    constLean := table.map (·.2.2)
    typeLean := [(w!"Leanify.RandomVectors.RVec", w!"Leanify.RandomVectors.RVec.zero")]
    modules := [w!"Leanify.Library.RandomVectorsModel"]
    nouns := [
      { sing := phrase!"random vector", plural := phrase!"random vectors", ty := RV, pred := close (c 1),
        doc := "a function of the outcome, on `[0,1]` with Lebesgue measure, into the real vectors of one dimension, with measurable coordinates (Mathlib `Measurable`)" }]
    mods := [
      mod phrase!"$v$-dimensional" true ofDim "with values in `ℝᵈ`",
      mod phrase!"in $\\mathbb{R}^v$" false ofDim "of dimension `d`",
      mod phrase!"in $\\mathbb{R}^{v}$" false ofDim "of dimension `d`",
      mod phrase!"of dimension $v$" false ofDim "with values in `ℝᵈ`",
      mod phrase!"integrable" true (close <| lamT RV any integrable) "every coordinate is integrable (Mathlib `Integrable`)",
      rel phrase!"independent of $v$" 11 "`P(X ≤ s, Y ≤ t) = P(X ≤ s) P(Y ≤ t)` for all vectors `s`, `t`, coordinatewise (Mathlib `IndepFun`)",
      rel phrase!"equal in distribution to $v$" 10 "the same dimension and the same joint distribution function (Mathlib `IdentDistrib`)",
      rel phrase!"with the same distribution as $v$" 10 "the same dimension and the same joint distribution function",
      mod phrase!"with joint distribution function $v$" false
        (close <| lamT (V ⟶ .real) any fun f => lamT RV any fun x => app2 (c 17) x f)
        "`P(X ≤ t) = F(t)` for every vector `t` of the dimension of `X`, coordinatewise (Mathlib `HasLaw`, by the distribution function)",
      mod phrase!"with characteristic function $v$" false
        (close <| lamT (V ⟶ C) any fun f => lamT RV any fun x =>
          allT V fun t => imp (eq (vdim t) (dimOf x)) (eq (app2 (c 15) x t) (app f t)))
        "`E[e^{i⟨t,X⟩}] = φ(t)` for every vector `t` of the dimension of `X` (Mathlib `charFun`)"]
    notions := [
      { name := phrase!"dimension of $v$", value := close (c 2), ty := RV ⟶ .real, doc := "`d`, for a random vector with values in `ℝᵈ`" },
      onVec phrase!"characteristic function of $v$" 15 C "`t ↦ E[e^{i⟨t,X⟩}]`, on the vectors of the dimension of `X` (Mathlib `charFun`)",
      onVec phrase!"joint distribution function of $v$" 16 .real "`t ↦ P(X ≤ t)`, coordinatewise, on the vectors of the dimension of `X`",
      mean phrase!"mean vector of $v$", mean phrase!"expectation of $v$", mean phrase!"expected value of $v$",
      coordMean phrase!"mean of the $v$th coordinate of $v$", coordMean phrase!"expectation of the $v$th coordinate of $v$",
      coordMean phrase!"expected value of the $v$th coordinate of $v$"]
    methods := [
      { ty := RV, op := .ofReal, const := o.co + 3, doc := "a real number `c` as the constant random vector `(c)` of dimension 1" },
      { ty := RV, op := .add, const := o.co + 6, doc := "`X + Y`, of the same dimension", dom := some (close (c 4)) },
      { ty := RV, op := .sub, const := o.co + 7, doc := "`X - Y`, of the same dimension", dom := some (close (c 4)) },
      { ty := RV, op := .neg, const := o.co + 8, doc := "`-X`" },
      { ty := RV, op := .mul, const := o.co + 9, doc := "`cX`, for a random vector `c` of dimension 1 (a number)", dom := some (close (c 5)) },
      { ty := RV, op := .fn w!"@identdist", const := o.co + 10,
        doc := "`X\\stackrel{d}{=}Y`, `identically distributed`: the same dimension and the same joint distribution function" },
      { ty := RV, op := .fn w!"@indep", const := o.co + 11,
        doc := "`independent`, of two random vectors: the joint distribution function of the coordinates of both is the product of theirs" },
      { ty := RV, op := .fn w!"@of", const := o.co + 12, doc := "a vector `b` as the constant random vector (`X + b`)" },
      { ty := RV, op := .fn w!"@act", const := o.co + 13, dom := some (close (c 14)),
        doc := "`AX`, for a matrix `A` with as many columns as `X` has coordinates: `ω ↦ A X(ω)`" },
      { ty := RV, op := .fn w!"@sim", const := o.co + 17,
        doc := "`X\\sim F`, for a function `F` of vectors: `F` is the joint distribution function of `X`" }] }

/-- The field in a vocabulary of its own: after `vectors`, `matrices` and `complex`. -/
def vocab : Vocab :=
  let G := Vocab.tag w!"vectors" Vectors.vocab ++ Vocab.tag w!"matrices" Matrices.vocab ++ Vocab.tag w!"complex" Complex.vocab
  let nv := Vectors.vocab.consts.length
  let nm := Matrices.vocab.consts.length
  G.join (Vocab.tag w!"randomvectors" (own
    { cv := 0, tv := 0, cm := nv, tm := 1, cc := nv + nm, tc := 2, co := G.consts.length, to := 3 }))

end Leanify.RandomVectors
