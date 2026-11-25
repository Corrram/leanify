import Leanify.Library.Vectors

/-! # Vocabulary: majorization

Majorization of real vectors (the field `vectors`, which this field includes), as in
Marshall, Olkin and Arnold: `$x$ is majorized by $y$`, `the $k$th largest coordinate of $x$`.

* notions: the `k`th largest coordinate `x_{[k]}` of a vector of dimension `n ≥ k`, the sum of
  its `k` largest coordinates, the positive-part sum `∑ (x_i - t)^+`;
* adjectives of vectors: `majorized by $y$` (the same dimension and sum, and `∑_{i≤k} x_{[i]} ≤
  ∑_{i≤k} y_{[i]}` for every `k`), `weakly submajorized by $y$` (the partial sums only),
  `weakly supermajorized by $y$` (`∑_{i≤k} x_{(i)} ≥ ∑_{i≤k} y_{(i)}` for the smallest
  coordinates), `decreasingly ordered` (`x_1 ≥ x_2 ≥ …`).

Every meaning is a term of the core language with the constants of `vectors` (dimension,
coordinates). -/

namespace Leanify.Majorization
open Build Core
open Leanify.Vectors (V)

def dim (x : B) : B := app (const 0) x
def coord (i x : B) : B := app2 (const 10) i x
def finSum (a b : B) (body : B → B) : B := app (app (app (prim .finSum) a) b) (lamR body)
def countGe (x t : B) : B := finSum (num 1) (dim x) fun i => cases (le t (coord i x)) (num 1) (num 0)
def countGt (x t : B) : B := finSum (num 1) (dim x) fun i => cases (lt t (coord i x)) (num 1) (num 0)
def inRange (i n : B) : B := and (isInt i) (and (le (num 1) i) (le i n))
/-- `t` is the `k`th largest coordinate: fewer than `k` coordinates exceed it, at least `k` are at least it. -/
def kth (k x : B) : B :=
  theR fun t => and (exR fun i => and (inRange i (dim x)) (eq (coord i x) t)) (and (lt (countGt x t) k) (le k (countGe x t)))
def kthSmall (k x : B) : B := kth (add (sub (dim x) k) (num 1)) x
def topSum (k x : B) : B := finSum (num 1) k fun j => kth j x
def bottomSum (k x : B) : B := finSum (num 1) k fun j => kthSmall j x
def forK (x : B) (body : B → B) : B := allR fun k => imp (inRange k (dim x)) (body k)
def sameDim (x y : B) : B := eq (dim x) (dim y)
def total (x : B) : B := finSum (num 1) (dim x) fun i => coord i x
def any (_ : B) : B := tt
def rel (p : Phrase) (body : B → B → B) (doc : String) : Modifier :=
  { phrase := p, prenominal := false, ty := V, doc, pred := close <| lamT V any fun y => lamT V any fun x => body y x }

/-- The words of the field itself. -/
def own : Vocab where
  mods := [
    rel phrase!"majorized by $v$" (fun y x => and (sameDim x y) (and (eq (total x) (total y)) (forK x fun k => le (topSum k x) (topSum k y))))
      "`∑_{i≤k} x_{[i]} ≤ ∑_{i≤k} y_{[i]}` for every `k`, with equality for `k = n`",
    rel phrase!"weakly submajorized by $v$" (fun y x => and (sameDim x y) (forK x fun k => le (topSum k x) (topSum k y)))
      "`∑_{i≤k} x_{[i]} ≤ ∑_{i≤k} y_{[i]}` for every `k`",
    rel phrase!"weakly supermajorized by $v$" (fun y x => and (sameDim x y) (forK x fun k => le (bottomSum k y) (bottomSum k x)))
      "`∑_{i≤k} x_{(i)} ≥ ∑_{i≤k} y_{(i)}` for every `k`, the smallest coordinates",
    { phrase := phrase!"decreasingly ordered", prenominal := true, ty := V,
      pred := close <| lamT V any fun x => allR fun i => imp (and (inRange i (dim x)) (lt i (dim x))) (le (coord (add i (num 1)) x) (coord i x)),
      doc := "`x_1 ≥ x_2 ≥ … ≥ x_n`" }]
  notions := [
    { name := phrase!"$v$th largest coordinate of $v$", ty := .real ⟶ V ⟶ .real,
      doms := [none, dom2 V fun k x => inRange k (dim x)], doc := "`x_{[k]}`, `1 ≤ k ≤ n`",
      value := close <| lamR fun k => lamT V (fun x => inRange k (dim x)) fun x => kth k x },
    { name := phrase!"sum of the $v$ largest coordinates of $v$", ty := .real ⟶ V ⟶ .real,
      doms := [none, dom2 V fun k x => and (isInt k) (and (le (num 0) k) (le k (dim x)))], doc := "`∑_{i=1}^{k} x_{[i]}`",
      value := close <| lamR fun k => lamT V (fun x => and (isInt k) (and (le (num 0) k) (le k (dim x)))) fun x => topSum k x },
    { name := phrase!"positive-part sum of $v$ at $v$", ty := V ⟶ .real ⟶ .real, doc := "`∑_i (x_i - t)^+`",
      value := close <| lamT V any fun x => lamR fun t => finSum (num 1) (dim x) fun i => app2 (prim .max) (sub (coord i x) t) (num 0) }]

/-- `vectors` and these words, as one vocabulary. -/
def vocab : Vocab :=
  let G := Vocab.tag w!"vectors" Vectors.vocab
  let O := Vocab.tag w!"majorization" own
  { G with mods := G.mods ++ O.mods, notions := G.notions ++ O.notions }

end Leanify.Majorization
