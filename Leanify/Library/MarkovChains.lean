import Leanify.Library.MatrixNorms

/-! # Vocabulary: finite Markov chains

Markov chains on the states `1, …, n` through their transition matrices, the real matrices
of the field `matrices` (with `matrixnorms`, which this field includes): `Let $P$ be an
irreducible stochastic matrix.`, `$\pi$ is a stationary distribution of $P$`. A
distribution on the states is a real function whose values at `1, …, n` are the
probabilities.

* adjectives of matrices: `doubly stochastic`, `irreducible` (every state leads to every
  state: `(P^k)_{ij} > 0` for some `k ≥ 1`), `primitive` (some power has positive entries);
* adjectives of states: `absorbing state of $P$` (`P_{ii} = 1`);
* adjectives of functions: `stationary distribution of $P$` (`π ≥ 0`, `∑ π_i = 1`,
  `∑_i π_i P_{ij} = π_j`), `reversible distribution for $P$` (stationary and
  `π_i P_{ij} = π_j P_{ji}`), `probability distribution on $n$ states`;
* notions: the transition probability from `i` to `j` in `k` steps (`(P^k)_{ij}`), the
  distribution after `k` steps from `μ` (`j ↦ ∑_i μ_i (P^k)_{ij}`), the stationary
  probability of a state (of an irreducible stochastic matrix, which has exactly one
  stationary distribution).

Every meaning is a term of the core language with the constants of `matrices` (entries,
powers, sizes). -/

namespace Leanify.MarkovChains
open Build Core
open Leanify.Matrices (M)

abbrev F : Ty := Ty.rfun

def rows (a : B) : B := app (const Matrices.Const.rows) a
def entry (a i j : B) : B := app (app (app (const Matrices.Const.entry) a) i) j
def pow (a k : B) : B := app2 (const Matrices.Const.pow) a k
def square (a : B) : B := app (const Matrices.Const.square) a
def stochastic (a : B) : B := app (const Matrices.Const.stochastic) a
def finSum (a b : B) (body : B → B) : B := app (app (app (prim .finSum) a) b) (lamR body)
def inRange (i n : B) : B := and (isInt i) (and (le (num 1) i) (le i n))
def natP (k : B) : B := and (isInt k) (le (num 0) k)
def posNat (k : B) : B := and (isInt k) (le (num 1) k)
def forStates (a : B) (body : B → B) : B := allR fun i => imp (inRange i (rows a)) (body i)
def irreducible (a : B) : B :=
  and (square a) (forStates a fun i => forStates a fun j => exR fun k => and (posNat k) (lt (num 0) (entry (pow a k) i j)))
def primitive (a : B) : B :=
  and (square a) (exR fun k => and (posNat k) (forStates a fun i => forStates a fun j => lt (num 0) (entry (pow a k) i j)))
def distOn (n p : B) : B :=
  and (allR fun i => imp (inRange i n) (le (num 0) (app p i))) (eq (finSum (num 1) n fun i => app p i) (num 1))
def stationary (a p : B) : B :=
  and (square a) (and (distOn (rows a) p)
    (forStates a fun j => eq (finSum (num 1) (rows a) fun i => mul (app p i) (entry a i j)) (app p j)))
def mPred (p : B → B) : Tm := close <| lamT M (fun _ => tt) p
def adjM (p : Phrase) (pre : Bool) (body : B → B) (doc : String) : Modifier :=
  { phrase := p, prenominal := pre, ty := M, pred := mPred body, doc }
def ergodic (a : B) : B := and (stochastic a) (irreducible a)

/-- The words of the field itself. -/
def own : Vocab where
  mods := [
    adjM phrase!"doubly stochastic" true
      (fun a => and (stochastic a) (forStates a fun j => eq (finSum (num 1) (rows a) fun i => entry a i j) (num 1)))
      "stochastic, and the columns sum to `1`",
    adjM phrase!"irreducible" true irreducible "square, and for all states `i`, `j` some `(P^k)_{ij} > 0` with `k ≥ 1`",
    adjM phrase!"primitive" true primitive "square, and some power `P^k`, `k ≥ 1`, has positive entries",
    { phrase := phrase!"absorbing state of $v$", prenominal := false, ty := .real,
      pred := close <| lamT M (fun _ => tt) fun a => lamR fun i => and (inRange i (rows a)) (eq (entry a i i) (num 1)),
      doc := "a state `i` with `P_{ii} = 1`" },
    { phrase := phrase!"stationary distribution of $v$", prenominal := false, ty := F,
      pred := close <| lamT M (fun _ => tt) fun a => lamT F (fun _ => tt) fun p => stationary a p,
      doc := "`π_i ≥ 0`, `∑ π_i = 1`, `∑_i π_i P_{ij} = π_j` for the states `1, …, n`" },
    { phrase := phrase!"reversible distribution for $v$", prenominal := false, ty := F,
      pred := close <| lamT M (fun _ => tt) fun a => lamT F (fun _ => tt) fun p =>
        and (stationary a p) (forStates a fun i => forStates a fun j => eq (mul (app p i) (entry a i j)) (mul (app p j) (entry a j i))),
      doc := "stationary, and `π_i P_{ij} = π_j P_{ji}` (detailed balance)" },
    { phrase := phrase!"probability distribution on $v$ states", prenominal := false, ty := F,
      pred := close <| lamR fun n => lamT F (fun _ => tt) fun p => and (posNat n) (distOn n p),
      doc := "`p_i ≥ 0` for `1 ≤ i ≤ n` and `∑ p_i = 1`" }]
  notions := [
    { name := phrase!"transition probability from $v$ to $v$ in $v$ steps under $v$", ty := .real ⟶ .real ⟶ .real ⟶ M ⟶ .real,
      doms := [none, none, dom1 .real natP,
        dom4 M fun i j _ a => and (square a) (and (inRange i (rows a)) (inRange j (rows a)))],
      doc := "`(P^k)_{ij}`, for a square `P` and states `i`, `j`",
      value := close <| lamR fun i => lamR fun j => lamT .real natP fun k =>
        lamT M (fun a => and (square a) (and (inRange i (rows a)) (inRange j (rows a)))) fun a => entry (pow a k) i j },
    { name := phrase!"distribution after $v$ steps under $v$ from $v$", ty := .real ⟶ M ⟶ F ⟶ F,
      doms := [dom1 .real natP, dom1 M square, none],
      doc := "`j ↦ ∑_i μ_i (P^k)_{ij}`",
      value := close <| lamT .real natP fun k => lamT M square fun a => lamT F (fun _ => tt) fun mu => lamR fun j =>
        finSum (num 1) (rows a) fun i => mul (app mu i) (entry (pow a k) i j) },
    { name := phrase!"stationary probability of $v$ under $v$", ty := .real ⟶ M ⟶ .real,
      doms := [none, dom2 M fun i a => and (ergodic a) (inRange i (rows a))],
      doc := "`π_i` for the stationary distribution `π` of an irreducible stochastic `P` (there is exactly one)",
      value := close <| lamR fun i => lamT M (fun a => and (ergodic a) (inRange i (rows a))) fun a =>
        theR fun q => exT F fun p => and (stationary a p) (eq (app p i) q) }]

/-- `matrixnorms` (with `matrices`) and these words, as one vocabulary. -/
def vocab : Vocab :=
  let G := MatrixNorms.vocab
  let O := Vocab.tag w!"markovchains" own
  { G with mods := G.mods ++ O.mods, notions := G.notions ++ O.notions }

end Leanify.MarkovChains
