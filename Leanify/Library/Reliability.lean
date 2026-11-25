import Leanify.Library.Core

/-! # Vocabulary: reliability of systems

The reliability of systems of independent components from that of the components
(`We write $R_{k,n}(p)$ for the reliability of the $k$-out-of-$n$ system with component
reliability $p$.`), and lifetimes with constant failure rates.

* notions: the reliability of a series and of a parallel system of `n` components with
  reliability `p` (`p^n`, `1-(1-p)^n`), of the `k`-out-of-`n` system
  (`∑_{i=k}^{n} \binom{n}{i} p^i (1-p)^{n-i}`), of a series and a parallel system of
  components `1, …, n` with reliabilities `p_1, …, p_n` (`∏ p_i`, `1 - ∏ (1-p_i)`), of a
  bridge of five components with reliability `p` (`2p² + 2p³ - 5p⁴ + 2p⁵`); the reliability at
  time `t` of a component with constant failure rate `λ` (`e^{-λt}`), the mean time to
  failure of a series and of a parallel system of `n` such components (`1/(nλ)`,
  `(1/λ) ∑_{i=1}^{n} 1/i`); the availability `MTTF/(MTTF + MTTR)`.

Every meaning is a term of the core language. -/

namespace Leanify.Reliability
open Build Core

abbrev F : Ty := Ty.rfun

def prob (p : B) : B := and (le (num 0) p) (le p (num 1))
def posInt (k : B) : B := and (isInt k) (le (num 1) k)
def pos (x : B) : B := lt (num 0) x
def zpow (x k : B) : B := app2 (prim .zpow) x k
def binom (n k : B) : B := app2 (prim .binom) n k
def finSum (a b : B) (body : B → B) : B := app (app (app (prim .finSum) a) b) (lamR body)
def finProd (a b : B) (body : B → B) : B := app (app (app (prim .finProd) a) b) (lamR body)
def exp (x : B) : B := app (prim (.realFn .exp)) x
def probs (n p : B) : B := allR fun i => imp (and (isInt i) (and (le (num 1) i) (le i n))) (prob (app p i))
def kOfN (k n p : B) : B := finSum k n fun i => mul (binom n i) (mul (zpow p i) (zpow (sub (num 1) p) (sub n i)))
def np (name : Phrase) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real posInt, dom1 .real prob], doc,
    value := close <| lamT .real posInt fun n => lamT .real prob fun p => body n p }
def nps (name : Phrase) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ F ⟶ .real, doms := [dom1 .real posInt, dom2 F probs], doc,
    value := close <| lamT .real posInt fun n => lamT F (fun p => probs n p) fun p => body n p }

def vocab : Vocab where
  notions := [
    np phrase!"reliability of the series system of $v$ components with reliability $v$" (fun n p => zpow p n) "`p^n`",
    np phrase!"reliability of the parallel system of $v$ components with reliability $v$"
      (fun n p => sub (num 1) (zpow (sub (num 1) p) n)) "`1 - (1-p)^n`",
    { name := phrase!"reliability of the $v$-out-of-$v$ system with component reliability $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real posInt, dom2 .real fun k n => and (posInt n) (le k n), dom1 .real prob],
      doc := "`∑_{i=k}^{n} \\binom{n}{i} p^i (1-p)^{n-i}`: at least `k` of `n` independent components work",
      value := close <| lamT .real posInt fun k => lamT .real (fun n => and (posInt n) (le k n)) fun n => lamT .real prob fun p => kOfN k n p },
    nps phrase!"reliability of the series system of the first $v$ components with reliabilities $v$"
      (fun n p => finProd (num 1) n fun i => app p i) "`∏_{i=1}^{n} p_i`",
    nps phrase!"reliability of the parallel system of the first $v$ components with reliabilities $v$"
      (fun n p => sub (num 1) (finProd (num 1) n fun i => sub (num 1) (app p i))) "`1 - ∏_{i=1}^{n} (1-p_i)`",
    { name := phrase!"reliability of the bridge system with component reliability $v$", ty := .real ⟶ .real,
      doms := [dom1 .real prob], doc := "`2p² + 2p³ - 5p⁴ + 2p⁵`, five components",
      value := close <| lamT .real prob fun p =>
        add (sub (add (mul (num 2) (zpow p (num 2))) (mul (num 2) (zpow p (num 3)))) (mul (num 5) (zpow p (num 4)))) (mul (num 2) (zpow p (num 5))) },
    { name := phrase!"reliability at time $v$ of a component with failure rate $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun t => le (num 0) t, dom1 .real pos], doc := "`e^{-λt}`",
      value := close <| lamT .real (fun t => le (num 0) t) fun t => lamT .real pos fun l => exp (neg (mul l t)) },
    { name := phrase!"mean time to failure of the series system of $v$ components with failure rate $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real posInt, dom1 .real pos], doc := "`1/(nλ)`",
      value := close <| lamT .real posInt fun n => lamT .real pos fun l => div (num 1) (mul n l) },
    { name := phrase!"mean time to failure of the parallel system of $v$ components with failure rate $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real posInt, dom1 .real pos], doc := "`(1/λ) ∑_{i=1}^{n} 1/i`",
      value := close <| lamT .real posInt fun n => lamT .real pos fun l => div (finSum (num 1) n fun i => div (num 1) i) l },
    { name := phrase!"availability with mean time to failure $v$ and mean time to repair $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom1 .real fun r => le (num 0) r], doc := "`MTTF/(MTTF + MTTR)`",
      value := close <| lamT .real pos fun f => lamT .real (fun r => le (num 0) r) fun r => div f (add f r) }]

end Leanify.Reliability
