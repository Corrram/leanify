import Leanify.Library.Core

/-! # Vocabulary: Poisson processes

Arrival counts and waiting times of a homogeneous Poisson process, by its rate (`We write
$p(k,t,\lambda)$ for the probability of $k$ arrivals by time $t$ at rate $\lambda$.`). The Poisson
distribution as an object is in the field `distributions`.

* notions: the probability of `k` arrivals by time `t`; the probability of at least one
  arrival; the expected waiting time for the `k`th arrival; the probability that the `k`th
  arrival comes after `t`; the rate of a thinned process; the mean and variance of a compound
  Poisson sum.

The quantities are constants, interpreted by the declarations of
`Leanify/Library/PoissonProcessesModel.lean`: the probabilities and expectations of the
process of independent exponential interarrival times (Mathlib `expMeasure`,
`Measure.infinitePi`), of its thinning, and of its compound sums for every law of the jumps
with the given mean and variance. The formulas (`e^{-λt}(λt)^k/k!`, `1 - e^{-λt}`, `k/λ`
(Erlang), `∑_{j<k} e^{-λt}(λt)^j/j!`, `pλ`, `λtμ`, `λt(σ² + μ²)`) are theorems, not
definitions. -/

namespace Leanify.PoissonProcesses
open Build Core

def pos (x : B) : B := lt (num 0) x
def natP (n : B) : B := and (isInt n) (le (num 0) n)
def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def nonneg (t : B) : B := le (num 0) t

/-! The indices of the constants (apart from the names of their meanings). -/
namespace Const
def probArrivals : Nat := 0
def probSomeArrival : Nat := 1
def waiting : Nat := 2
def probLate : Nat := 3
def thinnedRate : Nat := 4
def compoundMean : Nat := 5
def compoundVariance : Nat := 6
end Const

def vocab : Vocab where
  consts := [.real ⟶ .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real ⟶ .real,
    .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real ⟶ .real, .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real]
  constNames := [w!"P(N_{#2}=#1)_{#3}", w!"P(N_{#1}\\ge1)_{#2}", w!"\\mathbb{E}S_{#1}(#2)", w!"P(S_{#1}>#2)_{#3}",
    w!"\\lambda_{#1,#2}", w!"\\mathbb{E}X_{#1}(#2,#3)", w!"\\operatorname{Var}X"]
  constLean := [w!"Leanify.PoissonProcesses.probArrivals", w!"Leanify.PoissonProcesses.probSomeArrival",
    w!"Leanify.PoissonProcesses.waiting", w!"Leanify.PoissonProcesses.probLate", w!"Leanify.PoissonProcesses.thinnedRate",
    w!"Leanify.PoissonProcesses.compoundMean", w!"Leanify.PoissonProcesses.compoundVariance"]
  modules := [w!"Leanify.Library.PoissonProcessesModel"]
  notions := [
    { name := phrase!"probability of $v$ arrivals by time $v$ at rate $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real natP, dom2 .real fun _ t => nonneg t, dom3 .real fun _ _ l => pos l],
      doc := "the probability that `N_t = k` (`e^{-λt}(λt)^k/k!`)", value := .const Const.probArrivals },
    { name := phrase!"probability of an arrival by time $v$ at rate $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real nonneg, dom2 .real fun _ l => pos l], doc := "the probability that `N_t ≥ 1` (`1 - e^{-λt}`)",
      value := .const Const.probSomeArrival },
    { name := phrase!"expected waiting time for the $v$th arrival at rate $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real posInt, dom2 .real fun _ l => pos l], doc := "the expectation of the `k`th arrival time (`k/λ`, Erlang)",
      value := .const Const.waiting },
    { name := phrase!"probability that the $v$th arrival comes after time $v$ at rate $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real posInt, dom2 .real fun _ t => nonneg t, dom3 .real fun _ _ l => pos l],
      doc := "(`∑_{j=0}^{k-1} e^{-λt}(λt)^j/j!`)", value := .const Const.probLate },
    { name := phrase!"rate of the process with rate $v$ thinned with probability $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ p => and (le (num 0) p) (le p (num 1))],
      doc := "the mean number of kept arrivals by time `1`, each arrival kept with probability `p` (`pλ`)",
      value := .const Const.thinnedRate },
    { name := phrase!"mean of the compound Poisson sum at time $v$ with rate $v$ and jump mean $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real nonneg, dom2 .real fun _ l => pos l, none],
      doc := "the expectation of the sum of independent jumps with mean `μ` at the arrivals by `t` (`λtμ`)",
      value := .const Const.compoundMean },
    { name := phrase!"variance of the compound Poisson sum at time $v$ with rate $v$, jump mean $v$ and jump variance $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real nonneg, dom2 .real fun _ l => pos l, none, dom4 .real fun _ _ _ v => le (num 0) v],
      doc := "for every law of the jumps with mean `μ` and variance `σ²` (`λt(σ² + μ²)`)", value := .const Const.compoundVariance }]

end Leanify.PoissonProcesses
