import Leanify.Library.Core

/-! # Vocabulary: population genetics

The classical formulas of population genetics, by allele frequencies, fitnesses and population
sizes (`We write $\pi(r,N)$ for the fixation probability of a mutant with fitness $r$ in a Moran
population of size $N$.`).

* notions: the Hardy–Weinberg frequencies `p²` of homozygotes and `2p(1-p)` of heterozygotes
  for an allele of frequency `p`; the frequency `pr/(pr + 1 - p)` after one generation of
  selection with relative fitness `r`; the fixation probability `(1 - 1/r)/(1 - 1/r^N)` of a
  mutant with fitness `r` in a Moran population of size `N` (`1/N` for `r = 1`) and Kimura's
  `(1 - e^{-2s})/(1 - e^{-4Ns})` for a selection coefficient `s` (`1/(2N)` for `s = 0`); the
  heterozygosity `H(1 - 1/(2N))^t` after `t` generations of drift; the effective size
  `4N_m N_f/(N_m + N_f)` of a population with `N_m` males and `N_f` females; the equilibrium
  frequency `ν/(μ + ν)` under forward and backward mutation rates `μ`, `ν`.

Every meaning is a term of the core language. -/

namespace Leanify.PopulationGenetics
open Build Core

def unit (p : B) : B := and (le (num 0) p) (le p (num 1))
def pos (x : B) : B := lt (num 0) x
def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def natP (n : B) : B := and (isInt n) (le (num 0) n)
def zpow (x k : B) : B := app2 (prim .zpow) x k
def exp (x : B) : B := app (prim (.realFn .exp)) x

def vocab : Vocab where
  notions := [
    { name := phrase!"homozygote frequency for an allele with frequency $v$", ty := .real ⟶ .real, doms := [dom1 .real unit],
      doc := "`p²` (Hardy–Weinberg)", value := close <| lamT .real unit fun p => mul p p },
    { name := phrase!"heterozygote frequency for an allele with frequency $v$", ty := .real ⟶ .real, doms := [dom1 .real unit],
      doc := "`2p(1-p)` (Hardy–Weinberg, two alleles)", value := close <| lamT .real unit fun p => mul (num 2) (mul p (sub (num 1) p)) },
    { name := phrase!"frequency after selection of an allele with frequency $v$ and relative fitness $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real unit, dom2 .real fun _ r => pos r],
      doc := "`pr/(pr + 1 - p)`: one generation of haploid selection",
      value := close <| lamT .real unit fun p => lamT .real pos fun r => div (mul p r) (add (mul p r) (sub (num 1) p)) },
    { name := phrase!"fixation probability of a mutant with fitness $v$ in a Moran population of size $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ n => posInt n],
      doc := "`(1 - 1/r)/(1 - 1/r^N)`, and `1/N` for `r = 1`: one mutant among `N` individuals",
      value := close <| lamT .real pos fun r => lamT .real posInt fun n =>
        cases (eq r (num 1)) (div (num 1) n) (div (sub (num 1) (div (num 1) r)) (sub (num 1) (div (num 1) (zpow r n)))) },
    { name := phrase!"Kimura fixation probability for selection coefficient $v$ and population size $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [none, dom2 .real fun _ n => posInt n],
      doc := "`(1 - e^{-2s})/(1 - e^{-4Ns})`, and `1/(2N)` for `s = 0` (diffusion approximation, one new mutant)",
      value := close <| lamR fun s => lamT .real posInt fun n =>
        cases (eq s (num 0)) (div (num 1) (mul (num 2) n))
          (div (sub (num 1) (exp (neg (mul (num 2) s)))) (sub (num 1) (exp (neg (mul (num 4) (mul n s)))))) },
    { name := phrase!"heterozygosity after $v$ generations in a population of size $v$ with initial heterozygosity $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real natP, dom2 .real fun _ n => posInt n, dom3 .real fun _ _ h => unit h],
      doc := "`H(1 - 1/(2N))^t` (Wright–Fisher drift)",
      value := close <| lamT .real natP fun t => lamT .real posInt fun n => lamT .real unit fun h =>
        mul h (zpow (sub (num 1) (div (num 1) (mul (num 2) n))) t) },
    { name := phrase!"effective size of a population with $v$ males and $v$ females", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real posInt, dom2 .real fun _ f => posInt f],
      doc := "`4N_m N_f/(N_m + N_f)`",
      value := close <| lamT .real posInt fun m => lamT .real posInt fun f => div (mul (num 4) (mul m f)) (add m f) },
    { name := phrase!"equilibrium frequency for the forward mutation rate $v$ and the backward mutation rate $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ v => pos v],
      doc := "`ν/(μ + ν)`: the frequency of the allele that mutates away at rate `μ` and back at rate `ν`",
      value := close <| lamT .real pos fun m => lamT .real pos fun v => div v (add m v) }]

end Leanify.PopulationGenetics
