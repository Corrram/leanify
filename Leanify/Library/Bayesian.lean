import Leanify.Library.Core

/-! # Vocabulary: conjugate Bayesian updating

The posteriors of the standard conjugate families, by their parameters (`We write $m$ for
the posterior mean of the beta prior with parameters $a$ and $b$ after $k$ successes in $n$
trials.`), and Bayes' formula for two hypotheses.

* notions: for a beta prior with parameters `a, b > 0` and binomial data (`k` successes in
  `n` trials): the posterior parameters `a + k`, `b + n - k`, the posterior mean
  `(a+k)/(a+b+n)` and mode `(a+k-1)/(a+b+n-2)`; for a gamma prior with shape `α` and rate `β`
  and Poisson counts with sum `s` over `n` observations: the posterior mean `(α+s)/(β+n)`; for
  a normal prior with mean `μ₀` and variance `τ²` and `n` normal observations with variance
  `σ²` and mean `x̄`: the posterior mean `(μ₀/τ² + n x̄/σ²)/(1/τ² + n/σ²)` and variance
  `1/(1/τ² + n/σ²)`; the posterior probability of `H` from the prior `P(H)` and the likelihoods
  `P(E|H)`, `P(E|¬H)` (`P(E|H)P(H)/(P(E|H)P(H) + P(E|¬H)(1-P(H)))`); the Bayes factor.

Every meaning is a term of the core language. -/

namespace Leanify.Bayesian
open Build Core

def pos (x : B) : B := lt (num 0) x
def prob (p : B) : B := and (le (num 0) p) (le p (num 1))
def natP (k : B) : B := and (isInt k) (le (num 0) k)
def dataOk (k n : B) : B := and (natP n) (and (natP k) (le k n))
def betaBin (name : Phrase) (body : B → B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
    doms := [dom1 .real pos, dom1 .real pos, none, dom4 .real fun _ _ k n => dataOk k n], doc,
    value := close <| lamT .real pos fun a => lamT .real pos fun b => lamR fun k =>
      lamT .real (fun n => dataOk k n) fun n => body a b k n }
def precision (t2 n s2 : B) : B := add (div (num 1) t2) (div n s2)

def vocab : Vocab where
  notions := [
    betaBin phrase!"posterior mean of the beta prior with parameters $v$ and $v$ after $v$ successes in $v$ trials"
      (fun a b k n => div (add a k) (add (add a b) n)) "`(a+k)/(a+b+n)`",
    { name := phrase!"posterior mode of the beta prior with parameters $v$ and $v$ after $v$ successes in $v$ trials",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom1 .real pos, none, dom4 .real fun a b k n => and (dataOk k n) (and (lt (num 1) (add a k)) (lt (num 1) (sub (add b n) k)))],
      doc := "`(a+k-1)/(a+b+n-2)`, where both posterior parameters exceed `1`",
      value := close <| lamT .real pos fun a => lamT .real pos fun b => lamR fun k =>
        lamT .real (fun n => and (dataOk k n) (and (lt (num 1) (add a k)) (lt (num 1) (sub (add b n) k)))) fun n =>
          div (sub (add a k) (num 1)) (sub (add (add a b) n) (num 2)) },
    betaBin phrase!"first posterior parameter of the beta prior with parameters $v$ and $v$ after $v$ successes in $v$ trials"
      (fun a _ k _ => add a k) "`a + k`",
    betaBin phrase!"second posterior parameter of the beta prior with parameters $v$ and $v$ after $v$ successes in $v$ trials"
      (fun _ b k n => sub (add b n) k) "`b + n - k`",
    { name := phrase!"posterior mean of the gamma prior with shape $v$ and rate $v$ after $v$ observations with sum $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom1 .real pos, dom1 .real natP, dom1 .real fun s => le (num 0) s],
      doc := "`(α+s)/(β+n)`, Poisson data",
      value := close <| lamT .real pos fun al => lamT .real pos fun be => lamT .real natP fun n =>
        lamT .real (fun s => le (num 0) s) fun s => div (add al s) (add be n) },
    { name := phrase!"posterior mean of the normal prior with mean $v$ and variance $v$ after $v$ observations with mean $v$ and variance $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, dom1 .real pos, dom1 .real natP, none, dom1 .real pos],
      doc := "`(μ₀/τ² + n x̄/σ²)/(1/τ² + n/σ²)`",
      value := close <| lamR fun m0 => lamT .real pos fun t2 => lamT .real natP fun n => lamR fun xb => lamT .real pos fun s2 =>
        div (add (div m0 t2) (div (mul n xb) s2)) (precision t2 n s2) },
    { name := phrase!"posterior variance of the normal prior with variance $v$ after $v$ observations with variance $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real, doms := [dom1 .real pos, dom1 .real natP, dom1 .real pos],
      doc := "`1/(1/τ² + n/σ²)`",
      value := close <| lamT .real pos fun t2 => lamT .real natP fun n => lamT .real pos fun s2 => div (num 1) (precision t2 n s2) },
    { name := phrase!"posterior probability with prior $v$ and likelihoods $v$ and $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real prob, dom1 .real prob, dom3 .real fun h l1 l0 => and (prob l0) (pos (add (mul l1 h) (mul l0 (sub (num 1) h))))],
      doc := "`P(E|H)P(H)/(P(E|H)P(H) + P(E|¬H)(1-P(H)))`, Bayes' formula",
      value := close <| lamT .real prob fun h => lamT .real prob fun l1 =>
        lamT .real (fun l0 => and (prob l0) (pos (add (mul l1 h) (mul l0 (sub (num 1) h))))) fun l0 =>
          div (mul l1 h) (add (mul l1 h) (mul l0 (sub (num 1) h))) },
    { name := phrase!"Bayes factor with likelihoods $v$ and $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [none, dom1 .real pos], doc := "`P(E|H₁)/P(E|H₀)`",
      value := close <| lamR fun l1 => lamT .real pos fun l0 => div l1 l0 }]

end Leanify.Bayesian
