import Leanify.Library.Core

/-! # Vocabulary: entropy and divergences

Information measures of probability distributions on `ℕ₀`, read as in the field
`distributions` (weights `p(k)` at the natural numbers, which that field binds:
`Let $p$ and $q$ be probability distributions on $\mathbb{N}_0$.`), with the natural
logarithm and `0 log 0 = 0`:

* the entropy `H(p) = -∑ p(k) log p(k)`, the Rényi entropy of order `α`, and the binary
  entropy `h(t) = -t log t - (1-t) log(1-t)` of a number `t ∈ [0,1]`;
* the Kullback–Leibler divergence (relative entropy) `D(p‖q) = ∑ p(k) log(p(k)/q(k))`,
  the χ² divergence, the total variation and Hellinger distances, and the Bhattacharyya
  coefficient.

A series is defined where it converges; the Kullback–Leibler and χ² divergences also ask
that `q(k) = 0` only where `p(k) = 0`. Every meaning is a term of the core language: the
field has no constants and no model. An article names it with `distributions`
(`\usepackage[vocab={distributions,information}]{leanify}`). -/

namespace Leanify.Information
open Build Core

abbrev F : Ty := Ty.rfun

def log (x : B) : B := app (prim (.realFn .log)) x
def rpow (x p : B) : B := app2 (prim .rpow) x p
def sqrt (x : B) : B := rpow x (div (num 1) (num 2))
/-- `t log t`, with `0 log 0 = 0`. -/
def xlogx (t : B) : B := cases (eq t (num 0)) (num 0) (mul t (log t))
/-- The terms `k ↦ w(k)` at the natural numbers `k`. -/
def terms (w : B → B) : B := lamT .real (fun k => and (isNat k) (le (num 0) k)) w
def converges (w : B → B) : B := app2 (prim .seriesConv) (num 0) (terms w)
def series (w : B → B) : B := app2 (prim .series) (num 0) (terms w)
/-- `∑_k w(k)` (where the series converges: the domain of the notion says so). -/
def sumOf (w : B → B) : B := series w
/-- `q(k) = 0` only where `p(k) = 0`. -/
def dominated (p q : B) : B := allR fun k => imp (and (isNat k) (eq (app q k) (num 0))) (eq (app p k) (num 0))

/-- `x ↦ log(p(k)/q(k))` weighted by `p(k)`, `0` where `p(k) = 0`. -/
def klTerm (p q k : B) : B := cases (eq (app p k) (num 0)) (num 0) (mul (app p k) (log (div (app p k) (app q k))))
def chiTerm (p q k : B) : B := cases (eq (app q k) (num 0)) (num 0) (div (mul (sub (app p k) (app q k)) (sub (app p k) (app q k))) (app q k))

/-- A notion of one function, defined where `d` holds. -/
def of1 (name : Phrase) (d : B → B) (body : B → B) (doc : String) : Notion :=
  { name, ty := F ⟶ .real, doms := [dom1 F d], doc, value := close <| lamT F d body }
/-- A notion of two functions, defined where `d p q` holds. -/
def of2 (name : Phrase) (d : B → B → B) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := F ⟶ F ⟶ .real, doms := [none, dom2 F d], doc,
    value := close <| lamT F (fun _ => tt) fun p => lamT F (fun q => d p q) fun q => body p q }

def entropyTerm (p : B) (k : B) : B := xlogx (app p k)
def klDom (p q : B) : B := and (dominated p q) (converges fun k => klTerm p q k)
def chiDom (p q : B) : B := and (dominated p q) (converges fun k => chiTerm p q k)
def tvDom (p q : B) : B := converges fun k => abs (sub (app p k) (app q k))
def hellDom (p q : B) : B := converges fun k => let d := sub (sqrt (app p k)) (sqrt (app q k)); mul d d
def bhDom (p q : B) : B := converges fun k => sqrt (mul (app p k) (app q k))

def kl (p q : B) : B := sumOf fun k => klTerm p q k
def tv (p q : B) : B := mul (div (num 1) (num 2)) (sumOf fun k => abs (sub (app p k) (app q k)))
def hellinger (p q : B) : B :=
  sqrt (mul (div (num 1) (num 2)) (sumOf fun k => let d := sub (sqrt (app p k)) (sqrt (app q k)); mul d d))

def vocab : Vocab where
  notions := [
    of1 phrase!"entropy of $v$" (fun p => converges (entropyTerm p)) (fun p => neg (sumOf (entropyTerm p)))
      "`-∑ p(k) log p(k)` (`0 log 0 = 0`), where the series converges",
    of1 phrase!"Shannon entropy of $v$" (fun p => converges (entropyTerm p)) (fun p => neg (sumOf (entropyTerm p)))
      "`-∑ p(k) log p(k)`",
    { name := phrase!"Rényi entropy of order $v$ of $v$", ty := .real ⟶ F ⟶ .real,
      doms := [dom1 .real fun a => and (lt (num 0) a) (ne a (num 1)), dom2 F fun a p => converges fun k => rpow (app p k) a],
      doc := "`log(∑ p(k)^α)/(1 - α)`, `α > 0`, `α ≠ 1`, where the series converges",
      value := close <| lamT .real (fun a => and (lt (num 0) a) (ne a (num 1))) fun a =>
        lamT F (fun p => converges fun k => rpow (app p k) a) fun p =>
          div (log (sumOf fun k => rpow (app p k) a)) (sub (num 1) a) },
    { name := phrase!"binary entropy of $v$", ty := .real ⟶ .real,
      doms := [dom1 .real fun t => and (le (num 0) t) (le t (num 1))],
      doc := "`-t log t - (1-t) log(1-t)`, for `t ∈ [0,1]` (Mathlib `Real.binEntropy`)",
      value := close <| lamT .real (fun t => and (le (num 0) t) (le t (num 1))) fun t =>
        neg (add (xlogx t) (xlogx (sub (num 1) t))) },
    of2 phrase!"Kullback-Leibler divergence of $v$ from $v$" klDom kl
      "`∑ p(k) log(p(k)/q(k))`, where `q(k) = 0` only if `p(k) = 0` and the series converges (Mathlib `InformationTheory.klDiv`)",
    of2 phrase!"relative entropy of $v$ with respect to $v$" klDom kl "the Kullback–Leibler divergence `D(p‖q)`",
    of2 phrase!"chi-squared divergence of $v$ from $v$" chiDom (fun p q => sumOf fun k => chiTerm p q k)
      "`∑ (p(k) - q(k))²/q(k)`, where `q(k) = 0` only if `p(k) = 0` and the series converges",
    of2 phrase!"total variation distance between $v$ and $v$" tvDom tv "`(1/2) ∑ |p(k) - q(k)|`",
    of2 phrase!"Hellinger distance between $v$ and $v$" hellDom hellinger "`√((1/2) ∑ (√p(k) - √q(k))²)`",
    of2 phrase!"Bhattacharyya coefficient of $v$ and $v$" bhDom
      (fun p q => sumOf fun k => sqrt (mul (app p k) (app q k))) "`∑ √(p(k) q(k))`"]

end Leanify.Information
