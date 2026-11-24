import Leanify.Library.Core

/-! # Vocabulary: descriptive statistics of a sample

A sample `x_1, …, x_n` is the first `n` terms of a sequence, the values `x(1), …, x(n)` of
a real function (`Let $x:\mathbb{R}\to\mathbb{R}$ be a function.`): the sample mean and
variance, moments, the empirical distribution function, order statistics and the median,
the sample covariance and correlation of two samples, and the least-squares line.

* notions of the first `n` terms of `x` (`n ≥ 1`): the sample mean `(1/n) ∑ x_i`, the
  sample variance `(1/(n-1)) ∑ (x_i - x̄)²` (`n ≥ 2`) and the variance with `1/n`, the sample
  standard deviation, the `k`th sample moment, the empirical distribution function
  `t ↦ #{i : x_i ≤ t}/n`, the `k`th order statistic (the `k`th smallest value, counted with
  multiplicity), the sample median, the range;
* of two samples: the sample covariance and the sample correlation coefficient (where the
  variances do not vanish), and the slope and intercept of the least-squares line of `y` on
  `x`.

Every meaning is a term of the core language (finite sums; an order statistic is the
description of the value below which fewer than `k` and at or below which at least `k`
terms lie). -/

namespace Leanify.Samples
open Build Core

abbrev F : Ty := Ty.rfun

def natP (n : B) : B := and (isInt n) (le (num 0) n)
def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def atLeast2 (n : B) : B := and (isInt n) (le (num 2) n)
def finSum (a b : B) (body : B → B) : B := app (app (app (prim .finSum) a) b) (lamR body)
def zpow (x k : B) : B := app2 (prim .zpow) x k
def sqrt (x : B) : B := app2 (prim .rpow) x (div (num 1) (num 2))
def sum (n : B) (body : B → B) : B := finSum (num 1) n body
def mean (n x : B) : B := div (sum n fun i => app x i) n
def ssq (n x : B) : B := sum n fun i => mul (sub (app x i) (mean n x)) (sub (app x i) (mean n x))
def sxy (n x y : B) : B := sum n fun i => mul (sub (app x i) (mean n x)) (sub (app y i) (mean n y))
/-- The number of the first `n` terms at most `t`. -/
def countLe (n x t : B) : B := sum n fun i => cases (le (app x i) t) (num 1) (num 0)
def countLt (n x t : B) : B := sum n fun i => cases (lt (app x i) t) (num 1) (num 0)
/-- `t` is the `k`th smallest of the first `n` terms. -/
def isOrder (k n x t : B) : B := and (lt (countLt n x t) k) (le k (countLe n x t))
def orderStat (k n x : B) : B := theR fun t => and (exR fun i => and (and (isInt i) (and (le (num 1) i) (le i n))) (eq (app x i) t)) (isOrder k n x t)

/-- A statistic of the first `n` terms of `x`, `n` in the domain `d`. -/
def stat (name : Phrase) (d : B → B) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ F ⟶ .real, doms := [dom1 .real d, none], doc,
    value := close <| lamT .real d fun n => lamT F (fun _ => tt) fun x => body n x }
def stat2 (name : Phrase) (d : B → B → B → B) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ F ⟶ F ⟶ .real, doms := [dom1 .real atLeast2, none, dom3 F d], doc,
    value := close <| lamT .real atLeast2 fun n => lamT F (fun _ => tt) fun x => lamT F (fun y => d n x y) fun y => body n x y }

/-- A quantity of the least-squares line of `y` on `x` for the first `n` terms (`x` not
constant on them). -/
def lsq (name : Phrase) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty := F ⟶ F ⟶ .real ⟶ .real, doms := [none, none, dom3 .real fun _ x n => and (atLeast2 n) (ne (ssq n x) (num 0))], doc,
    value := close <| lamT F (fun _ => tt) fun y => lamT F (fun _ => tt) fun x =>
      lamT .real (fun n => and (atLeast2 n) (ne (ssq n x) (num 0))) fun n => body y x n }

def vocab : Vocab where
  notions := [
    stat phrase!"sample mean of the first $v$ terms of $v$" posInt mean "`(1/n) ∑_{i=1}^{n} x_i`",
    stat phrase!"sample variance of the first $v$ terms of $v$" atLeast2 (fun n x => div (ssq n x) (sub n (num 1)))
      "`(1/(n-1)) ∑ (x_i - x̄)²`, `n ≥ 2` (unbiased)",
    stat phrase!"empirical variance of the first $v$ terms of $v$" posInt (fun n x => div (ssq n x) n) "`(1/n) ∑ (x_i - x̄)²`",
    stat phrase!"sample standard deviation of the first $v$ terms of $v$" atLeast2 (fun n x => sqrt (div (ssq n x) (sub n (num 1))))
      "`√((1/(n-1)) ∑ (x_i - x̄)²)`, `n ≥ 2`",
    { name := phrase!"$v$th sample moment of the first $v$ terms of $v$", ty := .real ⟶ .real ⟶ F ⟶ .real,
      doms := [dom1 .real natP, dom1 .real posInt, none], doc := "`(1/n) ∑ x_i^k`",
      value := close <| lamT .real natP fun k => lamT .real posInt fun n => lamT F (fun _ => tt) fun x =>
        div (sum n fun i => zpow (app x i) k) n },
    { name := phrase!"empirical distribution function of the first $v$ terms of $v$", ty := .real ⟶ F ⟶ F,
      doms := [dom1 .real posInt, none], doc := "`t ↦ #{i ≤ n : x_i ≤ t}/n`",
      value := close <| lamT .real posInt fun n => lamT F (fun _ => tt) fun x => lamR fun t => div (countLe n x t) n },
    { name := phrase!"$v$th order statistic of the first $v$ terms of $v$", ty := .real ⟶ .real ⟶ F ⟶ .real,
      doms := [dom1 .real posInt, dom2 .real fun k n => and (posInt n) (le k n), none],
      doc := "the `k`th smallest of `x_1, …, x_n`, counted with multiplicity; `1 ≤ k ≤ n`",
      value := close <| lamT .real posInt fun k => lamT .real (fun n => and (posInt n) (le k n)) fun n =>
        lamT F (fun _ => tt) fun x => orderStat k n x },
    stat phrase!"sample median of the first $v$ terms of $v$" posInt
      (fun n x => cases (isInt (div n (num 2)))
        (div (add (orderStat (div n (num 2)) n x) (orderStat (add (div n (num 2)) (num 1)) n x)) (num 2))
        (orderStat (div (add n (num 1)) (num 2)) n x))
      "the middle order statistic (`n` odd), the mean of the two middle ones (`n` even)",
    stat phrase!"range of the first $v$ terms of $v$" posInt (fun n x => sub (orderStat n n x) (orderStat (num 1) n x))
      "the largest minus the smallest of `x_1, …, x_n`",
    stat2 phrase!"sample covariance of the first $v$ terms of $v$ and $v$" (fun _ _ _ => tt)
      (fun n x y => div (sxy n x y) (sub n (num 1))) "`(1/(n-1)) ∑ (x_i - x̄)(y_i - ȳ)`, `n ≥ 2`",
    stat2 phrase!"sample correlation coefficient of the first $v$ terms of $v$ and $v$"
      (fun n x y => and (ne (ssq n x) (num 0)) (ne (ssq n y) (num 0)))
      (fun n x y => div (sxy n x y) (sqrt (mul (ssq n x) (ssq n y))))
      "Pearson's `r`, where neither sample is constant",
    lsq phrase!"slope of the least-squares line of $v$ on $v$ for the first $v$ terms"
      (fun y x n => div (sxy n x y) (ssq n x)) "`∑(x_i - x̄)(y_i - ȳ)/∑(x_i - x̄)²`, where `x_1, …, x_n` are not all equal",
    lsq phrase!"intercept of the least-squares line of $v$ on $v$ for the first $v$ terms"
      (fun y x n => sub (mean n y) (mul (div (sxy n x y) (ssq n x)) (mean n x)))
      "`ȳ - b x̄` with the slope `b`, where `x_1, …, x_n` are not all equal"]

end Leanify.Samples
