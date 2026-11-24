import Leanify.Library.Core

/-! # Vocabulary: counting

The standard counts of enumerative combinatorics, as closed formulas in factorials and
binomial coefficients (`the number of $k$-element subsets of a set of $n$ elements`).

* subsets and arrangements: the number of `k`-element subsets of a set of `n` elements
  (`\binom{n}{k}`), of subsets of a set of `n` elements (`2^n`), of `k`-permutations of `n`
  elements (`n!/(n-k)!`), of permutations of `n` elements (`n!`), of `k`-element multisets
  from `n` elements (`\binom{n+k-1}{k}`);
* maps: the number of maps from a set of `k` elements to a set of `n` elements (`n^k`), of
  injective maps (`n!/(n-k)!`), of surjective maps (`∑_j (-1)^j \binom{n}{j}(n-j)^k`);
* compositions and paths: the number of compositions of `n` into `k` positive parts
  (`\binom{n-1}{k-1}`), into `k` nonnegative parts (`\binom{n+k-1}{k-1}`), and of lattice
  paths from `(0,0)` to `(m,n)` with unit steps right and up (`\binom{m+n}{m}`);
* the multinomial coefficient of `n` over `a` and `b` and `c` (`n!/(a!b!c!)`, `a+b+c = n`).

Every meaning is a term of the core language, for nonnegative integers. -/

namespace Leanify.Counting
open Build Core

def natP (n : B) : B := and (isInt n) (le (num 0) n)
def zpow (x k : B) : B := app2 (prim .zpow) x k
def binom (n k : B) : B := app2 (prim .binom) n k
def fact (n : B) : B := app (prim .factorial) n
def finSum (a b : B) (body : B → B) : B := app (app (app (prim .finSum) a) b) (lamR body)
def falling (n k : B) : B := div (fact n) (fact (sub n k))
def kLeN (k n : B) : B := and (natP n) (le k n)

/-- A count of `n` with `k` (the arguments in the order of the phrase: `first`, `second`),
both nonnegative integers. -/
def count2 (name : Phrase) (d : B → B → B) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real natP, dom2 .real fun a b => and (natP b) (d a b)], doc,
    value := close <| lamT .real natP fun a => lamT .real (fun b => and (natP b) (d a b)) fun b => body a b }
def count1 (name : Phrase) (body : B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real, doms := [dom1 .real natP], doc, value := close <| lamT .real natP body }

def vocab : Vocab where
  notions := [
    count2 phrase!"number of $v$-element subsets of a set of $v$ elements" (fun _ _ => tt) (fun k n => binom n k) "`\\\\binom{n}{k}`",
    count1 phrase!"number of subsets of a set of $v$ elements" (fun n => zpow (num 2) n) "`2^n`",
    count2 phrase!"number of $v$-permutations of $v$ elements" (fun k n => le k n) (fun k n => falling n k) "`n!/(n-k)!`, `k ≤ n`",
    count1 phrase!"number of permutations of $v$ elements" fact "`n!`",
    count2 phrase!"number of $v$-element multisets of $v$ elements" (fun _ _ => tt) (fun k n => binom (sub (add n k) (num 1)) k)
      "`\\\\binom{n+k-1}{k}`",
    count2 phrase!"number of maps from a set of $v$ elements to a set of $v$ elements" (fun _ _ => tt) (fun k n => zpow n k) "`n^k`",
    count2 phrase!"number of injective maps from a set of $v$ elements to a set of $v$ elements" (fun _ _ => tt)
      (fun k n => cases (le k n) (falling n k) (num 0)) "`n!/(n-k)!` for `k ≤ n`, `0` else",
    count2 phrase!"number of surjective maps from a set of $v$ elements to a set of $v$ elements" (fun _ _ => tt)
      (fun k n => finSum (num 0) n fun j => mul (mul (zpow (neg (num 1)) j) (binom n j)) (zpow (sub n j) k))
      "`∑_{j=0}^{n} (-1)^j \\\\binom{n}{j} (n-j)^k` (inclusion–exclusion)",
    count2 phrase!"number of compositions of $v$ into $v$ positive parts" (fun _ _ => tt)
      (fun n k => cases (and (le (num 1) k) (le k n)) (binom (sub n (num 1)) (sub k (num 1))) (num 0))
      "`\\\\binom{n-1}{k-1}` for `1 ≤ k ≤ n`, `0` else",
    count2 phrase!"number of compositions of $v$ into $v$ nonnegative parts" (fun _ k => le (num 1) k)
      (fun n k => binom (sub (add n k) (num 1)) (sub k (num 1))) "`\\\\binom{n+k-1}{k-1}`, `k ≥ 1`",
    count2 phrase!"number of lattice paths from $(0,0)$ to $(v,v)$" (fun _ _ => tt) (fun m n => binom (add m n) m)
      "`\\\\binom{m+n}{m}`, with unit steps right and up",
    { name := phrase!"multinomial coefficient of $v$ over $v$, $v$ and $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real natP, dom1 .real natP, dom1 .real natP, dom4 .real fun n a b c => and (natP c) (eq (add (add a b) c) n)],
      doc := "`n!/(a! b! c!)`, `a + b + c = n`",
      value := close <| lamT .real natP fun n => lamT .real natP fun a => lamT .real natP fun b =>
        lamT .real (fun c => and (natP c) (eq (add (add a b) c) n)) fun c => div (fact n) (mul (mul (fact a) (fact b)) (fact c)) }]

end Leanify.Counting
