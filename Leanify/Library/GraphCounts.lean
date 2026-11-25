import Leanify.Library.Core

/-! # Vocabulary: counting in graph theory

Closed-form counts of the standard graphs and extremal numbers, as numbers of their parameters
(`We write $\tau(n)$ for the number of spanning trees of the complete graph on $n$ vertices.`).
Graphs as objects are in the field `graphs`.

* notions: the numbers of edges `n(n-1)/2` of the complete graph, `mn` of the complete bipartite
  graph and `n2^{n-1}` of the hypercube of dimension `n`; the number `2^{n(n-1)/2}` of labelled
  graphs on `n` vertices; the numbers of spanning trees `n^{n-2}` of the complete graph (Cayley),
  `m^{n-1}n^{m-1}` of the complete bipartite graph and `n` of the cycle; the chromatic polynomials
  `k(k-1)⋯(k-n+1)` of the complete graph, `k(k-1)^{n-1}` of a tree and `(k-1)^n + (-1)^n(k-1)` of
  the cycle; the number of edges of the Turán graph `T(n,r)` (`r` parts), and the bound
  `\binom{s+t-2}{s-1}` on the Ramsey number `R(s,t)` (Erdős–Szekeres).

Every meaning is a term of the core language. -/

namespace Leanify.GraphCounts
open Build Core

def natP (n : B) : B := and (isInt n) (le (num 0) n)
def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def zpow (x k : B) : B := app2 (prim .zpow) x k
def binom (n k : B) : B := app2 (prim .binom) n k
def finProd (a b : B) (body : B → B) : B := app (app (app (prim .finProd) a) b) (lamR body)
def one (name : Phrase) (d : B → B) (body : B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real, doms := [dom1 .real d], doc, value := close <| lamT .real d body }
def two (name : Phrase) (d1 d2 : B → B) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real d1, dom2 .real fun _ y => d2 y], doc,
    value := close <| lamT .real d1 fun x => lamT .real d2 fun y => body x y }
def ge3 (n : B) : B := and (isInt n) (le (num 3) n)

def vocab : Vocab where
  notions := [
    one phrase!"number of edges of the complete graph on $v$ vertices" natP (fun n => div (mul n (sub n (num 1))) (num 2)) "`n(n-1)/2`",
    two phrase!"number of edges of the complete bipartite graph with parts of sizes $v$ and $v$" natP natP (fun m n => mul m n) "`mn`",
    one phrase!"number of edges of the hypercube of dimension $v$" natP (fun n => mul n (zpow (num 2) (sub n (num 1)))) "`n2^{n-1}`",
    one phrase!"number of labelled graphs on $v$ vertices" natP (fun n => zpow (num 2) (div (mul n (sub n (num 1))) (num 2)))
      "`2^{n(n-1)/2}`",
    one phrase!"number of spanning trees of the complete graph on $v$ vertices" posInt (fun n => zpow n (sub n (num 2)))
      "`n^{n-2}` (Cayley's formula)",
    two phrase!"number of spanning trees of the complete bipartite graph with parts of sizes $v$ and $v$" posInt posInt
      (fun m n => mul (zpow m (sub n (num 1))) (zpow n (sub m (num 1)))) "`m^{n-1}n^{m-1}`",
    one phrase!"number of spanning trees of the cycle on $v$ vertices" ge3 (fun n => n) "`n`",
    two phrase!"chromatic polynomial of the complete graph on $v$ vertices at $v$" natP (fun _ => tt)
      (fun n k => finProd (num 0) (sub n (num 1)) fun i => sub k i) "`k(k-1)⋯(k-n+1)`",
    two phrase!"chromatic polynomial of a tree on $v$ vertices at $v$" posInt (fun _ => tt)
      (fun n k => mul k (zpow (sub k (num 1)) (sub n (num 1)))) "`k(k-1)^{n-1}`",
    two phrase!"chromatic polynomial of the cycle on $v$ vertices at $v$" ge3 (fun _ => tt)
      (fun n k => add (zpow (sub k (num 1)) n) (mul (zpow (neg (num 1)) n) (sub k (num 1)))) "`(k-1)^n + (-1)^n(k-1)`",
    two phrase!"number of edges of the Turán graph on $v$ vertices with $v$ parts" natP posInt
      (fun n r => sub (sub (div (mul n (sub n (num 1))) (num 2))
          (mul (sub n (mul r (floor (div n r)))) (div (mul (add (floor (div n r)) (num 1)) (floor (div n r))) (num 2))))
        (mul (sub r (sub n (mul r (floor (div n r))))) (div (mul (floor (div n r)) (sub (floor (div n r)) (num 1))) (num 2))))
      "`\\binom{n}{2} - s\\binom{q+1}{2} - (r-s)\\binom{q}{2}` for `n = qr + s`, `0 ≤ s < r`: the largest number of edges of a graph on `n` vertices without `K_{r+1}` (Turán)",
    two phrase!"binomial bound on the Ramsey number for $v$ and $v$" posInt posInt
      (fun s t => binom (sub (add s t) (num 2)) (sub s (num 1))) "`\\binom{s+t-2}{s-1}`: `R(s,t)` is at most this"]

end Leanify.GraphCounts
