import Leanify.Library.Core

/-! # Vocabulary: sequences of functions

A sequence of real functions `f_0, f_1, …` is a real function of two variables, `f(n, x)`
(`Let $f:\mathbb{R}^2\to\mathbb{R}$ be a function.`): pointwise and uniform convergence on a set,
uniform boundedness and equicontinuity, and the Weierstrass M-test's summability
(`$f$ converges uniformly to $g$ on $[0,1]$`).

* adjectives of sequences of functions: `pointwise convergent to $g$ on $[a,b]$`, `uniformly
  convergent to $g$ on $[a,b]$`, `uniformly Cauchy on $[a,b]$`, `uniformly bounded on $[a,b]$`,
  `equicontinuous on $[a,b]$`, `monotonically increasing in $n$` (`f(n,x) ≤ f(n+1,x)`), and
  `pointwise convergent to $g$`, `uniformly convergent to $g$` on the whole line;
* notions: the supremum distance between `f_n` and `g` on `[a,b]` (`sup_{x∈[a,b]} |f(n,x) - g(x)|`,
  for bounded differences), the `n`th partial sum of the series of functions at `x`.

The sequence is indexed by the natural numbers; every meaning is a term of the core language. -/

namespace Leanify.FunctionSequences
open Build Core

abbrev F : Ty := Ty.rfun
abbrev F2 : Ty := .real ⟶ .real ⟶ .real

def nat (n : B) : B := and (isInt n) (le (num 0) n)
def inI (a b x : B) : B := and (le a x) (le x b)
def pos (e : B) : B := lt (num 0) e
def eventually (body : B → B) : B := exR fun n0 => allR fun n => imp (and (nat n) (le n0 n)) (body n)
def pointwise (f g : B) (onS : B → B) : B :=
  allR fun x => imp (onS x) (allR fun e => imp (pos e) (eventually fun n => lt (abs (sub (app2 f n x) (app g x))) e))
def uniform (f g : B) (onS : B → B) : B :=
  allR fun e => imp (pos e) (eventually fun n => allR fun x => imp (onS x) (lt (abs (sub (app2 f n x) (app g x))) e))
def any (_ : B) : B := tt
def pointwiseAll (f g : B) : B :=
  allR fun x => allR fun e => imp (pos e) (eventually fun n => lt (abs (sub (app2 f n x) (app g x))) e)
def uniformAll (f g : B) : B :=
  allR fun e => imp (pos e) (eventually fun n => allR fun x => lt (abs (sub (app2 f n x) (app g x))) e)
def onAB (p : Phrase) (body : B → (B → B) → B) (doc : String) : Modifier :=
  { phrase := p, prenominal := false, ty := F2, doc,
    pred := close <| lamR fun a => lamR fun b => lamT F2 any fun f => body f (inI a b) }
def withG (p : Phrase) (body : B → B → (B → B) → B) (doc : String) : Modifier :=
  { phrase := p, prenominal := false, ty := F2, doc,
    pred := close <| lamT F any fun g => lamR fun a => lamR fun b => lamT F2 any fun f => body f g (inI a b) }
def withGLine (p : Phrase) (body : B → B → (B → B) → B) (doc : String) : Modifier :=
  { phrase := p, prenominal := false, ty := F2, doc,
    pred := close <| lamT F any fun g => lamT F2 any fun f => body f g any }
def finSum (a b : B) (body : B → B) : B := app (app (app (prim .finSum) a) b) (lamR body)

def vocab : Vocab where
  mods := [
    withG phrase!"pointwise convergent to $v$ on $[v,v]$" (fun f g s => pointwise f g s) "`f(n,x) → g(x)` for every `x ∈ [a,b]`",
    withG phrase!"uniformly convergent to $v$ on $[v,v]$" (fun f g s => uniform f g s) "`sup_{x∈[a,b]} |f(n,x) - g(x)| → 0`",
    withGLine phrase!"pointwise convergent to $v$" (fun f g _ => pointwiseAll f g) "`f(n,x) → g(x)` for every `x`",
    withGLine phrase!"uniformly convergent to $v$" (fun f g _ => uniformAll f g) "`sup_x |f(n,x) - g(x)| → 0`",
    onAB phrase!"uniformly Cauchy on $[v,v]$"
      (fun f s => allR fun e => imp (pos e) (exR fun n0 => allR fun m => allR fun n =>
        imp (and (and (nat m) (nat n)) (and (le n0 m) (le n0 n))) (allR fun x => imp (s x) (lt (abs (sub (app2 f m x) (app2 f n x))) e))))
      "`|f(m,x) - f(n,x)| < ε` for all large `m`, `n` and all `x ∈ [a,b]`",
    onAB phrase!"uniformly bounded on $[v,v]$"
      (fun f s => exR fun m => allR fun n => imp (nat n) (allR fun x => imp (s x) (le (abs (app2 f n x)) m)))
      "`|f(n,x)| ≤ M` for all `n` and `x ∈ [a,b]`",
    onAB phrase!"equicontinuous on $[v,v]$"
      (fun f s => allR fun x => imp (s x) (allR fun e => imp (pos e) (exR fun d => and (pos d) (allR fun n => imp (nat n)
        (allR fun y => imp (and (s y) (lt (abs (sub y x)) d)) (lt (abs (sub (app2 f n y) (app2 f n x))) e))))))
      "for every `x` and `ε > 0` one `δ > 0` serves every `f_n`",
    { phrase := phrase!"monotonically increasing in the index", prenominal := false, ty := F2,
      pred := close <| lamT F2 any fun f => allR fun n => imp (nat n) (allR fun x => le (app2 f n x) (app2 f (add n (num 1)) x)),
      doc := "`f(n,x) ≤ f(n+1,x)` for all `n` and `x`" }]
  notions := [
    { name := phrase!"supremum distance between the $v$th term of $v$ and $v$ on $[v,v]$", ty := .real ⟶ F2 ⟶ F ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real nat, none, none, none, none],
      doc := "`sup_{x∈[a,b]} |f(n,x) - g(x)|`, the least upper bound (where the differences are bounded)",
      value := close <| lamT .real nat fun n => lamT F2 any fun f => lamT F any fun g => lamR fun a => lamR fun b =>
        theR fun m => and (allR fun x => imp (inI a b x) (le (abs (sub (app2 f n x) (app g x))) m))
          (allR fun m' => imp (allR fun x => imp (inI a b x) (le (abs (sub (app2 f n x) (app g x))) m')) (le m m')) },
    { name := phrase!"$v$th partial sum of the series of functions $v$ at $v$", ty := .real ⟶ F2 ⟶ .real ⟶ .real,
      doms := [dom1 .real nat, none, none], doc := "`∑_{k=0}^{n} f(k,x)`",
      value := close <| lamT .real nat fun n => lamT F2 any fun f => lamR fun x => finSum (num 0) n fun k => app2 f k x }]

end Leanify.FunctionSequences
