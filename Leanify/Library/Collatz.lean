import Leanify.Library.Core

/-! # Vocabulary: the Collatz map

The Collatz (`3n + 1`) map on the positive integers and its trajectories (`We write
$\sigma_\infty(n)$ for the total stopping time of $n$.`). A trajectory is the sequence of
iterates `T^0(n) = n`, `T^{k+1}(n) = T(T^k(n))`, an existential witness of this recursion.

* notions: the Collatz map `T(n) = n/2` for even `n`, `3n + 1` for odd `n`; the accelerated map
  `(3n + 1)/2` for odd `n`; the `k`th iterate `T^k(n)`; the total stopping time (the least `k` with
  `T^k(n) = 1`, where there is one); the stopping time (the least `k ≥ 1` with `T^k(n) < n`, where
  there is one); the highest point `max_{j ≤ k} T^j(n)` of the first `k` steps;
* adjectives of numbers: `with finite total stopping time` (its trajectory reaches `1`).

Every meaning is a term of the core language. -/

namespace Leanify.Collatz
open Build Core

abbrev F : Ty := Ty.rfun

def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def natP (k : B) : B := and (isInt k) (le (num 0) k)
def even (n : B) : B := isInt (div n (num 2))
def collatzMap (n : B) : B := cases (even n) (div n (num 2)) (add (mul (num 3) n) (num 1))
def accel (n : B) : B := cases (even n) (div n (num 2)) (div (add (mul (num 3) n) (num 1)) (num 2))
def traj (n xs : B) : B := and (eq (app xs (num 0)) n) (allR fun j => imp (natP j) (eq (app xs (add j (num 1))) (collatzMap (app xs j))))
def iter (k n : B) : B := theR fun v => exT F fun xs => and (traj n xs) (eq (app xs k) v)
def reaches (n : B) : B := exR fun k => and (natP k) (eq (iter k n) (num 1))
def totalStop (n : B) : B :=
  theR fun k => and (natP k) (and (eq (iter k n) (num 1)) (allR fun j => imp (and (natP j) (lt j k)) (ne (iter j n) (num 1))))
def drops (n : B) : B := exR fun k => and (posInt k) (lt (iter k n) n)
def stop (n : B) : B :=
  theR fun k => and (posInt k) (and (lt (iter k n) n) (allR fun j => imp (and (posInt j) (lt j k)) (le n (iter j n))))
def highest (k n : B) : B :=
  theR fun m => and (exR fun j => and (natP j) (and (le j k) (eq (iter j n) m))) (allR fun j => imp (and (natP j) (le j k)) (le (iter j n) m))

def vocab : Vocab where
  mods := [
    { phrase := phrase!"with finite total stopping time", prenominal := false, ty := .real,
      pred := predR fun n => and (posInt n) (reaches n), doc := "a positive integer whose trajectory reaches `1`" }]
  notions := [
    { name := phrase!"Collatz map", ty := F, doc := "`n ↦ n/2` for even `n`, `3n + 1` otherwise", value := close <| lamR collatzMap },
    { name := phrase!"accelerated Collatz map", ty := F, doc := "`n ↦ n/2` for even `n`, `(3n + 1)/2` otherwise",
      value := close <| lamR accel },
    { name := phrase!"$v$th Collatz iterate of $v$", ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real natP, dom1 .real posInt],
      doc := "`T^k(n)`", value := close <| lamT .real natP fun k => lamT .real posInt fun n => iter k n },
    { name := phrase!"total stopping time of $v$", ty := .real ⟶ .real, doms := [dom1 .real fun n => and (posInt n) (reaches n)],
      doc := "the least `k` with `T^k(n) = 1`, where the trajectory reaches `1`",
      value := close <| lamT .real (fun n => and (posInt n) (reaches n)) totalStop },
    { name := phrase!"stopping time of $v$", ty := .real ⟶ .real, doms := [dom1 .real fun n => and (posInt n) (drops n)],
      doc := "the least `k ≥ 1` with `T^k(n) < n`, where there is one",
      value := close <| lamT .real (fun n => and (posInt n) (drops n)) stop },
    { name := phrase!"highest point of the first $v$ Collatz steps from $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real natP, dom1 .real posInt], doc := "`max_{j ≤ k} T^j(n)`",
      value := close <| lamT .real natP fun k => lamT .real posInt fun n => highest k n }]

end Leanify.Collatz
