import Leanify.Library.Core

/-! # Vocabulary: combinatorial games

Impartial games by their heaps (`We write
$s(a,b)$ for the nim-sum of $a$ and $b$.`). Two-person zero-sum games with payoffs are in the
field `games`.

* notions: the nim-sum (bitwise exclusive or) of two and of three natural numbers; the number
  of winning moves in the Nim position with three heaps (the heaps `h` with `h ⊕ s < h`, for
  the nim-sum `s`; none in a losing position); the Grundy value `n mod (k+1)` of a heap of `n`
  in the subtraction game with moves `1, …, k`; the coordinates `⌊nφ⌋` and `⌊nφ²⌋` of the `n`th
  losing position of Wythoff's game, `φ = (1 + √5)/2`.

Every meaning is a term of the core language. -/

namespace Leanify.CombinatorialGames
open Build Core

def natP (n : B) : B := and (isInt n) (le (num 0) n)
def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def zpow (x k : B) : B := app2 (prim .zpow) x k
def finSum (a b : B) (body : B → B) : B := app (app (app (prim .finSum) a) b) (lamR body)
def bit (k a : B) : B := sub (floor (div a (zpow (num 2) k))) (mul (num 2) (floor (div a (zpow (num 2) (add k (num 1))))))
def mod2 (s : B) : B := sub s (mul (num 2) (floor (div s (num 2))))
/-- `a ⊕ b`: the binary digits added modulo 2 (`a + b` digits are enough). -/
def xor (a b : B) : B := finSum (num 0) (add a b) fun k => mul (zpow (num 2) k) (mod2 (add (bit k a) (bit k b)))
def xor3 (a b c : B) : B := xor (xor a b) c
def ind (p : B) : B := cases p (num 1) (num 0)
def phi : B := div (add (num 1) (app2 (prim .rpow) (num 5) (div (num 1) (num 2)))) (num 2)

def vocab : Vocab where
  notions := [
    { name := phrase!"nim-sum of $v$ and $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real natP, dom2 .real fun _ b => natP b],
      doc := "`a ⊕ b`: the bitwise exclusive or",
      value := close <| lamT .real natP fun a => lamT .real natP fun b => xor a b },
    { name := phrase!"nim-sum of $v$, $v$ and $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real natP, dom2 .real fun _ b => natP b, dom3 .real fun _ _ c => natP c],
      doc := "`a ⊕ b ⊕ c`: `0` exactly for the losing positions of Nim (Bouton)",
      value := close <| lamT .real natP fun a => lamT .real natP fun b => lamT .real natP fun c => xor3 a b c },
    { name := phrase!"number of winning moves in the Nim position with heaps $v$, $v$ and $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real natP, dom2 .real fun _ b => natP b, dom3 .real fun _ _ c => natP c],
      doc := "the number of heaps `h` with `h ⊕ s < h`, `s = a ⊕ b ⊕ c`: the moves to a losing position",
      value := close <| lamT .real natP fun a => lamT .real natP fun b => lamT .real natP fun c =>
        add (ind (lt (xor a (xor3 a b c)) a)) (add (ind (lt (xor b (xor3 a b c)) b)) (ind (lt (xor c (xor3 a b c)) c))) },
    { name := phrase!"Grundy value of a heap of $v$ in the subtraction game with moves up to $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real natP, dom2 .real fun _ k => posInt k],
      doc := "`n mod (k+1)`: a move takes `1` to `k` tokens",
      value := close <| lamT .real natP fun n => lamT .real posInt fun k =>
        sub n (mul (add k (num 1)) (floor (div n (add k (num 1))))) },
    { name := phrase!"first coordinate of the $v$th Wythoff pair", ty := .real ⟶ .real, doms := [dom1 .real natP],
      doc := "`⌊nφ⌋`, `φ = (1 + √5)/2`: the `n`th losing position of Wythoff's game is `(⌊nφ⌋, ⌊nφ²⌋)`",
      value := close <| lamT .real natP fun n => floor (mul n phi) },
    { name := phrase!"second coordinate of the $v$th Wythoff pair", ty := .real ⟶ .real, doms := [dom1 .real natP],
      doc := "`⌊nφ²⌋`", value := close <| lamT .real natP fun n => floor (mul n (mul phi phi)) }]

end Leanify.CombinatorialGames
