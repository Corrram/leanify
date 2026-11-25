import Leanify.Library.Core

/-! # Vocabulary: fixed income

Bonds, loans and perpetuities, by rates per period (`We write $P(F,c,y,n)$ for the price of a bond
with face value $F$, coupon rate $c$ and yield $y$ maturing in $n$ periods.`). Present and future
values and annuities are in the field `finance`.

* notions: the price `cF∑_{k=1}^{n}(1+y)^{-k} + F(1+y)^{-n}` of a bond, its Macaulay duration
  `(∑ k·CF_k(1+y)^{-k})/P` and modified duration `D/(1+y)`; the current yield `cF/P`; the
  values `C/r` of a perpetuity and `C/(r-g)` of a growing perpetuity (Gordon); the effective
  annual rate `(1 + r/m)^m - 1` of `m` compoundings; the payment `Lr/(1 - (1+r)^{-n})` of a loan
  and its balance `L(1+r)^k - A((1+r)^k - 1)/r` after `k` payments `A`.

Every meaning is a term of the core language. -/

namespace Leanify.FixedIncome
open Build Core

def pos (x : B) : B := lt (num 0) x
def posInt (n : B) : B := and (isInt n) (le (num 1) n)
def natP (n : B) : B := and (isInt n) (le (num 0) n)
def zpow (x k : B) : B := app2 (prim .zpow) x k
def finSum (a b : B) (body : B → B) : B := app (app (app (prim .finSum) a) b) (lamR body)
def rate (y : B) : B := lt (neg (num 1)) y
def price (f c y n : B) : B := add (mul (mul c f) (finSum (num 1) n fun k => zpow (add (num 1) y) (neg k))) (mul f (zpow (add (num 1) y) (neg n)))
def macaulay (f c y n : B) : B :=
  div (add (finSum (num 1) n fun k => mul k (mul (mul c f) (zpow (add (num 1) y) (neg k)))) (mul n (mul f (zpow (add (num 1) y) (neg n)))))
    (price f c y n)
def bond (name : Phrase) (body : B → B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
    doms := [dom1 .real pos, dom2 .real fun _ c => le (num 0) c, dom3 .real fun _ _ y => rate y, dom4 .real fun _ _ _ n => posInt n], doc,
    value := close <| lamT .real pos fun f => lamT .real (fun c => le (num 0) c) fun c => lamT .real rate fun y => lamT .real posInt fun n => body f c y n }

def vocab : Vocab where
  notions := [
    bond phrase!"price of a bond with face value $v$, coupon rate $v$ and yield $v$ maturing in $v$ periods" price
      "`cF∑_{k=1}^{n}(1+y)^{-k} + F(1+y)^{-n}`",
    bond phrase!"Macaulay duration of a bond with face value $v$, coupon rate $v$ and yield $v$ maturing in $v$ periods" macaulay
      "the present-value weighted mean time of the payments, in periods",
    bond phrase!"modified duration of a bond with face value $v$, coupon rate $v$ and yield $v$ maturing in $v$ periods"
      (fun f c y n => div (macaulay f c y n) (add (num 1) y)) "`D/(1+y)`",
    { name := phrase!"current yield of a bond with face value $v$ and coupon rate $v$ at the price $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ c => le (num 0) c, dom3 .real fun _ _ p => pos p], doc := "`cF/P`",
      value := close <| lamT .real pos fun f => lamT .real (fun c => le (num 0) c) fun c => lamT .real pos fun p => div (mul c f) p },
    { name := phrase!"value of a perpetuity paying $v$ at the rate $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [none, dom2 .real fun _ r => pos r], doc := "`C/r`",
      value := close <| lamR fun c => lamT .real pos fun r => div c r },
    { name := phrase!"value of a growing perpetuity paying $v$ at the rate $v$ with growth $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, none, dom3 .real fun _ r g => lt g r], doc := "`C/(r-g)` (Gordon)",
      value := close <| lamR fun c => lamR fun r => lamT .real (fun g => lt g r) fun g => div c (sub r g) },
    { name := phrase!"effective annual rate of the nominal rate $v$ compounded $v$ times a year", ty := .real ⟶ .real ⟶ .real,
      doms := [none, dom2 .real fun r m => and (posInt m) (lt (num 0) (add (num 1) (div r m)))], doc := "`(1 + r/m)^m - 1`",
      value := close <| lamR fun r => lamT .real (fun m => and (posInt m) (lt (num 0) (add (num 1) (div r m)))) fun m =>
        sub (zpow (add (num 1) (div r m)) m) (num 1) },
    { name := phrase!"payment of a loan of $v$ over $v$ periods at the rate $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, dom2 .real fun _ n => posInt n, dom3 .real fun _ _ r => pos r], doc := "`Lr/(1 - (1+r)^{-n})`",
      value := close <| lamR fun l => lamT .real posInt fun n => lamT .real pos fun r =>
        div (mul l r) (sub (num 1) (zpow (add (num 1) r) (neg n))) },
    { name := phrase!"balance of a loan of $v$ after $v$ payments of $v$ at the rate $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, dom2 .real fun _ k => natP k, none, dom4 .real fun _ _ _ r => pos r],
      doc := "`L(1+r)^k - A((1+r)^k - 1)/r`",
      value := close <| lamR fun l => lamT .real natP fun k => lamR fun a => lamT .real pos fun r =>
        sub (mul l (zpow (add (num 1) r) k)) (div (mul a (sub (zpow (add (num 1) r) k) (num 1))) r) }]

end Leanify.FixedIncome
