import Leanify.Library.Core

/-! # Vocabulary: betting and odds

Odds, stakes and the Kelly criterion, by probabilities and odds (`We write $f(p,b)$ for the
Kelly fraction for winning probability $p$ and net odds $b$.`).

* notions: the probability `1/o` implied by decimal odds `o` and the fair decimal odds `1/p` of
  a probability; the odds `p/(1-p)` in favour of an event; the expected profit `po - 1` of a
  unit stake; the Kelly fraction `p - (1-p)/b` for net odds `b`; the expected logarithmic growth
  `p log(1 + bf) + (1-p) log(1 - f)` of staking the fraction `f`; the bookmaker's margin
  `1/o₁ + 1/o₂ - 1` of a two-way market.

Every meaning is a term of the core language. -/

namespace Leanify.Betting
open Build Core

def pos (x : B) : B := lt (num 0) x
def prob (x : B) : B := and (lt (num 0) x) (lt x (num 1))
def odds (o : B) : B := lt (num 1) o
def log (x : B) : B := app (prim (.realFn .log)) x

def vocab : Vocab where
  notions := [
    { name := phrase!"probability implied by the decimal odds $v$", ty := .real ⟶ .real, doms := [dom1 .real odds],
      doc := "`1/o`", value := close <| lamT .real odds fun o => div (num 1) o },
    { name := phrase!"fair decimal odds for the probability $v$", ty := .real ⟶ .real, doms := [dom1 .real prob],
      doc := "`1/p`", value := close <| lamT .real prob fun p => div (num 1) p },
    { name := phrase!"odds in favour for the probability $v$", ty := .real ⟶ .real, doms := [dom1 .real prob],
      doc := "`p/(1-p)`", value := close <| lamT .real prob fun p => div p (sub (num 1) p) },
    { name := phrase!"expected profit of a unit stake at decimal odds $v$ with winning probability $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real odds, dom2 .real fun _ p => prob p], doc := "`po - 1`",
      value := close <| lamT .real odds fun o => lamT .real prob fun p => sub (mul p o) (num 1) },
    { name := phrase!"Kelly fraction for winning probability $v$ and net odds $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real prob, dom2 .real fun _ b => pos b], doc := "`p - (1-p)/b`: negative when the bet is unfavourable",
      value := close <| lamT .real prob fun p => lamT .real pos fun b => sub p (div (sub (num 1) p) b) },
    { name := phrase!"expected logarithmic growth of staking the fraction $v$ at net odds $v$ with winning probability $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun f => and (le (num 0) f) (lt f (num 1)), dom2 .real fun _ b => pos b, dom3 .real fun _ _ p => prob p],
      doc := "`p log(1 + bf) + (1-p) log(1 - f)`",
      value := close <| lamT .real (fun f => and (le (num 0) f) (lt f (num 1))) fun f => lamT .real pos fun b => lamT .real prob fun p =>
        add (mul p (log (add (num 1) (mul b f)))) (mul (sub (num 1) p) (log (sub (num 1) f))) },
    { name := phrase!"bookmaker margin of the decimal odds $v$ and $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real odds, dom2 .real fun _ o => odds o], doc := "`1/o₁ + 1/o₂ - 1` (the overround)",
      value := close <| lamT .real odds fun a => lamT .real odds fun b => sub (add (div (num 1) a) (div (num 1) b)) (num 1) }]

end Leanify.Betting
