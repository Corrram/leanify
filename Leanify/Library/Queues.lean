import Leanify.Library.Core

/-! # Vocabulary: queues

The steady state of the classical queueing models, by their formulas (`We write $L$ for the
mean number of customers in the M/M/1 queue with arrival rate $\lambda$ and service rate
$\mu$.`).

* notions: the traffic intensity `ρ = λ/μ`; for the M/M/1 queue with `0 < λ < μ`: the
  mean number of customers in the system `ρ/(1-ρ)` and waiting `ρ²/(1-ρ)`, the mean sojourn
  time `1/(μ-λ)` and waiting time `ρ/(μ-λ)`, the probability of `n` customers `(1-ρ)ρ^n`;
  the Erlang B formula `(a^n/n!)/∑_{k≤n} a^k/k!` and the Erlang C formula for `n` servers
  and offered load `a < n`; the Pollaczek–Khinchine mean waiting time `λ E[S²]/(2(1-ρ))` of
  the M/G/1 queue with `ρ = λ E[S] < 1`; the M/M/c probability of waiting.

Every meaning is a term of the core language (finite sums, factorials, integer powers). -/

namespace Leanify.Queues
open Build Core

def pos (x : B) : B := lt (num 0) x
def stable (l m : B) : B := and (pos l) (lt l m)
def natP (k : B) : B := and (isInt k) (le (num 0) k)
def posInt (k : B) : B := and (isInt k) (le (num 1) k)
def zpow (x k : B) : B := app2 (prim .zpow) x k
def fact (n : B) : B := app (prim .factorial) n
def finSum (a b : B) (body : B → B) : B := app (app (app (prim .finSum) a) b) (lamR body)
def rho (l m : B) : B := div l m
def term (a k : B) : B := div (zpow a k) (fact k)
def erlangB (n a : B) : B := div (term a n) (finSum (num 0) n fun k => term a k)
def erlangCTop (n a : B) : B := mul (term a n) (div n (sub n a))
def erlangC (n a : B) : B := div (erlangCTop n a) (add (finSum (num 0) (sub n (num 1)) fun k => term a k) (erlangCTop n a))
/-- A notion of an M/M/1 queue with arrival rate `λ` and service rate `μ`, `0 < λ < μ`. -/
def mm1 (name : Phrase) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real pos, dom2 .real fun l m => stable l m], doc,
    value := close <| lamT .real pos fun l => lamT .real (fun m => stable l m) fun m => body l m }

def vocab : Vocab where
  notions := [
    { name := phrase!"traffic intensity of the queue with arrival rate $v$ and service rate $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [none, dom1 .real pos], doc := "`ρ = λ/μ`",
      value := close <| lamR fun l => lamT .real pos fun m => rho l m },
    mm1 phrase!"mean number of customers in the M/M/1 queue with arrival rate $v$ and service rate $v$"
      (fun l m => div (rho l m) (sub (num 1) (rho l m))) "`L = ρ/(1-ρ)`",
    mm1 phrase!"mean number of customers waiting in the M/M/1 queue with arrival rate $v$ and service rate $v$"
      (fun l m => div (mul (rho l m) (rho l m)) (sub (num 1) (rho l m))) "`L_q = ρ²/(1-ρ)`",
    mm1 phrase!"mean sojourn time in the M/M/1 queue with arrival rate $v$ and service rate $v$"
      (fun l m => div (num 1) (sub m l)) "`W = 1/(μ-λ)`",
    mm1 phrase!"mean waiting time in the M/M/1 queue with arrival rate $v$ and service rate $v$"
      (fun l m => div (rho l m) (sub m l)) "`W_q = ρ/(μ-λ)`",
    { name := phrase!"probability of $v$ customers in the M/M/1 queue with arrival rate $v$ and service rate $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real, doms := [dom1 .real natP, dom1 .real pos, dom3 .real fun _ l m => stable l m],
      doc := "`(1-ρ)ρ^n`, the stationary distribution",
      value := close <| lamT .real natP fun n => lamT .real pos fun l => lamT .real (fun m => stable l m) fun m =>
        mul (sub (num 1) (rho l m)) (zpow (rho l m) n) },
    { name := phrase!"Erlang B formula for $v$ servers and offered load $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real posInt, dom1 .real pos],
      doc := "`(a^n/n!)/∑_{k=0}^{n} a^k/k!`, the blocking probability of M/M/n/n",
      value := close <| lamT .real posInt fun n => lamT .real pos fun a => erlangB n a },
    { name := phrase!"Erlang C formula for $v$ servers and offered load $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real posInt, dom2 .real fun n a => and (pos a) (lt a n)],
      doc := "the probability of waiting in M/M/n, for an offered load `a < n`",
      value := close <| lamT .real posInt fun n => lamT .real (fun a => and (pos a) (lt a n)) fun a => erlangC n a },
    { name := phrase!"Pollaczek-Khinchine mean waiting time for arrival rate $v$, mean service time $v$ and second moment $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun l s => and (pos s) (lt (mul l s) (num 1)), dom1 .real pos],
      doc := "`λ E[S²]/(2(1 - λ E[S]))`, M/G/1 with `λ E[S] < 1`",
      value := close <| lamT .real pos fun l => lamT .real (fun s => and (pos s) (lt (mul l s) (num 1))) fun s =>
        lamT .real pos fun s2 => div (mul l s2) (mul (num 2) (sub (num 1) (mul l s))) }]

end Leanify.Queues
