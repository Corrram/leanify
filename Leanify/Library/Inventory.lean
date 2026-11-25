import Leanify.Library.Core

/-! # Vocabulary: inventory models

The deterministic lot-size models and the newsvendor model of operations research, by their
parameters (`We write $Q^*(D,K,h)$ for the economic order quantity for demand rate $D$,
ordering cost $K$ and holding cost $h$.`).

* notions: the cost per unit time `DK/Q + hQ/2` of ordering `Q` units at a time; the economic
  order quantity `√(2DK/h)` and its cost `√(2DKh)` (Harris–Wilson); the cycle length `Q/D`;
  the reorder point `DL` for a lead time `L`; the economic order quantity with backorders
  `√(2DK/h) √((h+p)/p)` for a shortage cost `p`; the economic production quantity
  `√(2DK/(h(1 - D/P)))` for a production rate `P > D`; the critical fractile
  `c_u/(c_u + c_o)` of the newsvendor model with underage cost `c_u` and overage cost `c_o`,
  and its optimal quantity for a demand uniform on `[a,b]` (`a + (b-a) c_u/(c_u+c_o)`) and
  for an exponential demand with mean `μ` (`μ log((c_u+c_o)/c_o)`).

Every meaning is a term of the core language. -/

namespace Leanify.Inventory
open Build Core

def pos (x : B) : B := lt (num 0) x
def sqrt (x : B) : B := app2 (prim .rpow) x (div (num 1) (num 2))
def log (x : B) : B := app (prim (.realFn .log)) x
def eoq (d k h : B) : B := sqrt (div (mul (num 2) (mul d k)) h)
def frac (u o : B) : B := div u (add u o)
def three (name : Phrase) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real,
    doms := [dom1 .real pos, dom2 .real fun _ k => pos k, dom3 .real fun _ _ h => pos h], doc,
    value := close <| lamT .real pos fun d => lamT .real pos fun k => lamT .real pos fun h => body d k h }
def two (name : Phrase) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real pos, dom2 .real fun _ y => pos y], doc,
    value := close <| lamT .real pos fun x => lamT .real pos fun y => body x y }

def vocab : Vocab where
  notions := [
    { name := phrase!"cost per unit time of ordering $v$ units for demand rate $v$, ordering cost $v$ and holding cost $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ d => pos d, dom3 .real fun _ _ k => pos k, dom4 .real fun _ _ _ h => pos h],
      doc := "`DK/Q + hQ/2`: ordering and holding costs per unit time with lots of `Q` units",
      value := close <| lamT .real pos fun q => lamT .real pos fun d => lamT .real pos fun k => lamT .real pos fun h =>
        add (div (mul d k) q) (div (mul h q) (num 2)) },
    three phrase!"economic order quantity for demand rate $v$, ordering cost $v$ and holding cost $v$" eoq
      "`√(2DK/h)` (Harris–Wilson)",
    three phrase!"minimal cost per unit time for demand rate $v$, ordering cost $v$ and holding cost $v$"
      (fun d k h => sqrt (mul (num 2) (mul d (mul k h)))) "`√(2DKh)`: the cost at the economic order quantity",
    two phrase!"cycle length of ordering $v$ units for demand rate $v$" (fun q d => div q d) "`Q/D`",
    two phrase!"reorder point for demand rate $v$ and lead time $v$" (fun d l => mul d l) "`DL`",
    { name := phrase!"economic order quantity with backorders for demand rate $v$, ordering cost $v$, holding cost $v$ and shortage cost $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ k => pos k, dom3 .real fun _ _ h => pos h, dom4 .real fun _ _ _ p => pos p],
      doc := "`√(2DK/h) √((h+p)/p)`",
      value := close <| lamT .real pos fun d => lamT .real pos fun k => lamT .real pos fun h => lamT .real pos fun p =>
        mul (eoq d k h) (sqrt (div (add h p) p)) },
    { name := phrase!"economic production quantity for demand rate $v$, production rate $v$, setup cost $v$ and holding cost $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun d p => lt d p, dom3 .real fun _ _ k => pos k, dom4 .real fun _ _ _ h => pos h],
      doc := "`√(2DK/(h(1 - D/P)))`, for a production rate `P > D`",
      value := close <| lamT .real pos fun d => lamT .real (fun p => lt d p) fun p => lamT .real pos fun k => lamT .real pos fun h =>
        sqrt (div (mul (num 2) (mul d k)) (mul h (sub (num 1) (div d p)))) },
    two phrase!"critical fractile for underage cost $v$ and overage cost $v$" frac "`c_u/(c_u + c_o)`",
    { name := phrase!"newsvendor quantity for uniform demand on $[v,v]$ with underage cost $v$ and overage cost $v$",
      ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [none, dom2 .real fun a b => lt a b, dom3 .real fun _ _ u => pos u, dom4 .real fun _ _ _ o => pos o],
      doc := "`a + (b-a) c_u/(c_u + c_o)`: the critical-fractile quantile of the demand",
      value := close <| lamR fun a => lamT .real (fun b => lt a b) fun b => lamT .real pos fun u => lamT .real pos fun o =>
        add a (mul (sub b a) (frac u o)) },
    three phrase!"newsvendor quantity for exponential demand with mean $v$, underage cost $v$ and overage cost $v$"
      (fun m u o => mul m (log (div (add u o) o))) "`μ log((c_u + c_o)/c_o)`"]

end Leanify.Inventory
