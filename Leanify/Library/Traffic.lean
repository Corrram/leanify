import Leanify.Library.Core

/-! # Vocabulary: traffic flow

The Greenshields model of a road and the basic relations of traffic flow (`We
write $q(k,u,j)$ for the Greenshields flow at density $k$ with free-flow speed $u$ and jam density
$j$.`). Queues are in the field `queues`.

* notions: the Greenshields speed `v_f(1 - k/k_j)` and flow `v_f k(1 - k/k_j)` at density `k`; the
  capacity `v_f k_j/4` and the critical density `k_j/2`; the speed `(v_f/2)(1 + √(1 - q/q_max))`
  of the uncongested branch at flow `q`; the headway `1/q` and the spacing `1/k`.

Every meaning is a term of the core language. -/

namespace Leanify.Traffic
open Build Core

def pos (x : B) : B := lt (num 0) x
def sqrt (x : B) : B := app2 (prim .rpow) x (div (num 1) (num 2))

def vocab : Vocab where
  notions := [
    { name := phrase!"Greenshields speed at density $v$ with free-flow speed $v$ and jam density $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun k => le (num 0) k, dom2 .real fun _ u => pos u, dom3 .real fun k _ j => and (pos j) (le k j)],
      doc := "`v_f(1 - k/k_j)`",
      value := close <| lamT .real (fun k => le (num 0) k) fun k => lamT .real pos fun u => lamT .real (fun j => and (pos j) (le k j)) fun j =>
        mul u (sub (num 1) (div k j)) },
    { name := phrase!"Greenshields flow at density $v$ with free-flow speed $v$ and jam density $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun k => le (num 0) k, dom2 .real fun _ u => pos u, dom3 .real fun k _ j => and (pos j) (le k j)],
      doc := "`v_f k(1 - k/k_j)`",
      value := close <| lamT .real (fun k => le (num 0) k) fun k => lamT .real pos fun u => lamT .real (fun j => and (pos j) (le k j)) fun j =>
        mul (mul u k) (sub (num 1) (div k j)) },
    { name := phrase!"capacity of a road with free-flow speed $v$ and jam density $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real pos, dom2 .real fun _ j => pos j], doc := "`v_f k_j/4` (Greenshields)",
      value := close <| lamT .real pos fun u => lamT .real pos fun j => div (mul u j) (num 4) },
    { name := phrase!"critical density for the jam density $v$", ty := .real ⟶ .real, doms := [dom1 .real pos],
      doc := "`k_j/2` (Greenshields)", value := close <| lamT .real pos fun j => div j (num 2) },
    { name := phrase!"uncongested speed at flow $v$ with free-flow speed $v$ and capacity $v$", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun q => le (num 0) q, dom2 .real fun _ u => pos u, dom3 .real fun q _ c => and (pos c) (le q c)],
      doc := "`(v_f/2)(1 + √(1 - q/q_max))` (Greenshields)",
      value := close <| lamT .real (fun q => le (num 0) q) fun q => lamT .real pos fun u => lamT .real (fun c => and (pos c) (le q c)) fun c =>
        mul (div u (num 2)) (add (num 1) (sqrt (sub (num 1) (div q c)))) },
    { name := phrase!"headway at flow $v$", ty := .real ⟶ .real, doms := [dom1 .real pos], doc := "`1/q`",
      value := close <| lamT .real pos fun q => div (num 1) q },
    { name := phrase!"spacing at density $v$", ty := .real ⟶ .real, doms := [dom1 .real pos], doc := "`1/k`",
      value := close <| lamT .real pos fun k => div (num 1) k }]

end Leanify.Traffic
