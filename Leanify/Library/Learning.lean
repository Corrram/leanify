import Leanify.Library.Core

/-! # Vocabulary: machine learning

Activation functions, losses and the metrics of a binary classifier from its confusion counts
(`We write $F(a,b,c)$ for the F1 score for $a$ true positives, $b$ false
positives and $c$ false negatives.`). Predictive values of a diagnostic test from sensitivity and
specificity are in the field `diagnostictests`.

* notions: the sigmoid function `1/(1 + e^{-x})`, the rectified linear unit `max(x, 0)` and the
  softplus function `log(1 + e^x)`; the binary cross-entropy `-(y log p + (1-y) log(1-p))` and the
  hinge loss `max(0, 1 - ys)`; the precision `TP/(TP + FP)`, the recall `TP/(TP + FN)`, the F1
  score `2TP/(2TP + FP + FN)`, the accuracy and the Matthews correlation coefficient of the
  confusion counts.

Every meaning is a term of the core language. -/

namespace Leanify.Learning
open Build Core

abbrev F : Ty := Ty.rfun

def natP (n : B) : B := and (isInt n) (le (num 0) n)
def exp (x : B) : B := app (prim (.realFn .exp)) x
def log (x : B) : B := app (prim (.realFn .log)) x
def sqrt (x : B) : B := app2 (prim .rpow) x (div (num 1) (num 2))
def maxR (a b : B) : B := app2 (prim .max) a b
def prob (p : B) : B := and (lt (num 0) p) (lt p (num 1))
def label (y : B) : B := or (eq y (num 1)) (eq y (neg (num 1)))
def counts2 (name : Phrase) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real natP, dom2 .real fun a b => and (natP b) (lt (num 0) (add a b))], doc,
    value := close <| lamT .real natP fun a => lamT .real (fun b => and (natP b) (lt (num 0) (add a b))) fun b => body a b }
def counts4 (name : Phrase) (ok : B → B → B → B → B) (body : B → B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
    doms := [dom1 .real natP, dom2 .real fun _ b => natP b, dom3 .real fun _ _ c => natP c, dom4 .real fun a b c d => and (natP d) (ok a b c d)], doc,
    value := close <| lamT .real natP fun a => lamT .real natP fun b => lamT .real natP fun c =>
      lamT .real (fun d => and (natP d) (ok a b c d)) fun d => body a b c d }

def vocab : Vocab where
  notions := [
    { name := phrase!"sigmoid function", ty := F, doc := "`x ↦ 1/(1 + e^{-x})`",
      value := close <| lamR fun x => div (num 1) (add (num 1) (exp (neg x))) },
    { name := phrase!"rectified linear unit", ty := F, doc := "`x ↦ max(x, 0)`", value := close <| lamR fun x => maxR x (num 0) },
    { name := phrase!"softplus function", ty := F, doc := "`x ↦ log(1 + e^x)`", value := close <| lamR fun x => log (add (num 1) (exp x)) },
    { name := phrase!"binary cross-entropy of the prediction $v$ for the label $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real prob, dom2 .real fun _ y => and (le (num 0) y) (le y (num 1))],
      doc := "`-(y log p + (1-y) log(1-p))`",
      value := close <| lamT .real prob fun p => lamT .real (fun y => and (le (num 0) y) (le y (num 1))) fun y =>
        neg (add (mul y (log p)) (mul (sub (num 1) y) (log (sub (num 1) p)))) },
    { name := phrase!"hinge loss of the score $v$ for the label $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [none, dom2 .real fun _ y => label y], doc := "`max(0, 1 - ys)` for a label `y = ±1`",
      value := close <| lamR fun s => lamT .real label fun y => maxR (num 0) (sub (num 1) (mul y s)) },
    counts2 phrase!"precision for $v$ true positives and $v$ false positives" (fun tp fp => div tp (add tp fp)) "`TP/(TP + FP)`",
    counts2 phrase!"recall for $v$ true positives and $v$ false negatives" (fun tp fn => div tp (add tp fn)) "`TP/(TP + FN)`",
    { name := phrase!"F1 score for $v$ true positives, $v$ false positives and $v$ false negatives", ty := .real ⟶ .real ⟶ .real ⟶ .real,
      doms := [dom1 .real natP, dom2 .real fun _ b => natP b, dom3 .real fun a b c => and (natP c) (lt (num 0) (add a (add b c)))],
      doc := "`2TP/(2TP + FP + FN)`",
      value := close <| lamT .real natP fun a => lamT .real natP fun b => lamT .real (fun c => and (natP c) (lt (num 0) (add a (add b c)))) fun c =>
        div (mul (num 2) a) (add (mul (num 2) a) (add b c)) },
    counts4 phrase!"classification accuracy for $v$ true positives, $v$ true negatives, $v$ false positives and $v$ false negatives"
      (fun a b c d => lt (num 0) (add (add a b) (add c d)))
      (fun a b c d => div (add a b) (add (add a b) (add c d))) "`(TP + TN)/(TP + TN + FP + FN)`",
    counts4 phrase!"Matthews correlation coefficient for $v$ true positives, $v$ true negatives, $v$ false positives and $v$ false negatives"
      (fun a b c d => lt (num 0) (mul (mul (add a c) (add a d)) (mul (add b c) (add b d))))
      (fun a b c d => div (sub (mul a b) (mul c d)) (sqrt (mul (mul (add a c) (add a d)) (mul (add b c) (add b d)))))
      "`(TP·TN - FP·FN)/√((TP+FP)(TP+FN)(TN+FP)(TN+FN))`"]

end Leanify.Learning
