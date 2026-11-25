import Leanify.Library.Core

/-! # Vocabulary: diagnostic tests and 2×2 tables

The measures of a diagnostic test and of a two-by-two table of exposure and outcome (`We
write $P(s,c,p)$ for the positive predictive value for sensitivity
$s$, specificity $c$ and prevalence $p$.`).

* notions: the positive and negative predictive values (Bayes' formula), the positive and
  negative likelihood ratios `s/(1-c)` and `(1-s)/c`, the Youden index `s + c - 1` and the
  accuracy `sp + c(1-p)` of a test with sensitivity `s` and specificity `c` at prevalence `p`;
  the post-test odds (pre-test odds times the likelihood ratio); the odds ratio `ad/(bc)` and
  the relative risk `(a/(a+b))/(c/(c+d))` of the table `[[a, b], [c, d]]` (exposed in the first
  row, cases in the first column); the number needed to treat `1/(r_c - r_t)`.

Every meaning is a term of the core language. -/

namespace Leanify.DiagnosticTests
open Build Core

def pos (x : B) : B := lt (num 0) x
def prob (x : B) : B := and (lt (num 0) x) (lt x (num 1))
def three (name : Phrase) (body : B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real, doms := [dom1 .real prob, dom2 .real fun _ c => prob c, dom3 .real fun _ _ p => prob p], doc,
    value := close <| lamT .real prob fun s => lamT .real prob fun c => lamT .real prob fun p => body s c p }
def two (name : Phrase) (body : B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real, doms := [dom1 .real prob, dom2 .real fun _ c => prob c], doc,
    value := close <| lamT .real prob fun s => lamT .real prob fun c => body s c }
def table (name : Phrase) (body : B → B → B → B → B) (doc : String) : Notion :=
  { name, ty := .real ⟶ .real ⟶ .real ⟶ .real ⟶ .real,
    doms := [dom1 .real pos, dom2 .real fun _ b => pos b, dom3 .real fun _ _ c => pos c, dom4 .real fun _ _ _ d => pos d], doc,
    value := close <| lamT .real pos fun a => lamT .real pos fun b => lamT .real pos fun c => lamT .real pos fun d => body a b c d }

def vocab : Vocab where
  notions := [
    three phrase!"positive predictive value for sensitivity $v$, specificity $v$ and prevalence $v$"
      (fun s c p => div (mul s p) (add (mul s p) (mul (sub (num 1) c) (sub (num 1) p)))) "`sp/(sp + (1-c)(1-p))`",
    three phrase!"negative predictive value for sensitivity $v$, specificity $v$ and prevalence $v$"
      (fun s c p => div (mul c (sub (num 1) p)) (add (mul c (sub (num 1) p)) (mul (sub (num 1) s) p))) "`c(1-p)/(c(1-p) + (1-s)p)`",
    three phrase!"accuracy for sensitivity $v$, specificity $v$ and prevalence $v$"
      (fun s c p => add (mul s p) (mul c (sub (num 1) p))) "`sp + c(1-p)`",
    two phrase!"positive likelihood ratio for sensitivity $v$ and specificity $v$" (fun s c => div s (sub (num 1) c)) "`s/(1-c)`",
    two phrase!"negative likelihood ratio for sensitivity $v$ and specificity $v$" (fun s c => div (sub (num 1) s) c) "`(1-s)/c`",
    two phrase!"Youden index for sensitivity $v$ and specificity $v$" (fun s c => sub (add s c) (num 1)) "`s + c - 1`",
    { name := phrase!"post-test odds for the pre-test odds $v$ and the likelihood ratio $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real fun o => le (num 0) o, dom2 .real fun _ l => le (num 0) l], doc := "`o · LR`",
      value := close <| lamT .real (fun o => le (num 0) o) fun o => lamT .real (fun l => le (num 0) l) fun l => mul o l },
    table phrase!"odds ratio of the table with entries $v$, $v$, $v$ and $v$" (fun a b c d => div (mul a d) (mul b c)) "`ad/(bc)`",
    table phrase!"relative risk of the table with entries $v$, $v$, $v$ and $v$"
      (fun a b c d => div (div a (add a b)) (div c (add c d))) "`(a/(a+b))/(c/(c+d))`",
    { name := phrase!"number needed to treat for the control event rate $v$ and the treatment event rate $v$", ty := .real ⟶ .real ⟶ .real,
      doms := [dom1 .real prob, dom2 .real fun c t => and (le (num 0) t) (lt t c)],
      doc := "`1/(r_c - r_t)`: the reciprocal of the absolute risk reduction",
      value := close <| lamT .real prob fun c => lamT .real (fun t => and (le (num 0) t) (lt t c)) fun t => div (num 1) (sub c t) }]

end Leanify.DiagnosticTests
