import Leanify.Library.UnitSquare
import Leanify.Library.Distributions
import Leanify.Library.Numbers
import Leanify.Library.Torus

/-! # The fields of the vocabulary

An article names the fields it draws its words from (`\usepackage[vocab={numbers,
analysis}]{leanify}`, or `--vocab numbers,analysis`). Each field gives every phrase
at most one meaning; the core vocabulary is always there. When two named fields read
the same words differently, Leanify refuses the phrase and the article says which
meaning it uses, in a sentence of its own (`By a distribution we mean a probability
distribution on $\mathbb{N}_0$.`): what the reader sees is what Leanify reads.
`docs/vocabulary.md` explains this and lists the fields. -/

namespace Leanify.Fields

/-- The fields, by name. -/
def all : List (String × Vocab) := [
  ("unitsquare", UnitSquare.vocab),
  ("distributions", Distributions.vocab),
  ("numbers", Numbers.vocab),
  ("torus", Torus.vocab)]

/-- The names of the fields. -/
def names : List String := all.map (·.1)

/-- The core vocabulary followed by the named fields, in order (each entry tagged
with its field). -/
def select (fs : List String) : Vocab :=
  fs.foldl (fun V f => match all.lookup f with
    | some W => V ++ Vocab.tag (f.toList.map Char.toNat) W
    | none => V) Vocab.core

/-- The named fields that do not exist. -/
def unknown (fs : List String) : List String := fs.filter fun f => (all.lookup f).isNone

end Leanify.Fields
