import Leanify.Library.UnitSquare
import Leanify.Library.Distributions
import Leanify.Library.Numbers
import Leanify.Library.Torus
import Leanify.Library.Complex
import Leanify.Library.Hyperbolic
import Leanify.Library.Trigonometry
import Leanify.Library.Markov
import Leanify.Library.Arithmetic
import Leanify.Library.Combinatorics
import Leanify.Library.Polynomials
import Leanify.Library.Graphs
import Leanify.Library.Permutations
import Leanify.Library.Matrices
import Leanify.Library.Special
import Leanify.Library.Topology
import Leanify.Library.Analysis
import Leanify.Library.Vectors
import Leanify.Library.Geometry
import Leanify.Library.Congruences
import Leanify.Library.Groups
import Leanify.Library.Means
import Leanify.Library.Densities
import Leanify.Library.Fourier
import Leanify.Library.Information
import Leanify.Library.Optimization
import Leanify.Library.Dynamics

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
  ("hilbert", Hilbert.vocab),
  ("markov", Markov.vocab),
  ("distributions", Distributions.vocab),
  ("numbers", Numbers.vocab),
  ("torus", Torus.vocab),
  ("complex", Complex.vocab),
  ("hyperbolic", Hyperbolic.vocab),
  ("trigonometry", Trigonometry.vocab),
  ("arithmetic", Arithmetic.vocab),
  ("combinatorics", Combinatorics.vocab),
  ("polynomials", Polynomials.vocab),
  ("graphs", Graphs.vocab),
  ("permutations", Permutations.vocab),
  ("matrices", Matrices.vocab),
  ("special", Special.vocab),
  ("topology", Topology.vocab),
  ("analysis", Analysis.vocab),
  ("vectors", Vectors.vocab),
  ("geometry", Geometry.vocab),
  ("congruences", Congruences.vocab),
  ("groups", Groups.vocab),
  ("means", Means.vocab),
  ("densities", Densities.vocab),
  ("fourier", Fourier.vocab),
  ("information", Information.vocab),
  ("optimization", Optimization.vocab),
  ("dynamics", Dynamics.vocab)]

/-- The names of the fields. -/
def names : List String := all.map (·.1)

/-- The fields that a field includes: `hilbert` is `unitsquare` with more words, and `markov`
is `hilbert` with more. Their entries are tagged with the field that adds them. -/
def includes : List (String × List String) :=
  [("hilbert", ["unitsquare"]), ("markov", ["unitsquare", "hilbert"])]

/-- The core vocabulary followed by the named fields, in order (each entry tagged
with its field). A field that another named field includes is left out: its words are there. -/
def select (fs : List String) : Vocab :=
  let fs := fs.filter fun f => !fs.any fun g => ((includes.lookup g).getD []).contains f
  fs.foldl (fun V f => match all.lookup f with
    | some W => V ++ (if (includes.lookup f).isSome then W else Vocab.tag (f.toList.map Char.toNat) W)
    | none => V) Vocab.core

/-- The named fields that do not exist. -/
def unknown (fs : List String) : List String := fs.filter fun f => (all.lookup f).isNone

end Leanify.Fields
