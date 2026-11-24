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

/-- Bundles: a name for several fields of one area, so that an article names the area
(`\usepackage[vocab=statistics]{leanify}`) and not each of its fields. A bundle may name
other bundles, so they form a tree, and a field may be in several. A bundle has no words
of its own: the article is read with its fields, in this order, exactly as if it had
named them. The fields of a bundle read no phrase in two ways (`scripts/ci.sh` reads the
test article of every member with the bundle and compares). -/
def bundles : List (String × List String) := [
  ("probability", ["distributions", "densities", "information"]),
  ("dependence", ["markov"]),
  ("statistics", ["probability", "dependence"]),
  ("numbertheory", ["numbers", "arithmetic", "congruences"]),
  ("discrete", ["combinatorics", "permutations", "graphs"]),
  ("linearalgebra", ["vectors", "matrices"]),
  ("algebra", ["linearalgebra", "polynomials", "groups"]),
  ("functions", ["analysis", "optimization", "fourier", "dynamics"]),
  ("elementary", ["special", "hyperbolic", "trigonometry", "means"]),
  ("realanalysis", ["functions", "topology", "elementary"])]

/-- The names of the bundles. -/
def bundleNames : List String := bundles.map (·.1)

/-- The fields that the names stand for: a field is itself, a bundle its fields (and those
of the bundles in it), each once, in the order of the first mention. -/
def expand (fs : List String) : List String :=
  let rec go : Nat → List String → List String
    | 0, fs => fs
    | k + 1, fs => fs.flatMap fun f => match bundles.lookup f with
      | some ms => go k ms
      | none => [f]
  (go 8 fs).eraseDups

/-- The core vocabulary followed by the named fields, in order (each entry tagged
with its field). A bundle stands for its fields. A field that another named field includes
is left out: its words are there. -/
def select (fs : List String) : Vocab :=
  let fs := expand fs
  let fs := fs.filter fun f => !fs.any fun g => ((includes.lookup g).getD []).contains f
  fs.foldl (fun V f => match all.lookup f with
    | some W => V ++ (if (includes.lookup f).isSome then W else Vocab.tag (f.toList.map Char.toNat) W)
    | none => V) Vocab.core

/-- The phrases of a vocabulary that have more than one meaning, with the fields of the
meanings: a notion with the same name and another type or value, a modifier or a noun with
the same phrase and type and another predicate, a symbol given twice. An article that
uses such a phrase is asked which meaning it has. -/
def collisions (V : Vocab) : List (Phrase × List Codes) :=
  let fields {α : Type} (field : α → Codes) (xs : List α) : List Codes := (xs.map field).eraseDups
  let ns := V.notions.filterMap fun n =>
    let same := V.notions.filter (·.name == n.name)
    if same.any fun m => m.ty != n.ty || m.value != n.value then some (n.name, fields (·.field) same) else none
  let ms := V.mods.filterMap fun n =>
    let same := V.mods.filter fun m => m.phrase == n.phrase && m.ty == n.ty && m.prenominal == n.prenominal
    if same.any (·.pred != n.pred) then some (n.phrase, fields (·.field) same) else none
  let nouns := V.nouns.filterMap fun n =>
    let same := V.nouns.filter (·.sing == n.sing)
    if same.any fun m => m.ty != n.ty || m.pred != n.pred then some (n.sing, fields (·.field) same) else none
  let syms := V.symbols.filterMap fun n =>
    let same := V.symbols.filter (·.sym == n.sym)
    if same.length > 1 then some ([PItem.m [.cmd (n.sym.drop 1)]], fields (·.field) same) else none
  (ns ++ ms ++ nouns ++ syms).eraseDups

/-- The collisions of a bundle: those of its fields with one another (not the two meanings
of *natural number* in the core, which every article has to choose between). -/
def bundleCollisions (b : String) : List (Phrase × List Codes) :=
  let coreKeys := (collisions Vocab.core).map (·.1)
  (collisions (select [b])).filter fun (p, _) => !coreKeys.contains p

/-- The named fields that do not exist. -/
def unknown (fs : List String) : List String := (expand fs).filter fun f => (all.lookup f).isNone

end Leanify.Fields
