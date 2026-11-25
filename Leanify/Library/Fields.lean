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
import Leanify.Library.Asymptotics
import Leanify.Library.Transforms
import Leanify.Library.Calculus
import Leanify.Library.Risk
import Leanify.Library.StochasticOrders
import Leanify.Library.Finance
import Leanify.Library.Topologies
import Leanify.Library.MetricSpaces
import Leanify.Library.Approximation
import Leanify.Library.Iteration
import Leanify.Library.OdeSolvers
import Leanify.Library.Series
import Leanify.Library.Integration
import Leanify.Library.PlaneGeometry
import Leanify.Library.MatrixNorms
import Leanify.Library.SpecialNumbers
import Leanify.Library.Recurrences
import Leanify.Library.Copulas
import Leanify.Library.OrthogonalPolynomials
import Leanify.Library.Counting
import Leanify.Library.Samples
import Leanify.Library.TimeSeries
import Leanify.Library.Testing
import Leanify.Library.Descent
import Leanify.Library.FunctionalEquations
import Leanify.Library.Convexity
import Leanify.Library.Fractional
import Leanify.Library.Utility
import Leanify.Library.MarkovChains
import Leanify.Library.Curves
import Leanify.Library.ContinuedFractions
import Leanify.Library.Digits
import Leanify.Library.Branching
import Leanify.Library.Queues
import Leanify.Library.Reliability
import Leanify.Library.Codes
import Leanify.Library.HigherFunctions
import Leanify.Library.Summability
import Leanify.Library.IntegralEquations
import Leanify.Library.ClassicalPdes
import Leanify.Library.Economics
import Leanify.Library.Extremes
import Leanify.Library.Games
import Leanify.Library.Regression
import Leanify.Library.Bayesian
import Leanify.Library.Majorization
import Leanify.Library.Odes
import Leanify.Library.RandomWalks
import Leanify.Library.FunctionSequences
import Leanify.Library.Concentration
import Leanify.Library.Channels
import Leanify.Library.Actuarial
import Leanify.Library.Epidemics
import Leanify.Library.Triangles
import Leanify.Library.Solids
import Leanify.Library.AnalyticNumberTheory
import Leanify.Library.Collatz
import Leanify.Library.Variations
import Leanify.Library.Quadratics
import Leanify.Library.ClassicalProbability
import Leanify.Library.Cryptography
import Leanify.Library.Fractals
import Leanify.Library.Diophantine
import Leanify.Library.Mechanics
import Leanify.Library.Inventory
import Leanify.Library.Algorithms
import Leanify.Library.PopulationGenetics
import Leanify.Library.Waves
import Leanify.Library.Relativity
import Leanify.Library.PopulationDynamics
import Leanify.Library.Circuits
import Leanify.Library.Thermodynamics
import Leanify.Library.SphericalGeometry
import Leanify.Library.FloatingPoint
import Leanify.Library.LatticePoints
import Leanify.Library.CombinatorialGames
import Leanify.Library.Kinetics
import Leanify.Library.Fluids
import Leanify.Library.Quantum
import Leanify.Library.Designs
import Leanify.Library.DiagnosticTests
import Leanify.Library.Signals
import Leanify.Library.Voting
import Leanify.Library.Materials
import Leanify.Library.Astronomy
import Leanify.Library.Electromagnetism
import Leanify.Library.Polyhedra
import Leanify.Library.Betting
import Leanify.Library.Surfaces
import Leanify.Library.GraphCounts
import Leanify.Library.Kinematics
import Leanify.Library.Optics
import Leanify.Library.Pharmacokinetics
import Leanify.Library.Macroeconomics
import Leanify.Library.Acoustics
import Leanify.Library.Ratings
import Leanify.Library.Learning
import Leanify.Library.Calendar
import Leanify.Library.Crystallography
import Leanify.Library.MapProjections
import Leanify.Library.Music

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
  ("realsets", Topology.vocab),
  ("realfunctions", Analysis.vocab),
  ("vectors", Vectors.vocab),
  ("geometry", Geometry.vocab),
  ("congruences", Congruences.vocab),
  ("groups", Groups.vocab),
  ("means", Means.vocab),
  ("densities", Densities.vocab),
  ("fourier", Fourier.vocab),
  ("information", Information.vocab),
  ("optimization", Optimization.vocab),
  ("dynamics", Dynamics.vocab),
  ("asymptotics", Asymptotics.vocab),
  ("transforms", Transforms.vocab),
  ("calculus", Calculus.vocab),
  ("risk", Risk.vocab),
  ("stochasticorders", StochasticOrders.vocab),
  ("finance", Finance.vocab),
  ("topologies", Topologies.vocab),
  ("metricspaces", MetricSpaces.vocab),
  ("approximation", Approximation.vocab),
  ("iteration", Iteration.vocab),
  ("odesolvers", OdeSolvers.vocab),
  ("series", Series.vocab),
  ("integration", Integration.vocab),
  ("planegeometry", PlaneGeometry.vocab),
  ("matrixnorms", MatrixNorms.vocab),
  ("specialnumbers", SpecialNumbers.vocab),
  ("recurrences", Recurrences.vocab),
  ("copulas", Copulas.vocab),
  ("orthogonalpolynomials", OrthogonalPolynomials.vocab),
  ("counting", Counting.vocab),
  ("samples", Samples.vocab),
  ("timeseries", TimeSeries.vocab),
  ("testing", Testing.vocab),
  ("descent", Descent.vocab),
  ("functionalequations", FunctionalEquations.vocab),
  ("convexity", Convexity.vocab),
  ("fractional", Fractional.vocab),
  ("utility", Utility.vocab),
  ("markovchains", MarkovChains.vocab),
  ("curves", Curves.vocab),
  ("continuedfractions", ContinuedFractions.vocab),
  ("digits", Digits.vocab),
  ("branching", Branching.vocab),
  ("queues", Queues.vocab),
  ("reliability", Reliability.vocab),
  ("codes", Codes.vocab),
  ("higherfunctions", HigherFunctions.vocab),
  ("summability", Summability.vocab),
  ("integralequations", IntegralEquations.vocab),
  ("classicalpdes", ClassicalPdes.vocab),
  ("economics", Economics.vocab),
  ("extremes", Extremes.vocab),
  ("games", Games.vocab),
  ("regression", Regression.vocab),
  ("bayesian", Bayesian.vocab),
  ("majorization", Majorization.vocab),
  ("odes", Odes.vocab),
  ("randomwalks", RandomWalks.vocab),
  ("functionsequences", FunctionSequences.vocab),
  ("concentration", Concentration.vocab),
  ("channels", Channels.vocab),
  ("actuarial", Actuarial.vocab),
  ("epidemics", Epidemics.vocab),
  ("triangles", Triangles.vocab),
  ("solids", Solids.vocab),
  ("analyticnumbertheory", AnalyticNumberTheory.vocab),
  ("collatz", Collatz.vocab),
  ("variations", Variations.vocab),
  ("quadratics", Quadratics.vocab),
  ("classicalprobability", ClassicalProbability.vocab),
  ("cryptography", Cryptography.vocab),
  ("fractals", Fractals.vocab),
  ("diophantine", Diophantine.vocab),
  ("mechanics", Mechanics.vocab),
  ("inventory", Inventory.vocab),
  ("algorithms", Algorithms.vocab),
  ("populationgenetics", PopulationGenetics.vocab),
  ("waves", Waves.vocab),
  ("relativity", Relativity.vocab),
  ("populationdynamics", PopulationDynamics.vocab),
  ("circuits", Circuits.vocab),
  ("thermodynamics", Thermodynamics.vocab),
  ("sphericalgeometry", SphericalGeometry.vocab),
  ("floatingpoint", FloatingPoint.vocab),
  ("latticepoints", LatticePoints.vocab),
  ("combinatorialgames", CombinatorialGames.vocab),
  ("kinetics", Kinetics.vocab),
  ("fluids", Fluids.vocab),
  ("quantum", Quantum.vocab),
  ("designs", Designs.vocab),
  ("diagnostictests", DiagnosticTests.vocab),
  ("signals", Signals.vocab),
  ("voting", Voting.vocab),
  ("materials", Materials.vocab),
  ("astronomy", Astronomy.vocab),
  ("electromagnetism", Electromagnetism.vocab),
  ("polyhedra", Polyhedra.vocab),
  ("betting", Betting.vocab),
  ("surfaces", Surfaces.vocab),
  ("graphcounts", GraphCounts.vocab),
  ("kinematics", Kinematics.vocab),
  ("optics", Optics.vocab),
  ("pharmacokinetics", Pharmacokinetics.vocab),
  ("macroeconomics", Macroeconomics.vocab),
  ("acoustics", Acoustics.vocab),
  ("ratings", Ratings.vocab),
  ("learning", Learning.vocab),
  ("calendar", Calendar.vocab),
  ("crystallography", Crystallography.vocab),
  ("mapprojections", MapProjections.vocab),
  ("music", Music.vocab)]

/-- The names of the fields. -/
def names : List String := all.map (·.1)

/-- The fields that a field includes: `hilbert` is `unitsquare` with more words, `markov` is
`hilbert` with more, `copulas` is `markov` with more, `metricspaces` is `topologies` with
more, `planegeometry` is `geometry`, `matrixnorms` is `matrices` and `markovchains` is `matrixnorms` with more and `majorization` is `vectors` with more. Their entries are tagged with the field that adds
them. -/
def includes : List (String × List String) :=
  [("hilbert", ["unitsquare"]), ("markov", ["unitsquare", "hilbert"]), ("metricspaces", ["topologies"]), ("planegeometry", ["geometry"]),
   ("matrixnorms", ["matrices"]), ("copulas", ["unitsquare", "hilbert", "markov"]),
   ("markovchains", ["matrices", "matrixnorms"]),
   ("majorization", ["vectors"])]

/-- Bundles: a name for several fields, so that an article names a branch of mathematics
(`\usepackage[vocab=analysis]{leanify}`) and not each of its fields. A bundle may name
other bundles, so they form a tree: `math` has every field, its seven realms are the
branches of mathematics, and inside them are areas (`probability`, `linearalgebra`). A field
may be in several (`realsets` is in `analysis` and in `topology`). A bundle has no words of
its own: the article is read with its fields, in this order, exactly as if it had named
them. The fields of a bundle read no phrase in two ways, except a notion whose meanings take
arguments of different types (`resolvedByType`), where the type of the argument decides
(`lake exe glossary --bundles` checks this, and `scripts/ci.sh` reads the test article of
every member with the bundle and compares). `docs/libraries.md` draws the tree. -/
def bundles : List (String × List String) := [
  -- the realms, and `math` with all of them
  ("math", ["analysis", "algebra", "topology", "numerics", "stochastic", "discrete", "numbertheory"]),
  ("analysis", ["realfunctions", "realsets", "calculus", "series", "integration", "optimization", "asymptotics",
    "transforms", "fourier", "signals", "dynamics", "functionalequations", "convexity", "fractional", "summability", "functionsequences", "odes", "epidemics", "populationdynamics", "pharmacokinetics", "variations", "physics", "integralequations", "classicalpdes", "elementary", "complex", "torus"]),
  ("algebra", ["linearalgebra", "polynomials", "quadratics", "groups"]),
  ("topology", ["realsets", "topologies", "metricspaces", "geometry", "planegeometry", "triangles", "solids", "polyhedra", "sphericalgeometry", "mapprojections", "surfaces", "curves", "fractals"]),
  ("numerics", ["approximation", "iteration", "odesolvers", "matrixnorms", "descent", "floatingpoint"]),
  ("stochastic", ["statistics", "finance", "utility", "economics", "macroeconomics", "games", "ratings", "queues", "reliability", "actuarial", "inventory", "voting"]),
  ("discrete", ["combinatorics", "counting", "permutations", "graphs", "graphcounts", "recurrences", "codes", "algorithms", "combinatorialgames", "designs"]),
  ("numbertheory", ["numbers", "arithmetic", "congruences", "specialnumbers", "analyticnumbertheory", "continuedfractions", "digits", "collatz", "cryptography", "diophantine", "latticepoints", "calendar"]),
  -- the areas inside them
  ("physics", ["mechanics", "waves", "relativity", "circuits", "thermodynamics", "kinetics", "fluids", "quantum", "materials", "astronomy", "electromagnetism", "kinematics", "optics", "acoustics", "music", "crystallography"]),
  ("elementary", ["special", "hyperbolic", "trigonometry", "means", "orthogonalpolynomials", "higherfunctions"]),
  ("linearalgebra", ["vectors", "matrices", "majorization"]),
  ("probability", ["distributions", "densities", "information", "channels", "concentration", "classicalprobability", "risk", "stochasticorders", "markovchains", "branching", "randomwalks", "extremes", "populationgenetics", "betting"]),
  ("dependence", ["copulas"]),
  ("statistics", ["probability", "samples", "regression", "timeseries", "testing", "bayesian", "diagnostictests", "learning", "dependence"])]

/-- The realms: the bundles that `math` names, each a branch of mathematics. -/
def realms : List String := (bundles.lookup "math").getD []

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

/-- The types of the first `k` arguments of a type. -/
def argTys : Nat → Ty → List Ty
  | k + 1, .fn a b => a :: argTys k b
  | _, _ => []

/-- The number of arguments of a phrase (its formulas). -/
def slots (p : Phrase) : Nat :=
  p.foldl (fun k i => match i with | .v => k + 1 | .f segs => k + segs.length - 1 | _ => k) 0

/-- A notion phrase whose meanings take arguments of different types (`the inverse of
$v$`: of a permutation, a matrix, a real function). In a formula or a sentence the types of
the arguments decide between them, as the type of the object decides between adjectives;
only a definition `We write … for the inverse of $\sigma$`, whose letter has no type yet,
has to say which one it means. -/
def resolvedByType (V : Vocab) (p : Phrase) : Bool :=
  let ns := V.notions.filter (·.name == p)
  let keys := (ns.map fun n => argTys (slots p) n.ty).eraseDups
  !ns.isEmpty && slots p > 0 && keys.length == (ns.map fun n => (n.ty, n.value)).eraseDups.length &&
    V.mods.all (·.phrase != p) && V.nouns.all (·.sing != p)

/-- The collisions of a bundle: those of its fields with one another (not the two meanings
of *natural number* in the core, which every article has to choose between, nor a notion
whose meanings the types of its arguments tell apart). -/
def bundleCollisions (b : String) : List (Phrase × List Codes) :=
  let coreKeys := (collisions Vocab.core).map (·.1)
  let V := select [b]
  (collisions V).filter fun (p, _) => !coreKeys.contains p && !resolvedByType V p

/-- The notion phrases of a bundle that the types of their arguments resolve. -/
def bundleOverloads (b : String) : List (Phrase × List Codes) :=
  let coreKeys := (collisions Vocab.core).map (·.1)
  let V := select [b]
  (collisions V).filter fun (p, _) => !coreKeys.contains p && resolvedByType V p

/-- The named fields that do not exist. -/
def unknown (fs : List String) : List String := (expand fs).filter fun f => (all.lookup f).isNone

end Leanify.Fields
