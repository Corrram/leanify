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
import Leanify.Library.Structures
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
import Leanify.Library.RandomVariables
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
import Leanify.Library.RandomVectors
import Leanify.Library.LinearSystems
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
import Leanify.Library.FixedIncome
import Leanify.Library.Options
import Leanify.Library.PoissonProcesses
import Leanify.Library.SurveySampling
import Leanify.Library.Convergence
import Leanify.Library.FiniteFields
import Leanify.Library.LieAlgebras
import Leanify.Library.Words
import Leanify.Library.Orbits
import Leanify.Library.Variograms
import Leanify.Library.Traffic
import Leanify.Library.GeometricProbability

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
  ("structures", Structures.vocab),
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
  ("music", Music.vocab),
  ("fixedincome", FixedIncome.vocab),
  ("options", Options.vocab),
  ("poissonprocesses", PoissonProcesses.vocab),
  ("surveysampling", SurveySampling.vocab),
  ("convergence", Convergence.vocab),
  ("finitefields", FiniteFields.vocab),
  ("liealgebras", LieAlgebras.vocab),
  ("words", Words.vocab),
  ("orbits", Orbits.vocab),
  ("variograms", Variograms.vocab),
  ("traffic", Traffic.vocab),
  ("geometricprobability", GeometricProbability.vocab),
  ("randomvariables", RandomVariables.vocab),
  ("randomvectors", RandomVectors.vocab),
  ("linearsystems", LinearSystems.vocab)]

/-- The names of the fields. -/
def names : List String := all.map (·.1)

/-- The fields that a field builds on, the first of a chain first: `hilbert` is `unitsquare`
with more words, `markov` is `hilbert` with more, `copulas` is `markov` with more,
`metricspaces` is `topologies` with more, `planegeometry` is `geometry`, `matrixnorms` is
`matrices`, `markovchains` is `matrixnorms` and `majorization` is `vectors` with more;
`linearsystems` builds on `vectors` and `matrices`, and `randomvectors` on these, `complex`
and `linearsystems`. A field comes with the fields it builds on; fields that build on the
same field share its words and types (`select`). -/
def includes : List (String × List String) :=
  [("hilbert", ["unitsquare"]), ("markov", ["unitsquare", "hilbert"]), ("metricspaces", ["topologies"]), ("planegeometry", ["geometry"]),
   ("matrixnorms", ["matrices"]), ("copulas", ["unitsquare", "hilbert", "markov"]),
   ("markovchains", ["matrices", "matrixnorms"]),
   ("majorization", ["vectors"]), ("randomvectors", ["vectors", "matrices", "complex", "linearsystems"]),
   ("linearsystems", ["vectors", "matrices"])]

/-- Bundles: a name for several fields, so that an article names a branch of mathematics
(`\usepackage[vocab=analysis]{leanify}`) and not each of its fields. A bundle may name
other bundles, so they form a tree: `math` has every field, its seven realms are the
branches of mathematics, and inside them are areas (`probability`, `linearalgebra`). A field
may be in several (`realsets` is in `analysis` and in `topology`). A bundle has no words of
its own: the article is read with its fields, in this order, exactly as if it had named
them. The fields of a bundle read no phrase in two ways, except a notion whose meanings take
arguments of different types (`resolvedByType`), where the type of the argument decides, a
modifier whose variables have different types, and a noun whose meanings have different
complements or, one of them, none (`collisions`), where the formula or the complement decides
(`lake exe glossary --bundles` checks this, and `scripts/ci.sh` reads the test article of
every member with the bundle and compares). `docs/libraries.md` draws the tree. -/
def bundles : List (String × List String) := [
  -- the realms, and `math` with all of them
  ("math", ["analysis", "algebra", "topology", "numerics", "stochastic", "discrete", "numbertheory"]),
  ("analysis", ["realfunctions", "realsets", "calculus", "series", "integration", "optimization", "asymptotics",
    "transforms", "fourier", "signals", "dynamics", "functionalequations", "convexity", "fractional", "summability", "functionsequences", "odes", "epidemics", "populationdynamics", "pharmacokinetics", "variations", "physics", "integralequations", "classicalpdes", "elementary", "complex", "torus"]),
  ("algebra", ["linearalgebra", "polynomials", "quadratics", "structures", "finitefields", "liealgebras"]),
  ("topology", ["realsets", "structures", "topologies", "metricspaces", "geometry", "planegeometry", "triangles", "solids", "polyhedra", "sphericalgeometry", "mapprojections", "surfaces", "curves", "fractals"]),
  ("numerics", ["approximation", "iteration", "odesolvers", "matrixnorms", "descent", "floatingpoint", "convergence"]),
  ("stochastic", ["statistics", "finance", "fixedincome", "options", "utility", "economics", "macroeconomics", "games", "ratings", "queues", "reliability", "actuarial", "inventory", "voting", "traffic"]),
  ("discrete", ["combinatorics", "counting", "words", "permutations", "graphs", "graphcounts", "recurrences", "codes", "algorithms", "combinatorialgames", "designs"]),
  ("numbertheory", ["numbers", "arithmetic", "congruences", "specialnumbers", "analyticnumbertheory", "continuedfractions", "digits", "collatz", "cryptography", "diophantine", "latticepoints", "calendar"]),
  -- the areas inside them
  ("physics", ["mechanics", "waves", "relativity", "circuits", "thermodynamics", "kinetics", "fluids", "quantum", "materials", "astronomy", "electromagnetism", "kinematics", "optics", "acoustics", "music", "crystallography", "orbits"]),
  ("elementary", ["special", "hyperbolic", "trigonometry", "means", "orthogonalpolynomials", "higherfunctions"]),
  ("linearalgebra", ["vectors", "matrices", "majorization", "linearsystems"]),
  -- names of parts of `structures`, kept for articles that name them
  ("groups", ["structures"]), ("rings", ["structures"]), ("spaces", ["structures"]),
  ("probability", ["randomvariables", "randomvectors", "distributions", "densities", "information", "channels", "concentration", "classicalprobability", "geometricprobability", "risk", "stochasticorders", "markovchains", "branching", "randomwalks", "poissonprocesses", "extremes", "populationgenetics", "betting"]),
  ("dependence", ["copulas"]),
  ("statistics", ["probability", "samples", "regression", "timeseries", "testing", "bayesian", "diagnostictests", "learning", "surveysampling", "variograms", "dependence"])]

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

/-- The fields whose own words are written for wherever the fields they build on stand in
the vocabulary (`randomvectors` on `vectors`, `matrices`, `complex` and `linearsystems`):
the words, for the first constant and the type of each field of `includes`, in its order, and
of the field itself. The own words of any other field that builds on fields are found from
its vocabulary (`ownWords`). -/
def extensions : List (String × (List (Nat × Nat) → Nat → Nat → Vocab)) :=
  [("randomvectors", fun bs co to =>
      match bs with
      | [(cv, tv), (cm, tm), (cc, tc), _] => RandomVectors.own { cv, tv, cm, tm, cc, tc, co, to }
      | _ => {}),
   ("linearsystems", fun bs co _ =>
      match bs with
      | [(_, tv), (_, tm)] => LinearSystems.own tv tm co
      | _ => {})]

/-- Where the own words of a field stand in a vocabulary: its first constant, type and
interval type. -/
abbrev Places := List (String × Nat × Nat × Nat)

/-- A vocabulary with the own words of the field `f` after it, where `f` is one of a chain
of fields each of which is the one before it with more words (`copulas` is `markov` is
`hilbert` is `unitsquare`, each with more), and the fields before it in the chain stand
at `at_`. In its vocabulary (`all`), the words of `f` come after those of the field before
it and use its constants by their indices there: they are renumbered for where the parts
stand. An interval type that `f` describes further (`[0,1]` of `unitsquare`, to which
`hilbert` adds its inner product) is replaced by the description of `f`. -/
def ownWords (V : Vocab) (at_ : Places) (f : String) (chain : List String) : Vocab :=
  match all.lookup f, chain.getLast?.bind (fun b => all.lookup b) with
  | some W, some B =>
    -- (where each field of the chain begins in the vocabulary of `f`, and here)
    let sizes (g : String) : Nat × Nat × Nat :=
      ((all.lookup g).map fun P => (P.consts.length, P.types.length, P.intervals.length)).getD (0, 0, 0)
    let los : List (Nat × Nat × Nat) := (0, 0, 0) :: chain.map sizes
    let here (g : String) : Nat × Nat × Nat :=
      if g == f then (V.consts.length, V.types.length, V.intervals.length) else (at_.lookup g).getD (0, 0, 0)
    let segs : List ((Nat × Nat × Nat) × (Nat × Nat × Nat)) := los.zip ((chain ++ [f]).map here)
    let at' (pick : Nat × Nat × Nat → Nat) (i : Nat) : Nat :=
      match segs.reverse.find? fun (lo, _) => pick lo ≤ i with
      | some (lo, h) => pick h + (i - pick lo)
      | none => i
    let fc := at' (·.1)
    let ft := at' (·.2.1)
    let own := Vocab.remap fc ft { W with
      types := W.types.drop B.types.length, consts := W.consts.drop B.consts.length,
      constNames := W.constNames.drop B.consts.length, constLean := W.constLean.drop B.consts.length,
      typeLean := W.typeLean.drop B.types.length, adjectives := W.adjectives.drop B.adjectives.length,
      nouns := W.nouns.drop B.nouns.length, mods := W.mods.drop B.mods.length,
      notions := W.notions.drop B.notions.length, methods := W.methods.drop B.methods.length,
      symbols := W.symbols.drop B.symbols.length, intervals := W.intervals.drop B.intervals.length }
    let V' := V.join own
    -- (the interval types of the chain that `f` describes further)
    let again := (Vocab.remap fc ft { W with intervals := W.intervals.take B.intervals.length }).intervals
    let ivs := (again.zip (B.intervals.zip (List.range B.intervals.length))).foldl (fun ivs (iv, old, k) =>
      if W.intervals[k]? == some old then ivs else ivs.set (at' (·.2.2) k) iv) V'.intervals
    { V' with intervals := ivs }
  | _, _ => V

/-- The core vocabulary followed by the named fields, in order (each entry tagged
with its field). A bundle stands for its fields. A field that builds on other fields
(`includes`) comes with them: they stand before it, once, and every field that builds on
them shares their words and types (a vector of `majorization` is a vector for
`randomvectors`). -/
def select (fs : List String) : Vocab :=
  ((expand fs).foldl (place 8) (Vocab.core, [])).1
where
  /-- The vocabulary with the field `f`, after the fields it builds on (unless it is there). -/
  place : Nat → Vocab × Places → String → Vocab × Places
    | 0, acc, _ => acc
    | fuel + 1, acc, f =>
      if (acc.2.lookup f).isSome then acc else
      let bases := (includes.lookup f).getD []
      let (V, at_) := bases.foldl (place fuel) acc
      let here := (V.consts.length, V.types.length, V.intervals.length)
      let tag := Vocab.tag (f.toList.map Char.toNat)
      match extensions.lookup f, all.lookup f with
      | some own, _ =>
        (V.join (tag (own (bases.map fun b => ((at_.lookup b).map fun (c, t, _) => (c, t)).getD (0, 0)) here.1 here.2.1)),
         at_ ++ [(f, here)])
      | none, some W =>
        if bases.isEmpty then (V ++ tag W, at_ ++ [(f, here)])
        else (ownWords V at_ f bases, at_ ++ [(f, here)])
      | none, none => (V, at_)

/-- The phrases of a vocabulary that have more than one meaning, with the fields of the
meanings: a notion with the same name and another type or value, a modifier or a noun with
the same phrase and type and another predicate, a symbol given twice. An article that
uses such a phrase is asked which meaning it has. -/
def collisions (V : Vocab) : List (Phrase × List Codes) :=
  let fields {α : Type} (field : α → Codes) (xs : List α) : List Codes := (xs.map field).eraseDups
  let ns := V.notions.filterMap fun n =>
    let same := V.notions.filter (·.name == n.name)
    if same.any fun m => m.ty != n.ty || m.value != n.value then some (n.name, fields (·.field) same) else none
  -- (the types of the variables of a modifier: of the leading arguments of its predicate)
  let rec lamTys : Nat → Tm → List Ty
    | k + 1, .lam t _ b => t :: lamTys k b
    | _, _ => []
  let slotsOf (p : Phrase) : Nat :=
    p.foldl (fun k i => match i with | .v => k + 1 | .f segs => k + segs.length - 1 | _ => k) 0
  let ms := V.mods.filterMap fun n =>
    let same := V.mods.filter fun m => m.phrase == n.phrase && m.ty == n.ty && m.prenominal == n.prenominal
    -- (modifiers told apart by the types of their variables, `dense in $v$` of a set and of a
    -- topology, are not: the formula says which is meant)
    let preds := (same.map (·.pred)).eraseDups
    let byVars := slotsOf n.phrase > 0 &&
      (preds.map fun p => lamTys (slotsOf n.phrase) p).eraseDups.length == preds.length
    if !byVars && same.any (·.pred != n.pred) then some (n.phrase, fields (·.field) same) else none
  let nouns := V.nouns.filterMap fun n =>
    let same := V.nouns.filter (·.sing == n.sing)
    -- (nouns told apart by the types of their complements, `subset of $A$`, are not)
    let meanings : List (Ty × Tm × Option (List Codes × Ty × Tm)) := (same.map fun m => (m.ty, m.pred, m.arg)).eraseDups
    -- (nor a noun with a complement beside the noun without one, `vector space over $K$`
    -- and `vector space`, `vector in $V$` and `vector`: the complement says which is meant)
    let argTys : List (Option Ty) := meanings.map fun m => m.2.2.map (·.2.1)
    let byArg := argTys.eraseDups.length == meanings.length
    -- (nouns of maps of different types: a signature says which, `a bijection $f\colon G\to H$`)
    let bySig := meanings.all (fun m => match m.1 with
        | .fn _ _ => true
        | t => V.methods.any fun me => me.ty == t && me.op == .sig) &&
      (meanings.map (·.1)).eraseDups.length == meanings.length
    let byArg := byArg || bySig
    if !byArg && same.any (fun m => m.ty != n.ty || m.pred != n.pred) then some (n.sing, fields (·.field) same) else none
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
