import Leanify.Grammar
import Leanify.Vocab

/-! # Elaboration: the fixed readings of the grammar

Every construction of `Grammar` has exactly one reading, given here. Symbols
introduced by the article are *definitions*: their meaning is their defining
formula, nothing else. Applying a symbol outside the domain stated in its
definition is recorded as a definedness condition, never silently allowed.

Readings (`x`, `y` range over the domain of the noun or binder):
* `let S denote the class of Ns, that is, NP` — `S := {F | NP(F)}`; `N` names `S`.
* `For a N $x$, the NAME is $X(…) := e$` — defines `X` on `N`; further `= e'` are claims.
* `define $f:A\to B$ by …` — defines `f` on `A`; `f(A) ⊆ B` is a claim.
* `We say that a N $x$ is P of a M $y$ if φ for all …` — defines the relation `P`.
* `exactly one N $x$ with φ satisfies ψ` — `∃x∈N, φ ∧ ψ ∧ ∀y∈N, φ(y) ∧ ψ(y) → y = x`;
  following clauses about `its …` are inside this scope.
* `X is the only N with φ` — `X ∈ N ∧ φ(X) ∧ ∀y∈N, φ(y) → y = X`.
* `The maximum $F=m$ is attained only by X` — `∀x, F(x) ≤ m`, `X` is in the domain,
  `F(X) = m`, and `F(x) = m → x = X` (minimum: `≥`).
* `$λ$ increases bijectively from A onto B` — maps `A` into `B`, strictly increasing, onto `B`.
* `On I, … its derivative $d$ is positive for φ` — the derivative within `I` of the
  preceding right-hand side is `d`, and `φ → d > 0`.
* `φ for every $x\in A$, with equality only at ψ` — `∀x∈A, φ ∧ (a = b → ψ)` for the
  inequality `a ≤ b` of `φ`.
* `no N other than X attains the maximum` — `∀y∈N, F(y) = m → y = X`.
* `the map $λ$ sends F to G` — `∀x, F(λ x) = G(x)`.
* `only X attains it` — `X` attains the topic extremum, and no other element does.
* `X is P of Y` — the article's relation `P` holds of `X` and `Y`.
* `fix $b\in B$ and set|put|define DEFS` — the definitions under the binder `b`, which
  stays bound for the following sentences of the section.
* `For $b\in B$, set $f(x)\coloneqq e$` where the symbol `f` does not show `b` —
  `f` takes `b` as an implicit parameter, supplied from the scope at each use.
* a family defined again on a further parameter domain — one family on the union,
  defined only if no parameter lies in both domains.
* `define continuous functions $f:A\to\R$ by $f(a)=c$ and $f'(x)=g(x)$` —
  `f(x) = c + ∫_a^x g` for `x ∈ A`, defined when `g` is integrable there; where
  no piece of a piecewise `g` applies, the integrand is `0`.
* `every $(x,z)\in A^2$ satisfies $a\ge b$`, then `equality holds exactly on $S$`
  (`when φ`) — `∀ x z ∈ A, a = b ↔ (x,z) ∈ S` (`↔ φ`).
* `Both constants are sharp.` — each inequality `a ≤ b` of the preceding claim about every
  element of a domain cannot be improved: `∀ ε > 0, ∃ x, b - a < ε`.
* `$S$ is compact, convex, centrally symmetric` (a set of the plane), `$f$ is
  continuous, concave, strictly increasing` (on the domain of its definition).
* `Let $x\in A$.` in a result — `x` ranges over `A` in the rest of the result; a
  later `If φ,` about `x` is a hypothesis.
* `We call a copula $C$ NAME (ABBR) if φ.`, `$C$ is called NAME if φ.` — the
  article's notion `NAME` (also `ABBR`) of copulas: `λ C, φ`. Later `$C$ is NAME`,
  `every NAME copula is NAME'`, `an ABBR copula $C$` use it.
* `…, the map $x\mapsto e$, $x\in D$, is non-increasing` — `∀ x y ∈ D, x ≤ y → e(y) ≤ e(x)`.
* A definition inside a result (`Let $a,b\in A$, and let $G\coloneqq\sqrt{ab}$.`), in
  a claim (`the geometric mean $G\coloneqq\sqrt{ab}$ is at most …`) or after it
  (`…, where $d\coloneqq\sqrt a-\sqrt b$`) — a definition whose implicit parameters
  are the variables of its context that it uses, local to the result and its proof.
-/
namespace Leanify
open Grammar

structure Glob where
  key : Codes
  ty : Ty
  /-- Domain predicates of the curried arguments (`none`: the whole type). -/
  doms : List (Option Tm)
  family : Bool
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

inductive Role where
  | definition
  | statement (env : Nat)
  | step (env : Nat)
  | text
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

structure Claim where
  sent : Nat
  body : Tm
  role : Role
  cites : List Codes
  premises : List Nat
  /-- Made under a hypothesis that the proof refutes (`Suppose, for contradiction, …`,
  or the assumption that a contradiction ends): its hypotheses are not meant to hold
  together. For every other claim they should, and the report says whether they do. -/
  refuted : Bool := false
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

structure Err where
  code : Nat
  detail : Codes
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

inductive Outcome where
  | prose
  | failed (e : Err)
  | compiled (defs : List Nat) (claims : List Nat)
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

/-- Error codes (rendered by the driver). -/
def E.undefined := 1
def E.type := 2
def E.unsupported := 3
def E.noun := 4
def E.label := 5
def E.free := 6
def E.redefined := 7
def E.referent := 8
def E.shadow := 9
/-- The sentence has the form of an open construction (`$x$ is NAME`), but its words are
not a notion of the article: it is prose. -/
def E.prose := 10
/-- A phrase has several meanings in the article's vocabulary (in different fields). -/
def E.ambiguous := 11
/-- A convention lets constants depend on a phrase that is neither a variable nor the
fixed data. -/
def E.dependence := 12
/-- A finding whose detail is the whole message: what was not read, and how to write it. -/
def E.finding := 13

abbrev Local := Codes × Ty
abbrev Scope := List Local

/-- A generic constant of the article's conventions: `Throughout, $C$ and $C_m$ denote
positive constants.`, `In the definitions below, $C_{j,I}>0$ and $b_{j,I}\ge0$ may depend
on $j,I$ and the fixed data, and are uniform in $\ell$.` -/
structure GenericConst where
  /-- The letter (`C` for `C`, `C_m`, `C_{j,I}`). -/
  base : Codes
  /-- 0: a real number, 1: positive, 2: non-negative. -/
  sign : Nat := 0
  /-- The variables it may depend on besides the indices in its subscript, when the
  convention lists them (`strict`); otherwise its indices and the fixed data. -/
  deps : List Codes := []
  strict : Bool := false
  /-- Whether it may depend on the fixed data (`Fix …`, `… are fixed`). -/
  fixedOk : Bool := true
  /-- Variables it does not depend on (`uniform in`, `independent of`). -/
  uniform : List Codes := []
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

/-- A field: a function of `space` spatial coordinates (and a last time coordinate
if `time`), real-valued (`dim = 1`) or with `dim` components, the component index
(from 1) being its first argument. `doms` are the predicates of the coordinates'
domains (`[0,1)` for the time of `\mathbb{R}^3\times[0,1)`). -/
structure FieldInfo where
  dim : Nat
  space : Nat
  time : Bool
  doms : List (Option Tm)
  /-- On a torus `\mathbb{T}^n`: a function on `ℝⁿ` of period 1 in each spatial coordinate. -/
  periodic : Bool := false
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

/-- The number of coordinates of a field. -/
def FieldInfo.coords (i : FieldInfo) : Nat := i.space + (if i.time then 1 else 0)

/-- The topic extremum of a statement: the function's formula, its value, and
whether it is a maximum. -/
structure Extremum where
  isMax : Bool
  f : MT
  value : MT
  deriving Repr, Inhabited, Lean.ToExpr

/-- A bound variable: its name, type and domain predicate. -/
structure BindInfo where
  name : Codes
  ty : Ty
  pred : Option Tm
  deriving Inhabited, DecidableEq, Repr, Lean.ToExpr

/-- An item of a notation template: a fixed token, or the `k`-th argument. -/
inductive TItem where
  | fixed (t : Tok)
  | slot (k : Nat)
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

/-- A notation of the article (`We write $\mathbf E[X]$ for …`): formulas matching
`pat` are read as `repl`, with the arguments put in. -/
structure Template where
  pat : List TItem
  repl : List TItem
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

/-- A hypothesis of a result or a proof: `Assume that …`, or the heading of a case. -/
structure Hyp where
  /-- The list item it holds in (`0`: the whole result or proof). -/
  item : Nat
  /-- Made to be refuted (`Suppose, for contradiction, that …`). -/
  contra : Bool
  /-- The heading of a case. -/
  heading : Bool
  /-- The environment and the sentence that made it. -/
  env : Nat
  sent : Nat
  clause : Clause
  /-- The assumption it belongs to: the sentence that began it (`Assume further that …`
  belongs to the assumption before it). A new case and a contradiction end an
  assumption as a whole. -/
  group : Nat := 0
  deriving Inhabited, Repr, Lean.ToExpr

structure St where
  /-- The vocabulary of the article. -/
  vocab : Vocab := {}
  /-- Letters and Greek letters of the formulas of the sentences Leanify did not read so
  far: symbols the article may have introduced in words (`e` is in it when it is not
  only the base of a power). -/
  unreadIds : List Codes := []
  globs : List Glob := []
  values : List Tm := []
  claims : List Claim := []
  /-- Noun phrases naming a predicate (a class). -/
  nouns : List (List Codes × Nat) := []
  /-- Noun phrases naming an operation, e.g. `survival copula`. -/
  ops : List (List Codes × Nat) := []
  /-- Relation phrases, e.g. `supported on the graph`. -/
  preds : List (List Codes × Nat) := []
  /-- Named objects, e.g. `tent map`. -/
  named : List (List Codes × Nat) := []
  /-- Classes by their plural noun, e.g. `bivariate copulas` (for names). -/
  classes : List (List Codes × Nat) := []
  labels : List (Codes × List Nat) := []
  /-- Labels of definitions (cited definitions are always available). -/
  defLabels : List Codes := []
  /-- Extremum of each result environment. -/
  extrema : List (Nat × Extremum) := []
  /-- Citations accumulated in the current proof, and its earlier steps. -/
  proofEnv : Nat := 0
  proofCites : List Nat := []
  proofSteps : List Nat := []
  /-- The most recent subject (for `its`). -/
  subject : Option (Tm × Ty) := none
  /-- The function of the most recent extremum (for `and the minimum V only by X`). -/
  lastExtremum : Option MT := none
  /-- The maps of the most recent sentence about maps (for `the first`, `the second`). -/
  lastMaps : List (Codes × MT) := []
  /-- Binders of the current result that later sentences of the result inherit. -/
  envBinders : List BindInfo := []
  /-- The hypotheses of the current result or proof, in order: every later claim of
  their scope is made under them. -/
  envHyps : List Hyp := []
  /-- A claim was made since the latest hypothesis. -/
  hypUsed : Bool := false
  /-- The letters the article declares to be integers (`Throughout, $p$ and $q$ denote
  integers.`): wherever one of them is bound, it is an integer. -/
  letters : List Codes := []
  /-- The hypotheses of each result at its end (its proof starts with them). -/
  resultHyps : List (Nat × List Hyp) := []
  /-- The statement of each result (by environment), for `the statement holds for $E$`
  in its proof: the clauses of its claims, or `none` if they are not claims about the
  variables of the result alone (a clause with binders of its own, a topic). -/
  resultStmts : List (Nat × Option (List Clause)) := []
  /-- The variable of the induction of a proof (`We argue by induction on $n$.`), with
  the environment of the proof. -/
  inductionVar : Option (Nat × Codes) := none
  /-- The sequences bound so far (`x_1,\ldots,x_n`): the name and the first and last
  index, for the definedness of their terms `x_i`. -/
  seqs : List (Codes × MT × MT) := []
  topic : Topic := .none
  /-- Variables fixed in the running text (`fix $b\in B$`), by section. -/
  fixed : List (Nat × BindInfo) := []
  /-- Definitions made under binders whose symbol does not show their variables
  (`z_-(x)` under `For $b\in B$`): the variables, supplied from the scope at each use. -/
  implicits : List (Nat × List Codes) := []
  /-- The parameters of a definition made among the variables of a result or proof
  (implicit ones, then its arguments), with their domains: the hypotheses in force that
  speak about them become part of the domain of the last (`Compile.defsUnderHyps`). -/
  telescopes : List (Nat × List BindInfo) := []
  /-- Notions defined by the article (`We call a copula $C$ NAME (ABBR) if …`): the
  phrases that name them (the name and the abbreviation) and the predicate. -/
  notions : List (List Codes × Nat) := []
  /-- The subject of the latest notion definition (for `Similarly, $C$ is called …`). -/
  notionSubject : Option BindInfo := none
  /-- Definitions local to an environment (made inside a result or a proof): the
  definition and the environment. They are visible there and in its proof. -/
  locals : List (Nat × Nat) := []
  /-- The variables of each result at its end (its proof starts with them). -/
  resultBinders : List (Nat × List BindInfo) := []
  /-- The environment of the current sentence, and the result its proof proves. -/
  curEnv : Nat := 0
  curProved : Option Nat := none
  /-- The binders and the formula of the latest inequality claimed for every point
  of a domain (for `equality holds exactly on …`). -/
  lastIneq : Option (List BindInfo × MT) := none
  /-- The binders and the inequalities of the latest claim about every element of a
  domain (for `both constants are sharp`). -/
  lastBounds : Option (List BindInfo × List MT) := none
  /-- The notations of the article, in order. -/
  templates : List Template := []
  /-- The article's conventions for words (`Throughout, increasing means
  non-decreasing.`): the words, and the words they stand for. -/
  wordAliases : List (List Codes × List Tok) := []
  /-- The generic constants the article declares (`Throughout, $C$ and $C_m$ denote
  positive constants.`), the latest last. -/
  genericConsts : List GenericConst := []
  /-- The names of the variables of the functions of several variables the article
  defines (`f(x,y)\coloneqq …`), by definition: `\partial_x f` is the derivative in
  the argument named `x`. -/
  params : List (Nat × List Codes) := []
  /-- The fields of the article and of the current result, by name (the latest first). -/
  fields : List (Codes × FieldInfo) := []
  /-- Names that state their dependence (`Q(\nu)` for the `Q` of `there is $Q=Q(\nu)$`),
  and the symbols they stand for, while the clause of their existence is read. -/
  aliases : List (Codes × List Codes × MT) := []
  deriving Inhabited, Lean.ToExpr

abbrev M := ExceptT Err (StateM St)

def fail {α : Type} (code : Nat) (detail : Codes := []) : M α := throw ⟨code, detail⟩

def liftO {α : Type} (o : Option α) (code : Nat) (detail : Codes := []) : M α :=
  match o with | some a => pure a | none => fail code detail

namespace Elab

def tTrue : Tm := .tt
def interval (lo hi : Tm) (x : Tm) : Tm := .and (.le lo x) (.le x hi)

/-- Membership in an interval with open or closed ends. -/
def intervalTm (lo hi : Tm) (lopen ropen : Bool) (x : Tm) : Tm :=
  .and (if lopen then .lt lo x else .le lo x) (if ropen then .lt x hi else .le x hi)

/-- `\infty` as the upper end of an interval, `-\infty` as its lower end. -/
def isInfty (upper : Bool) : MT → Bool
  | .id n => upper && n == w!"\\infty"
  | .neg (.id n) => !upper && n == w!"\\infty"
  | _ => false

/-- Membership in an interval whose ends may be infinite (`(0,\infty)`): an
infinite end, `none`, imposes no condition. -/
def rayTm (lo hi : Option Tm) (lopen ropen : Bool) (x : Tm) : Tm :=
  match lo, hi with
  | some l, some h => intervalTm l h lopen ropen x
  | some l, none => if lopen then .lt l x else .le l x
  | none, some h => if ropen then .lt x h else .le x h
  | none, none => .tt

/-- The key of a symbol: `x`, or a constant with a subscript (`d_0`, `g_*`,
`\Delta_0`), whose key is the whole symbol. -/
def symKey : MT → Option Codes
  | .id k => some k
  | .hat (.id k) => some ([92] ++ w!"hat{" ++ k ++ [125])
  | .sub (.id k) (.num n) => some (k ++ [95] ++ (Nat.toDigits 10 n).map Char.toNat)
  | .sub (.id k) (.id i) => some (k ++ [95] ++ i)
  | .sub (.id k) (.tuple xs) => do
    let ns ← xs.mapM fun x => match x with | .id n => some n | _ => none
    some (k ++ [95, 123] ++ (ns.intersperse [44]).flatten ++ [125])
  | _ => none

/-- The identifiers of a formula (in order of occurrence). -/
def mtIds : Nat → MT → List Codes
  | 0, _ => []
  | f + 1, m =>
    match m with
    | .id n => if n == [42] then [] else [n]
    | .sub (.id k) (.num n) => [k ++ [95] ++ (Nat.toDigits 10 n).map Char.toNat]
    | .sub (.id k) (.id [42]) => [k ++ [95, 42]]
    | .sub (.id k) (.tuple xs) => match symKey (.sub (.id k) (.tuple xs)) with
      | some key => [key]
      | none => [k]
    | .tuple xs | .conj xs | .minm xs | .maxm xs => xs.flatMap (mtIds f)
    | .add x y | .minus x y | .mul x y | .div x y | .frac x y => mtIds f x ++ mtIds f y
    -- `\hat x` is the name `\hat{x}`, or `\widehat` applied to `x`
    | .hat (.id k) => [[92] ++ w!"hat{" ++ k ++ [125], k]
    | .neg x | .abs x | .hat x => mtIds f x
    | .sub b i => mtIds f b ++ mtIds f i
    | .sup b e => mtIds f b ++ mtIds f e
    | .app h as => mtIds f h ++ as.flatMap (mtIds f)
    | _ => []

def singular (w : Codes) : Codes :=
  match w.reverse with
  | 115 :: r => r.reverse
  | _ => w

/-- Is definition `i` visible here? A definition local to an environment is visible in
that environment and in the proof of the result it belongs to. -/
def visibleIn (st : St) (i : Nat) : Bool :=
  match st.locals.lookup i with
  | some e => e == st.curEnv || st.curProved == some e
  | none => true

def lookupGlob (key : Codes) : M (Option (Nat × Glob)) := do
  let st ← get
  let rec find : Nat → List Glob → Option (Nat × Glob)
    | _, [] => none
    | i, g :: gs => match find (i + 1) gs with
      | some r => some r
      | none => if g.key == key && !key.isEmpty && visibleIn st i then some (i, g) else none
  pure (find 0 st.globs)

def addGlob (g : Glob) (v : Tm) : M Nat := do
  -- A definition is a closed term, and the domain of its `i`-th argument speaks only about
  -- that argument and the `i` arguments before it. A variable from outside would have no
  -- value in the definition (its conditions would then hold for an empty reason), and
  -- would be another variable wherever the definition is used.
  if Tm.shift 1 0 v != v || g.doms.zipIdx.any (fun (p, i) => p.any fun p => Tm.shift 1 (i + 1) p != p) then
    fail E.finding (w!"the definition of " ++ g.key ++ w!" uses a variable that is not one of its arguments (the domain of an argument depends on it): state the variable with the definition (For $n\\ge1$ and $x\\in[0,n]$, set $…$)")
  let st ← get
  let visibleIdx := (List.range st.globs.length).find? fun j => (st.globs[j]?).any (·.key == g.key) && visibleIn st j
  match (if g.key.isEmpty then none else visibleIdx) with
  | some i =>
    -- a family extended to a further parameter domain (`κ_w` for `w∈[1/2,1)`, then `κ_b`
    -- for `b∈(0,1/2)`): from here on, the symbol names one family on the union, which
    -- is the earlier family on its domain; its definedness asks that a parameter in
    -- both domains have one value. Earlier uses keep the earlier family.
    let old := st.globs[i]!
    match old.family, g.family, old.doms.head?, g.doms.head?, v, old.ty with
    | true, true, some (some p1), some (some p2), .lam _ _ b2, .fn t cod =>
      if old.ty != g.ty then fail E.redefined g.key else
      let dom := Tm.lam t .tt (.or (.app p1 (.loc 0)) (.app p2 (.loc 0)))
      let val := Tm.lam t (.app dom (.loc 0))
        (.cases (.app p1 (.loc 0)) (.app (.glob i) (.loc 0)) (.cases (.app p2 (.loc 0)) b2 (.undef cod)))
      let rest := match g.doms with | _ :: r => r | [] => []
      set { st with globs := st.globs ++ [{ old with doms := some dom :: rest }], values := st.values ++ [val] }
      pure st.globs.length
    | _, _, _, _, _, _ => fail E.redefined g.key
  | none =>
    set { st with globs := st.globs ++ [g], values := st.values ++ [v] }
    pure st.globs.length

def addClaim (c : Claim) : M Nat := do
  let st ← get
  set { st with claims := st.claims ++ [c] }
  pure st.claims.length

def globTy (i : Nat) : M Ty := do
  let st ← get
  match st.globs[i]? with
  | some g => pure g.ty
  | none => fail E.undefined

def lookupLocal : Scope → Codes → Option (Nat × Ty)
  | [], _ => none
  | (n, t) :: sc, x => if n == x then some (0, t) else (lookupLocal sc x).map fun (i, t) => (i + 1, t)

/-- Is `h` a number, so that `h(a)` is a product: a bound real variable (`c`, `B_I` of a
convention), a sequence of real numbers at an index (`x_n`), or a defined real constant
(`d_0`)? -/
def numberHead (sc : Scope) (h : MT) : M Bool := do
  let ivs := (← get).vocab.intervals
  let num (t : Ty) : Bool := t == .real || ivs.any (·.ty == t)
  match h with
  | .id n =>
    match lookupLocal sc n with
    | some (_, t) => pure (num t)
    | none => pure ((← lookupGlob n).any fun (_, g) => g.ty == .real)
  | .sub (.id k) _ =>
    match (symKey h).bind (lookupLocal sc ·) with
    | some (_, t) => pure (num t)
    | none =>
      match lookupLocal sc k with
      | some (_, t) => pure (t == .fn .real .real)
      | none => match symKey h with
        | some key => pure ((← lookupGlob key).any fun (_, g) => g.ty == .real)
        | none => pure false
  | _ => pure false

/-- Shift free local indices `≥ c` by `k`. -/
abbrev shift := Tm.shift

/-- The implicit parameters of definition `i`, as locals of the scope. -/
def implicitArgs (sc : Scope) (i : Nat) : M (List (Tm × Ty)) := do
  match (← get).implicits.lookup i with
  | some ns => ns.mapM fun n =>
    match lookupLocal sc n with
    | some (j, t) => pure (.loc j, t)
    | none => fail E.free n
  | none => pure []

/-- Closed terms (predicates of globals) used under `n` binders need no shift,
but a predicate applied to a local must be written as an application. -/
def applyPred (p : Tm) (x : Tm) : Tm := .app p x

/-! ## Notation on the vocabulary's types

As in Python, where `+` calls the `__add__` of its operands' class, notation means
what the type of its operands says: real numbers are the core's, and a vocabulary
gives notation a meaning on its own types by `methods` (`Vocab.lean`). -/

/-- Whether a type is one of the vocabulary's own. -/
def isBase : Ty → Bool
  | .base _ => true
  | _ => false

/-- The interval type of the vocabulary that `t` is, if it is one (`[0,1]` of the field
`unitsquare`): its elements are numbers. -/
def intervalOf (t : Ty) : M (Option IntervalType) := do
  pure ((← get).vocab.intervals.find? (·.ty == t))

/-- The interval type that the domain `[lo,hi]` is in the article's vocabulary, if any. -/
def intervalType (d : MT) : M (Option IntervalType) := do
  match d with
  | .interval (.num lo) (.num hi) => pure ((← get).vocab.intervals.find? fun i => i.lo == lo && i.hi == hi)
  | _ => pure none

/-- A type of the vocabulary with notation of its own (`\mathbb{C}`): a base type that is
not an interval of real numbers. -/
def ownTy (t : Ty) : M Bool := do
  pure (isBase t && !(← get).vocab.intervals.any (·.ty == t))

/-- The type of a number: the real numbers, or an interval type of the vocabulary. -/
def numTy (t : Ty) : M Bool := do
  pure (t == .real || (← get).vocab.intervals.any (·.ty == t))

/-- The result type of a function type applied to `n` arguments. -/
def resultTy : Nat → Ty → Ty
  | 0, t => t
  | n + 1, .fn _ b => resultTy n b
  | _, t => t

/-- The method `op` of the type `t`: its constant, and the constant's type. -/
def method (t : Ty) (op : OpKey) : M (Option (Tm × Ty)) := do
  let V := (← get).vocab
  pure ((V.methods.find? fun m => m.ty == t && m.op == op).map fun m =>
    (Tm.const m.const, V.consts.getD m.const .prop))

/-- The name of a type of the vocabulary, for findings. -/
def tyName (t : Ty) : M Codes := do
  match t with
  | .base k => pure ((((← get).vocab.types[k]?).map (w!"$" ++ · ++ w!"$")).getD w!"this type")
  | _ => pure w!"this type"

/-- The notation `op`, for findings. -/
def opName : OpKey → Codes
  | .ofReal => w!"a real number" | .add => w!"$+$" | .sub | .neg => w!"$-$"
  | .mul => w!"$\\cdot$" | .div => w!"$/$" | .pow => w!"a power"
  | .abs => w!"$\\lvert\\cdot\\rvert$" | .sum => w!"$\\sum$" | .prod => w!"$\\prod$"
  | .le | .lt => w!"an order ($\\le$, $<$)" | .fn n => w!"$" ++ n ++ w!"$"
  | .decor n => w!"$" ++ n ++ w!"$"

/-- `op` on elements of `t`, applied to `args`: the method's constant. -/
def callMethod (t : Ty) (op : OpKey) (args : List Tm) : M (Tm × Ty) := do
  let some (c, cty) ← method t op
    | fail E.finding (opName op ++ w!" has no meaning on " ++ (← tyName t) ++ w!" in the vocabulary")
  pure (args.foldl .app c, resultTy args.length cty)

def coerce (t : Tm) (src dst : Ty) : M Tm := do
  if src == dst then return t
  -- an element of an interval type is the number it is
  let (t, src) ← match ← intervalOf src with
    | some iv => pure (Tm.app (.const iv.val) t, Ty.real)
    | none => pure (t, src)
  if src == dst then return t
  if src != .real then fail E.type
  match ← intervalOf dst with
  -- a number as an element of an interval type: defined for the numbers of the interval
  | some iv =>
    let inside := Tm.lam .real .tt (.and (.le (.num iv.lo) (.loc 0)) (.le (.loc 0) (.num iv.hi)))
    pure (.guard (.app inside t) (.app (.const iv.point) t))
  | none =>
    -- a real number as an element of a type of the vocabulary (its method `ofReal`)
    if isBase dst then
      match ← method dst .ofReal with
      | some (c, _) => pure (.app c t)
      | none => fail E.type
    else fail E.type

def asReal (p : Tm × Ty) : M Tm := coerce p.1 p.2 .real

/-- `a op b` with an operand of a vocabulary's type: that type's method `op`, a real
operand being an element of the type; `a/b` is defined when `b` is not `0`. -/
def arith (op : OpKey) (a b : Tm × Ty) : M (Tm × Ty) := do
  let t := if (← ownTy a.2) then a.2 else b.2
  let x ← coerce a.1 a.2 t
  let y ← coerce b.1 b.2 t
  let r ← callMethod t op [x, y]
  if op == .div then
    let zero ← coerce (.num 0) .real t
    return (.guard (.not (.eq y zero)) r.1, r.2)
  return r

/-- The finding for `\mathbb{F}_p` and `\mathbb{Z}/p\mathbb{Z}`. -/
def finiteField : Codes :=
  w!"finite fields and residue rings ($\\mathbb{F}_p$, $\\mathbb{Z}/p\\mathbb{Z}$) are not read: write their elements as integers and equations between them as congruences ($a\\equiv b\\pmod p$)"

/-- That a set of points of an interval type, or of its square, is measurable: asked
where a set function (a measure, of type `(T → Prop) → ℝ` or `(T → T → Prop) → ℝ`) is
applied to it. -/
def measGuard (ivs : List IntervalType) (fnTy : Ty) (arg : Tm) : Option Tm :=
  ivs.findSome? fun iv =>
    if fnTy == .fn (.fn iv.ty .prop) .real then some (.app (.const iv.measurable1) arg)
    else if fnTy == .fn (.fn iv.ty (.fn iv.ty .prop)) .real then some (.app (.const iv.measurable2) arg)
    else none

/-- The domains of the arguments that follow, once the argument before them is `a`. The
domain of an argument is a predicate written where the argument itself (`loc 0`) and the
arguments before it (`loc 1` the latest, and so on) are bound, as inside the definition:
a domain may speak about the arguments before it (`Let $n\ge1$ and $x\in[0,n]$. Set
$r\coloneqq\frac1{x+1}$.` makes `r` a function of `n` and of `x\in[0,n]`). The `k`-th
following domain names `a` by `loc (k+1)`. -/
def domsAfter (a : Tm) (doms : List (Option Tm)) : List (Option Tm) :=
  doms.zipIdx.map fun (p, k) => p.map (Tm.subst a (k + 1))

/-- Apply a head of type `ty` to arguments, inserting coercions, the domain
guards of the head's definition, and measurability guards for measures; with the
domains of the arguments that are left. -/
def applyAllD (head : Tm) (ty : Ty) (doms : List (Option Tm)) :
    List (Tm × Ty) → M (Tm × Ty × List (Option Tm))
  | [] => pure (head, ty, doms)
  | (a, aty) :: rest =>
    match ty with
    | .fn dom cod => do
      let a' ← coerce a aty dom
      let applied := Tm.app head a'
      let guarded := match doms.head? with
        -- (the domain is about this argument: its own place in it is `a'`)
        | some (some p) => Tm.guard (applyPred (Tm.subst a' 0 p) a') applied
        | _ => applied
      let guarded := match measGuard (← get).vocab.intervals ty a' with
        | some g => Tm.guard g guarded
        | none => guarded
      applyAllD guarded cod (domsAfter a' (doms.drop 1)) rest
    | _ =>
      -- a real number applied to one argument is a product
      if ty == .real && rest.isEmpty then do
        let a' ← coerce a aty .real
        pure (.mul head a', .real, [])
      else fail E.type

def applyAll (head : Tm) (ty : Ty) (doms : List (Option Tm)) (args : List (Tm × Ty)) : M (Tm × Ty) := do
  let (t, ty, _) ← applyAllD head ty doms args
  pure (t, ty)

/-- The standard functions (`\exp`, `\log`, …) as heads, with their domains:
`\log` on `(0,\infty)`, `\tan` where `\cos` is not zero. -/
def builtinFn (n : Codes) : Option (Tm × Ty × List (Option Tm)) :=
  let fn (k : RealFn) (dom : Option Tm) := some (Tm.prim (.realFn k), Ty.real ⟶ .real, [dom])
  if n == w!"\\exp" then fn .exp none
  else if n == w!"\\log" then fn .log (some (.lam .real .tt (.lt (.num 0) (.loc 0))))
  else if n == w!"\\sin" then fn .sin none
  else if n == w!"\\cos" then fn .cos none
  else if n == w!"sgn" || n == w!"\\sgn" || n == w!"sign" then
    -- the sign: 1, -1 or 0
    some (.lam .real .tt (.cases (.lt (.num 0) (.loc 0)) (.num 1)
      (.cases (.lt (.loc 0) (.num 0)) (.neg (.num 1)) (.num 0))), Ty.real ⟶ .real, [none])
  else if n == w!"@factorial" then
    some (.prim .factorial, Ty.real ⟶ .real, [some (.lam .real .tt (.app (.prim .isNat) (.loc 0)))])
  else if n == w!"@binom" then
    some (.prim .binom, Ty.real ⟶ .real ⟶ .real,
      [some (.lam .real .tt (.app (.prim .isNat) (.loc 0))), some (.lam .real .tt (.app (.prim .isNat) (.loc 0)))])
  else if n == w!"@floor" then some (.prim .floor, Ty.real ⟶ .real, [none])
  else if n == w!"@ceil" then some (.prim .ceil, Ty.real ⟶ .real, [none])
  else if n == w!"\\tan" then
    fn .tan (some (.lam .real .tt (.not (.eq (.app (.prim (.realFn .cos)) (.loc 0)) (.num 0)))))
  else none

/-- The number of elements of the set `p` of real numbers: defined only when it is finite. -/
def cardTm (p : Tm) : Tm := .the .real (.app (.app (.prim .cardIs) (shift 1 0 p)) (.loc 0))

/-- `x ∣ y` for integers: `y = x·k` for an integer `k`. -/
def dvdTm (x y : Tm) : Tm :=
  let isInt (t : Tm) : Tm := .app (.prim .isInt) t
  .and (isInt x) (.and (isInt y)
    (.ex .real (.and (isInt (.loc 0)) (.eq (shift 1 0 y) (.mul (shift 1 0 x) (.loc 0))))))

/-- `\gcd(a,b)`: the natural number that divides `a` and `b` and that every common
divisor divides (`\gcd(0,0)=0`); defined for integers. -/
def gcdTm (a b : Tm) : Tm :=
  let isInt (t : Tm) : Tm := .app (.prim .isInt) t
  .guard (.and (isInt a) (isInt b))
    (.the .real (.and (.app (.prim .isNat) (.loc 0))
      (.and (dvdTm (.loc 0) (shift 1 0 a)) (.and (dvdTm (.loc 0) (shift 1 0 b))
        (.all .real (.imp (.and (dvdTm (.loc 0) (shift 2 0 a)) (dvdTm (.loc 0) (shift 2 0 b)))
          (dvdTm (.loc 0) (.loc 1))))))))

/-- Standard constants and sets: `\pi`, `\emptyset`, `\mathbb{R}` and its rays. -/
def builtinConst (n : Codes) : Option (Tm × Ty) :=
  if n == w!"\\pi" then some (.prim .pi, .real)
  else if n == w!"\\emptyset" || n == w!"\\varnothing" then some (.lam .real .tt (.not .tt), .fn .real .prop)
  else if n == w!"\\mathbb{R}" then some (.lam .real .tt .tt, .fn .real .prop)
  else if n == w!"\\mathbb{Z}" then some (.lam .real .tt (.app (.prim .isInt) (.loc 0)), .fn .real .prop)
  -- the rational numbers: `x·q = p` for integers `p` and `q ≠ 0`
  else if n == w!"\\mathbb{Q}" then
    some (.lam .real .tt (.ex .real (.ex .real (.and (.app (.prim .isInt) (.loc 1))
      (.and (.app (.prim .isInt) (.loc 0)) (.and (.not (.eq (.loc 0) (.num 0)))
        (.eq (.mul (.loc 2) (.loc 0)) (.loc 1))))))), .fn .real .prop)
  -- the natural numbers include 0, as in mathlib (`\mathbb{N}_0` says so explicitly)
  else if n == w!"\\mathbb{N}" || n == w!"\\mathbb{N}_0" then
    some (.lam .real .tt (.app (.prim .isNat) (.loc 0)), .fn .real .prop)
  else if n == w!"\\mathbb{R}_{>0}" then some (.lam .real .tt (.lt (.num 0) (.loc 0)), .fn .real .prop)
  else if n == w!"\\mathbb{R}_{\\ge0}" then some (.lam .real .tt (.le (.num 0) (.loc 0)), .fn .real .prop)
  else none

/-- Names of indices (`n`, `k`, …): integers, in exponents and limits. -/
def indexNames : List Codes := Math.indexNames

/-- An index: one of the index names, or a letter the article declares to be an integer. -/
def isIndex (st : St) (v : Codes) : Bool := indexNames.contains v || st.letters.contains v

/-- `x` is an integer, for a variable named `v` that the article declares to be one
(otherwise no condition). -/
def declaredInt (st : St) (v : Codes) (x : Tm) : Tm :=
  if st.letters.contains v then .app (.prim .isInt) x else .tt

/-- The exponent mentions an index. -/
def indexExp (e : MT) : Bool := (mtIds 32 e).any indexNames.contains

/-- `a^p`: an integer power when the exponent is built from indices (`(-1)^{k+1}`,
`2^n`), defined for every base (but `0` to a negative power); otherwise a real
power of a nonnegative base. -/
def powTm (a p : Tm) (integer : Bool) : M (Tm × Ty) :=
  if integer then
    pure (.guard (.and (.app (.prim .isInt) p) (.or (.not (.eq a (.num 0))) (.le (.num 0) p)))
      (.app (.app (.prim .zpow) a) p), .real)
  else pure (.guard (.le (.num 0) a) (.app (.app (.prim .rpow) a) p), .real)

/-- `⊤`, possibly as the membership in all real numbers. -/
def isTrue : Tm → Bool
  | .tt => true
  | .app (.lam _ _ .tt) _ => true
  | _ => false

/-- Pointwise inclusion `a ⊆ b` of two predicates of the same (curried) type. -/
def setSub (ty : Ty) (a b : Tm) : Tm :=
  match ty with
  | .fn t1 (.fn t2 .prop) =>
    .all t1 (.all t2 (.imp (.app (.app (shift 2 0 a) (.loc 1)) (.loc 0))
      (.app (.app (shift 2 0 b) (.loc 1)) (.loc 0))))
  | .fn t1 .prop => .all t1 (.imp (.app (shift 1 0 a) (.loc 0)) (.app (shift 1 0 b) (.loc 0)))
  | _ => .tt

/-- `p`, with the definedness of `e` asserted where `p` stands: a bound on a norm
says that the norm is finite (in any context, also under a negation). -/
def definedAnd (e p : Tm) : Tm :=
  match Tm.defined e with
  | .tt => p
  | d => .and d p

/-- The argument types of a predicate type `t₁ → … → tₙ → Prop`. -/
def predArgs : Ty → Option (List Ty)
  | .prop => some []
  | .fn a b => (predArgs b).map (a :: ·)
  | _ => none

/-- `A ⊆ B` for predicates of any number of arguments. -/
def setSubN (tys : List Ty) (a b : Tm) : Tm :=
  let k := tys.length
  let args := (List.range k).map fun j => Tm.loc (k - 1 - j)
  let ap (t : Tm) := args.foldl Tm.app (shift k 0 t)
  tys.foldr (fun t acc => .all t acc) (.imp (ap a) (ap b))

def isPredTy : Ty → Bool
  | .fn _ .prop => true
  | .fn _ (.fn _ .prop) => true
  | _ => false

def relTm (r : Rel) (x y : Tm × Ty) : M Tm := do
  -- (elements of a vocabulary's type: a real number among them is one of them, and
  -- an order is the type's method)
  if (← ownTy x.2) || (← ownTy y.2) then
    let t := if (← ownTy x.2) then x.2 else y.2
    let a ← coerce x.1 x.2 t
    let b ← coerce y.1 y.2 t
    match r with
    | .eq => return .eq a b
    | .ne => return .not (.eq a b)
    | .le => return (← callMethod t .le [a, b]).1
    | .lt => return (← callMethod t .lt [a, b]).1
    | .ge => return (← callMethod t .le [b, a]).1
    | .gt => return (← callMethod t .lt [b, a]).1
    | _ => pure ()
  match r with
  | .eq =>
    if x.2 == y.2 then pure (.eq x.1 y.1)
    else pure (.eq (← asReal x) (← asReal y))
  | .ne =>
    if x.2 == y.2 then pure (.not (.eq x.1 y.1))
    else pure (.not (.eq (← asReal x) (← asReal y)))
  | .le => pure (.le (← asReal x) (← asReal y))
  | .lt => pure (.lt (← asReal x) (← asReal y))
  | .ge => pure (.le (← asReal y) (← asReal x))
  | .gt => pure (.lt (← asReal y) (← asReal x))
  | .dvd => pure (dvdTm (← asReal x) (← asReal y))
  | .ndvd => do
    let a ← asReal x; let b ← asReal y
    pure (.and (.app (.prim .isInt) a) (.and (.app (.prim .isInt) b) (.not (dvdTm a b))))
  | .subset => if isPredTy x.2 && x.2 == y.2 then pure (setSub x.2 x.1 y.1) else fail E.type
  | .supset => if isPredTy x.2 && x.2 == y.2 then pure (setSub x.2 y.1 x.1) else fail E.type
  | _ => fail E.unsupported

def conjAll : List Tm → Tm
  | [] => .tt
  | [p] => p
  | p :: ps => .and p (conjAll ps)

/-- `∀` over a list of binders (innermost last), with domain hypotheses. -/
def forallBinders : List (Codes × Ty × Option Tm) → Tm → Tm
  | [], body => body
  | (n, t, p) :: bs, body =>
    let inner := forallBinders bs body
    -- a threshold of a smallness condition (`@c…`) is existential
    if n.head? == some 64 then
      match p with
      | some p => .ex t (.and p inner)
      | none => .ex t inner
    else
    match p with
    | some p => .all t (.imp p inner)
    | none => .all t inner

/-- Pointwise set equality of two predicates of the same (curried) type. -/
def setEq (ty : Ty) (a b : Tm) : Tm :=
  match ty with
  | .fn t1 (.fn t2 .prop) =>
    .all t1 (.all t2 (.iff (.app (.app (shift 2 0 a) (.loc 1)) (.loc 0))
      (.app (.app (shift 2 0 b) (.loc 1)) (.loc 0))))
  | .fn t1 .prop => .all t1 (.iff (.app (shift 1 0 a) (.loc 0)) (.app (shift 1 0 b) (.loc 0)))
  | _ => .eq a b

/-- A closed numeric bound: numerals, their negations and quotients. -/
def constMT : MT → Option Tm
  | .num n => some (.num n)
  | .neg x => (constMT x).map .neg
  | .frac x y | .div x y => do some (.div (← constMT x) (← constMT y))
  | _ => none

/-- A closed end of an interval domain; `none` for an infinite end, which must be
open (`[0,\infty)`, not `[0,\infty]`). -/
def constEnd (upper isOpen : Bool) (m : MT) : M (Option Tm) :=
  if isInfty upper m then (if isOpen then pure none else fail E.unsupported)
  else match constMT m with
    | some t => pure (some t)
    | none => fail E.unsupported

/-- The point-free subject: a term substituted for unapplied functions on its type. -/
abbrev PF := Option (Tm × Ty)

/-- Definition `i` applied to its implicit parameters, if it has any. -/
def withImplicit (sc : Scope) (i : Nat) (g : Glob) : M (Tm × Ty × List (Option Tm)) := do
  match ← implicitArgs sc i with
  | [] => pure (.glob i, g.ty, g.doms)
  | as => applyAllD (.glob i) g.ty g.doms as

/-- The derivative operators in front of a function: `\partial_x`, `\partial_1`,
`\partial_x^2`, `\partial_x\partial_y` (each `some` subscript) and `\Delta` (`none`). -/
def derivOps : Nat → MT → Option (List (Option MT))
  | 0, _ => none
  | f + 1, m =>
    match m with
    | .sub (.id d) i => if d == w!"\\partial" then some [some i] else none
    | .sup (.sub (.id d) i) (.num k) =>
      if d == w!"\\partial" && 1 ≤ k && k ≤ 4 then some (List.replicate k (some i)) else none
    | .id d => if d == w!"\\Delta" then some [none] else none
    | .mul a b => do
      let x ← derivOps f a
      let y ← derivOps f b
      some (x ++ y)
    | _ => none

/-- The operators and the function they apply to, through nested products
(`\partial_x(\partial_y f(x,y))`, `\partial_x\partial_y f`). -/
def gatherDeriv : Nat → List (Option MT) → MT → List (Option MT) × MT
  | 0, ops, m => (ops, m)
  | f + 1, ops, m =>
    match m with
    | .mul a b =>
      match derivOps 8 a with
      | some more => gatherDeriv f (ops ++ more) b
      | none => (ops, m)
    | _ => (ops, m)

/-- `\frac{\partial f}{\partial x}` as `\partial_x f`. -/
def fracDeriv : MT → Option MT
  | .frac (.mul (.id d) fn) (.mul (.id d') (.id x)) =>
    if d == w!"\\partial" && d' == w!"\\partial" then some (.mul (.sub (.id d) (.id x)) fn) else none
  | _ => none

/-- The number of real arguments of a real function of several real variables. -/
def realArity : Ty → Option Nat
  | .fn .real .real => some 1
  | .fn .real r => (realArity r).map (· + 1)
  | _ => none

/-- `F` applied to arguments. -/
def applyN (F : Tm) (args : List Tm) : Tm := args.foldl (fun acc a => .app acc a) F

/-- The translates of a set `K` of `ℝˢ` by the integer lattice: `λ x, ∃ m ∈ ℤˢ, K (x - m)`
(the support of a periodic function in `K`, on the torus). -/
def latticeSet (s : Nat) (K : Tm) : Tm :=
  let xs := (List.range s).map fun l => Tm.loc (2 * s - 1 - l)
  let ms := (List.range s).map fun l => Tm.loc (s - 1 - l)
  let body := conjAll (ms.map (fun m => Tm.app (.prim .isInt) m) ++
    [applyN (shift (2 * s) 0 K) (List.zipWith Tm.sub xs ms)])
  let exs := (List.range s).foldl (fun acc _ => Tm.ex .real acc) body
  (List.range s).foldl (fun acc _ => Tm.lam .real .tt acc) exs

/-- The partial derivative of `F` (a function of `n` real variables) in its `j`-th
variable (from 0): `(x₁,…,xₙ) ↦ the d with HasDerivAt (t ↦ F(…,t,…)) d xⱼ`. It is
defined where that derivative exists. -/
def partialFn (n j : Nat) (F : Tm) (dom : Option Tm := none) : Tm :=
  -- under the `n` binders, the description's `d`, and `t`
  let inner := applyN (shift (n + 2) 0 F)
    ((List.range n).map fun i => if i == j then Tm.loc 0 else .loc (2 + (n - 1 - i)))
  let g := Tm.lam .real .tt inner
  -- within the domain of the variable (one-sided at an end point), or on `ℝ`
  let univ := match dom with | some d => shift (n + 1) 0 d | none => Tm.lam .real .tt .tt
  let xj := Tm.loc (1 + (n - 1 - j))
  let body := Tm.app (.app (.app (.app (.prim .hasDerivWithin) g) univ) xj) (.loc 0)
  (List.range n).foldl (fun acc _ => Tm.lam .real .tt acc) (.the .real body)

/-- The partial derivative of `F` in its `j`-th variable at the point `pt`. -/
def partialAt (j : Nat) (F : Tm) (pt : List Tm) (dom : Option Tm := none) : Tm :=
  -- under the description's `d` and `t`
  let inner := applyN (shift 2 0 F) ((List.range pt.length).zip pt |>.map fun (i, p) => if i == j then Tm.loc 0 else shift 2 0 p)
  let g := Tm.lam .real .tt inner
  let univ := match dom with | some d => shift 1 0 d | none => Tm.lam .real .tt .tt
  let xj := shift 1 0 (pt.getD j (.num 0))
  .the .real (.app (.app (.app (.app (.prim .hasDerivWithin) g) univ) xj) (.loc 0))

/-- The Laplacian `\Delta F = ∑ⱼ ∂ⱼ∂ⱼ F` of a function of `n` real variables. -/
def laplacianFn (n : Nat) (F : Tm) : Tm :=
  let terms := (List.range n).map fun j =>
    applyN (shift n 0 (partialFn n j (partialFn n j F))) ((List.range n).map fun i => .loc (n - 1 - i))
  let sum := match terms with
    | t :: ts => ts.foldl (fun acc x => Tm.add acc x) t
    | [] => .num 0
  (List.range n).foldl (fun acc _ => Tm.lam .real .tt acc) sum

/-- The factors of a product, from the left (`\nu\Delta u` is `\nu`, `\Delta`, `u`;
`(u\cdot\nabla)u` is `u`, `\nabla`, `u`). -/
def mulFactors : Nat → MT → List MT
  | 0, m => [m]
  | f + 1, .mul a b => mulFactors f a ++ mulFactors f b
  | _ + 1, m => [m]

/-- The fields named in a formula at the level of functions (not applied to a point:
`\partial_tu+\nabla p=f`), with their descriptions. -/
def fieldsIn (fs : List (Codes × FieldInfo)) : Nat → MT → List (Codes × FieldInfo)
  | 0, _ => []
  | f + 1, m =>
    match m with
    | .id n => match fs.lookup n with | some i => [(n, i)] | none => []
    | .app _ _ => []
    | .add a b | .minus a b | .mul a b => fieldsIn fs f a ++ fieldsIn fs f b
    | .neg a => fieldsIn fs f a
    | _ => []

/-- Fields with a subscript in their name (`P_{\mathrm{per}}`) as identifiers. -/
def fieldIds (fs : List (Codes × FieldInfo)) : Nat → MT → MT
  | 0, m => m
  | f + 1, m =>
    let go := fieldIds fs f
    match m with
    | .sub b i =>
      match symKey m with
      | some k => if (fs.lookup k).isSome then .id k else .sub (go b) (go i)
      | none => .sub (go b) (go i)
    | .sup b e => .sup (go b) (go e)
    | .app g as => .app (go g) (as.map go)
    | .add x y => .add (go x) (go y)
    | .minus x y => .minus (go x) (go y)
    | .mul x y => .mul (go x) (go y)
    | .div x y => .div (go x) (go y)
    | .frac x y => .frac (go x) (go y)
    | .neg x => .neg (go x)
    | .abs x => .abs (go x)
    | .tuple xs => .tuple (xs.map go)
    | .chain x rs => .chain (go x) (rs.map fun (r, y) => (r, go y))
    | .conj xs => .conj (xs.map go)
    | .bound b s => .bound b (go s)
    | .image e v d => .image (go e) v (go d)
    | .int lo hi b v => .int (go lo) (go hi) (go b) v
    | _ => m

/-- Does a formula apply a vector field to a point (`u(x,t)`)? -/
def appliesVector (fs : List (Codes × FieldInfo)) : Nat → MT → Bool
  | 0, _ => false
  | f + 1, m =>
    match m with
    | .app (.id n) _ => (fs.lookup n).any (1 < ·.dim)
    | .add a b | .minus a b | .mul a b => appliesVector fs f a || appliesVector fs f b
    | .neg a => appliesVector fs f a
    | _ => false

/-- The sum of a list of real terms (`0` if empty). -/
def sumAll : List Tm → Tm
  | [] => .num 0
  | t :: ts => ts.foldl (fun acc x => .add acc x) t

/-- The number of elements of a set `\{1\le t\le N : φ\}` whose variable has no stated
domain and is not an index is not read: it would count real numbers, and an article
that counts such `t` means integers. -/
def unstatedCount (set : MT) : M Unit := do
  match set with
  | .setOf (.id v) d _ =>
    if Math.isUnstatedReals d && !(← get).letters.contains v then
      fail E.finding (w!"the number of elements of a set that does not say what $" ++ v ++
        w!"$ ranges over: write $\\{" ++ v ++ w!"\\in\\mathbb{Z} : …\\}$, or state the convention (Throughout, $" ++
        v ++ w!"$ denotes an integer.)")
  | _ => pure ()

/-- Elaborate a formula. Fuel bounds the recursion (kernel-reducible). -/
def term : Nat → Scope → PF → MT → M (Tm × Ty)
  | 0, _, _, _ => fail E.unsupported
  | f + 1, sc, pf, m0 => do
    -- `Q(\nu)` for the `Q` of `there is $Q=Q(\nu)$`
    let als : List (Codes × List Codes × MT) := (← get).aliases
    let m : MT := match m0 with
      | .app h args =>
        match symKey h, args.mapM symKey with
        | some k, some ks =>
          match als.find? (fun a => a.1 == k && a.2.1 == ks) with
          | some a => a.2.2
          | none => m0
        | _, _ => m0
      | _ => m0
    -- (`Q(3)` for the `Q` of `Q(\nu)`: a number, not a function of `\nu`)
    if let .app h _ := m then
      if let some k := symKey h then
        if als.any (·.1 == k) then
          fail E.finding (k ++ w!" is a number chosen for each value of the variables its name lists, not a function of them: write it with the same variables, or define the function")
    match m with
    | .num n => pure (.num n, .real)
    | .id n => do
      match lookupLocal sc n with
      | some (i, t) =>
        match pf, t with
        | some (s, sty), .fn a b => if a == sty then pure (.app (.loc i) s, b) else pure (.loc i, t)
        | _, _ => pure (.loc i, t)
      | none =>
        match ← lookupGlob n with
        | some (i, g) => do
          -- a symbol with implicit parameters (`G` for `\sqrt{ab}`) takes them from the scope
          let (t, ty, doms) ← withImplicit sc i g
          match pf, ty with
          | some (s, sty), .fn a _ =>
            if a == sty then applyAll t ty doms [(s, sty)] else pure (t, ty)
          | _, _ => pure (t, ty)
        | none =>
          -- a symbol of the vocabulary: a constant (`\mathrm{i}`), or all the elements
          -- of a type (`\mathbb{C}`)
          match (← get).vocab.symbols.find? (·.sym == n) with
          | some s => match s.const with
            | some i => pure (.const i, s.ty)
            | none => pure (.lam s.ty .tt .tt, .fn s.ty .prop)
          | none =>
          match builtinConst n with
          | some r => pure r
          | none =>
            -- `\overline{z}`, `\bar z` of a variable of a vocabulary's type: its
            -- method for the decoration (the conjugate of a complex number)
            let decor : Option (Codes × Codes) := [w!"\\overline", w!"\\bar"].findSome? fun p =>
              if n.take (p.length + 1) == p ++ [123] && n.getLast? == some 125 then
                some (p, (n.drop (p.length + 1)).dropLast) else none
            match decor.bind fun (p, v) => (lookupLocal sc v).map (p, ·) with
            | some (p, i, t) =>
              if (← ownTy t) then callMethod t (.decor p) [.loc i] else fail E.undefined n
            | none => fail E.undefined n
    -- (with an operand of a vocabulary's type, that type's method)
    | .add x y => do
      let a ← term f sc pf x; let b ← term f sc pf y
      if (← ownTy a.2) || (← ownTy b.2) then arith .add a b
      else pure (.add (← asReal a) (← asReal b), .real)
    | .minus x y => do
      let a ← term f sc pf x; let b ← term f sc pf y
      if (← ownTy a.2) || (← ownTy b.2) then arith .sub a b
      else pure (.sub (← asReal a) (← asReal b), .real)
    | .mul x y => do
      -- `\partial^I f(x,y)`
      match ← multiPartial f sc pf x y with
      | some r => pure r
      | none =>
      -- `\frac{\partial f}{\partial x}(x,y)`
      match fracDeriv x, y with
      | some dx, .tuple as => term f sc pf (match dx with
          | .mul op fn => .mul op (.app fn as)
          | _ => dx)
      | _, _ =>
      match derivOps 8 x with
      | some ops => do
        -- a partial derivative (or the Laplacian) of a function of several variables
        let (ops, tgt) := gatherDeriv 8 ops y
        let (hd, args) := match tgt with
          | .app h as => (h, some as)
          | t => (t, none)
        let (F, fty, doms) ← head f sc hd
        if doms.any (·.isSome) then fail E.unsupported
        let some n := realArity fty | fail E.type
        let st ← get
        let params : List Codes := match F with
          | .glob i => (st.params.lookup i).getD []
          | _ => []
        let pos (i : MT) : M Nat := do
          match i with
          | .num k => if 1 ≤ k && k ≤ n then pure (k - 1) else fail E.type
          | .id v =>
            let fromArgs := args.bind fun as => as.findIdx? fun a => match a with
              | .id w => w == v
              | _ => false
            match fromArgs <|> params.idxOf? v with
            | some j => if j < n then pure j else fail E.type
            | none => fail E.undefined ([92, 112, 97, 114, 116, 105, 97, 108, 95] ++ v)
          | _ => fail E.unsupported
        -- the innermost operator applies first
        let mut D := F
        for op in ops.reverse do
          match op with
          | some i => D := partialFn n (← pos i) D
          | none => D := laplacianFn n D
        match args with
        | some as => applyAll D fty [] (← as.mapM (term f sc pf))
        | none => pure (D, fty)
      | none => do
      let a ← term f sc pf x; let b ← term f sc pf y
      if (← ownTy a.2) || (← ownTy b.2) then arith .mul a b
      else pure (.mul (← asReal a) (← asReal b), .real)
    | .div x y | .frac x y => do
      match fracDeriv m with
      | some dm => term f sc pf dm
      | none => do
      -- (a quotient ring `\mathbb{Z}/p\mathbb{Z}` is not a set of real numbers)
      if let .id z := x then if z == w!"\\mathbb{Z}" then fail E.finding finiteField
      let a ← term f sc pf x; let b ← term f sc pf y
      if (← ownTy a.2) || (← ownTy b.2) then arith .div a b
      else pure (.div (← asReal a) (← asReal b), .real)
    | .neg x => do
      let a ← term f sc pf x
      if (← ownTy a.2) then callMethod a.2 .neg [a.1]
      else pure (.neg (← asReal a), .real)
    | .abs x => do
      let st ← get
      match x with
      -- `|u(x,t)|`: the Euclidean norm of the value of a field
      | .app (.id n) _ =>
        if (st.fields.lookup n).isSome then do
          match ← fieldAt f sc [] x with
          | [v] => pure (.abs v, .real)
          | vs => pure (.app (.app (.prim .rpow) (sumAll (vs.map fun v => Tm.mul v v))) (.div (.num 1) (.num 2)), .real)
        else do let a ← asReal (← term f sc pf x); pure (.abs a, .real)
      | _ => do
        -- `|A|` of a set: its number of elements
        unstatedCount x
        let (a, aty) ← term f sc pf x
        if aty == .fn .real .prop then pure (cardTm a, .real)
        -- (of an element of a vocabulary's type: its method, the modulus of a
        -- complex number)
        else if (← ownTy aty) then callMethod aty .abs [a]
        else do let a ← asReal (a, aty); pure (.abs a, .real)
    | .minm [x, y] => do
      let a ← asReal (← term f sc pf x); let b ← asReal (← term f sc pf y)
      pure (.app (.app (.prim .min) a) b, .real)
    | .maxm [x, y] => do
      let a ← asReal (← term f sc pf x); let b ← asReal (← term f sc pf y)
      pure (.app (.app (.prim .max) a) b, .real)
    -- `\min\{a,b,c\}` is `\min\{\min\{a,b\},c\}`
    | .minm (x :: y :: z :: rest) => term f sc pf (.minm (.minm [x, y] :: z :: rest))
    | .maxm (x :: y :: z :: rest) => term f sc pf (.maxm (.maxm [x, y] :: z :: rest))
    -- `v(s-v)^2`: a number before parentheses is a factor, and the exponent is the factor's
    | .sup (.app h [a]) e => do
      if ← numberHead sc h then term f sc pf (.mul h (.sup a e))
      else supTerm f sc pf (.app h [a]) e
    | .sup b e => supTerm f sc pf b e
    | .hat x => do
      -- `\hat x` is a name of its own (`\hat{x}`), unless the article or its vocabulary
      -- defines `\widehat` as an operation (the Fourier transform, the survival copula)
      match ← lookupGlob w!"\\widehat", x with
      | none, .id v => term f sc pf (.id ([92] ++ w!"hat{" ++ v ++ [125]))
      | _, _ =>
      let (h, g) ← liftO (← lookupGlob w!"\\widehat") E.undefined w!"\\widehat"
      let a ← term f sc pf x
      applyAll (.glob h) g.ty g.doms [a]
    | .sub b i =>
      match b with
      | .app (.id nm) [x] => if nm == w!"@norm" then normTm f sc pf x (some i) else subTm f sc pf m b i
      | _ => subTm f sc pf m b i
    | .app (.sup (.id fn) (.neg (.num 1))) [a] => do
      -- `f^{-1}(a)`: the element of the domain of `f` that `f` sends to `a`
      let (i, g) ← liftO (← lookupGlob fn) E.undefined fn
      match g.ty with
      | .fn dty cty => do
        let at_ ← term f sc pf a
        let a' ← coerce at_.1 at_.2 cty
        let fy ← applyAll (.glob i) g.ty g.doms [(.loc 0, dty)]
        let dom := match g.doms.head? with | some (some p) => [Tm.app p (.loc 0)] | _ => []
        pure (.the dty (conjAll (dom ++ [.eq fy.1 (shift 1 0 a')])), dty)
      | _ => fail E.type fn
    -- `xz(x+z)`: a number before parentheses is a factor, not a function
    | .app (.id n) [a] =>
      if n == w!"@norm" then normTm f sc pf a none else
      if n == w!"@card" then do
        unstatedCount a
        let (p, pty) ← term f sc pf a
        if pty == .fn .real .prop then pure (cardTm p, .real) else fail E.type
      else
      -- `\gcd(a,b)`
      if n == w!"\\gcd" && (lookupLocal sc n).isNone then
        match a with
        | .tuple [x, y] => do
          if (← lookupGlob n).isSome then fail E.unsupported
          pure (gcdTm (← asReal (← term f sc pf x)) (← asReal (← term f sc pf y)), .real)
        | _ => fail E.undefined n
      else
      match lookupLocal sc n with
      | some (_, t) =>
        -- `Q(\nu)` with `Q` a number is a product or a name that says what it depends on
        let single := match a with | .id _ | .sub (.id _) _ => true | _ => false
        let isNum ← numTy t
        if isNum && single then
          fail E.finding (n ++ w!"(…) is a product or a name that states what it depends on: write the product without parentheses, or introduce the name as `there is $" ++ n ++ w!"=" ++ n ++ w!"(…)$`")
        else if isNum then term f sc pf (.mul (.id n) a)
        else do
          let (h, hty, doms) ← head f sc (.id n)
          applyAll h hty doms [← term f sc pf a]
      | none => do
        -- a function the article does not define, of an element of a vocabulary's
        -- type: the type's method of that name (`\exp`, `\Re` of a complex number)
        if (← get).vocab.methods.any (·.op == .fn n) && (← lookupGlob n).isNone then
          let at_ ← term f sc pf a
          if (← ownTy at_.2) then
            if (← method at_.2 (.fn n)).isSome then return (← callMethod at_.2 (.fn n) [at_.1])
          let (h, hty, doms) ← head f sc (.id n)
          return (← applyAll h hty doms [at_])
        let (h, hty, doms) ← head f sc (.id n)
        applyAll h hty doms [← term f sc pf a]
    -- `(f\circ g)(x)` is `f(g(x))`
    | .app (.app (.id op) [f', g']) args =>
      if op == w!"\\circ" then term f sc pf (.app f' [.app g' args])
      else do
        let (h, hty, doms) ← head f sc (.app (.id op) [f', g'])
        let xs ← args.mapM (term f sc pf)
        applyAll h hty doms xs
    | .app hd args => do
      match hd, args with
      -- `\limsup_{n\to\infty} a_n`, `\liminf_{x\to\infty} f(x)`: the number `L` such that, for
      -- every `ε>0`, the values beyond every `N` exceed `L-ε` somewhere and eventually stay
      -- below `L+ε` (for `\liminf`, the reverse); defined only when it exists. An index runs
      -- through the natural numbers
      | .id op, [.id v, a, body] =>
        if op == w!"@limsup" || op == w!"@liminf" then do
          if !isInfty true a then fail E.unsupported
          if (lookupLocal sc v).isSome then fail E.shadow v
          let sc' : Scope := (v, .real) :: (w!"@N", .real) :: (w!"@e", .real) :: (w!"@L", .real) :: sc
          let pf' := pf.map fun (s, t) => (shift 4 0 s, t)
          let e ← asReal (← term f sc' pf' body)
          let inDom := if isIndex (← get) v then Tm.app (.prim .isNat) (.loc 0) else .tt
          -- (`v` is `loc 0`, `N` `loc 1`, `ε` `loc 2`, `L` `loc 3`)
          let beyond := Tm.and inDom (.le (.loc 1) (.loc 0))
          let above := Tm.lt (.sub (.loc 3) (.loc 2)) e
          let below := Tm.lt e (.add (.loc 3) (.loc 2))
          let (often, eventually) := if op == w!"@limsup" then (above, below) else (below, above)
          let p := Tm.all .real (.imp (.lt (.num 0) (.loc 0)) (.and
            (.all .real (.ex .real (conjAll [beyond, definedAnd e often])))
            (.ex .real (.all .real (.imp beyond (definedAnd e eventually))))))
          pure (.the .real p, .real)
        else do
          let (h, hty, doms) ← head f sc hd
          let xs ← args.mapM (term f sc pf)
          applyAll h hty doms xs
      -- `\gcd(a,b)`, unless the article defines `\gcd`
      | .id op, [x, y] =>
        if op == w!"\\gcd" && (lookupLocal sc op).isNone && (← lookupGlob op).isNone then do
          pure (gcdTm (← asReal (← term f sc pf x)) (← asReal (← term f sc pf y)), .real)
        else
        if op == w!"\\cup" || op == w!"\\times" || op == w!"\\cap" || op == w!"\\setminus" then setOp f sc pf op x y
        else do
          let (h, hty, doms) ← head f sc hd
          let xs ← args.mapM (term f sc pf)
          applyAll h hty doms xs
      | _, _ => do
        let (h, hty, doms) ← head f sc hd
        let xs ← args.mapM (term f sc pf)
        applyAll h hty doms xs
    -- `\int_{\mathbb{R}^n} e\,dx` over a point `x` of `ℝⁿ` (its coordinates `x#1`, …):
    -- a description, undefined unless `e` is integrable
    | .int (.sup (.id r) (.num n)) (.id over) body v => do
      if r != w!"\\mathbb{R}" || over != w!"@over" || n < 2 || 8 < n then fail E.unsupported
      if (lookupLocal sc v).isSome then fail E.shadow v
      let names := (List.range n).map fun k => v ++ w!"#" ++ (Nat.toDigits 10 (k + 1)).map Char.toNat
      let sc' : Scope := (names.reverse.map fun nm => (nm, Ty.real)) ++ sc
      let b ← asReal (← term f sc' (pf.map fun (s, t) => (shift n 0 s, t)) body)
      let g := (List.range n).foldl (fun acc _ => Tm.lam .real .tt acc) b
      pure (.the .real (.app (.app (.prim (.integralN n)) (shift 1 0 g)) (.loc 0)), .real)
    | .int lo hi body v => do
      if (lookupLocal sc v).isSome then fail E.shadow v
      match ← intervalType (.interval lo hi) with
      -- over an interval that is a type of the vocabulary (`\int_0^1` in `unitsquare`): the
      -- integral of the type, over its elements; defined when the integrand is integrable
      | some iv =>
        let b ← asReal (← term f ((v, iv.ty) :: sc) (pf.map fun (s, t) => (shift 1 0 s, t)) body)
        let fn := Tm.lam iv.ty .tt b
        pure (.guard (.app (.const iv.integrable) fn) (.app (.const iv.integral) fn), .real)
      -- `\int_a^b e\,dx`: the oriented integral of a function of a real variable, which
      -- has to be meaningful between `a` and `b`; defined when it is integrable there
      | none =>
        let a ← asReal (← term f sc pf lo)
        let c ← asReal (← term f sc pf hi)
        let b ← asReal (← term f ((v, .real) :: sc) (pf.map fun (s, t) => (shift 1 0 s, t)) body)
        let a1 := shift 1 0 a
        let c1 := shift 1 0 c
        -- (between the ends, in either order; numerals in order need no second case)
        let between := match a, c with
          | .num x, .num y => if x ≤ y then interval a1 c1 (.loc 0)
              else Tm.or (interval a1 c1 (.loc 0)) (interval c1 a1 (.loc 0))
          | _, _ => Tm.or (interval a1 c1 (.loc 0)) (interval c1 a1 (.loc 0))
        let fn := Tm.lam .real between b
        pure (.guard (.app (.app (.app (.prim .intervalIntegrable) fn) a) c)
          (.app (.app (.app (.prim .intervalIntegral) a) c) fn), .real)
    | .chain (.tuple xs) [(.eq, .tuple ys)] => do
      -- `(a,b) = (c,d)`: componentwise
      if xs.length != ys.length then fail E.type
      let ps ← (xs.zip ys).mapM fun (a, b) => do relTm .eq (← term f sc pf a) (← term f sc pf b)
      pure (conjAll ps, .prop)
    -- `(a,b)` as a set: the open interval (as after `\in`)
    | .tuple [a, b] => do
      let sc' : Scope := (w!"@x", Ty.real) :: sc
      let p ← member f sc' (.loc 0, .real) (.tuple [a, b])
      pure (.lam .real .tt p, .fn .real .prop)
    | .finset xs => do
      -- `\{a,b\}`: the numbers equal to one of the elements
      let ts ← xs.mapM fun x => do asReal (← term f sc none x)
      let eqs := ts.map fun t => Tm.eq (.loc 0) (shift 1 0 t)
      match eqs with
      | e :: es => pure (.lam .real .tt (es.foldl (fun acc q => .or acc q) e), .fn .real .prop)
      | [] => fail E.unsupported
    -- connectives and quantifiers between formulas
    | .lnot x => do pure (.not (← propOf f sc pf x), .prop)
    | .land x y => do pure (.and (← propOf f sc pf x) (← propOf f sc pf y), .prop)
    | .lor x y => do pure (.or (← propOf f sc pf x) (← propOf f sc pf y), .prop)
    | .limp x y => do pure (.imp (← propOf f sc pf x) (← propOf f sc pf y), .prop)
    | .liff x y => do pure (.iff (← propOf f sc pf x) (← propOf f sc pf y), .prop)
    -- `\forall I\in\mathbb{N}_0^n`: a multi-index, its components `I_1`, …, `I_n`
    | .quant isAll [v] (.sup base (.num n)) body =>
      if n < 2 || 8 < n then fail E.unsupported else
      let names := (List.range n).map fun k => v ++ [95] ++ (Nat.toDigits 10 (k + 1)).map Char.toNat
      term f sc pf (names.foldr (fun nm acc => MT.quant isAll [nm] base acc) body)
    | .quant isAll vs dom body =>
      -- each variable ranges over the real numbers in `dom`
      match vs with
      | [] => do pure (← propOf f sc pf body, .prop)
      | v :: rest => do
        if (lookupLocal sc v).isSome then fail E.shadow v
        let sc' : Scope := (v, Ty.real) :: sc
        let pf' := pf.map fun (s, t) => (shift 1 0 s, t)
        let m ← member f sc' (.loc 0, .real) dom
        -- (a letter the article declares to be an integer)
        let m := match declaredInt (← get) v (.loc 0), m with
          | .tt, m => m
          | i, .tt => i
          | i, m => .and i m
        let b ← propOf f sc' pf' (.quant isAll rest dom body)
        -- (over all real numbers, without a condition)
        pure (if isAll then .all .real (if m == .tt then b else .imp m b)
          else .ex .real (if m == .tt then b else .and m b), .prop)
    -- `x\notin A`
    | .chain x [(.nmem, dom)] => do
      let a ← term f sc pf x
      pure (.not (← member f sc a dom), .prop)
    -- `A\subseteq B`: every real number in `A` is in `B`
    -- `\supp u(\cdot,t)\cup\supp p(\cdot,t)\subseteq K`: the supports, in `K`
    | .chain x [(.subset, k)] => do
      let st ← get
      let rec supps : Nat → MT → Option (List (Codes × List MT))
        | 0, _ => none
        | g + 1, m => match m with
          | .mul (.id s) (.app (.id u) args) =>
            if s == w!"supp" && (st.fields.lookup u).isSome then some [(u, args)] else none
          | .mul (.id s) (.id u) =>
            if s == w!"supp" && (st.fields.lookup u).isSome then some [(u, [])] else none
          | .app (.id c) [a, b] =>
            if c == w!"\\cup" then do some ((← supps g a) ++ (← supps g b)) else none
          | _ => none
      -- sets of points of `ℝⁿ`: `K\subseteq L`
      let sets ← tryCatch (do
          let (a, aty) ← term f sc pf x
          let (b, bty) ← term f sc pf k
          match predArgs aty with
          | some tys => pure (if aty == bty && 2 ≤ tys.length then some (setSubN tys a b) else none)
          | none => pure none) fun _ => pure none
      match sets with
      | some p => pure (p, .prop)
      | none =>
      match supps 8 x with
      | none => do
        let sc' : Scope := (w!"@x", Ty.real) :: sc
        let a ← member f sc' (.loc 0, .real) x
        let b ← member f sc' (.loc 0, .real) k
        pure (.all .real (.imp a b), .prop)
      | some ss => do
        let (kt, kty) ← term f sc pf k
        let ps ← ss.mapM fun (u, args) => do
          let some i := st.fields.lookup u | fail E.type
          let (F, _, _) ← head f sc (.id u)
          let comps := if 1 < i.dim then (List.range i.dim).map fun c => Tm.app F (.num (c + 1)) else [F]
          -- the slice in the spatial coordinates (`u(\cdot,t)`), or the field
          let rest ← (args.filter fun a => match a with | .id c => c != w!"\\cdot" | _ => true).mapM fun a => do
            asReal (← term f sc pf a)
          let s := if args.isEmpty then i.coords else i.space
          if kty != Ty.setN s then fail E.type
          pure (comps.map fun c =>
            let slice := (List.range s).foldl (fun acc _ => Tm.lam .real .tt acc)
              (applyN (shift s 0 c) (((List.range s).map fun j => Tm.loc (s - 1 - j)) ++ rest.map (shift s 0)))
            -- on a torus, in `K` up to integer translations
            Tm.app (.app (.prim (.supportIn s)) slice) (if i.periodic then latticeSet s kt else kt))
        pure (conjAll ps.flatten, .prop)
    | .chain x [(.supset, y)] => do
      let sc' : Scope := (w!"@x", Ty.real) :: sc
      let a ← member f sc' (.loc 0, .real) x
      let b ← member f sc' (.loc 0, .real) y
      pure (.all .real (.imp b a), .prop)
    -- `\sup_{t\in D} e<\infty`: bounded above on `D`
    | .chain (.bound true (.image body v dom)) [(.lt, inf)] =>
      if !isInfty true inf then chainRest f sc pf (.bound true (.image body v dom)) [(.lt, inf)] else do
      let sc' : Scope := (v, .real) :: (w!"@M", .real) :: sc
      let pf' := pf.map fun (s, t) => (shift 2 0 s, t)
      let d ← member f sc' (.loc 0, .real) dom
      let e ← asReal (← term f sc' pf' body)
      -- each value is defined (a norm finite) and at most `M`
      pure (.ex .real (.all .real (.imp d (definedAnd e (.le e (.loc 1))))), .prop)
    -- `\limsup_{t\uparrow a} e=\infty`: unbounded as `t` tends to `a` (from below, above,
    -- or both), within the domain of the fields of `e`
    | .chain (.app (.id op) [.id v, a, body]) [(.eq, inf)] =>
      if !isInfty true inf || !(op == w!"@limsup-" || op == w!"@limsup+" || op == w!"@limsup") then
        chainRest f sc pf (.app (.id op) [.id v, a, body]) [(.eq, inf)] else do
      let st ← get
      -- `∀ M, ∀ δ > 0, ∃ v, 0 < |v - a| < δ (on the chosen side), v in the domain, e(v) > M`
      let sc' : Scope := (v, .real) :: (w!"@d", .real) :: (w!"@M", .real) :: sc
      let pf' := pf.map fun (s, t) => (shift 3 0 s, t)
      let a' ← asReal (← term f sc' pf' a)
      let e ← asReal (← term f sc' pf' body)
      let near := if op == w!"@limsup-" then Tm.and (.lt (.sub a' (.loc 1)) (.loc 0)) (.lt (.loc 0) a')
        else if op == w!"@limsup+" then Tm.and (.lt a' (.loc 0)) (.lt (.loc 0) (.add a' (.loc 1)))
        else Tm.and (.lt (.num 0) (.abs (.sub (.loc 0) a'))) (.lt (.abs (.sub (.loc 0) a')) (.loc 1))
      -- the time domain of a field of `e`
      let tdom : Option Tm := (st.fields.findSome? fun (n, i) =>
        if i.time && (mtIds 64 body).contains n then i.doms.getLast? else none).bind id
      let inDom := match tdom with | some d => Tm.app d (.loc 0) | none => .tt
      pure (.all .real (.all .real (.imp (.lt (.num 0) (.loc 0))
        (.ex .real (conjAll [near, inDom, definedAnd e (.lt (.loc 2) e)])))), .prop)
    -- `\lim_{v\to a} e=\infty` (`-\infty`): beyond every bound near `a` (beyond every bound of
    -- `v` for `a=\infty`), within the points where `e` is defined (for an index, the natural
    -- numbers), which accumulate at `a`
    | .chain (.limit v target body) [(.eq, inf)] =>
      if !(isInfty true inf || isInfty false inf) then chainRest f sc pf (.limit v target body) [(.eq, inf)] else do
      if (lookupLocal sc v).isSome then fail E.shadow v
      let up := isInfty true inf
      let toInf := isInfty true target
      -- (`v` is `loc 0`, the nearness `d` (or the bound `N`) `loc 1`, `M` `loc 2`)
      let sc' : Scope := (v, .real) :: (w!"@d", .real) :: (w!"@M", .real) :: sc
      let pf' := pf.map fun (s, t) => (shift 3 0 s, t)
      let e ← asReal (← term f sc' pf' body)
      let a' ← if toInf then pure (Tm.num 0) else asReal (← term f sc' pf' target)
      let inDom := if isIndex (← get) v && toInf then Tm.and (.app (.prim .isNat) (.loc 0)) (Tm.defined e)
        else Tm.defined e
      let near := if toInf then Tm.le (.loc 1) (.loc 0)
        else Tm.and (.lt (.num 0) (.abs (.sub (.loc 0) a'))) (.lt (.abs (.sub (.loc 0) a')) (.loc 1))
      let big := if up then Tm.lt (.loc 2) e else Tm.lt e (.loc 2)
      -- (`d > 0` for a finite `a`; in the scope `d :: M :: sc`)
      let pos := if toInf then Tm.tt else Tm.lt (.num 0) (.loc 0)
      -- (the accumulation does not mention `M`: `subst` drops its binder)
      let accumulate := Tm.all .real (.imp (Tm.subst (.num 0) 1 pos)
        (.ex .real (Tm.subst (.num 0) 2 (.and inDom near))))
      let diverge := Tm.all .real (.ex .real (.and pos (.all .real (.imp (.and inDom near) big))))
      pure (.and accumulate diverge, .prop)
    -- `a\equiv b\pmod m`: `m` divides `a-b`
    | .chain x [(.equiv, .app (.id md) [y, m])] =>
      if md == w!"@mod" then do
        -- (a congruence is between integers)
        let a ← asReal (← term f sc pf x)
        let b ← asReal (← term f sc pf y)
        let (d, _) ← term f sc pf (.chain m [(.dvd, .minus x y)])
        pure (.and (.app (.prim .isInt) a) (.and (.app (.prim .isInt) b) d), .prop)
      else fail E.unsupported
    | .chain x rest => do
      -- an equation between fields (`\partial_tu+\nabla p=f`, `\nabla\cdot u=0`,
      -- `u(\cdot,0)=0`): componentwise, at every point of the fields' domain
      let st ← get
      match rest with
      | [(.eq, y)] =>
        if !(fieldsIn st.fields 16 x ++ fieldsIn st.fields 16 y).isEmpty
            || appliesVector st.fields 16 x || appliesVector st.fields 16 y
            || (match x with | .app (.id n) _ => (st.fields.lookup n).isSome | _ => false) then
          fieldEq f sc x y
        else chainRest f sc pf x rest
      | _ => chainRest f sc pf x rest
    | .conj xs => do
      let ps ← xs.mapM fun x => do
        let (p, t) ← term f sc pf x
        if t == .prop then pure p else fail E.type
      pure (conjAll ps, .prop)
    | .setOf pat dom conds => setOf f sc pat dom conds
    | .setCond pat conds => do
      -- the variables of the pattern that are not bound range over the reals
      let st ← get
      -- (a family `e_b` does not prevent `e` from naming a variable)
      let fresh := ((mtIds 32 pat).filter fun n =>
        (lookupLocal sc n).isNone && !(st.globs.any fun g => g.key == n && !g.family)).eraseDups
      -- a variable with a membership `v\in D` among the conditions (`D` a class)
      -- ranges over the elements of `D`; the others over the real numbers
      let classOf (v : Codes) : Option Codes := conds.findSome? fun c => match c with
        | .chain (.id v') [(.mem, .id d)] => if v' == v then some d else none
        | _ => none
      let ftys ← fresh.mapM fun v => do
        match classOf v with
        | some d => match ← lookupGlob d with
          | some (_, g) => match g.ty with
            | .fn a .prop => pure a
            | _ => pure Ty.real
          | none => pure Ty.real
        | none => pure Ty.real
      let fv := fresh.zip ftys
      let sc' := fv.reverse ++ sc
      let cs ← conds.mapM fun c => do
        let (p, t) ← term f sc' none c
        if t == .prop then pure p else fail E.type
      let body := conjAll cs
      let lams (b : Tm) : Tm := fv.foldr (fun (_, t) acc => Tm.lam t .tt acc) b
      let tyOf : Ty := ftys.foldr Ty.fn .prop
      -- the image `{(e₁,e₂) : conds}` as the relation `(p,q) ↦ ∃ vars, conds ∧ p = e₁ ∧ q = e₂`
      let image2 (e1 e2 : MT) : M (Tm × Ty) := do
        let k := fresh.length
        let a ← term f sc' none e1
        let b ← term f sc' none e2
        let aty := if (← intervalOf a.2).isSome then a.2 else Ty.real
        let bty := if (← intervalOf b.2).isSome then b.2 else Ty.real
        let a' ← coerce a.1 a.2 aty
        let b' ← coerce b.1 b.2 bty
        -- under the existentials, `p` and `q` are `loc (k+1)` and `loc k`
        let inner := Tm.and (shift 2 k body)
          (.and (.eq (.loc (k + 1)) (shift 2 k a')) (.eq (.loc k) (shift 2 k b')))
        let exs := fv.foldr (fun (_, t) acc => Tm.ex t acc) inner
        pure (.lam aty .tt (.lam bty .tt exs), .fn aty (.fn bty .prop))
      match pat with
      | .id v => if fresh == [v] then pure (lams body, tyOf) else fail E.unsupported
      | .tuple [e1, e2] =>
        match e1, e2 with
        -- `{(u,v) : conds}`: a pattern of two variables (`{(x,x) : …}` is an image)
        | .id v1, .id v2 =>
          if v1 != v2 && fresh == [v1, v2] then pure (lams body, tyOf) else image2 e1 e2
        | _, _ => image2 e1 e2
      | e => do
        -- the image `{e : conds}` as the set `y ↦ ∃ vars, conds ∧ y = e`
        let k := fresh.length
        if k == 0 then fail E.unsupported
        let a ← term f sc' none e
        let aty := if (← intervalOf a.2).isSome then a.2 else Ty.real
        let a' ← coerce a.1 a.2 aty
        let inner := Tm.and (shift 1 k body) (.eq (.loc k) (shift 1 k a'))
        let exs := fv.foldr (fun (_, t) acc => Tm.ex t acc) inner
        pure (.lam aty .tt exs, .fn aty .prop)
    | .equiv x y => do
      let (p, pt) ← term f sc pf x
      let (q, qt) ← term f sc pf y
      if pt != .prop || qt != .prop then fail E.type
      pure (.and p (.iff p q), .prop)
    | .image (.tuple [e1, e2]) v (.id dom) => do
      -- {(e1(v), e2(v)) : v ∈ D} as the relation (r, n) ↦ ∃ v ∈ D, e1 = r ∧ e2 = n
      let (dp, dg) ← liftO (← lookupGlob dom) E.undefined dom
      let vty ← match dg.ty with | .fn a .prop => pure a | _ => fail E.type
      let sc' := (v, vty) :: (w!"", .real) :: (w!"", .real) :: sc
      let a ← asReal (← term f sc' none e1)
      let b ← asReal (← term f sc' none e2)
      let body := Tm.and (.app (.glob dp) (.loc 0)) (.and (.eq a (.loc 2)) (.eq b (.loc 1)))
      pure (.lam .real .tt (.lam .real .tt (.ex vty body)), .fn .real (.fn .real .prop))
    | .image e v (.id dom) => do
      -- {e(v) : v ∈ D} as the set y ↦ ∃ v ∈ D, e = y
      let (dp, dg) ← liftO (← lookupGlob dom) E.undefined dom
      let vty ← match dg.ty with | .fn a .prop => pure a | _ => fail E.type
      let sc' := (v, vty) :: (w!"", .real) :: sc
      let a ← asReal (← term f sc' none e)
      pure (.lam .real .tt (.ex vty (.and (.app (.glob dp) (.loc 0)) (.eq a (.loc 1)))), .fn .real .prop)
    | .image e v dom => do
      -- {e(v) : v ∈ D} for a set D of real numbers: y ↦ ∃ v ∈ D, e = y
      let sc' := (v, Ty.real) :: (w!"", .real) :: sc
      let m ← member f sc' (.loc 0, .real) dom
      let m := match declaredInt (← get) v (.loc 0) with
        | .tt => m
        | i => .and i m
      let a ← asReal (← term f sc' none e)
      pure (.lam .real .tt (.ex .real (.and m (.eq a (.loc 1)))), .fn .real .prop)
    | .cases rows => casesRows f sc pf rows
    | .interval lo hi => do
      -- an interval as a set of real numbers
      let l ← asReal (← term f sc none lo)
      let h ← asReal (← term f sc none hi)
      pure (.lam .real .tt (interval (shift 1 0 l) (shift 1 0 h) (.loc 0)), .fn .real .prop)
    | .bigop isSum v lo hi body => do
      -- with numeral bounds, the finite sum (product) of the terms
      match constMT lo, constMT hi with
      | some (.num a), some (.num b) => do
        if b < a || b > a + 100 then fail E.unsupported (if isSum then w!"\\sum" else w!"\\prod")
        if (lookupLocal sc v).isSome then fail E.shadow v
        -- each term is the body with the index replaced by its value (terms of a
        -- vocabulary's type: its method `+` or `\cdot`)
        let terms ← (List.range (b - a + 1)).mapM fun k =>
          term f sc pf (MT.substId v (MT.num (a + k)) 64 body)
        let ivs := (← get).vocab.intervals
        if terms.any (fun t => isBase t.2 && !ivs.any (·.ty == t.2)) then
          match terms with
          | t0 :: ts => ts.foldlM (fun acc x => arith (if isSum then .add else .mul) acc x) t0
          | [] => fail E.unsupported
        else
        let terms ← terms.mapM asReal
        match terms with
        | t0 :: ts => pure (ts.foldl (fun acc x => if isSum then .add acc x else .mul acc x) t0, .real)
        | [] => fail E.unsupported
      -- `\sum_{k=a}^{b} e` over the integers between `a` and `b` (integers themselves), and
      -- `\sum_{k=a}^{\infty} e`, the limit of the partial sums (when it exists)
      | _, _ => do
        if (lookupLocal sc v).isSome then fail E.shadow v
        let l ← asReal (← term f sc none lo)
        let isInt (t : Tm) : Tm := .app (.prim .isInt) t
        let sc' : Scope := (v, Ty.real) :: sc
        let bt ← term f sc' (pf.map fun (s, t) => (shift 1 0 s, t)) body
        -- (terms of a vocabulary's type: its method `\sum` or `\prod`)
        let cx ← ownTy bt.2
        let b ← if cx then pure bt.1 else asReal bt
        if isInfty true hi then do
          if !isSum || cx then fail E.unsupported (if isSum then w!"\\sum" else w!"\\prod")
          let lam := Tm.lam .real (.and (isInt (.loc 0)) (.le (shift 1 0 l) (.loc 0))) b
          let conv := Tm.app (.app (.prim .seriesConv) l) lam
          pure (.guard (.and (isInt l) conv) (.app (.app (.prim .series) l) lam), .real)
        else do
          let h ← asReal (← term f sc none hi)
          let lam := Tm.lam .real (.and (isInt (.loc 0))
            (.and (.le (shift 1 0 l) (.loc 0)) (.le (.loc 0) (shift 1 0 h)))) b
          if cx then
            let (s, sty) ← callMethod bt.2 (if isSum then .sum else .prod) [l, h, lam]
            return (.guard (.and (isInt l) (isInt h)) s, sty)
          let p : Prim := if isSum then .finSum else .finProd
          pure (.guard (.and (isInt l) (isInt h)) (.app (.app (.app (.prim p) l) h) lam), .real)
    -- `\lim_{x\to a} e`, `\lim_{x\to\infty} e`, and `\lim_{n\to\infty} a_n` for a sequence
    -- (an index `n`, `m`, `k`, `j`, `i` runs through the natural numbers): the limit within
    -- the points where the expression is defined, when it exists
    | .limit v target body => do
      if (lookupLocal sc v).isSome then fail E.shadow v
      let sc' : Scope := (v, Ty.real) :: sc
      let b ← asReal (← term f sc' (pf.map fun (s, t) => (shift 1 0 s, t)) body)
      let seq := isIndex (← get) v
      let dom := if seq && isInfty true target then
          Tm.and (.app (.prim .isNat) (.loc 0)) (Tm.defined b) else Tm.defined b
      let D := Tm.lam .real .tt dom
      let F := Tm.lam .real dom b
      if isInfty true target then
        pure (.guard (.app (.app (.prim .limTopConv) D) F) (.app (.app (.prim .limTop) D) F), .real)
      else do
        let a ← asReal (← term f sc none target)
        pure (.guard (.app (.app (.app (.prim .limAtConv) a) D) F)
          (.app (.app (.app (.prim .limAt) a) D) F), .real)
    | .bound isSup st => do
      -- the `s` with `y ≤ s` for every element `y`, and `s ≤ u` for every such bound `u`
      -- (for `\inf`, the reverse); defined exactly when the bound exists
      let (p, pty) ← term f sc pf st
      match pty with
      | .fn ety .prop => do
        if ety != .real then fail E.type
        let le (a b : Tm) : Tm := if isSup then .le a b else .le b a
        let isBound := Tm.all .real (.imp (.app (shift 2 0 p) (.loc 0)) (le (.loc 0) (.loc 1)))
        let isBoundU := Tm.all .real (.imp (.app (shift 3 0 p) (.loc 0)) (le (.loc 0) (.loc 1)))
        let least := Tm.all .real (.imp isBoundU (le (.loc 1) (.loc 0)))
        pure (.the .real (.and isBound least), .real)
      | _ => fail E.type
    | .extr isMax st => do
      -- the element `x` of the set with `y ≤ x` (`x ≤ y`) for every element `y`
      let (p, pty) ← term f sc pf st
      match pty with
      | .fn ety .prop => do
        let xr ← coerce (.loc 1) ety .real
        let yr ← coerce (.loc 0) ety .real
        let bound := if isMax then Tm.le yr xr else Tm.le xr yr
        let body := Tm.and (.app (shift 1 0 p) (.loc 0)) (.all ety (.imp (.app (shift 2 0 p) (.loc 0)) bound))
        pure (.the ety body, ety)
      | _ => fail E.type
    | m => match m with
      | .tuple _ => fail E.finding w!"a tuple $(a,b,…)$ is read only as an interval or as the point of a domain, not as a value"
      | .mapsto .. => fail E.finding w!"a map $x\\mapsto e$ is read only after `the map` or `the function` (its monotonicity, its range) or in a definition"
      | .setCond .. => fail E.finding w!"a set $\\{x : φ\\}$ needs the set its elements are taken from: $\\{x\\in A : φ\\}$"
      | _ => fail E.unsupported
where
  casesRows : Nat → Scope → PF → List (MT × MT) → M (Tm × Ty)
    | 0, _, _, _ => fail E.unsupported
    | _ + 1, _, _, [] => pure (.undef .real, .real)
    | g + 1, sc, pf, (v, c) :: rs => do
      let (vt, ty) ← term g sc pf v
      let vt ← coerce vt ty .real
      let (ct, cty) ← term g sc pf c
      if cty != .prop then fail E.type
      let (rt, _) ← casesRows g sc pf rs
      pure (.cases ct vt rt, .real)
  /-- A superscript: a family (`\gamma^T`), a transpose, or a power. -/
  supTerm : Nat → Scope → PF → MT → MT → M (Tm × Ty)
    | 0, _, _, _, _ => fail E.unsupported
    | f + 1, sc, pf, b, e => do
      -- `e^x` is `\exp(x)`, unless the article names something `e`
      let isE ← match b with
        | .id [101] => do
          pure ((lookupLocal sc [101]).isNone && (← lookupGlob [101]).isNone &&
            !(← get).unreadIds.contains [101])
        | _ => pure false
      if isE then do
        let a ← term f sc pf e
        if (← ownTy a.2) then callMethod a.2 (.fn w!"\\exp") [a.1]
        else pure (.app (.prim (.realFn .exp)) (← asReal a), .real)
      else
      -- a power of an element of a vocabulary's type: its method, with a natural
      -- exponent (`z^n` with `n ∈ ℕ`; `z^{-n}` is `1/z^n`); the base is read again
      -- below otherwise (the state is restored)
      let st0 ← get
      let bt ← tryCatch (some <$> term f sc pf b) (fun _ => pure none)
      if let some (z, t) := bt then
        if (← ownTy t) then
          match e with
          | .num n => return (← callMethod t .pow [z, .num n])
          | .neg (.num n) => return (← arith .div (.num 1, .real) (← callMethod t .pow [z, .num n]))
          | _ => do
            let p ← asReal (← term f sc pf e)
            let (r, rty) ← callMethod t .pow [z, p]
            return (.guard (.app (.prim .isNat) p) r, rty)
      set st0
      -- a family written with a superscript (`\gamma^T`)
      let fam ← match b, e with
        | .id k, .id d => if d == w!"\\top" || d == w!"\\perp" then pure none else lookupGlob (k ++ w!"^")
        | .id _, .num _ => pure none
        | .id k, _ => lookupGlob (k ++ w!"^")
        | _, _ => pure none
      match fam with
      | some (h, g) => do
        let a ← term f sc none e
        applyAll (.glob h) g.ty g.doms [a]
      | none =>
      match e with
      | .id d =>
        if d == w!"\\top" || d == w!"\\perp" then do
          let (h, g) ← liftO (← lookupGlob (w!"^" ++ d)) E.undefined (w!"^" ++ d)
          let x ← term f sc pf b
          applyAll (.glob h) g.ty g.doms [x]
        else do
          let a ← asReal (← term f sc pf b)
          let p ← asReal (← term f sc pf e)
          powTm a p (indexExp e || (mtIds 32 e).any (← get).letters.contains)
      | .num n => do
        let a ← asReal (← term f sc pf b)
        pure (.powNat a n, .real)
      -- `x^{-2}` is `1/x^2`: defined for `x ≠ 0`, whatever its sign
      | .neg (.num n) => do
        let a ← asReal (← term f sc pf b)
        pure (.div (.num 1) (if n == 1 then a else .powNat a n), .real)
      | _ => do
        let a ← asReal (← term f sc pf b)
        let p ← asReal (← term f sc pf e)
        powTm a p (indexExp e || (mtIds 32 e).any (← get).letters.contains)
  head : Nat → Scope → MT → M (Tm × Ty × List (Option Tm))
    | 0, _, _ => fail E.unsupported
    | g + 1, sc, hd =>
      match hd with
      | .id n =>
        match lookupLocal sc n with
        | some (i, t) => pure (.loc i, t, [])
        | none => do
          match ← lookupGlob n, builtinFn n with
          | none, some b => pure b
          | _, _ =>
          -- a function of the vocabulary (`\sinh` of the field `hyperbolic`): a symbol
          -- whose constant is a function
          let gl? ← lookupGlob n
          let symbols := (← get).vocab.symbols
          let sym : Option (Nat × Ty) := match gl? with
            | some _ => none
            | none => (symbols.find? (·.sym == n)).bind fun s => match s.const, s.ty with
              | some i, .fn _ _ => some (i, s.ty)
              | _, _ => none
          if let some (i, ty) := sym then return (.const i, ty, []) else
          let (i, gl) ← liftO (← lookupGlob n) E.undefined n
          -- (a function with implicit parameters, `f(t)\coloneqq\frac tc` among the
          -- variables of a result, takes them from the scope)
          withImplicit sc i gl
      -- `x_n` for a real function `x` of the scope (the weights of a distribution): `x(n)`
      | .sub (.id key) i =>
        -- a bound variable with a subscript in its name (`B_I` of a convention): a number
        -- before parentheses is a factor
        match (symKey hd).bind (lookupLocal sc ·) with
        | some (j, t) => pure (.loc j, t, [])
        | none =>
        match lookupLocal sc key with
        | some (j, .fn .real b) => do
          let a ← asReal (← term g sc none i)
          pure (.app (.loc j) a, b, [])
        | _ => do
        -- a constant with a subscript (`z_-`), unless the index is a variable
        let ck := match i with
          | .id x => if (lookupLocal sc x).isSome then none else symKey hd
          | _ => symKey hd
        let c ← match ck with
          | some k => lookupGlob k
          | none => pure none
        match c with
        | some (h, gl) =>
          if gl.family then fail E.unsupported key else withImplicit sc h gl
        | none =>
        -- `\eta_-` is a symbol of its own: a sign is not an index
        let sign := match i with | .id [c] => c == 43 || c == 45 || c == 42 | _ => false
        if sign then fail E.undefined ((symKey hd).getD key)
        let (h, gl) ← liftO (← lookupGlob key) E.undefined key
        let a ← term g sc none i
        let (h0, ty0, doms0) ← withImplicit sc h gl
        -- (the domains of the arguments that follow may speak about the index: `g_c(t)`
        -- for `t\in[0,c]`)
        applyAllD h0 ty0 doms0 [a]
      -- a family written with a sub- and a superscript (`R_b^-`, `T^0_q`)
      | .sup (.sub (.id key) i) sup => do
        let s ← match sup with
          | .id s => pure s
          | .num n => pure ((Nat.toDigits 10 n).map Char.toNat)
          | _ => fail E.unsupported
        let k := key ++ w!"^" ++ s
        let (h, gl) ← liftO (← lookupGlob k) E.undefined k
        if !gl.family then fail E.unsupported k
        let a ← term g sc none i
        applyAllD (.glob h) gl.ty gl.doms [a]
      | _ => do
        let (t, ty) ← term g sc none hd
        pure (t, ty, [])
  /-- `A\cup B` (sets of the same kind) and `A\times B` (sets of numbers; a number
  is the set containing it). -/
  setOp : Nat → Scope → PF → Codes → MT → MT → M (Tm × Ty)
    | 0, _, _, _, _, _ => fail E.unsupported
    | g + 1, sc, pf, op, x, y => do
      let a ← term g sc pf x
      let b ← term g sc pf y
      -- a number beside a set of numbers is the set of that number (`\mathbb{R}\setminus\{0\}`)
      let single (p q : Tm × Ty) : Tm × Ty :=
        if p.2 == .real && q.2 == .fn .real .prop && op != w!"\\times" then
          (.lam .real .tt (.eq (.loc 0) (shift 1 0 p.1)), .fn .real .prop) else p
      let (a, b) := (single a b, single b a)
      -- `A\cup B`, `A\cap B`, `A\setminus B`
      let comb (p q : Tm) : Tm :=
        if op == w!"\\cup" then .or p q
        else if op == w!"\\cap" then (if isTrue p then q else .and p q)
        else (if isTrue p then .not q else .and p (.not q))
      if op == w!"\\cup" || op == w!"\\cap" || op == w!"\\setminus" then
        if a.2 != b.2 then fail E.type
        match a.2 with
        | .fn t1 .prop =>
          pure (.lam t1 .tt (comb (.app (shift 1 0 a.1) (.loc 0)) (.app (shift 1 0 b.1) (.loc 0))), a.2)
        | .fn t1 (.fn t2 .prop) =>
          let ap := Tm.app (.app (shift 2 0 a.1) (.loc 1)) (.loc 0)
          let bp := Tm.app (.app (shift 2 0 b.1) (.loc 1)) (.loc 0)
          pure (.lam t1 .tt (.lam t2 .tt (comb ap bp)), a.2)
        | _ => fail E.type
      -- `2\times3`: a product of numbers
      else if a.2 == .real && b.2 == .real then pure (.mul a.1 b.1, .real)
      else do
        let set1 (p : Tm × Ty) : M Tm := do
          match p.2 with
          | .fn .real .prop => pure p.1
          | _ => do
            let v ← asReal p
            pure (.lam .real .tt (.eq (.loc 0) (shift 1 0 v)))
        let sa ← set1 a
        let sb ← set1 b
        pure (.lam .real .tt (.lam .real .tt (.and (.app (shift 2 0 sa) (.loc 1)) (.app (shift 2 0 sb) (.loc 0)))),
          .fn .real (.fn .real .prop))
  chainRest : Nat → Scope → PF → MT → List (Rel × MT) → M (Tm × Ty)
    | 0, _, _, _, _ => fail E.unsupported
    | f + 1, sc, pf, x, rest => do
      -- the implied constant of `\ll`, `\gg` and `O(…)`, placed by the article's convention
      let implied : M Tm := match lookupLocal sc w!"@ll" with
        | some (i, _) => pure (.loc i)
        | none => fail E.finding w!"\\ll, \\gg and O(…) need a convention for their implied constants: say what they may depend on (Implied constants are absolute. Implied constants may depend on $k$.)"
      -- `A=O(B)`: `|A|\le C|B|`
      match rest with
      | [(.eq, .app (.id [79]) [b])] =>
        if (lookupLocal sc [79]).isSome || (← lookupGlob [79]).isSome then fail E.unsupported else do
        let c ← implied
        let a ← asReal (← term f sc pf x)
        let b ← asReal (← term f sc pf b)
        pure (.le (.abs a) (.mul c (.abs b)), .prop)
      | _ =>
      let ts ← (x :: rest.map (·.2)).mapM (term f sc pf)
      let rels := rest.map (·.1)
      if rels.any (· == .mem) then
        match x, rest with
        | _, [(.mem, dom)] => do
          let a ← term f sc pf x
          let p ← member f sc a dom
          pure (p, .prop)
        | _, _ => fail E.unsupported
      else
      -- set equality between predicates
      match ts, rels with
      | [a, b], [.eq] =>
        if isPredTy a.2 && a.2 == b.2 then pure (setEq a.2 a.1 b.1, .prop)
        -- `A=\{1\}`: a set of numbers and the set of one number
        else if a.2 == .fn .real .prop && b.2 == .real then
          pure (setEq a.2 a.1 (.lam .real .tt (.eq (.loc 0) (shift 1 0 b.1))), .prop)
        else if b.2 == .fn .real .prop && a.2 == .real then
          pure (setEq b.2 (.lam .real .tt (.eq (.loc 0) (shift 1 0 a.1))) b.1, .prop)
        else do pure (← relTm .eq a b, .prop)
      | _, _ => do
        let rec pairs : List (Tm × Ty) → List Rel → M (List Tm)
          | a :: b :: more, r :: rs => do
            let p ← if r == .eq && isPredTy a.2 && a.2 == b.2 then pure (setEq a.2 a.1 b.1)
              -- `A\ll B`: `|A|\le CB`; `A\gg B`: `|B|\le CA`
              else if r == .ll then do pure (.le (.abs (← asReal a)) (.mul (← implied) (← asReal b)))
              else if r == .gg then do pure (.le (.abs (← asReal b)) (.mul (← implied) (← asReal a)))
              -- `A\asymp B`: `|A|\le CB` and `|B|\le CA`
              else if r == .asymp then do
                let c ← implied
                pure (.and (.le (.abs (← asReal a)) (.mul c (← asReal b))) (.le (.abs (← asReal b)) (.mul c (← asReal a))))
              else relTm r a b
            let ps ← pairs (b :: more) rs
            pure (p :: ps)
          | _, _ => pure []
        pure (conjAll (← pairs ts rels), .prop)
  /-- The components of a field expression at the point `pt` (its coordinates): a
  field (`u` gives `u_1(pt),…`), a field applied to a point (`u(x,t)`), sums,
  differences and multiples, `\partial_t u`, `\partial_i u`, `\Delta u` (in the
  spatial coordinates), `\nabla p`, `\nabla\cdot u`, `\operatorname{div}u` and
  `(u\cdot\nabla)v`. A real number has one component. -/
  fieldAt : Nat → Scope → List Tm → MT → M (List Tm)
    | 0, _, _, _ => fail E.unsupported
    | g + 1, sc, pt, m => do
      let st ← get
      -- the components of a field, as functions of the coordinates
      let comps (n : Codes) (i : FieldInfo) : M (List Tm) := do
        let (F, _, _) ← head g sc (.id n)
        pure (if 1 < i.dim then (List.range i.dim).map fun k => Tm.app F (.num (k + 1)) else [F])
      let isField (m : MT) : Option (Codes × FieldInfo) := match m with
        | .id n => (st.fields.lookup n).map (n, ·)
        | _ => none
      let isOp (m : MT) (op : Codes) : Bool := match m with | .id n => n == op | _ => false
      match m with
      | .id n =>
        match st.fields.lookup n with
        | some i => do pure ((← comps n i).map (applyN · pt))
        | none => do pure [← asReal (← term g sc none m)]
      | .app (.id n) args =>
        match st.fields.lookup n with
        | some i => do
          -- the arguments, a point `x` of `\mathbb{R}^3` standing for its coordinates
          let xs ← args.mapM fun a => do
            match a with
            | .id v =>
              match lookupLocal sc (v ++ w!"#1") with
              | some _ => (List.range i.space).mapM fun k => do
                  let some (j, _) := lookupLocal sc (v ++ w!"#" ++ (Nat.toDigits 10 (k + 1)).map Char.toNat)
                    | fail E.undefined v
                  pure (Tm.loc j)
              | none => pure [← asReal (← term g sc none a)]
            | _ => pure [← asReal (← term g sc none a)]
          pure ((← comps n i).map (applyN · xs.flatten))
        | none => do pure [← asReal (← term g sc none m)]
      | .add a b => do pure (List.zipWith Tm.add (← fieldAt g sc pt a) (← fieldAt g sc pt b))
      | .minus a b => do pure (List.zipWith Tm.sub (← fieldAt g sc pt a) (← fieldAt g sc pt b))
      | .neg a => do pure ((← fieldAt g sc pt a).map Tm.neg)
      | .mul .. =>
        let fs := mulFactors 16 m
        match fs with
        -- `(u\cdot\nabla)v`: `∑ⱼ uⱼ ∂ⱼvᵢ`
        | [u, nab, v] =>
          match isField u, isOp nab w!"\\nabla", isField v with
          | some (un, ui), true, some (vn, vi) => do
            if ui.dim != ui.space then fail E.type
            let us ← comps un ui
            let vs ← comps vn vi
            pure (vs.map fun vc => sumAll ((List.range ui.space).map fun j =>
              Tm.mul (applyN (us.getD j (.num 0)) pt) (partialAt j vc pt (vi.doms[j]?).join)))
          | _, _, _ => factorsAt g sc pt fs
        | _ => factorsAt g sc pt fs
      | _ => do pure [← asReal (← term g sc none m)]
  /-- A product of factors at a point: operators (`\partial_t`, `\Delta`, `\nabla`,
  `\operatorname{div}`) applied to the field after them, and real factors. -/
  factorsAt : Nat → Scope → List Tm → List MT → M (List Tm)
    | 0, _, _, _ => fail E.unsupported
    | g + 1, sc, pt, fs => do
      let st ← get
      match fs with
      | [] => pure [.num 1]
      | [m] => fieldAt g sc pt m
      | op :: rest =>
        let field : Option (Codes × FieldInfo) := match rest with
          | [.id n] => (st.fields.lookup n).map (n, ·)
          | _ => none
        let isOp (op' : Codes) : Bool := match op with | .id n => n == op' | _ => false
        match field with
        | some (n, i) => do
          let (F, _, _) ← head g sc (.id n)
          let cs := if 1 < i.dim then (List.range i.dim).map fun k => Tm.app F (.num (k + 1)) else [F]
          let k := i.coords
          -- derivatives within the domain of each coordinate
          let dj (j : Nat) : Option Tm := (i.doms[j]?).join
          if isOp w!"\\nabla" then
            -- the gradient of a real field (in the spatial coordinates)
            if 1 < i.dim then fail E.unsupported else
            pure ((List.range i.space).map fun j => partialAt j F pt (dj j))
          else if isOp w!"div" || isOp w!"\\operatorname{div}" || isOp w!"\\divergence" then do
            if i.dim != i.space then fail E.type
            pure [sumAll ((List.range i.space).map fun j => partialAt j (cs.getD j (.num 0)) pt (dj j))]
          else
          match derivOps 8 op with
          | some ops => do
            -- the coordinate of an operator (`none`: the spatial Laplacian)
            let coord (o : Option MT) : M (Option Nat) := match o with
              | some (.id t) => if t == w!"t" && i.time then pure (some (k - 1)) else fail E.unsupported
              | some (.num j) => if 1 ≤ j && j ≤ i.space then pure (some (j - 1)) else fail E.type
              | none => pure none
              | _ => fail E.unsupported
            -- the inner operators as functions, the outermost at the point
            let some (outer, inner) := (match ops with | o :: os => some (o, os) | [] => none) | fail E.unsupported
            let mut out := cs
            for o in inner.reverse do
              match ← coord o with
              | some j => out := out.map (partialFn k j · (dj j))
              | none =>
                out := out.map fun c => (List.range k).foldl (fun acc _ => Tm.lam .real .tt acc)
                  (sumAll ((List.range i.space).map fun j =>
                    partialAt j (partialFn k j (shift k 0 c) (dj j)) ((List.range k).map fun l => .loc (k - 1 - l)) (dj j)))
            match ← coord outer with
            | some j => pure (out.map fun c => partialAt j c pt (dj j))
            | none => pure (out.map fun c => sumAll ((List.range i.space).map fun j => partialAt j (partialFn k j c (dj j)) pt (dj j)))
          | none => do
            let a ← asReal (← term g sc none op)
            pure ((← fieldAt g sc pt (.id n)).map (Tm.mul a))
        | none => do
          -- a real factor
          let a ← asReal (← term g sc none op)
          pure ((← factorsAt g sc pt rest).map (Tm.mul a))
  /-- An equation between fields: at every point of their domain, componentwise
  (`0` is the zero vector). `u(\cdot,0)=0`: at every point of space, at time `0`. -/
  fieldEq : Nat → Scope → MT → MT → M (Tm × Ty)
    | 0, _, _, _ => fail E.unsupported
    | g + 1, sc, x, y => do
      let st ← get
      let fsAll := fieldsIn st.fields 16 x ++ fieldsIn st.fields 16 y
      -- a slice `u(\cdot,s)`: the `\cdot` is the spatial point
      let slice : Option (Codes × FieldInfo × List MT) := match x with
        | .app (.id n) args =>
          if args.any (fun a => match a with | .id c => c == w!"\\cdot" | _ => false) then
            (st.fields.lookup n).map fun i => (n, i, args)
          else none
        | _ => none
      let compare (ls rs : List Tm) : M Tm := do
        let rs := if rs.length == 1 && ls.length > 1 then List.replicate ls.length (rs.getD 0 (.num 0)) else rs
        if ls.length != rs.length then fail E.type
        pure (conjAll (List.zipWith Tm.eq ls rs))
      match slice, fsAll with
      | some (n, i, args), _ => do
        -- ∀ spatial point, the field at it and the other arguments
        let k := i.space
        let sc' : Scope := ((List.range k).map fun j => (w!"@x" ++ (Nat.toDigits 10 j).map Char.toNat, Ty.real)).reverse ++ sc
        let pt : List Tm := (List.range k).map fun j => .loc (k - 1 - j)
        let rest ← (args.filter fun a => match a with | .id c => c != w!"\\cdot" | _ => true).mapM fun a => do
          asReal (← term g sc' none a)
        let (F, _, _) ← head g sc' (.id n)
        let ls := if 1 < i.dim then (List.range i.dim).map (fun c => applyN (Tm.app F (.num (c + 1))) (pt ++ rest))
          else [applyN F (pt ++ rest)]
        let rs ← fieldAt g sc' pt y
        let body ← compare ls rs
        let guard := conjAll (((i.doms.take k).zip pt).filterMap fun (d, p) => d.map (Tm.app · p))
        let body := if guard == .tt then body else .imp guard body
        pure ((List.range k).foldl (fun acc _ => Tm.all .real acc) body, .prop)
      | none, (_, i) :: _ => do
        let k := i.coords
        let sc' : Scope := ((List.range k).map fun j => (w!"@x" ++ (Nat.toDigits 10 j).map Char.toNat, Ty.real)).reverse ++ sc
        let pt : List Tm := (List.range k).map fun j => .loc (k - 1 - j)
        let ls ← fieldAt g sc' pt x
        let rs ← fieldAt g sc' pt y
        let body ← compare ls rs
        let guard := conjAll ((i.doms.zip pt).filterMap fun (d, p) => d.map (Tm.app · p))
        let body := if guard == .tt then body else .imp guard body
        pure ((List.range k).foldl (fun acc _ => Tm.all .real acc) body, .prop)
      | none, [] => do
        -- vectors at given points (`u(x,t)=0`)
        let ls ← fieldAt g sc [] x
        let rs ← fieldAt g sc [] y
        pure (← compare ls rs, .prop)
  /-- A norm: `\lVert v\rVert` of a vector (Euclidean), or with a space
  `\lVert u(t)\rVert_{L^2(\mathbb{R}^3)}`, `\lVert u(t)\rVert_{L^\infty}` of a field at a time
  (over space; the Euclidean norm of its value at each point). -/
  normTm : Nat → Scope → PF → MT → Option MT → M (Tm × Ty)
    | 0, _, _, _, _ => fail E.unsupported
    | f + 1, sc, _, x, none => do
      let vals ← fieldAt f sc [] x
      pure (.app (.app (.prim .rpow) (sumAll (vals.map fun v => Tm.mul v v))) (.div (.num 1) (.num 2)), .real)
    | f + 1, sc, pf, x, some space => do
      let st ← get
      let p : Option Bool := match space with
        | .mul (.sup (.id l) e) _ | .sup (.id l) e =>
          if l != [76] then none else match e with
            | .num 2 => some true
            | .id i => if i == w!"\\infty" then some false else none
            | _ => none
        | _ => none
      let some isL2 := p | fail E.finding w!"a norm other than \\|u(t)\\|_{L^2} and \\|u(t)\\|_{L^\\infty} of a field: the norm of this space is not in the vocabulary"
      -- the field, at the given time, as a function of the spatial coordinates
      let (u, targs) ← match x with
        | .app (.id u) as => pure (u, as)
        | .id u => pure (u, [])
        | _ => fail E.unsupported
      let some i := st.fields.lookup u | fail E.unsupported
      -- the space of the norm is the field's: `\mathbb{R}^n`, or `\mathbb{T}^n` for a periodic
      -- field (its `L^\infty` norm over a period is its `L^\infty` norm on `ℝⁿ`; an `L^2`
      -- norm over a period is not read yet)
      let onTorus : Option Bool := match space with
        | .mul _ (.sup (.id d) _) => if d == w!"\\mathbb{T}" then some true else if d == w!"\\mathbb{R}" then some false else none
        | .mul _ (.id d) => if d == w!"\\mathbb{T}" then some true else if d == w!"\\mathbb{R}" then some false else none
        | _ => none
      if onTorus.any (· != i.periodic) || (i.periodic && isL2) then fail E.unsupported
      let rest ← targs.mapM fun a => do asReal (← term f sc pf a)
      let s := i.coords - rest.length
      if s != i.space && rest.length != 0 then fail E.unsupported
      let (F, _, _) ← head f sc (.id u)
      let comps := if 1 < i.dim then (List.range i.dim).map fun c => Tm.app F (.num (c + 1)) else [F]
      let pt := ((List.range s).map fun j => Tm.loc (s - 1 - j)) ++ rest.map (shift s 0)
      let sq := sumAll (comps.map fun c => let v := applyN (shift s 0 c) pt; Tm.mul v v)
      let mag := (List.range s).foldl (fun acc _ => Tm.lam .real .tt acc)
        (.app (.app (.prim .rpow) sq) (.div (.num 1) (.num 2)))
      -- the norm, a description: undefined when infinite
      pure (.the .real (.app (.app (.prim (if isL2 then .l2NormN s else .supNormN s)) (shift 1 0 mag)) (.loc 0)), .real)
  /-- `\partial^I f(x,y)`: the partial derivative of a multi-index `I` (its components
  `I_1`, … bound as variables) of a function of several variables, at a point or as a
  function; `none` for any other product. -/
  multiPartial : Nat → Scope → PF → MT → MT → M (Option (Tm × Ty))
    | 0, _, _, _, _ => pure none
    | f + 1, sc, pf, x, y => do
      let some mi := (match x with
          | .sup (.id d) (.id mi) => if d == w!"\\partial" then some mi else none
          | _ => none) | pure none
      let comps := ((List.range 8).map fun k => mi ++ [95] ++ (Nat.toDigits 10 (k + 1)).map Char.toNat).takeWhile
        fun nm => (lookupLocal sc nm).isSome
      let n := comps.length
      if n < 1 then fail E.undefined mi
      let (hd, args) := match y with
        | .app h as => (h, as)
        | _ => (y, [])
      let (F, fty, _) ← head f sc hd
      if realArity fty != some n then fail E.type
      let G := Tm.the (Ty.fns (n + n)) (.app (.app (.prim (.partialMulti n)) (shift 1 0 F)) (.loc 0))
      let idx ← comps.mapM fun nm => do asReal (← term f sc none (.id nm))
      if args.isEmpty then
        -- as a function of the point
        pure (some ((List.range n).foldl (fun acc _ => Tm.lam .real .tt acc)
          (applyN (shift n 0 G) (idx.map (shift n 0) ++ (List.range n).map fun j => Tm.loc (n - 1 - j))), Ty.fns n))
      else do
        if args.length != n then fail E.type
        let xs ← args.mapM fun a => do asReal (← term f sc pf a)
        pure (some (applyN G (idx ++ xs), .real))
  /-- A subscripted symbol `b_i` (the formula `m`). -/
  subTm : Nat → Scope → PF → MT → MT → MT → M (Tm × Ty)
    | 0, _, _, _, _, _ => fail E.unsupported
    | f + 1, sc, pf, m, b, i => do
      -- a bound variable with a subscript in its name (`C_m` of `there is $C_m>0$`)
      match (symKey m).bind (lookupLocal sc ·) with
      | some (j, t) => pure (.loc j, t)
      | none =>
      match b with
      | .id key => do
        -- (a finite field is not a set of real numbers)
        if key == w!"\\mathbb{F}" then fail E.finding finiteField
        -- `x_i` for a sequence `x` of the scope (`x_1,\ldots,x_n`): its term, defined for
        -- the integers `i` from the first index to the last
        if let some (j, .fn .real .real) := lookupLocal sc key then
          if let some (_, lo, hi) := (← get).seqs.find? (·.1 == key) then
            let a ← asReal (← term f sc none i)
            let l ← asReal (← term f sc none lo)
            let h ← asReal (← term f sc none hi)
            return (.guard (conjAll [.app (.prim .isInt) a, .le l a, .le a h]) (.app (.loc j) a), .real)
        -- a constant with a subscript (`d_0`), unless the index is a variable
        let ck := match i with
          | .id x => if (lookupLocal sc x).isSome then none else symKey m
          | _ => symKey m
        let c ← match ck with
          | some k => lookupGlob k
          | none => pure none
        match c with
        | some (h, g) =>
          if g.family then fail E.unsupported key
          else do
            let (hd, hty, hdoms) ← withImplicit sc h g
            match pf, hty with
            | some (s, sty), .fn a _ =>
              if a == sty then applyAll hd hty hdoms [(s, sty)] else pure (hd, hty)
            | _, _ => pure (hd, hty)
        | none =>
        let sign := match i with | .id [c] => c == 43 || c == 45 || c == 42 | _ => false
        if sign then fail E.undefined ((symKey m).getD key)
        let (h, g) ← liftO (← lookupGlob key) E.undefined key
        if !g.family then fail E.unsupported key
        let a ← term f sc none i
        let (h0, ty0, doms0) ← withImplicit sc h g
        applyAll h0 ty0 doms0 [a]
      | _ => fail E.finding w!"a subscript on a formula, such as $(B_k)_L$: name the quantity (Set $C_k\\coloneqq …$) and subscript the name"
  propOf : Nat → Scope → PF → MT → M Tm
    | 0, _, _, _ => fail E.unsupported
    | g + 1, sc, pf, x => do
      let (p, t) ← term g sc pf x
      if t == .prop then pure p else fail E.type
  member : Nat → Scope → Tm × Ty → MT → M Tm
    | 0, _, _, _ => fail E.unsupported
    | g + 1, sc, x, dom =>
      match dom with
      | .interval lo hi => do
        -- (an element of the interval type that the domain is: nothing to say)
        if ((← intervalType dom).map (·.ty)) == some x.2 then pure .tt
        else
          let l ← asReal (← term g sc none lo)
          let h ← asReal (← term g sc none hi)
          pure (interval l h (← asReal x))
      | .ival lo hi lopen ropen => do
        let l ← if isInfty false lo then (if lopen then pure none else fail E.unsupported)
          else do let t ← term g sc none lo; pure (some (← asReal t))
        let h ← if isInfty true hi then (if ropen then pure none else fail E.unsupported)
          else do let t ← term g sc none hi; pure (some (← asReal t))
        pure (rayTm l h lopen ropen (← asReal x))
      | .tuple [lo, hi] => do
        -- `x ∈ (a,b)`: an open interval, `x ∈ (0,\infty)` a ray
        let l ← if isInfty false lo then pure none
          else do let t ← term g sc none lo; pure (some (← asReal t))
        let h ← if isInfty true hi then pure none
          else do let t ← term g sc none hi; pure (some (← asReal t))
        pure (rayTm l h true true (← asReal x))
      | .id n => do
        if n == w!"\\mathbb{R}" then do let _ ← asReal x; pure .tt else
        match ← lookupGlob n, builtinConst n with
        | none, some (p, .fn a .prop) => do let x' ← coerce x.1 x.2 a; pure (.app p x')
        | _, _ =>
        let (i, gl) ← liftO (← lookupGlob n) E.undefined n
        match gl.ty with
        | .fn a .prop => do let x' ← coerce x.1 x.2 a; pure (.app (.glob i) x')
        | _ => fail E.type
      | _ => do
        -- any other set of real numbers: `\{x\in A : …\}`, `A\cup B`, …
        let (p, t) ← term g sc none dom
        match t with
        | .fn a .prop => do let x' ← coerce x.1 x.2 a; pure (.app p x')
        | _ => fail E.type
  setOf : Nat → Scope → MT → MT → List MT → M (Tm × Ty)
    | 0, _, _, _, _ => fail E.unsupported
    | g + 1, sc, pat, dom, conds =>
      match pat, dom with
      | .id v, d => do
        -- (no stated domain: the real numbers)
        let d := if Math.isUnstatedReals d then .id w!"\\mathbb{R}" else d
        let (ty, pred) ← elemDom g d
        let sc' := (v, ty) :: sc
        let cs ← conds.mapM fun c => do
          let (p, t) ← term g sc' none c
          if t == .prop then pure p else fail E.type
        let mem := match pred with | some p => [p] | none => []
        -- (a letter the article declares to be an integer)
        let st ← get
        let mem := match (if ty == .real then declaredInt st v (.loc 0) else .tt) with
          | .tt => mem
          | i => i :: mem
        pure (.lam ty .tt (conjAll (mem ++ cs)), .fn ty .prop)
      | .tuple [.id v1, .id v2], .sup d (.num 2) => do
        let (ty, pred) ← elemDom g d
        let sc' := (v2, ty) :: (v1, ty) :: sc
        let cs ← conds.mapM fun c => do
          let (p, t) ← term g sc' none c
          if t == .prop then pure p else fail E.type
        -- both coordinates lie in the domain; `p` speaks about `loc 0`
        let mem := match pred with
          | some p => [Tm.and (.app (.lam ty .tt p) (.loc 1)) (.app (.lam ty .tt p) (.loc 0))]
          | none => []
        pure (.lam ty .tt (.lam ty .tt (conjAll (mem ++ cs))), .fn ty (.fn ty .prop))
      | _, _ => fail E.unsupported
  /-- Element type of an interval domain, and the membership predicate of the
  innermost bound variable (`loc 0`). -/
  elemDom : Nat → MT → M (Ty × Option Tm)
    | 0, _ => fail E.unsupported
    | g + 1, d => do
      if let some iv ← intervalType d then return (iv.ty, none)
      match d with
        | .interval (.neg (.num a)) (.num b) => pure (.real, some (interval (.neg (.num a)) (.num b) (.loc 0)))
        | .interval (.num a) (.num b) => pure (.real, some (interval (.num a) (.num b) (.loc 0)))
        | .ival a b lo ro => do
          let a' ← constEnd false lo a
          let b' ← constEnd true ro b
          pure (.real, some (rayTm a' b' lo ro (.loc 0)))
        | .tuple [a, b] => do
          let a' ← constEnd false true a
          let b' ← constEnd true true b
          pure (.real, some (rayTm a' b' true true (.loc 0)))
        | .id n =>
          if n == w!"\\mathbb{R}" then pure (.real, none)
          else match builtinConst n with
            | some (.lam .real .tt p, .fn .real .prop) => pure (.real, some p)
            | _ => fail E.finding (w!"the elements of a set $\\{x\\in A : …\\}$ are taken from a set of numbers; " ++ n ++ w!" is not one Leanify knows")
        | _ => do
          -- any other closed set of real numbers (`\mathbb{R}\setminus\{0\}`)
          let (p, t) ← term g [] none d
          if t == .fn .real .prop then pure (.real, some (.app (shift 1 0 p) (.loc 0))) else fail E.unsupported

/-- Elaborate a lambda `pat ↦ body` with the given argument types and result type. -/
def lam (f : Nat) (sc : Scope) (pat : MT) (args : List Ty) (res : Option Ty) (body : MT) :
    M (Tm × Ty) := do
  let names ← match pat with
    | .id v => pure [v]
    | .tuple vs => vs.mapM fun v => match v with | .id n => pure n | _ => fail E.unsupported
    | _ => fail E.unsupported
  if names.length != args.length then fail E.type
  let sc' := (names.zip args).reverse ++ sc
  let (b, bty) ← term f sc' none body
  let (b, bty) ← match res with
    | some r => do pure (← coerce b bty r, r)
    | none => pure (b, bty)
  let rec wrap : List Ty → Tm × Ty
    | [] => (b, bty)
    | t :: ts => let (x, xt) := wrap ts; (.lam t .tt x, .fn t xt)
  pure (wrap args)

end Elab
end Leanify
