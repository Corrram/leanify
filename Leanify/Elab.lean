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

abbrev Local := Codes × Ty
abbrev Scope := List Local

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

structure St where
  /-- The vocabulary of the article. -/
  vocab : Vocab := {}
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
  topic : Topic := .none
  /-- Variables fixed in the running text (`fix $b\in B$`), by section. -/
  fixed : List (Nat × BindInfo) := []
  /-- Definitions made under binders whose symbol does not show their variables
  (`z_-(x)` under `For $b\in B$`): the variables, supplied from the scope at each use. -/
  implicits : List (Nat × List Codes) := []
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
  /-- The letters the article declares generic constants (`Throughout, $C$ and $C_m$
  denote positive constants.`), and whether they are positive. -/
  genericConsts : List (Codes × Bool) := []
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

def coerce (t : Tm) (src dst : Ty) : M Tm :=
  if src == dst then pure t
  else if src == .unit && dst == .real then pure (.ofUnit t)
  else if src == .real && dst == .unit then pure (.toUnit t)
  else fail E.type

def asReal (p : Tm × Ty) : M Tm := coerce p.1 p.2 .real

def isMeasure : Ty → Bool
  | .fn (.fn .unit .prop) .real => true
  | .fn (.fn .unit (.fn .unit .prop)) .real => true
  | _ => false

def measGuard (argTy : Ty) (arg : Tm) : Option Tm :=
  if argTy == Ty.set1 then some (.app (.prim .measurableSet1) arg)
  else if argTy == Ty.set2 then some (.app (.prim .measurableSet2) arg)
  else none

/-- Apply a head of type `ty` to arguments, inserting coercions, the domain
guards of the head's definition, and measurability guards for measures. -/
def applyAll (head : Tm) (ty : Ty) (doms : List (Option Tm)) : List (Tm × Ty) → M (Tm × Ty)
  | [] => pure (head, ty)
  | (a, aty) :: rest =>
    match ty with
    | .fn dom cod => do
      let a' ← coerce a aty dom
      let applied := Tm.app head a'
      let guarded := match doms.head? with
        | some (some p) => Tm.guard (applyPred p a') applied
        | _ => applied
      let guarded := if isMeasure ty then
          match measGuard dom a' with | some g => Tm.guard g guarded | none => guarded
        else guarded
      applyAll guarded cod (doms.drop 1) rest
    | _ =>
      -- a real number applied to one argument is a product
      if ty == .real && rest.isEmpty then do
        let a' ← coerce a aty .real
        pure (.mul head a', .real)
      else fail E.type

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

/-- Standard constants and sets: `\pi`, `\emptyset`, `\mathbb{R}` and its rays. -/
def builtinConst (n : Codes) : Option (Tm × Ty) :=
  if n == w!"\\pi" then some (.prim .pi, .real)
  else if n == w!"\\emptyset" || n == w!"\\varnothing" then some (.lam .real .tt (.not .tt), .fn .real .prop)
  else if n == w!"\\mathbb{R}" then some (.lam .real .tt .tt, .fn .real .prop)
  else if n == w!"\\mathbb{Z}" then some (.lam .real .tt (.app (.prim .isInt) (.loc 0)), .fn .real .prop)
  -- the natural numbers include 0, as in mathlib (`\mathbb{N}_0` says so explicitly)
  else if n == w!"\\mathbb{N}" || n == w!"\\mathbb{N}_0" then
    some (.lam .real .tt (.app (.prim .isNat) (.loc 0)), .fn .real .prop)
  else if n == w!"\\mathbb{R}_{>0}" then some (.lam .real .tt (.lt (.num 0) (.loc 0)), .fn .real .prop)
  else if n == w!"\\mathbb{R}_{\\ge0}" then some (.lam .real .tt (.le (.num 0) (.loc 0)), .fn .real .prop)
  else none

/-- Names of indices (`n`, `k`, …): integers, in exponents and limits. -/
def indexNames : List Codes := [w!"n", w!"m", w!"k", w!"j", w!"i", w!"N", w!"M", w!"K"]

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

def isPredTy : Ty → Bool
  | .fn _ .prop => true
  | .fn _ (.fn _ .prop) => true
  | _ => false

def relTm (r : Rel) (x y : Tm × Ty) : M Tm := do
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

def isZeroOne : MT → Bool
  | .interval (.num 0) (.num 1) => true
  | _ => false

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
  | as => do
    let (t, ty) ← applyAll (.glob i) g.ty g.doms as
    pure (t, ty, g.doms.drop as.length)

/-- Elaborate a formula. Fuel bounds the recursion (kernel-reducible). -/
def term : Nat → Scope → PF → MT → M (Tm × Ty)
  | 0, _, _, _ => fail E.unsupported
  | f + 1, sc, pf, m =>
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
          match builtinConst n with
          | some r => pure r
          | none => fail E.undefined n
    | .add x y => do
      let a ← asReal (← term f sc pf x); let b ← asReal (← term f sc pf y); pure (.add a b, .real)
    | .minus x y => do
      let a ← asReal (← term f sc pf x); let b ← asReal (← term f sc pf y); pure (.sub a b, .real)
    | .mul x y => do
      let a ← asReal (← term f sc pf x); let b ← asReal (← term f sc pf y); pure (.mul a b, .real)
    | .div x y | .frac x y => do
      let a ← asReal (← term f sc pf x); let b ← asReal (← term f sc pf y); pure (.div a b, .real)
    | .neg x => do let a ← asReal (← term f sc pf x); pure (.neg a, .real)
    | .abs x => do let a ← asReal (← term f sc pf x); pure (.abs a, .real)
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
    | .sup (.app (.id n) [a]) e =>
      match lookupLocal sc n with
      | some (_, t) =>
        if t == .real || t == .unit then term f sc pf (.mul (.id n) (.sup a e))
        else supTerm f sc pf (.app (.id n) [a]) e
      | none => supTerm f sc pf (.app (.id n) [a]) e
    | .sup b e => supTerm f sc pf b e
    | .hat x => do
      let (h, g) ← liftO (← lookupGlob w!"\\widehat") E.undefined w!"\\widehat"
      let a ← term f sc pf x
      applyAll (.glob h) g.ty g.doms [a]
    | .sub b i =>
      -- a bound variable with a subscript in its name (`C_m` of `there is $C_m>0$`)
      match (symKey m).bind (lookupLocal sc ·) with
      | some (j, t) => pure (.loc j, t)
      | none =>
      match b with
      | .id key => do
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
      | _ => fail E.unsupported
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
      match lookupLocal sc n with
      | some (_, t) =>
        if t == .real || t == .unit then term f sc pf (.mul (.id n) a)
        else do
          let (h, hty, doms) ← head f sc (.id n)
          applyAll h hty doms [← term f sc pf a]
      | none => do
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
      | .id op, [x, y] =>
        if op == w!"\\cup" || op == w!"\\times" || op == w!"\\cap" || op == w!"\\setminus" then setOp f sc pf op x y
        else do
          let (h, hty, doms) ← head f sc hd
          let xs ← args.mapM (term f sc pf)
          applyAll h hty doms xs
      | _, _ => do
        let (h, hty, doms) ← head f sc hd
        let xs ← args.mapM (term f sc pf)
        applyAll h hty doms xs
    | .int (.num 0) (.num 1) body v => do
      if (lookupLocal sc v).isSome then fail E.shadow v
      let b ← asReal (← term f ((v, .unit) :: sc) (pf.map fun (s, t) => (shift 1 0 s, t)) body)
      pure (.integral b, .real)
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
    | .quant isAll vs dom body =>
      -- each variable ranges over the real numbers in `dom`
      match vs with
      | [] => do pure (← propOf f sc pf body, .prop)
      | v :: rest => do
        if (lookupLocal sc v).isSome then fail E.shadow v
        let sc' : Scope := (v, Ty.real) :: sc
        let pf' := pf.map fun (s, t) => (shift 1 0 s, t)
        let m ← member f sc' (.loc 0, .real) dom
        let b ← propOf f sc' pf' (.quant isAll rest dom body)
        -- (over all real numbers, without a condition)
        pure (if isAll then .all .real (if m == .tt then b else .imp m b)
          else .ex .real (if m == .tt then b else .and m b), .prop)
    -- `x\notin A`
    | .chain x [(.nmem, dom)] => do
      let a ← term f sc pf x
      pure (.not (← member f sc a dom), .prop)
    -- `A\subseteq B`: every real number in `A` is in `B`
    | .chain x [(.subset, y)] => do
      let sc' : Scope := (w!"@x", Ty.real) :: sc
      let a ← member f sc' (.loc 0, .real) x
      let b ← member f sc' (.loc 0, .real) y
      pure (.all .real (.imp a b), .prop)
    | .chain x [(.supset, y)] => do
      let sc' : Scope := (w!"@x", Ty.real) :: sc
      let a ← member f sc' (.loc 0, .real) x
      let b ← member f sc' (.loc 0, .real) y
      pure (.all .real (.imp b a), .prop)
    | .chain x rest => do
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
            let p ← if r == .eq && isPredTy a.2 && a.2 == b.2 then pure (setEq a.2 a.1 b.1) else relTm r a b
            let ps ← pairs (b :: more) rs
            pure (p :: ps)
          | _, _ => pure []
        pure (conjAll (← pairs ts rels), .prop)
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
        let aty := if a.2 == .unit then Ty.unit else Ty.real
        let bty := if b.2 == .unit then Ty.unit else Ty.real
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
        let aty := if a.2 == .unit then Ty.unit else Ty.real
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
        -- each term is the body with the index replaced by its value
        let terms ← (List.range (b - a + 1)).mapM fun k =>
          do asReal (← term f sc pf (MT.substId v (MT.num (a + k)) 64 body))
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
        let b ← asReal (← term f sc' (pf.map fun (s, t) => (shift 1 0 s, t)) body)
        if isInfty true hi then do
          if !isSum then fail E.unsupported w!"\\prod"
          let lam := Tm.lam .real (.and (isInt (.loc 0)) (.le (shift 1 0 l) (.loc 0))) b
          let conv := Tm.app (.app (.prim .seriesConv) l) lam
          pure (.guard (.and (isInt l) conv) (.app (.app (.prim .series) l) lam), .real)
        else do
          let h ← asReal (← term f sc none hi)
          let lam := Tm.lam .real (.and (isInt (.loc 0))
            (.and (.le (shift 1 0 l) (.loc 0)) (.le (.loc 0) (shift 1 0 h)))) b
          let p : Prim := if isSum then .finSum else .finProd
          pure (.guard (.and (isInt l) (isInt h)) (.app (.app (.app (.prim p) l) h) lam), .real)
    -- `\lim_{x\to a} e`, `\lim_{x\to\infty} e`, and `\lim_{n\to\infty} a_n` for a sequence
    -- (an index `n`, `m`, `k`, `j`, `i` runs through the natural numbers): the limit within
    -- the points where the expression is defined, when it exists
    | .limit v target body => do
      if (lookupLocal sc v).isSome then fail E.shadow v
      let sc' : Scope := (v, Ty.real) :: sc
      let b ← asReal (← term f sc' (pf.map fun (s, t) => (shift 1 0 s, t)) body)
      let seq := indexNames.contains v
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
        | .id [101] => do pure ((lookupLocal sc [101]).isNone && (← lookupGlob [101]).isNone)
        | _ => pure false
      if isE then do
        let a ← asReal (← term f sc pf e)
        pure (.app (.prim (.realFn .exp)) a, .real)
      else
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
          powTm a p (indexExp e)
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
        powTm a p (indexExp e)
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
          let (i, gl) ← liftO (← lookupGlob n) E.undefined n
          pure (.glob i, gl.ty, gl.doms)
      -- `x_n` for a real function `x` of the scope (the weights of a distribution): `x(n)`
      | .sub (.id key) i =>
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
        let (t, ty) ← applyAll h0 ty0 doms0 [a]
        pure (t, ty, doms0.drop 1)
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
        let (t, ty) ← applyAll (.glob h) gl.ty gl.doms [a]
        pure (t, ty, gl.doms.drop 1)
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
        if x.2 == .unit && isZeroOne dom then pure .tt
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
        let (ty, pred) ← elemDom g d
        let sc' := (v, ty) :: sc
        let cs ← conds.mapM fun c => do
          let (p, t) ← term g sc' none c
          if t == .prop then pure p else fail E.type
        let mem := match pred with | some p => [p] | none => []
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
    | g + 1, d =>
      if isZeroOne d then pure (.unit, none)
      else match d with
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
            | _ => fail E.unsupported
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
