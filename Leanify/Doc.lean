import Leanify.Elab

/-! # Compiling an article

`compileArticle` reads the complete source: preamble macros, the document body,
its sentences and environments. Every sentence is either compiled (definitions
and claims) or kept as prose with the reason it has no reading. A sentence is
compiled entirely or not at all. Citations become premises: a proof sentence may
use earlier sentences of its proof and the results cited so far in that proof.
A result whose proof compiled completely has the proof's sentences (and their
citations) as its premises: this is the closing step of the proof. -/
namespace Leanify
open Grammar Elab

structure ProofInfo where
  env : Nat
  proves : Codes
  steps : List Nat
  cites : List Nat
  complete : Bool
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

structure Doc where
  globs : List Glob
  values : List Tm
  claims : List Claim
  sentences : List (Context × Nat × Nat)
  outcomes : List Outcome
  labels : List (Codes × List Nat)
  proofs : List ProofInfo
  /-- Names of definitions introduced by phrases rather than symbols. -/
  names : List (List Codes × Nat)
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

/-! ## Notation templates

`We write $\mathbf E[X]$ for …` declares a notation: later formulas that match the
template are read as what it stands for. A template is a list of fixed tokens and
arguments: the variables of the template that also occur in what it stands for.
An argument between fixed tokens is everything up to the next fixed token (as
for delimited TeX macros); an argument at the start or end is one atom (a symbol
or a group, with its sub- and superscripts). Matching is on the tokens of the
formulas, before they are parsed. -/

namespace Notation

def opens : Tok → Bool
  | .lbrace | .msym 40 | .msym 91 | .begin _ => true
  | _ => false

def closes : Tok → Bool
  | .rbrace | .msym 41 | .msym 93 | .finish _ => true
  | _ => false

/-- A balanced group starting with an opening token: the group and the rest. -/
def group : Nat → Nat → List PTok → List PTok → Option (List PTok × List PTok)
  | 0, _, _, _ => none
  | _ + 1, _, _, [] => none
  | f + 1, d, acc, t :: ts =>
    if opens t.tok then group f (d + 1) (t :: acc) ts
    else if closes t.tok then
      if d ≤ 1 then some ((t :: acc).reverse, ts) else group f (d - 1) (t :: acc) ts
    else group f d (t :: acc) ts

/-- One token or a group. -/
def unit (ts : List PTok) : Option (List PTok × List PTok) :=
  match ts with
  | t :: rest =>
    if opens t.tok then group (ts.length + 1) 0 [] ts
    else if closes t.tok then none
    else match t.tok with
      | .msym _ => none
      | _ => some ([t], rest)
  | [] => none

/-- Sub- and superscripts and primes after an atom. -/
def scripts : Nat → List PTok → List PTok → List PTok × List PTok
  | 0, acc, ts => (acc, ts)
  | f + 1, acc, t :: ts =>
    if t.tok == .msym 95 || t.tok == .msym 94 then
      match unit ts with
      | some (u, r) => scripts f (acc ++ [t] ++ u) r
      | none => (acc, t :: ts)
    else if t.tok == .msym 39 then scripts f (acc ++ [t]) ts
    else (acc, t :: ts)
  | _ + 1, acc, [] => (acc, [])

/-- An atom: a symbol (with a font: `\mathbf{x}`, `\mathcal P`, or the digits of a
number) or a group, with its scripts. -/
def atom (ts : List PTok) : Option (List PTok × List PTok) := do
  let (base, rest) ← match ts with
    | t :: r =>
      match t.tok with
      | .cmd n => if Math.wFonts.contains n then (unit r).map fun (u, r') => (t :: u, r') else some ([t], r)
      | .mnum _ =>
        let ds := r.takeWhile fun p => match p.tok with | .mnum _ => true | _ => false
        some (t :: ds, r.drop ds.length)
      | _ => unit ts
    | [] => none
  some (scripts (rest.length + 1) base rest)

/-- The shortest nonempty balanced prefix before a token `stop` outside groups. -/
def delimited (stop : Tok) : Nat → Nat → List PTok → List PTok → Option (List PTok × List PTok)
  | 0, _, _, _ => none
  | _ + 1, _, _, [] => none
  | f + 1, d, acc, t :: ts =>
    if d == 0 && t.tok == stop && !acc.isEmpty then some (acc.reverse, t :: ts)
    else if opens t.tok then delimited stop f (d + 1) (t :: acc) ts
    else if closes t.tok then (if d == 0 then none else delimited stop f (d - 1) (t :: acc) ts)
    else delimited stop f d (t :: acc) ts

def sameToks (a b : List PTok) : Bool := a.map (·.tok) == b.map (·.tok)

/-- Bind argument `k` (an argument used twice must match the same tokens). -/
def bind (k : Nat) (arg : List PTok) (acc : List (Nat × List PTok)) : Option (List (Nat × List PTok)) :=
  match acc.lookup k with
  | some old => if sameToks old arg then some acc else none
  | none => some ((k, arg) :: acc)

/-- Match the items of a template at the start of the tokens. -/
def matchItems : Nat → List TItem → List PTok → List (Nat × List PTok) →
    Option (List (Nat × List PTok) × List PTok)
  | 0, _, _, _ => none
  | _ + 1, [], ts, acc => some (acc, ts)
  | f + 1, .fixed t :: is, u :: ts, acc => if u.tok == t then matchItems f is ts acc else none
  | _ + 1, .fixed _ :: _, [], _ => none
  | f + 1, .slot k :: .fixed t :: is, ts, acc => do
    let (arg, r) ← delimited t (ts.length + 1) 0 [] ts
    matchItems f (.fixed t :: is) r (← bind k arg acc)
  | f + 1, .slot k :: is, ts, acc => do
    let (arg, r) ← atom ts
    matchItems f is r (← bind k arg acc)

/-- Match a template at the start of the tokens; a first argument is an atom. -/
def matchAt (pat : List TItem) (ts : List PTok) : Option (List (Nat × List PTok) × List PTok) :=
  let f := pat.length + ts.length + 2
  match pat with
  | .slot k :: rest => do
    let (arg, r) ← atom ts
    matchItems f rest r [(k, arg)]
  | _ => matchItems f pat ts []

/-- The tokens of what a template stands for, with the arguments put in (an
argument of several tokens in braces). -/
def substitute (repl : List TItem) (args : List (Nat × List PTok)) (pos : Nat) : List PTok :=
  repl.flatMap fun it => match it with
    | .fixed t => [⟨t, pos, true⟩]
    | .slot k =>
      match args.lookup k with
      | some [p] => [p]
      | some ps => ⟨.lbrace, pos, true⟩ :: ps ++ [⟨.rbrace, pos, true⟩]
      | none => []

/-- Replace every match of a template in the formulas of a token list. -/
def rewrite (tpl : Template) : Nat → List PTok → List PTok
  | 0, ts => ts
  | _ + 1, [] => []
  | f + 1, t :: ts =>
    if !t.math then t :: rewrite tpl f ts else
    match matchAt tpl.pat (t :: ts) with
    | some (args, rest) =>
      if rest.length < ts.length + 1 then substitute tpl.repl args t.pos ++ rewrite tpl f rest
      else t :: rewrite tpl f ts
    | none => t :: rewrite tpl f ts

/-- The labelled displays of a sentence: each label with the display's tokens
(without its labels and its final punctuation). -/
def labelledDisplays : Nat → List PTok → List (Codes × List PTok) → List (Codes × List PTok)
  | 0, _, acc => acc
  | _ + 1, [], acc => acc
  | f + 1, t :: ts, acc =>
    match t.tok with
    | .begin e =>
      if Lex.wDisplayEnvs.contains e then
        let body := ts.takeWhile (fun p => p.tok != .finish e)
        let labels := body.filterMap fun p => match p.tok with | .ref .label l => some l | _ => none
        let clean := body.filter fun p => match p.tok with | .ref .label _ => false | _ => true
        let clean := (clean.reverse.dropWhile fun p => p.tok == .msym 44 || p.tok == .msym 46).reverse
        let span := t :: clean ++ [⟨.finish e, t.pos, t.math⟩]
        labelledDisplays f (ts.drop (body.length + 1)) (labels.map (·, span) ++ acc)
      else labelledDisplays f ts acc
    | _ => labelledDisplays f ts acc

/-- `satisfying \eqref{l}`: the display `l` in place of the reference. -/
def expandRefs (ds : List (Codes × List PTok)) : Nat → List PTok → List PTok
  | 0, ts => ts
  | f + 1, a :: b :: rest =>
    match a.tok, b.tok with
    | .word w, .ref .eqref l =>
      match (if Grammar.lower w == w!"satisfying" then ds.lookup l else none) with
      | some span => a :: span.map (fun p => { p with pos := b.pos }) ++ expandRefs ds f rest
      | none => a :: expandRefs ds f (b :: rest)
    | _, _ => a :: expandRefs ds f (b :: rest)
  | _ + 1, ts => ts

/-- All templates, in order, three times (a notation may use an earlier one). -/
def rewriteAll (tpls : List Template) (ts : List PTok) : List PTok :=
  if tpls.isEmpty then ts else
  let pass (ts : List PTok) := tpls.foldl (fun acc tpl => rewrite tpl (acc.length + 1) acc) ts
  pass (pass (pass ts))

/-- The formulas of a sentence, in order (the tokens between `$…$`). -/
def formulas : Nat → List PTok → List (List PTok) → List (List PTok)
  | 0, _, acc => acc.reverse
  | _ + 1, [], acc => acc.reverse
  | f + 1, t :: ts, acc =>
    if t.tok == .mopen then
      let body := ts.takeWhile (·.tok != .mclose)
      formulas f (ts.drop (body.length + 1)) (body :: acc)
    else formulas f ts acc

/-- A token that may be an argument: a letter or a command that is not a font. -/
def slotTok : Tok → Bool
  | .mvar _ => true
  | .cmd n => !Math.wFonts.contains n
  | _ => false

/-- Which tokens are part of a name set in a font (`\mathrm{Bin}`, `\mathcal P`):
those are never arguments. -/
def fontMask : Nat → List Tok → List Bool
  | 0, _ => []
  | _ + 1, [] => []
  | f + 1, .cmd n :: .lbrace :: ts =>
    if Math.wFonts.contains n then
      let body := ts.takeWhile (· != .rbrace)
      false :: List.replicate (body.length + 2) true ++ fontMask f (ts.drop (body.length + 1))
    else false :: fontMask f (.lbrace :: ts)
  | f + 1, .cmd n :: t :: ts =>
    if Math.wFonts.contains n then false :: true :: fontMask f ts else false :: fontMask f (t :: ts)
  | f + 1, _ :: ts => false :: fontMask f ts

/-- Items of tokens, given the argument tokens (font-set names stay fixed). -/
def items (args : List Tok) (ts : List Tok) : List TItem :=
  (ts.zip (fontMask (ts.length + 1) ts ++ List.replicate ts.length false)).map fun (t, fixed) =>
    if fixed then .fixed t else
    match args.idxOf? t with
    | some k => if k < args.length then .slot k else .fixed t
    | none => .fixed t

/-- A template from a pattern and what it stands for: the arguments are the
letters and commands of the pattern that occur in `repl`, numbered by first
occurrence. -/
def template (pat repl : List PTok) : Template :=
  let ptoks := pat.map (·.tok)
  let free := (ptoks.zip (fontMask (ptoks.length + 1) ptoks ++ List.replicate ptoks.length false)).filterMap
    fun (t, fixed) => if fixed then none else some t
  let args := (free.filter fun t => slotTok t && repl.any (·.tok == t)).eraseDups
  ⟨items args ptoks, items args (repl.map (·.tok))⟩

/-- The sentence declares a notation (`We write …`): its own formulas are not rewritten. -/
def declares (ts : List PTok) : Bool :=
  let ws := ts.filterMap fun p => match p.tok with | .word w => some (Grammar.lower w) | _ => none
  ws.take 2 == [w!"we", w!"write"] || ws.take 3 == [w!"let", w!"us", w!"write"]

/-- The first occurrence of `seg` in `ts`: the tokens before it and after it. -/
def splitAt (seg : List MTok) : Nat → List MTok → List MTok → Option (List MTok × List MTok)
  | 0, _, _ => none
  | _ + 1, [], acc => if seg.isEmpty then some (acc.reverse, []) else none
  | f + 1, t :: ts, acc =>
    if !seg.isEmpty && (t :: ts).take seg.length == seg then some (acc.reverse, (t :: ts).drop seg.length)
    else splitAt seg f ts (t :: acc)

/-- An argument in braces is its contents. -/
def unbrace (arg : List MTok) : List MTok :=
  match arg with
  | .lb :: r => if r.getLast? == some .rb then r.dropLast else arg
  | _ => arg

/-- The arguments after the first fixed piece: each runs up to the next piece; the
last piece ends the formula. -/
def splitRest : Nat → List (List MTok) → List MTok → List (List MTok) → Option (List (List MTok))
  | 0, _, _, _ => none
  | _ + 1, [], rest, acc => if rest.isEmpty then some acc.reverse else none
  | _ + 1, [last], rest, acc =>
    if rest.length ≤ last.length then none else
    let arg := rest.take (rest.length - last.length)
    if rest.drop arg.length != last then none else some (unbrace arg :: acc).reverse
  | f + 1, s :: ss, rest, acc =>
    match splitAt s (rest.length + 1) rest [] with
    | some (arg, r) => if arg.isEmpty then none else splitRest f ss r (unbrace arg :: acc)
    | none => none

/-- The arguments of a formula with fixed pieces `segs` (`$C^v$` against `$C^{m+4}$`). -/
def splitSegs (segs : List (List MTok)) (u : List MTok) : Option (List (List MTok)) :=
  match segs with
  | [] => none
  | s0 :: more =>
    if u.take s0.length != s0 then none else splitRest (more.length + 1) more (u.drop s0.length) []

/-- The variables of a phrase, in order, as formulas of the sentence. -/
def matchSlots : Phrase → List Chunk → List (List MTok) → Option (List (List MTok))
  | [], [], acc => some acc.reverse
  | .w w :: ps, .w v :: cs, acc => if v == w then matchSlots ps cs acc else none
  | .m t :: ps, .m u :: cs, acc => if t == u then matchSlots ps cs acc else none
  | .f segs :: ps, .m u :: cs, acc => do
    let args ← splitSegs segs u
    matchSlots ps cs (args.reverse ++ acc)
  | .v :: ps, .m u :: cs, acc => matchSlots ps cs (u :: acc)
  | _, _, _ => none

def tokTex : Tok → Codes
  | .cmd n => [92] ++ n
  | .mvar c | .msym c | .csym c => [c]
  | .mnum n => (toString n).toList.map Char.toNat
  | .lbrace => [123]
  | .rbrace => [125]
  | _ => []

/-- TeX text of formula tokens (a font command's single argument in braces). -/
def texOf : Nat → List Tok → Codes
  | 0, _ => []
  | _ + 1, [] => []
  | f + 1, .cmd n :: t :: ts =>
    if Math.wFonts.contains n && t != .lbrace then
      [92] ++ n ++ [123] ++ tokTex t ++ [125] ++ texOf f ts
    else
      let sp : Codes := match t with | .mvar _ => [32] | _ => []
      [92] ++ n ++ sp ++ texOf f (t :: ts)
  | f + 1, t :: ts =>
    tokTex t ++ texOf f ts

/-- The symbol of a notation: its text up to its first argument, when that starts
with a command (`\mathrm{Poi}`, `\delta`, `\mathcal{P}`). -/
def symbolOf (pat : List TItem) : Option Codes :=
  let pre := pat.takeWhile fun it => match it with | .fixed _ => true | _ => false
  let toks : List Tok := pre.filterMap fun it => match it with | .fixed t => some t | _ => none
  let toks := (toks.reverse.dropWhile fun t => t == .msym 95 || t == .msym 94 || t == .msym 40).reverse
  match toks with
  | .cmd _ :: _ =>
    let tx := texOf (toks.length + 1) toks
    if tx.length ≤ 1 then none else some (tx.drop 1)
  | _ => none

/-- The token of a variable formula `$X$` or `$\lambda$`. -/
def varTok : List MTok → Option Tok
  | [.id [c]] => some (.mvar c)
  | [.cmd n] => some (.cmd n)
  | _ => none

/-- Replace the words of the article's conventions in the text of a sentence (not
after `strictly` or `non`: `strictly increasing` keeps its meaning). -/
def rewriteWords (aliases : List (List Codes × List Tok)) : Nat → Option Tok → List PTok → List PTok
  | 0, _, ts => ts
  | _ + 1, _, [] => []
  | f + 1, prev, t :: ts =>
    let guarded := match prev with
      | some (.word w) => Grammar.lower w == w!"strictly" || Grammar.lower w == w!"non"
      | some (.punct 45) => true
      | _ => false
    let hit := if t.math || guarded then none else aliases.findSome? fun (ws, repl) =>
      let n := ws.length
      let here := (t :: ts).take n
      if here.length == n && (here.zip ws).all (fun (p, w) => match p.tok with
          | .word v => Grammar.lower v == w
          | _ => false) then some (n, repl) else none
    match hit with
    | some (n, repl) =>
      repl.map (fun r => (⟨r, t.pos, false⟩ : PTok)) ++ rewriteWords aliases f none ((t :: ts).drop n)
    | none => t :: rewriteWords aliases f (some t.tok) ts

end Notation

namespace Compile


def intervalPred (lo hi : Tm) : Tm := .lam .real .tt (Elab.interval lo hi (.loc 0))

/-- A closed constant bound (numerals and their negations). -/
def constTm : MT → Option Tm
  | .num n => some (.num n)
  | .neg (.num n) => some (.neg (.num n))
  | .frac (.num a) (.num b) => some (.div (.num a) (.num b))
  | _ => none

def isUnitSquare : Option MT → Bool
  | some (.sup (.interval (.num 0) (.num 1)) (.num 2)) => true
  | _ => false

def isUnitInterval : Option MT → Bool
  | some (.interval (.num 0) (.num 1)) => true
  | _ => false

def isPair : Option MT → Option (MT × MT)
  | some (.tuple [a, b]) => some (a, b)
  | _ => none

def wordsOf (cs : List Chunk) : List Codes := cs.filterMap fun c => match c with | .w w => some w | _ => none
def mathsOf (cs : List Chunk) : List (List MTok) := cs.filterMap fun c => match c with | .m t => some t | _ => none

def lookupWords (tbl : List (List Codes × Nat)) (ws : List Codes) : Option Nat := tbl.lookup ws

/-! ## Noun phrases

A noun phrase is read compositionally: prenominal modifiers of the vocabulary,
a head noun (a vocabulary noun, a class the article defined, or a variable with a
signature `$f:A\to B$`), at most one variable (possibly with a membership
`$C\in\CC$`), and postnominal modifiers of the vocabulary. Its meaning is the
conjunction of the predicates of its parts. Every chunk must be read. -/

/-- The name of a variable chunk: a letter or a command (`\gamma`). -/
def varName : List MTok → Option Codes
  | [.id v] => some v
  | [.cmd c] => some ([92] ++ c)
  | _ => none

/-- Match a vocabulary phrase at the start of `cs`. The variable slot matches a
variable chunk (returned) or nothing. -/
def matchPhrase : Phrase → List Chunk → Option (Option (List MTok) × List Chunk)
  | [], cs => some (none, cs)
  | .w w :: ps, .w v :: cs => if v == w then matchPhrase ps cs else none
  | .m t :: ps, .m u :: cs => if t == u then matchPhrase ps cs else none
  | .v :: ps, .m u :: cs =>
    -- a variable (with or without membership) fills the slot
    match matchPhrase ps cs with
    | some (none, r) => some (some u, r)
    | _ => matchPhrase ps (.m u :: cs)
  | .v :: ps, cs => matchPhrase ps cs
  | _, _ => none

/-- The words `ws` joined by spaces, in quotes. -/
def quoted (ws : List Codes) : Codes := [34] ++ (ws.intersperse [32]).flatten ++ [34]

/-- The fields of entries, for messages: `core`, `numbers and analysis`. -/
def fieldsText (fs : List Codes) : Codes :=
  ((fs.map fun f => if f.isEmpty then w!"core" else f).eraseDups.intersperse w!" and ").flatten

/-- The one meaning of a phrase among the vocabulary entries that match it (each
with the chunks after it): the longest matches count, and entries with the same
key (type and meaning) are one meaning. Several meanings are an error that names
their fields: the article must say which one it means. -/
def theMeaning {α β : Type} [BEq β] (key : α → β) (field : α → Codes) (cs : List Chunk)
    (cands : List (α × List Chunk)) : M (Option (α × List Chunk)) := do
  match (cands.map (·.2.length)).min? with
  | none => pure none
  | some k =>
    let best := cands.filter (·.2.length == k)
    let distinct := best.foldl (fun acc c => if acc.any (fun d => key d.1 == key c.1) then acc else acc ++ [c]) []
    match distinct with
    | [c] => pure (some c)
    | _ =>
      let ws := wordsOf (cs.take (cs.length - k))
      fail E.ambiguous (quoted ws ++ w!" has several meanings (in " ++
        fieldsText (distinct.map (field ·.1)) ++ [41])

/-- Words of a noun, matched against the article's noun table (longest first). -/
def matchWords (tbl : List (List Codes × Nat)) (cs : List Chunk) : Option (Nat × List Chunk) :=
  let ws := cs.takeWhile (fun c => match c with | .w _ => true | _ => false)
  let words := ws.filterMap (fun c => match c with | .w w => some w | _ => none)
  let rec go : Nat → Option (Nat × List Chunk)
    | 0 => none
    | k + 1 =>
      match tbl.lookup (words.take (k + 1)) with
      | some i => some (i, cs.drop (k + 1))
      | none => go k
  go words.length

def conjPreds (ty : Ty) : List Tm → Option Tm
  | [] => none
  | [p] => some p
  -- (a predicate may use the variables bound before: under the new binder they
  -- are one further out)
  | ps => some (.lam ty .tt (Elab.conjAll (ps.map fun p => Tm.app (shift 1 0 p) (.loc 0))))

/-- An endpoint of an interval domain: a numeral, or a term in the scope `sc` of
the binders before it (`g_*`, or `x` in `e\in[0,x]`). -/
def closedBound (m : MT) (sc : Scope := []) : M Tm := do
  match constTm m with
  | some t => pure t
  | none => match Elab.constMT m with
    | some t => pure t
    | none => do
      let (t, ty) ← Elab.term 100000 sc none m
      coerce t ty .real

/-- The type and predicate of a domain formula (`[0,1]`, `[-1,1]`, `\CC`). The ends
of an interval may use the binders `sc` before it; the predicate is a term in `sc`. -/
def domainOf (calculus : Bool) (d : MT) (sc : Scope := []) : M (Ty × Option Tm) := do
  if isZeroOne d && !calculus then pure (.unit, none)
  else match d with
    | .interval lo hi => do
      let l ← closedBound lo sc
      let h ← closedBound hi sc
      pure (.real, some (intervalPred (shift 1 0 l) (shift 1 0 h)))
    | .ival lo hi lopen ropen => do
      let l ← if Elab.isInfty false lo then (if lopen then pure none else fail E.unsupported)
        else some <$> closedBound lo sc
      let h ← if Elab.isInfty true hi then (if ropen then pure none else fail E.unsupported)
        else some <$> closedBound hi sc
      pure (.real, some (.lam .real .tt (Elab.rayTm (l.map (shift 1 0)) (h.map (shift 1 0)) lopen ropen (.loc 0))))
    | .tuple [lo, hi] => do
      let l ← Elab.constEnd false true lo
      let h ← Elab.constEnd true true hi
      pure (.real, some (.lam .real .tt (Elab.rayTm l h true true (.loc 0))))
    | .id n => do
      -- the real numbers
      if n == w!"\\mathbb{R}" then pure (.real, none) else
      match ← lookupGlob n, Elab.builtinConst n with
      | none, some (p, .fn .real .prop) => pure (.real, some p)
      | _, _ =>
      let (i, g) ← liftO (← lookupGlob n) E.undefined n
      match g.ty with
      | .fn a .prop => pure (a, some (.glob i))
      | _ => fail E.type n
    | _ => do
      -- any other set of real numbers: `\mathbb{R}\setminus\{0\}`, `\{x\in A : …\}`; or a
      -- class of the article with its parameter (`\mathcal M_\beta`)
      let (p, t) ← Elab.term 100000 sc none d
      match t with
      | .fn a .prop => pure (a, some p)
      | _ => fail E.unsupported

def lamWrap : List Ty → Tm → Tm
  | [], b => b
  | t :: ts, b => .lam t .tt (lamWrap ts b)

def tyWrap : List Ty → Ty → Ty
  | [], r => r
  | t :: ts, r => .fn t (tyWrap ts r)

/-- The factors of a domain of several variables: `\mathbb{R}^3` is three copies of
`\mathbb{R}`, `A\times B` is `A` and `B`; any other domain is one factor. A function
on it is curried: `f:\mathbb{R}^2\to\mathbb{R}` has type `ℝ → ℝ → ℝ`, and `f(x,y)` applies
it to `x` and then to `y`. -/
def domainsOf (calculus : Bool) (d : MT) (sc : Scope := []) : M (List (Ty × Option Tm)) := do
  match d with
  | .sup base (.num n) =>
    if 2 ≤ n && n ≤ 8 then do
      let f ← domainOf calculus base sc
      pure (List.replicate n f)
    else pure [← domainOf calculus d sc]
  | .app (.id t) [a, b] =>
    if t == w!"\\times" then pure ((← domainsOf calculus a sc) ++ (← domainsOf calculus b sc))
    else pure [← domainOf calculus d sc]
  | _ => pure [← domainOf calculus d sc]
termination_by sizeOf d

/-- A field of a signature `u:\mathbb{R}^3\times[0,1)\to\mathbb{R}^3`: its description
and its type (the component index first for a vector field), when the domain has at
least two coordinates; `\mathbb{R}^n\times I` has `n` spatial coordinates and a time. -/
def fieldSig (d c : MT) : M (Option (FieldInfo × Ty)) := do
  let groups := match d with
    | .app (.id t) [a, b] => if t == w!"\\times" then [a, b] else [d]
    | _ => [d]
  let some (sp, tm) := (match groups with
      | [a] => some (a, none)
      | [a, b] => some (a, some b)
      | _ => none) | pure none
  -- the torus `\mathbb{T}^n`: periodic functions on `ℝⁿ`
  let (sp, periodic) : MT × Bool := match sp with
    | .sup (.id t) (.num n) => if t == w!"\\mathbb{T}" then (.sup (.id w!"\\mathbb{R}") (.num n), true) else (sp, false)
    | _ => (sp, false)
  let sds ← domainsOf true sp
  let tds ← match tm with
    | some b => domainsOf true b
    | none => pure []
  if tds.length > 1 || sds.any (·.1 != .real) || tds.any (·.1 != .real) then return none
  let dim ← match c with
    | .sup (.id r) (.num m) => if r == w!"\\mathbb{R}" && 2 ≤ m then pure m else return none
    | .id r => if r == w!"\\mathbb{R}" then pure 1 else return none
    | _ => return none
  let info : FieldInfo := { dim, space := sds.length, time := tds.length == 1, doms := (sds ++ tds).map (·.2), periodic }
  if info.coords < 2 then return none
  let coordTy := tyWrap (List.replicate info.coords .real) .real
  pure (some (info, if 1 < dim then .fn .real coordTy else coordTy))

/-- The set of points of a field's domain, as a curried predicate. -/
def domainSet (i : FieldInfo) : Tm :=
  let k := i.coords
  let body := Elab.conjAll ((i.doms.zip (List.range k)).filterMap fun (d, j) => d.map fun p => Tm.app p (.loc (k - 1 - j)))
  (List.range k).foldl (fun acc _ => Tm.lam .real .tt acc) body

/-- A component `c` of a periodic field has period 1 in each spatial coordinate. -/
def periodicTm (i : FieldInfo) (c : Tm) : Tm :=
  let k := i.coords
  let args := (List.range k).map fun l => Tm.loc (k - 1 - l)
  let moved (j : Nat) := (List.range k).map fun l => if l == j then Tm.add (.loc (k - 1 - l)) (.num 1) else .loc (k - 1 - l)
  let eqs := (List.range i.space).map fun j => Tm.eq (applyN (shift k 0 c) (moved j)) (applyN (shift k 0 c) args)
  (List.range k).foldl (fun acc _ => Tm.all .real acc) (Elab.conjAll eqs)

/-- A component `c` of a periodic field vanishes outside a compact time interval
inside `(0,∞)`: there are `0 < a ≤ b` with `c = 0` at every time outside `[a,b]`. -/
def timeSupportTm (i : FieldInfo) (c : Tm) : Tm :=
  let k := i.coords
  let args := (List.range k).map fun l => Tm.loc (k - 1 - l)
  -- under `a`, `b` and the `k` coordinates (the time last)
  let outside := Tm.or (.lt (.loc 0) (.loc (k + 1))) (.lt (.loc k) (.loc 0))
  let body := (List.range k).foldl (fun acc _ => Tm.all .real acc)
    (.imp outside (.eq (applyN (shift (k + 2) 0 c) args) (.num 0)))
  .ex .real (.ex .real (Elab.conjAll [.lt (.num 0) (.loc 1), .le (.loc 1) (.loc 0), body]))

/-- The components of a field (the bound variable `.loc 0`), as functions of the
coordinates. -/
def fieldComps (i : FieldInfo) (F : Tm) : List Tm :=
  if 1 < i.dim then (List.range i.dim).map fun c => Tm.app F (.num (c + 1)) else [F]

/-- A function space `C^\infty(D;\mathbb{R}^m)`, `C_c^\infty(D;\mathbb{R}^m)`, `C^\infty(D)`:
its domain, codomain and whether its functions have compact support in `D`. -/
def funSpace (ts : List MTok) : Option (MT × MT × Bool) := do
  let r ← match ts with | .id [67] :: r => some r | _ => none
  let (compact, r) := match r with
    | .sym 95 :: .id [99] :: r' => (true, r')
    | .sym 95 :: .lb :: .id [99] :: .rb :: r' => (true, r')
    | _ => (false, r)
  let r ← match r with
    | .sym 94 :: .cmd i :: r' => if i == w!"infty" then some r' else none
    | .sym 94 :: .lb :: .cmd i :: .rb :: r' => if i == w!"infty" then some r' else none
    | _ => none
  let inner ← match r with
    | .sym 40 :: r' => if r'.getLast? == some (.sym 41) then some r'.dropLast else none
    | _ => none
  let (dts, cts) := match inner.findIdx? (· == .sym 59) with
    | some j => (inner.take j, inner.drop (j + 1))
    | none => (inner, [MTok.id w!"\\mathbb{R}"])
  some (← Math.parseFormula dts, ← Math.parseFormula cts, compact)

/-- The binders of a noun phrase about fields and sets of points (`a force
$f\in C_c^\infty(\mathbb{R}^3\times(0,\infty);\mathbb{R}^3)$`, `a compact set
$K\subset\mathbb{R}^3$`, `smooth velocity and pressure fields $u,p$ on $D$`), which it
registers as fields; `none` for any other noun phrase. -/
def pdeNoun (np : List Chunk) : M (Option (List BindInfo)) := do
  let np := (kw [w!"a"] np <|> kw [w!"an"] np).getD np
  let ws := np.takeWhile fun c => match c with | .w _ | .p 45 => true | _ => false
  let words := ws.filterMap fun c => match c with | .w w => some (Grammar.lower w) | _ => none
  let rest := np.drop ws.length
  let smooth := words.head? == some w!"smooth"
  let words := if smooth then words.drop 1 else words
  let register (n : Codes) (i : FieldInfo) : M Unit :=
    modify fun st => { st with fields := (n, i) :: st.fields }
  -- the predicate `smooth on the domain` of each component (of the variable `.loc 0`)
  let smoothPred (i : FieldInfo) (ty : Ty) (compactSupp : Bool) (smooth : Bool := true) : Tm :=
    let S := domainSet i
    let ps := (fieldComps i (.loc 0)).flatMap fun c =>
      (if smooth then [Tm.app (.app (.prim (.smoothN i.coords)) c) (shift 1 0 S)] else []) ++
      (if i.periodic then [periodicTm i c] else []) ++
      (if compactSupp then
        -- on a torus, compact support is in time
        (if i.periodic then (if i.time then [timeSupportTm i c] else [])
         else [Tm.app (.app (.prim (.compactSuppIn i.coords)) c) (shift 1 0 S)])
       else [])
    .lam ty .tt (Elab.conjAll ps)
  match rest with
  -- `NOUN $f\in C_c^\infty(D;\mathbb{R}^m)$`
  | [.m ts] =>
    match ts.findIdx? (· == .cmd w!"in"), ts.findIdx? (fun t => t == .cmd w!"subset" || t == .cmd w!"subseteq") with
    | some j, _ =>
      let some v := (match ts.take j with | [.id v] => some v | _ => none) | pure none
      let some (d, cod, compact) := funSpace (ts.drop (j + 1)) | pure none
      let labels := [w!"force", w!"function", w!"map", w!"field", w!"vector", w!"velocity"]
      if !words.all labels.contains then return none
      match ← fieldSig d cod with
      | some (i, ty) => do
        register v i
        pure (some [⟨v, ty, some (smoothPred i ty compact)⟩])
      | none => pure none
    -- `[compact] set $K\subset\mathbb{R}^n$`, `… $K\subset(-1/2,1/2)^3$` (in a box)
    | none, some j =>
      let some v := (match ts.take j with | [.id v] => some v | _ => none) | pure none
      let some dm := Math.parseFormula (ts.drop (j + 1)) | pure none
      let some (n, side) ← (match dm with
          | .sup (.id r) (.num n) =>
            if r == w!"\\mathbb{R}" then pure (some (n, none)) else pure none
          | .sup s (.num n) =>
            tryCatch (do
              let (ty, p) ← domainOf true s
              pure (if ty == .real then some (n, p) else none)) fun _ => pure none
          | _ => pure none) | pure none
      if n < 1 || 8 < n then return none
      let compact := words == [w!"compact", w!"set"] || words == [w!"compact", w!"subset"]
      if !(compact || words == [w!"set"] || words == [w!"subset"]) then return none
      let ty := Ty.setN n
      -- `K ⊆ Sⁿ`: under the set and its `n` points
      let inBox : List Tm := match side with
        | some p =>
          let xs := (List.range n).map fun l => Tm.loc (n - 1 - l)
          [(List.range n).foldl (fun acc _ => Tm.all .real acc)
            (.imp (applyN (.loc n) xs) (Elab.conjAll (xs.map fun x => Tm.app (shift (n + 1) 0 p) x)))]
        | none => []
      let conds := (if compact then [Tm.app (.prim (.isCompactN n)) (.loc 0)] else []) ++ inBox
      pure (some [⟨v, ty, if conds.isEmpty then none else some (.lam ty .tt (Elab.conjAll conds))⟩])
    | none, none => pure none
  -- `[smooth] velocity and pressure fields $u,p$ on $D$`, `a [smooth] vector field $u$ on $D$`
  | [.m vs, .w on, .m dts] =>
    if Grammar.lower on != w!"on" then return none
    -- the names, separated by commas: letters, or letters with a subscript (`P_{\mathrm{per}}`)
    let parts := (Grammar.topCommas (vs.length + 1) 0 [] vs []).filter (!·.isEmpty)
    let some names := parts.mapM (fun p => (Math.parseFormula p).bind Elab.symKey) | pure none
    let some d := Math.parseFormula dts | pure none
    -- the kinds: `velocity`, `vector`, `force` (vector fields), `pressure`, `scalar` (real)
    let some last := words.getLast? | pure none
    if !(last == w!"field" || last == w!"fields") then return none
    let kinds := (words.dropLast).filter (· != w!"and")
    let vectorKind (k : Codes) : Option Bool :=
      if k == w!"velocity" || k == w!"vector" || k == w!"force" then some true
      else if k == w!"pressure" || k == w!"scalar" then some false else none
    let some kinds := kinds.mapM vectorKind | pure none
    let kinds := if kinds.length == 1 then List.replicate names.length (kinds.getD 0 false) else kinds
    if kinds.length != names.length then return none
    let mut out : List BindInfo := []
    for (n, vec) in names.zip kinds do
      -- the codomain: `\mathbb{R}^n` for a vector field on `n`-dimensional space
      let spD := match d with
        | .app (.id t) [a, _] => if t == w!"\\times" then a else d
        | _ => d
      -- (the torus `\mathbb{T}^n` has `n` coordinates)
      let sp ← match spD with
        | .sup (.id t) (.num n) => if t == w!"\\mathbb{T}" then pure (List.replicate n (Ty.real, (none : Option Tm))) else domainsOf true spD
        | _ => domainsOf true spD
      let cod : MT := if vec then .sup (.id w!"\\mathbb{R}") (.num sp.length) else .id w!"\\mathbb{R}"
      let some (i, ty) ← fieldSig d cod | return none
      register n i
      out := out ++ [⟨n, ty, if smooth || i.periodic then some (smoothPred i ty false smooth) else none⟩]
    pure (some out)
  | _ => pure none

/-- A variable chunk: its name, and the domain of a membership `$x\in A$`. -/
def varChunk (ts : List MTok) : M (Codes × Option (Ty × Option Tm)) := do
  match varName ts with
  | some v => pure (v, none)
  | none =>
    match Grammar.binderMath ts with
    | some ([v], dom) => do pure (v, some (← domainOf false dom))
    | _ => fail E.unsupported

/-- `$φ$ [and $ψ$]`: the conditions after `with` in a noun phrase. -/
def condsOf : Nat → List Chunk → List MT → List MT × List Chunk
  | 0, cs, acc => (acc.reverse, cs)
  | f + 1, cs, acc =>
    match Grammar.formula cs with
    | some (m, r) =>
      match r with
      | .w w :: r' => if w == w!"and" then condsOf f r' (m :: acc) else ((m :: acc).reverse, r)
      | _ => ((m :: acc).reverse, r)
    | none => (acc.reverse, cs)

/-- Read a noun phrase (without its determiner). -/
def nounPhrase (np : List Chunk) (outer : Scope := []) : M BindInfo := do
  -- `every $x\in[0,1]$` in a list of binders (`for every positive integer $n$ and every
  -- $x\in[0,1]$`): a variable and its domain
  match np with
  | [.m ts] =>
    match Grammar.binderMath ts with
    | some ([v], d) => do
      let (ty, p) ← domainOf false d outer
      return ⟨v, ty, p⟩
    | _ => pure ()
  | _ => pure ()
  let st ← get
  let V := st.vocab
  -- prenominal modifiers
  -- (each is the list of the vocabulary's modifiers with those words: the noun's type
  -- decides between them)
  let rec pre : Nat → List Chunk → List (List Chunk × List Modifier) → List (List Chunk × List Modifier) × List Chunk
    | 0, cs, acc => (acc.reverse, cs)
    | f + 1, cs, acc =>
      let cands := V.mods.filterMap (fun m => if m.prenominal then
          (matchPhrase m.phrase cs).bind fun (v, r) => if v.isNone then some (m, r) else none
        else none)
      match (cands.map (·.2.length)).min? with
      | some k => pre f (cs.drop (cs.length - k)) ((cs, (cands.filter (·.2.length == k)).map (·.1)) :: acc)
      | none => (acc.reverse, cs)
  let (pmGroups, r0) := pre 4 np []
  -- notions of the article before the noun (`an LTD copula $C$`)
  let rec matchName : List Codes → List Chunk → Option (List Chunk)
    | [], cs => some cs
    | w :: ws, .w v :: cs => if v == w then matchName ws cs else none
    | w :: ws, .p 45 :: cs => if w == w!"-" then matchName ws cs else none
    | _, _ => none
  let rec preN : Nat → List Chunk → List Nat → List Nat × List Chunk
    | 0, cs, acc => (acc.reverse, cs)
    | f + 1, cs, acc =>
      match st.notions.findSome? (fun (ph, i) => (matchName ph cs).map (i, ·)) with
      | some (i, r) => preN f r (i :: acc)
      | none => (acc.reverse, cs)
  let (nms, r0) := preN 4 r0 []
  -- the head: an article class, a vocabulary noun, or a variable with a signature
  -- (the article's own classes take precedence over the vocabulary's nouns)
  let head : M (Ty × List Tm × Option (List MTok) × List Chunk) := do
    match matchWords st.nouns r0 with
    | some (i, r) => do
      let gty : Option Ty := (st.globs[i]?).map (·.ty)
      let a ← match gty with
        | some (.fn a .prop) => pure a
        | _ => fail E.type
      match r with
      | .m ts :: r' =>
        if (Math.parseSig ts).isSome then fail E.unsupported else pure (a, [.glob i], some ts, r')
      | _ => pure (a, [.glob i], none, r)
    | none =>
      let cands := V.nouns.filterMap (fun n =>
          ((matchPhrase n.sing r0) <|> (matchPhrase n.plural r0)).map fun (v, r) => ((n, v), r))
      match ← theMeaning (fun (nv : Noun × Option (List MTok)) => (nv.1.ty, nv.1.pred, nv.2))
          (·.1.field) r0 cands with
      | some ((n, v), r) =>
        match v, r with
        -- `a copula $C$`: the variable follows a noun without a slot
        | none, .m ts :: r' =>
          let single := match ts with | [.id _] | [.cmd _] => true | _ => false
          if (Math.parseSig ts).isSome || (!(n.sing.all fun p => p != .v) && !r'.isEmpty && !single) then pure (n.ty, [n.pred], v, r)
          else pure (n.ty, [n.pred], some ts, r')
        | _, _ => pure (n.ty, [n.pred], v, r)
      | none =>
        -- `$f:A\to B$`, optionally after the noun `map` or `function`
        let r1 := match r0 with
          | .w w :: r => if w == w!"map" || w == w!"function" || w == w!"maps" || w == w!"functions" then r else r0
          | _ => r0
        match r1 with
        | .m ts :: r => do
          let sg ← liftO (Math.parseSig ts) E.noun ((wordsOf np).flatten)
          match sg with
          | .sig (.id f) d c => do
            -- a field (`u:\mathbb{R}^3\times[0,1)\to\mathbb{R}^3`)
            match ← fieldSig d c with
            | some (info, ty) =>
              modify fun st => { st with fields := (f, info) :: st.fields }
              pure (ty, [], some [.id f], r)
            | none =>
            let ds ← domainsOf false d
            let (ct, cp) ← domainOf false c
            if ds.any (·.2.isSome) || cp.isSome then fail E.unsupported
            pure (tyWrap (ds.map (·.1)) ct, [], some [.id f], r)
          | _ => fail E.unsupported
        | _ => fail E.noun (((wordsOf np).intersperse [32]).flatten)
  let (ty, preds, var, r1) ← head
  let pms ← pmGroups.mapM fun (cs, ms) => do
    let ms := ms.filter (·.ty == ty)
    if ms.isEmpty then fail E.type
    match ← theMeaning (fun (m : Modifier) => m.pred) (·.field) cs (ms.map (·, [])) with
    | some (m, _) => pure m
    | none => fail E.type
  let notionPreds ← nms.mapM fun i => do
    let some g := st.globs[i]? | fail E.type
    match g.ty with
    | .fn a .prop =>
      if a != ty then fail E.type
      -- the notion is a predicate on its domain (copulas), which the noun phrase
      -- states first
      else pure (Tm.glob i)
    | _ => fail E.type
  -- postnominal modifiers
  let rec post : Nat → List Chunk → List Tm → M (List Tm × List Chunk)
    | 0, cs, acc => pure (acc.reverse, cs)
    | f + 1, cs, acc => do
      let cands := V.mods.filterMap (fun m => if !m.prenominal && m.ty == ty then
          (matchPhrase m.phrase cs).bind fun (v, r) => if v.isNone then some (m, r) else none
        else none)
      match ← theMeaning (fun (m : Modifier) => m.pred) (·.field) cs cands with
      | some (m, r) => post f r (m.pred :: acc)
      | none => pure (acc.reverse, cs)
  let (qms, r2) ← post 4 r1 []
  -- `a copula $C$ with $\rho(C)=0$ [and $\beta(C)=0$]`: conditions on the variable
  let (conds, r2) := match r2 with
    | .w w :: r => if w == w!"with" then condsOf 4 r [] else ([], r2)
    | _ => ([], r2)
  if !r2.isEmpty then fail E.noun (((wordsOf np).intersperse [32]).flatten)
  let (name, member) ← match var with
    | some ts => do let (v, d) ← varChunk ts; pure (v, d)
    | none => pure ([], none)
  let memberPred ← match member with
    | some (t, p) => if t == ty then pure p.toList else fail E.type
    | none => pure []
  if !conds.isEmpty && name.isEmpty then fail E.unsupported
  -- (a condition may use the variables bound before: `let $\varphi$ be … with
  -- $N\varphi=F$`; inside the predicate they are one binder further out)
  let condPreds ← conds.mapM fun φ => do
    let (p, pty) ← Elab.term 100000 ([(name, ty)] ++ (if outer.isEmpty then [] else [([], ty)]) ++ outer) none φ
    if pty != .prop then fail E.type
    pure (Tm.lam ty .tt p)
  let all := (preds ++ pms.map (·.pred) ++ qms ++ memberPred ++ notionPreds ++ condPreds).eraseDups
  pure ⟨name, ty, conjPreds ty all⟩

/-- Free identifiers of a formula (for `On I,`). -/
def freeIds : Nat → List Codes → MT → List Codes
  | 0, _, _ => []
  | f + 1, bound, m =>
    match m with
    | .id n => if bound.contains n || n == [42] then [] else [n]
    | .num _ => []
    -- the base of `e_b` is a symbol, not a variable
    | .sub (.id _) i => freeIds f bound i
    | .sub b i => freeIds f bound b ++ freeIds f bound i
    | .sup b e => freeIds f bound b ++ freeIds f bound e
    | .hat x | .neg x | .abs x => freeIds f bound x
    | .app h as => freeIds f bound h ++ (as.flatMap (freeIds f bound))
    | .add x y | .minus x y | .mul x y | .div x y | .frac x y => freeIds f bound x ++ freeIds f bound y
    | .minm xs | .maxm xs | .tuple xs | .conj xs => xs.flatMap (freeIds f bound)
    | .int _ _ b v => freeIds f (v :: bound) b
    | .interval a b => freeIds f bound a ++ freeIds f bound b
    | .chain x rs => freeIds f bound x ++ rs.flatMap (fun r => freeIds f bound r.2)
    | .mapsto p b => freeIds f (freeIds f [] p ++ bound) b
    | _ => []

/-- A domain of multi-indices `\mathbb{N}_0^n` (`n ≥ 2`): the domain of the components and
`n`. -/
def multiIndex (d : MT) : Option (MT × Nat) :=
  match d with
  | .sup base (.num n) =>
    let nat := match base with
      | .id b => b == w!"\\mathbb{N}" || b == w!"\\mathbb{N}_0"
      | .sub (.id b) (.num 0) => b == w!"\\mathbb{N}"
      | _ => false
    if nat && 2 ≤ n && n ≤ 8 then some (base, n) else none
  -- `\mathbb{N}_0^n`, with both scripts on `\mathbb{N}`
  | .sub (.id b) (.sup (.num 0) (.num n)) =>
    if b == w!"\\mathbb{N}" && 2 ≤ n && n ≤ 8 then some (.sub (.id b) (.num 0), n) else none
  | _ => none

def binderInfos : Bind → M (List BindInfo)
  | .every vs d => do
    -- a multi-index `I\in\mathbb{N}_0^n`: its components `I_1`, …, `I_n`
    match vs, multiIndex d with
    | [v], some (base, n) => do
      let (ty, p) ← domainOf false base
      pure ((List.range n).map fun k => ⟨v ++ [95] ++ (Nat.toDigits 10 (k + 1)).map Char.toNat, ty, p⟩)
    | _, _ => do
    let (ty, p) ← domainOf false d
    pure (vs.map fun v => ⟨v, ty, p⟩)
  | .noun np => do pure [← nounPhrase np]
  | .on _ => pure []
  | .ifCond φ => do
    -- the free variables of φ range over ℝ; φ is the domain of the last one
    let st ← get
    let free := ((freeIds 64 [] φ).filter fun n => !(st.globs.any fun g => g.key == n && !g.family)).eraseDups
    match free.reverse with
    | [] => fail E.unsupported
    | last :: _ =>
      let sc : Scope := free.reverse.map (·, Ty.real)
      let (p, pty) ← Elab.term 100000 sc none φ
      if pty != .prop then fail E.type
      -- the predicate is applied to the last variable where all of them are bound,
      -- so `φ` is shifted past its own (unused) argument
      pure (free.map fun v => (⟨v, .real, if v == last then some (.lam .real .tt (shift 1 0 p)) else none⟩ : BindInfo))
  | .many bs => do
    let mut out : List BindInfo := []
    for b in bs do
      match b with
      | .every vs d => out := out ++ (← everyAfter out vs d)
      -- `For every $x\in A$ with $φ$`: a condition on the variables bound before it,
      -- part of the domain of the last one
      | .ifCond φ => do
        let some last := out.getLast? | fail E.unsupported
        let sc : Scope := (out.map fun b => (b.name, b.ty)).reverse
        let (p, pty) ← Elab.term 100000 sc none φ
        if pty != .prop then fail E.type
        let pred := match last.pred with
          | some q => Tm.lam last.ty .tt (.and (.app (shift 1 0 q) (.loc 0)) (shift 1 0 p))
          | none => Tm.lam last.ty .tt (shift 1 0 p)
        out := out.dropLast ++ [{ last with pred := some pred }]
      -- `For every positive integer $n$ and every $x\in[0,1]$`: a noun phrase, whose
      -- condition may use the variables bound before it
      | .noun np => do
        let b ← nounPhrase np (out.map fun b => (b.name, b.ty)).reverse
        out := out ++ [b]
      | _ => fail E.unsupported
    pure out
where
  /-- `Let $x\in(0,1]$ and $e\in[0,x]$`: a domain may use the variables bound
  before it; its predicate is applied where they and the variable are bound. -/
  everyAfter (before : List BindInfo) (vs : List Codes) (d : MT) : M (List BindInfo) :=
    everyIn (before.map fun b => (b.name, b.ty)).reverse vs d
  /-- The same, with the domain in the scope `sc` of the binders around it. -/
  everyIn (sc : Scope) (vs : List Codes) (d : MT) : M (List BindInfo) := do
    -- a multi-index: its components
    let (vs, d) := match vs, multiIndex d with
      | [v], some (base, n) => ((List.range n).map fun k => v ++ [95] ++ (Nat.toDigits 10 (k + 1)).map Char.toNat, base)
      | _, _ => (vs, d)
    let (ty, p) ← domainOf false d sc
    let (bis, _) := vs.foldl (fun (acc, j) v =>
      (acc ++ [(⟨v, ty, p.map (shift (j + 1) 0)⟩ : BindInfo)], j + 1)) (([] : List BindInfo), 0)
    pure bis

/-- The binders among `bs` whose variables are `used`, in their order. A used binder
whose domain uses the binders before it (`e\in[0,x]`) keeps them all. -/
def usedBinders (bs : List BindInfo) (used : List Codes) : List BindInfo :=
  let dependent (b : BindInfo) : Bool := b.pred.any fun p => shift 1 0 p != p
  let lastDep := ((bs.zipIdx.filter fun (b, _) => used.contains b.name && dependent b).map (·.2)).getLast?
  (bs.zipIdx.filter fun (b, i) => used.contains b.name || lastDep.any (i ≤ ·)).map (·.1)

/-- The variables of a list of binders, each domain in the scope of the variables
before it (`For $x\in(0,1]$ and $e\in[0,x]$`). -/
def bindersInfos (binds : List Bind) (before : List BindInfo := []) : M (List BindInfo) := do
  let mut out : List BindInfo := []
  for b in binds do
    match b with
    | .every vs d => out := out ++ (← binderInfos.everyAfter (before ++ out) vs d)
    | .noun np => out := out ++ [← nounPhrase np ((before ++ out).map fun b => (b.name, b.ty)).reverse]
    | b => out := out ++ (← binderInfos b)
  pure out

def scopeOf (bs : List BindInfo) : Scope := (bs.map fun b => (b.name, b.ty)).reverse

def wrap (bs : List BindInfo) (body : Tm) : Tm :=
  forallBinders (bs.map fun b => (b.name, b.ty, b.pred.map fun p => Tm.app p (.loc 0))) body

/-- The implicit parameters of the definitions named among `ids` (visible here). -/
def implicitVars (st : St) (ids : List Codes) : List Codes :=
  ids.flatMap fun n =>
    let rec find : Nat → List Glob → Option Nat
      | _, [] => none
      | i, g :: gs => match find (i + 1) gs with
        | some j => some j
        | none => if g.key == n && Elab.visibleIn st i then some i else none
    match find 0 st.globs with
    | some i => (st.implicits.lookup i).getD []
    | none => []

mutual
def clauseMaths : Clause → List MT
  | .fact f | .holds f => [f]
  | .deriv d _ c => [d, c]
  | .scoped f _ _ e => f :: e.toList
  | .everyNP _ b _ => [b]
  | .extremumOf _ v f _ a _ => v :: f.toList ++ a.toList
  | .increasing ms => ms
  | .ranges _ b => [b]
  | .extremaOver items f _ _ cond => items.map (·.2) ++ [f, cond]
  | .increases f a b => [f, a, b]
  | .sends m f g => [m, f, g]
  | .every _ d b => [d, b]
  | .equalityOn s => [s]
  | .equalityWhen φ => [φ]
  | .ifThen c cl => c :: clauseMaths cl
  | .adjectives s adjs => s :: adjs.filterMap (·.2)
  | .notions s _ _ => [s]
  | .isA s np _ => s :: (mathsOf np).filterMap Math.parseFormula
  | .thereIs _ c => clauseMaths c
  | .forEveryNP c np => clauseMaths c ++ (mathsOf np).filterMap Math.parseFormula
  | .existsNP np _ (some c) => clauseMaths c ++ (mathsOf np).filterMap Math.parseFormula
  | .existsNP np _ none => (mathsOf np).filterMap Math.parseFormula
  | .existsNPs nps cs => clauseMathsAll cs ++ (nps.flatMap mathsOf).filterMap Math.parseFormula
  | .noneExist c => clauseMaths c
  | .iff p q => [p, q]
  | .compare l _ r => [l, r]
  | _ => []

/-- The formulas of several clauses (structural, so that the kernel evaluates it). -/
def clauseMathsAll : List Clause → List MT
  | [] => []
  | c :: cs => clauseMaths c ++ clauseMathsAll cs
end

/-- The subformulas of a formula. -/
def mtChildren : MT → List MT
  | .sub b i | .sup b i => [b, i]
  | .hat x | .neg x | .abs x | .lnot x => [x]
  | .app f as => f :: as
  | .add x y | .minus x y | .mul x y | .div x y | .frac x y | .equiv x y
  | .land x y | .lor x y | .limp x y | .liff x y => [x, y]
  | .minm xs | .maxm xs | .tuple xs | .conj xs | .finset xs => xs
  | .int lo hi b _ => [lo, hi, b]
  | .interval a b | .ival a b _ _ => [a, b]
  | .setOf p d cs => p :: d :: cs
  | .setCond p cs => p :: cs
  | .image e _ d => [e, d]
  | .mapsto p b => [p, b]
  | .chain x rs => x :: rs.map (·.2)
  | .cases rows => rows.flatMap fun (a, b) => [a, b]
  | .sig n d c => [n, d, c]
  | .extr _ s | .bound _ s => [s]
  | .bigop _ _ lo hi b => [lo, hi, b]
  | .quant _ _ d b => [d, b]
  | .limit _ t b => [t, b]
  | _ => []

/-- The generic constants of a formula (`C`, `C_m`, `C_{j,I}`): their names and the
variables of their indices. -/
def genericsOf (bases : List Codes) : Nat → MT → List (Codes × List Codes)
  | 0, _ => []
  | f + 1, m =>
    match m with
    | .id k => if bases.contains k then [(k, [])] else []
    | .sub (.id k) i =>
      if bases.contains k then
        match symKey m with
        | some key => [(key, freeIds 64 [] i)]
        | none => []
      else genericsOf bases f i
    | _ => (mtChildren m).flatMap (genericsOf bases f)

/-- Binders, each universal or (`true`) existential with its domain as a conjunct. -/
def wrapMixed : List (BindInfo × Bool) → Tm → Tm
  | [], body => body
  | (b, isEx) :: bs, body =>
    let inner := wrapMixed bs body
    let p := b.pred.map fun p => Tm.app p (.loc 0)
    if isEx || b.name.head? == some 64 then .ex b.ty (match p with | some p => .and p inner | none => inner)
    else .all b.ty (match p with | some p => .imp p inner | none => inner)

/-- What a generic constant of a claim may depend on: the variables (its indices and the
dependencies its convention lists), whether the fixed data, the variables it must not
depend on, and whether its convention lists its dependencies. -/
structure GenSpec where
  allowed : List Codes
  fixedOk : Bool
  uniform : List Codes
  strict : Bool

/-- The binders with the generic constants: the binders a constant may depend on first
(its indices, the variables its convention names, the fixed data), each constant right
after the last of them, then the other binders, which it does not depend on. Where moving a
binder would change what a domain refers to, the binders keep their order and each
constant comes right after the last binder it may depend on; `none` if a constant would
then depend on a variable its convention excludes. -/
def placeGenerics (gens : List (BindInfo × GenSpec)) (bs : List BindInfo) (fixedNames : List Codes) :
    Option (List (BindInfo × Bool)) :=
  -- (a multi-index `I` stands for its components `I_1`, …)
  let component (a n : Codes) : Bool :=
    n.take (a.length + 1) == a ++ [95] && !(n.drop (a.length + 1)).isEmpty &&
      (n.drop (a.length + 1)).all fun c => 48 ≤ c && c ≤ 57
  let allows (s : GenSpec) (b : BindInfo) : Bool :=
    s.allowed.contains b.name || s.allowed.any (component · b.name) || (s.fixedOk && fixedNames.contains b.name)
  let isFront (b : BindInfo) : Bool := gens.any fun (_, s) => allows s b
  let dependent (b : BindInfo) : Bool := b.pred.any fun p => shift 1 0 p != p
  let firstRest := (List.range bs.length).find? fun i => !isFront bs[i]!
  -- a front binder after a rest binder, followed by a dependent rest binder
  let risky := (List.range bs.length).any fun i =>
    isFront bs[i]! && firstRest.any (· < i) &&
      ((List.range bs.length).any fun j => i < j && !isFront bs[j]! && dependent bs[j]!)
  let ordered := if !risky && !(bs.filter isFront).any dependent then
      bs.filter isFront ++ bs.filter fun b => !isFront b
    else bs
  let lastIdx (s : GenSpec) : Option Nat :=
    (List.range ordered.length).foldl (fun acc i => if allows s ordered[i]! then some i else acc) none
  let order := ((gens.filter fun (_, s) => (lastIdx s).isNone).map fun (g, _) => (g, true)) ++
    (List.range ordered.length).flatMap fun i =>
      (ordered[i]!, false) :: ((gens.filter fun (_, s) => lastIdx s == some i).map fun (g, _) => (g, true))
  -- each constant depends only on what it may depend on
  let ok := gens.all fun (g, s) =>
    match order.findIdx? (fun (b, ex) => ex && b.name == g.name) with
    | some p => (order.take p).all fun (b, ex) =>
        ex || allows s b || (!s.strict && !s.uniform.contains b.name)
    | none => true
  if ok then some order else none

/-- The two sides `(smaller, larger)` of a single inequality. -/
def ineqSides : MT → Option (MT × MT)
  | .chain a [(r, b)] =>
    if r == .le || r == .lt then some (a, b)
    else if r == .ge || r == .gt then some (b, a)
    else none
  | _ => none

/-- The inequalities a claim about every element of a domain asserts: the formula, both
sides of `φ, equivalently ψ`, or the parts of a list. -/
def boundsOf : MT → List MT
  | .equiv x y => [x, y].filter (ineqSides · |>.isSome)
  | .conj xs => xs.filter (ineqSides · |>.isSome)
  | m => if (ineqSides m).isSome then [m] else []

/-- Does the clause speak about the latest inequality (`equality holds …`)? -/
def usesIneq : Clause → Bool
  | .equalityOn _ | .equalityWhen _ => true
  | .ifThen _ cl => usesIneq cl
  | _ => false

/-- The free variables of the latest inequality that a clause refers to. -/
def ineqFree (st : St) (cl : Clause) : List Codes :=
  if usesIneq cl then
    match st.lastIneq with
    | some (bs, m) => freeIds 64 (bs.map (·.name)) m
    | none => []
  else []

/-- The free variables of a clause, its trailing definitions and the implicit
parameters of the definitions it uses (for the binders it inherits). -/
def clauseFree (st : St) (bound : List Codes) (cl : CClause) : List Codes :=
  let ids := (clauseMaths cl.clause ++ cl.defs).flatMap (freeIds 64 bound)
  ids ++ implicitVars st ids ++ ineqFree st cl.clause

/-- A piecewise formula that no piece covers is `0` there (for integrands). -/
def zeroElsewhere : Tm → Tm
  | .cases c v rest => .cases c v (zeroElsewhere rest)
  | .undef .real => .num 0
  | t => t

/-- The single inequality of a chain, for `with equality only at`. -/
def inequality : MT → Option MT
  | .chain x rs =>
    let terms := x :: rs.map (·.2)
    let idx := rs.findIdx? (fun r => r.1 == .le || r.1 == .lt || r.1 == .ge || r.1 == .gt)
    match idx with
    | some k =>
      if (rs.filter (fun r => r.1 == .le || r.1 == .lt || r.1 == .ge || r.1 == .gt)).length == 1 then
        match terms[k]?, terms[k+1]? with
        | some a, some b => some (.chain a [(.eq, b)])
        | _, _ => none
      else none
    | none => none
  | _ => none

/-- Record the binders and inequalities of a claim about every element of a domain. -/
def recordBounds (bs : List BindInfo) (body : MT) : M Unit := do
  let ms := boundsOf body
  if !ms.isEmpty then modify fun st => { st with lastBounds := some (bs, ms) }
  if (inequality body).isSome then modify fun st => { st with lastIneq := some (bs, body) }

def F := 100000

def prop (sc : Scope) (pf : PF) (m : MT) : M Tm := do
  let st ← get
  -- fields with a subscript in their name, as identifiers
  let m := if st.fields.any (fun (n, _) => n.contains 95) then Elab.fieldIds st.fields 64 m else m
  let (t, ty) ← term F sc pf m
  if ty == .prop then pure t else fail E.type

/-- The domain (type, predicate) of a point-free function formula such as `\nu-\rho`. -/
def pfDomain : Nat → MT → M (Option (Ty × Option Tm))
  | 0, _ => pure none
  | f + 1, m =>
    match m with
    | .id n => do
      match ← lookupGlob n with
      | some (_, g) => match g.ty with
        | .fn a _ => pure (some (a, (g.doms.head?).join))
        | _ => pure none
      | none => pure none
    | .minus x y | .add x y | .mul x y | .div x y => do
      match ← pfDomain f x with
      | some r => pure (some r)
      | none => pfDomain f y
    | .neg x => pfDomain f x
    | _ => pure none

def holdsAt (p : Option Tm) (x : Tm) : Tm := match p with | some p => .app p x | none => .tt

/-- A map `v ↦ body` used only on the points of a domain: its definedness
condition asks for the body only there. -/
def onDomain (p : Option Tm) : Tm → Tm
  | .lam t _ b => .lam t (holdsAt p (.loc 0)) b
  | t => t

/-- Resolve a relation object: a formula, or a named object (possibly introduced here). -/
def object (sc : Scope) (ty : Ty) : Obj → M Tm
  | .math (.mapsto pat body) => do
    match ty with
    | .fn a r => do let (t, _) ← Elab.lam F sc pat [a] (some r) body; pure t
    | _ => fail E.type
  | .math m => do let (t, mty) ← term F sc none m; coerce t mty ty
  | .named name none => do
    let some i := lookupWords (← get).named name | fail E.referent name.flatten
    pure (.glob i)
  | .named name (some (.mapsto pat body)) => do
    match ty with
    | .fn a r => do
      let (t, tty) ← Elab.lam F [] pat [a] (some r) body
      let i ← addGlob ⟨[], tty, [], false⟩ t
      modify fun st => { st with named := st.named ++ [(name, i)] }
      pure (.glob i)
    | _ => fail E.type
  | _ => fail E.unsupported

def predicate (sc : Scope) (s : Tm × Ty) (phrase : List Codes) (o : Obj) : M Tm := do
  let some i := lookupWords (← get).preds phrase | fail E.noun ((phrase.intersperse [32]).flatten)
  let g := ((← get).globs[i]?).getD default
  match g.ty with
  | .fn _ (.fn b .prop) => do
    let ot ← object sc b o
    let (t, _) ← applyAll (.glob i) g.ty g.doms [s, (ot, b)]
    pure t
  | _ => fail E.type

def subjectTm (sc : Scope) : Subj → M (Tm × Ty)
  | .math m => term F sc none m
  | .its name => do
    let some (s, sty) := (← get).subject | fail E.referent
    let some i := lookupWords (← get).ops name | fail E.noun ((name.intersperse [32]).flatten)
    let g := ((← get).globs[i]?).getD default
    applyAll (.glob i) g.ty g.doms [(s, sty)]

/-- Extremum statement: bound, attainment, uniqueness. -/
def extremumTm (sc : Scope) (isMax : Bool) (fm value : MT) (s : Tm × Ty) : M (Tm × Ty × Option Tm) := do
  let some (ty, p) ← pfDomain 16 fm | fail E.unsupported
  let s' ← coerce s.1 s.2 ty
  let inner := (w!"", ty) :: sc
  let fx ← asReal (← term F inner (some (.loc 0, ty)) fm)
  let mx ← asReal (← term F inner none value)
  let bound := Tm.all ty (.imp (holdsAt p (.loc 0)) (if isMax then .le fx mx else .le mx fx))
  let fs ← asReal (← term F sc (some (s', ty)) fm)
  let ms ← asReal (← term F sc none value)
  let attained := Tm.and (holdsAt p s') (.eq fs ms)
  let unique := Tm.all ty (.imp (holdsAt p (.loc 0)) (.imp (.eq fx mx) (.eq (.loc 0) (shift 1 0 s'))))
  pure (.and bound (.and attained unique), ty, p)

def attainsOnly (sc : Scope) (ex : Extremum) (s : Tm × Ty) (withAttained : Bool) : M Tm := do
  let some (ty, p) ← pfDomain 16 ex.f | fail E.unsupported
  let s' ← coerce s.1 s.2 ty
  let inner := (w!"", ty) :: sc
  let fx ← asReal (← term F inner (some (.loc 0, ty)) ex.f)
  let mx ← asReal (← term F inner none ex.value)
  let unique := Tm.all ty (.imp (holdsAt p (.loc 0)) (.imp (.eq fx mx) (.eq (.loc 0) (shift 1 0 s'))))
  if withAttained then
    let fs ← asReal (← term F sc (some (s', ty)) ex.f)
    let ms ← asReal (← term F sc none ex.value)
    pure (.and (.and (holdsAt p s') (.eq fs ms)) unique)
  else pure unique

def findExtremum (env : Nat) (isMax : Bool) : M Extremum := do
  let st ← get
  match st.extrema.find? (fun (e, x) => e == env && x.isMax == isMax) with
  | some (_, x) => pure x
  | none => fail E.referent

structure SentCtx where
  ctx : Context
  /-- Environment index of the result a proof proves. -/
  target : Nat
  idx : Nat

def claimRole (c : SentCtx) : Role :=
  match c.ctx.kind with
  | .result _ => .statement c.ctx.env
  | .proof => .step c.ctx.env
  | .text => .text

/-- Premise claim ids for citing a label (definitions contribute none). -/
def citeClaims (l : Codes) : M (List Nat) := do
  let st ← get
  match st.labels.lookup l with
  | some cs => pure cs
  | none => if st.defLabels.contains l then pure [] else fail E.label l

def addLabels (ls : List Codes) (claims : List Nat) (isDef : Bool) : M Unit := do
  for l in ls do
    modify fun st =>
      let st := if isDef then { st with defLabels := st.defLabels ++ [l] } else st
      match st.labels.lookup l with
      | some cs => { st with labels := st.labels.map fun (k, v) => if k == l then (k, cs ++ claims) else (k, v) }
      | none => { st with labels := st.labels ++ [(l, claims)] }

/-- Record a claim of the current sentence (with premises for proof steps). -/
def emit (c : SentCtx) (body : Tm) (cites : List Codes) : M Nat := do
  let st ← get
  match c.ctx.kind with
  | .proof => do
    let cited ← cites.mapM citeClaims
    let allCites := (st.proofCites ++ cited.flatten).eraseDups
    let premises := (allCites ++ st.proofSteps).eraseDups
    let id ← addClaim ⟨c.idx, body, .step c.ctx.env, cites, premises⟩
    modify fun st => { st with proofCites := allCites, proofSteps := st.proofSteps ++ [id] }
    pure id
  | _ => do
    discard <| cites.mapM citeClaims
    addClaim ⟨c.idx, body, claimRole c, cites, []⟩

/-! ## Definition sentences -/

/-- Registered operation names: the name as written, and without a final `of`. -/
def registerOp (name : List Codes) (i : Nat) : M Unit := do
  let base := match name.reverse with
    | w :: r => if w == w!"of" then r.reverse else name
    | [] => name
  let names := [name, base].eraseDups.filter (!·.isEmpty)
  modify fun st => { st with ops := st.ops ++ names.map (·, i) }

/-- The head of a defining left-hand side: the defined key, whether it is a
family, and its explicit arguments. -/
def defHead (binder : Codes) : MT → M (Codes × Bool × List Codes)
  | .app h args => do
    let names ← args.mapM fun a => match a with | .id n => pure n | _ => fail E.unsupported
    match h with
    | .id k => if names == [binder] then pure (k, false, []) else fail E.unsupported k
    | .sup (.id x) (.id d) => if x == binder then pure (w!"^" ++ d, false, names) else fail E.unsupported
    | .hat (.id x) => if x == binder then pure (w!"\\widehat", false, names) else fail E.unsupported
    | .sub (.id k) (.id x) => if x == binder then pure (k, true, names) else fail E.unsupported
    | _ => fail E.unsupported
  | .sup (.id x) (.id d) => if x == binder then pure (w!"^" ++ d, false, []) else fail E.unsupported
  | .hat (.id x) => if x == binder then pure (w!"\\widehat", false, []) else fail E.unsupported
  | .sub (.id k) (.id x) => if x == binder then pure (k, true, []) else fail E.unsupported
  | _ => fail E.unsupported

def argTypes : Ty → Nat → List Ty
  | _, 0 => []
  | .fn a b, n + 1 => a :: argTypes b n
  | _, _ => []

/-- Claims `a₁ R₁ a₂ R₂ …` after a definition `X := a₁`, pairwise, under binders. -/
def chainClaims (sc : Scope) (first : MT) (rest : List (Rel × MT)) : M (List Tm) := do
  let rec go : MT → List (Rel × MT) → M (List Tm)
    | _, [] => pure []
    | a, (r, b) :: more => do
      let ta ← term F sc none a
      let tb ← term F sc none b
      let p ← relTm r ta tb
      pure (p :: (← go b more))
  go first rest

/-- `For a N $x$, the NAME is DEF`. -/
def defItem (c : SentCtx) (b : BindInfo) (it : DefItem) : M (List Nat × List Nat) := do
  let bty := b.ty
  match it.defn with
  | .chain lhs ((.defeq, rhs) :: more) => do
    let (key, family, args) ← defHead b.name lhs
    let ats := match bty with
      | .fn _ _ => argTypes bty args.length
      | _ => []
    if ats.length != args.length then fail E.type
    let sc := ((args.zip ats).reverse) ++ [(b.name, bty)]
    let (body, rty) ← term F sc none rhs
    let value := Tm.lam bty (holdsAt b.pred (.loc 0)) (lamWrap ats body)
    let ty := Ty.fn bty (tyWrap ats rty)
    let i ← addGlob ⟨key, ty, b.pred :: ats.map (fun _ => none), family⟩ value
    registerOp it.name i
    let cs ← chainClaims sc rhs more
    let bs := b :: (args.zip ats).map fun (n, t) => ⟨n, t, none⟩
    let ids ← cs.mapM fun p => emit c (wrap bs p) []
    addLabels it.labels ids true
    pure ([i], ids)
  | .mapsto pat body => do
    -- an operation named by its noun, e.g. `the copula associated with γ`
    let nouns := (← get).nouns
    let some ni := it.name.findSome? (fun w => nouns.lookup [w]) | fail E.noun
    let gty : Option Ty := ((← get).globs[ni]?).map (·.ty)
    let elemTy ← match gty with
      | some (.fn a .prop) => pure a
      | _ => fail E.type
    let ats := argTypes elemTy (match pat with | .tuple vs => vs.length | _ => 1)
    let (lt, lty) ← Elab.lam F [(b.name, bty)] pat ats (some .real) body
    let value := Tm.lam bty (holdsAt b.pred (.loc 0)) lt
    let i ← addGlob ⟨[], .fn bty lty, [b.pred], false⟩ value
    registerOp it.name i
    pure ([i], [])
  | _ => fail E.unsupported

/-- One branch of a piecewise definition of `f`, in the scope of its argument `x`:
the condition under which it applies and its value. A parametric piece also
defines its parameter family (the `where` part). -/
def defBranch (f : Codes) (aty cty : Ty) : DefPiece → M (Tm × Tm)
  -- f(x) := rhs [, x ∈ D]
  | .formula (.chain (.app (.id f') [.id x]) [(.defeq, rhs)]) => do
    if f != f' then fail E.unsupported
    let (v, vty) ← term F [(x, aty)] none rhs
    pure (.tt, ← coerce v vty cty)
  | .formula (.conj [.chain (.app (.id f') [.id x]) [(.defeq, rhs)], .chain (.id x') [(.mem, d)]]) => do
    if f != f' || x != x' then fail E.unsupported
    let (v, vty) ← term F [(x, aty)] none rhs
    let cnd ← Elab.term.member F [(x, aty)] (.loc 0, aty) d
    pure (cnd, ← coerce v vty cty)
  -- f(c) := v for a constant c
  | .formula (.chain (.app (.id f') [a]) [(.defeq, rhs)]) => do
    if f != f' then fail E.unsupported
    let some at_ := Elab.constMT a | fail E.unsupported
    let (v, vty) ← term F [] none rhs
    let v ← coerce v vty cty
    let xr ← coerce (.loc 0) aty .real
    pure (.eq xr at_, shift 1 0 v)
  -- on D, parametrically by f(e_b) := g(b), b ∈ P, where e_b := h(b) [, b ∈ P']
  | .param d (.conj items) => do
    match items with
    | .chain (.app (.id f') [.sub (.id e) (.id b)]) [(.defeq, g)] :: .chain (.id b1) [(.mem, pdom)] ::
        .text wh :: .chain (.sub (.id e') (.id b2)) [(.defeq, h)] :: rest => do
      if f != f' || e != e' || b != b1 || b != b2 || wh != w!"where" then fail E.unsupported
      let edom ← match rest with
        | [] => pure pdom
        | [.chain (.id b3) [(.mem, d2)]] => if b3 == b then pure d2 else fail E.unsupported
        | _ => fail E.unsupported
      -- the family e_b on its domain
      let (_, epred) ← domainOf true edom
      let (hv, hty) ← term F [(b, .real)] none h
      let hv ← coerce hv hty .real
      let ie ← addGlob ⟨e, .fn .real .real, [epred], true⟩ (.lam .real (holdsAt epred (.loc 0)) hv)
      -- the value at x: the y with x = e_b and y = g(b) for some b ∈ P
      let (_, ppred) ← domainOf true pdom
      let sc : Scope := [(b, .real), (w!"", cty), (w!"", aty)]
      let (gv, gty) ← term F sc none g
      let gv ← coerce gv gty cty
      let eb := Tm.guard (holdsAt epred (.loc 0)) (.app (.glob ie) (.loc 0))
      let xr ← coerce (.loc 2) aty .real
      let body := Tm.ex .real (Elab.conjAll [holdsAt ppred (.loc 0), .eq eb xr, .eq (.loc 1) gv])
      let cnd ← Elab.term.member F [(w!"", aty)] (.loc 0, aty) d
      pure (cnd, .the cty body)
    | _ => fail E.unsupported
  | _ => fail E.unsupported

/-- `define $f:A\to B$ by PIECES [and observe that φ for every x∈A]`: `f` is the
function on `A` given by its pieces (point values, formulas on subdomains and
parametric pieces), each applying where its condition holds; it is defined only
where some piece applies. Its values lie in `B` (a claim). -/
def defBy (c : SentCtx) (sg : MT) (pieces : List DefPiece) (labels : List Codes)
    (observe : Option (MT × List Codes × MT)) : M (List Nat × List Nat) := do
  match sg with
  | .sig (.id f) dom cod => do
    let (cty, cpred) ← domainOf true cod
    -- `f(x,y)\coloneqq e` on `\mathbb{R}^2` or `A\times B`: a curried function
    let ds ← domainsOf true dom
    if ds.length ≥ 2 then
      match pieces with
      | [.formula (.chain (.app (.id f') args) [(.defeq, rhs)])] => do
        if f != f' || args.length != ds.length then fail E.unsupported
        let names ← args.mapM fun a => match a with | .id n => pure n | _ => fail E.unsupported
        let bs : List BindInfo := (names.zip ds).map fun (n, (t, p)) => ⟨n, t, p⟩
        let start := (← get).globs.length
        let sc : Scope := (bs.map fun b => (b.name, b.ty)).reverse
        let (body, bty) ← term F sc none rhs
        let body ← coerce body bty cty
        let value := bs.foldr (fun b t => Tm.lam b.ty (holdsAt b.pred (.loc 0)) t) body
        let i ← addGlob ⟨f, tyWrap (ds.map (·.1)) cty, ds.map (·.2), false⟩ value
        modify fun st => { st with params := st.params ++ [(i, names)] }
        let k := bs.length
        let applied := (List.range k).foldl (fun acc j => Tm.app acc (.loc (k - 1 - j))) (Tm.glob i)
        let ids ← match cpred with
          | some p => pure [← emit c (wrap bs (.app p applied)) []]
          | none => pure []
        addLabels labels ids true
        return ((List.range (i + 1 - start)).map (· + start), ids)
      | _ => fail E.unsupported
    let (aty, apred) ← domainOf true dom
    let start := (← get).globs.length
    let body ← match pieces with
      | [.formula (.chain (.app (.id f') [.id x]) [(.defeq, rhs)])] => do
        if f != f' then fail E.unsupported
        let (body, bty) ← term F [(x, aty)] none rhs
        coerce body bty cty
      | _ => do
        let bs ← pieces.mapM (defBranch f aty cty)
        pure (bs.foldr (fun (cnd, v) acc => Tm.cases cnd v acc) (.undef cty))
    let value := Tm.lam aty (holdsAt apred (.loc 0)) body
    let i ← addGlob ⟨f, .fn aty cty, [apred], false⟩ value
    let applied := Tm.guard (holdsAt apred (.loc 0)) (.app (.glob i) (.loc 0))
    let codomain := match cpred with
      | some p => [Tm.all aty (.imp (holdsAt apred (.loc 0)) (.app p applied))]
      | none => []
    let ids ← codomain.mapM fun p => emit c p []
    let obs ← match observe with
      | some (φ, vs, d) => do
        let bs ← binderInfos (.every vs d)
        let p ← prop (scopeOf bs) none φ
        pure [← emit c (wrap bs p) []]
      | none => pure []
    addLabels labels (ids ++ obs) true
    pure ((List.range (i + 1 - start)).map (· + start), ids ++ obs)
  | _ => fail E.unsupported

/-- The key and the index variable of a family's name: `f_b` is `f`, `R_b^-` is
`R^-` and `T^0_q` (that is, `T_q^0`) is `T^0`. -/
def familyKey : MT → Option (Codes × Codes)
  | .sub (.id f) (.id p) => some (f, p)
  | .sup (.sub (.id f) (.id p)) (.id s) => some (f ++ w!"^" ++ s, p)
  | .sup (.sub (.id f) (.id p)) (.num n) => some (f ++ w!"^" ++ (Nat.toDigits 10 n).map Char.toNat, p)
  | _ => none

/-- `For $b\in B$, define $f_b:A\to C$ by DISPLAY.`: the family `b ↦ f_b`, a map of
`A` for every `b`, with the claim that it takes values in `C`. -/
def defByFamily (c : SentCtx) (b : BindInfo) (sg : MT) (pieces : List DefPiece) (labels : List Codes) :
    M (List Nat × List Nat) := do
  match sg with
  | .sig name dom cod => do
    let some (f, p) := familyKey name | fail E.unsupported
    if p != b.name then fail E.unsupported
    let (aty, apred) ← domainOf true dom
    let (cty, cpred) ← domainOf true cod
    let (x, rhs) ← match pieces with
      | [.formula (.chain (.app lhs [.id x]) [(.defeq, rhs)])] =>
        if familyKey lhs == some (f, p) then pure (x, rhs) else fail E.unsupported
      | _ => fail E.unsupported
    let sc : Scope := [(x, aty), (b.name, b.ty)]
    let (body, bty) ← term F sc none rhs
    let body ← coerce body bty cty
    let value := Tm.lam b.ty (holdsAt b.pred (.loc 0)) (.lam aty (holdsAt apred (.loc 0)) body)
    let i ← addGlob ⟨f, .fn b.ty (.fn aty cty), [b.pred, apred], true⟩ value
    let ids ← match cpred with
      | some q => do
        let applied := Tm.guard (holdsAt b.pred (.loc 1))
          (Tm.guard (holdsAt apred (.loc 0)) (Tm.app (.app (.glob i) (.loc 1)) (.loc 0)))
        pure [← emit c (wrap [b, ⟨x, aty, apred⟩] (.app q applied)) []]
      | none => pure []
    addLabels labels ids true
    pure ([i], ids)
  | _ => fail E.unsupported

/-- `For B, the NAME $f_c:A\to B$ reads DISPLAY`. -/
def defReads (c : SentCtx) (b : BindInfo) (sg disp : MT) (labels : List Codes) : M (List Nat × List Nat) := do
  match sg, disp with
  | .sig (.sub (.id f) (.id p)) dom cod, .chain (.app (.sub (.id f') (.id p')) [.id x]) ((.defeq, rhs) :: more) => do
    if f != f' || p != b.name || p' != b.name then fail E.unsupported
    let (aty, apred) ← domainOf false dom
    let (cty, cpred) ← domainOf false cod
    if cpred.isSome then fail E.unsupported
    let sc : Scope := [(x, aty), (b.name, b.ty)]
    let (body, bty) ← term F sc none rhs
    let body' ← coerce body bty cty
    let value := Tm.lam b.ty (holdsAt b.pred (.loc 0)) (.lam aty (holdsAt apred (.loc 0)) body')
    let i ← addGlob ⟨f, .fn b.ty (.fn aty cty), [b.pred, apred], true⟩ value
    let cs ← chainClaims sc rhs more
    let ids ← cs.mapM fun q => emit c (wrap [b, ⟨x, aty, apred⟩] q) []
    addLabels labels ids true
    pure ([i], ids)
  | _, _ => fail E.unsupported

/-- `NAME is denoted by $S$`: binds the symbol `S` to a named notion of the
vocabulary (`Lebesgue measure on $[0,1]$`). -/
def denotedBy (name : List Chunk) (sym : MT) : M (List Nat × List Nat) := do
  let key ← match sym with | .id k => pure k | _ => fail E.unsupported
  let V := (← get).vocab
  let cands := V.notions.filterMap fun n => match matchPhrase n.name name with
    | some (none, []) => some (n, [])
    | _ => none
  match ← theMeaning (fun (n : Notion) => (n.ty, n.value)) (·.field) name cands with
  | some (n, _) => do
    let i ← addGlob ⟨key, n.ty, [], false⟩ n.value
    pure ([i], [])
  | none => fail E.noun (((wordsOf name).intersperse [32]).flatten)

/-- `For B, set $X_p\coloneqq e [\in D]$` or `$f(p)\coloneqq e$`. -/
def setDefSimple (c : SentCtx) (b : BindInfo) (m : MT) : M (List Nat × List Nat) := do
  match m with
  | .chain lhs ((.defeq, rhs) :: more) => do
    let (key, family) ← match lhs with
      | .sub (.id k) (.id p) => if p == b.name then pure (k, true) else fail E.unsupported
      -- `f(x)\coloneqq e`: a function of the binder's variable
      | .app (.id k) [.id p] => if p == b.name then pure (k, false) else fail E.unsupported
      -- `r_-(b)\coloneqq e`, `\eta_\pm(x)\coloneqq e`: a decorated name
      | .app h [.id p] =>
        match p == b.name, Elab.symKey h with
        | true, some k => pure (k, false)
        | _, _ => fail E.unsupported
      | _ => fail E.unsupported
    let sc : Scope := [(b.name, b.ty)]
    let (v, vty) ← term F sc none rhs
    let i ← addGlob ⟨key, .fn b.ty vty, [b.pred], family⟩ (.lam b.ty (holdsAt b.pred (.loc 0)) v)
    let x : Tm × Ty := (.guard (holdsAt b.pred (.loc 0)) (.app (.glob i) (.loc 0)), vty)
    let ps ← more.mapM fun (r, y) => do
      if r == .mem then Elab.term.member F sc x y
      else do relTm r x (← term F sc none y)
    let ids ← ps.mapM fun p => emit c (wrap [b] p) []
    pure ([i], ids)
  | _ => fail E.unsupported

/-- `For B, set $X_p\coloneqq e [\in D]$`: a family on the binder's domain, and the
claims of the rest of the chain. -/
def setDef (c : SentCtx) (b : BindInfo) (m : MT) : M (List Nat × List Nat) := do
  match m with
  -- `f_p(x,…)\coloneqq e`, `R_p^-(z)\coloneqq e`: a family with further real
  -- arguments; `z_-(x)\coloneqq e`, `c\coloneqq e`: a symbol that does not show `p`,
  -- whose implicit parameter `p` is supplied from the scope at each use
  | .chain lhs ((.defeq, rhs) :: more) =>
    let (hd, args) := match lhs with
      | .app h as => (h, as)
      | _ => (lhs, [])
    let names := args.filterMap fun a => match a with | .id n => some n | _ => none
    let simple := match lhs with
      | .sub (.id _) (.id p) => p == b.name
      | .app (.id _) [.id p] => p == b.name
      | _ => false
    if simple || names.length != args.length || names.contains b.name then setDefSimple c b m else do
    let (key, family) ← match hd with
      | .sub (.id k) (.id p) =>
        if p == b.name then pure (k, true) else
        match Elab.symKey hd with | some k' => pure (k', false) | none => fail E.unsupported
      | .sup (.sub (.id k) (.id p)) (.id s) => if p == b.name then pure (k ++ w!"^" ++ s, true) else fail E.unsupported
      | .id k => pure (k, false)
      | _ => match Elab.symKey hd with | some k' => pure (k', false) | none => fail E.unsupported
    if !more.isEmpty && !args.isEmpty then fail E.unsupported
    let ats := names.map fun _ => Ty.real
    let sc : Scope := (names.zip ats).reverse ++ [(b.name, b.ty)]
    let (v, vty) ← term F sc none rhs
    let value := Tm.lam b.ty (holdsAt b.pred (.loc 0)) (lamWrap ats v)
    let i ← addGlob ⟨key, .fn b.ty (tyWrap ats vty), b.pred :: ats.map (fun _ => none), family⟩ value
    if !family then modify fun st => { st with implicits := st.implicits ++ [(i, [b.name])] }
    let x : Tm × Ty := (.guard (holdsAt b.pred (.loc 0)) (.app (.glob i) (.loc 0)), vty)
    let sc1 : Scope := [(b.name, b.ty)]
    let ps ← more.mapM fun (r, y) => do
      if r == .mem then Elab.term.member F sc1 x y
      else do relTm r x (← term F sc1 none y)
    let ids ← ps.mapM fun p => emit c (wrap [b] p) []
    pure ([i], ids)
  | _ => fail E.unsupported

/-- The fixed variable (`fix $b\in B$` earlier in the section) that the subscript of a
definition's symbol names, as in `Set $R_b^-(z)\coloneqq …$`. -/
def fixedFor (c : SentCtx) (m : MT) : M (Option BindInfo) := do
  let lhs := match m with | .chain l _ => l | _ => m
  let hd := match lhs with | .app h _ => h | h => h
  let v := match hd with
    | .sub (.id _) (.id p) => some p
    | .sup (.sub (.id _) (.id p)) _ => some p
    | _ => none
  match v with
  | some p => pure (((← get).fixed.find? fun (s, b) => s == c.ctx.sec && b.name == p).map (·.2))
  | none => pure none

/-- `Set $d_0\coloneqq e$.`: constants, with the claims of the rest of each chain;
under a binder, families and functions of the binder's variable (`setDef`). -/
def constDefs (c : SentCtx) (b : Option BindInfo) (defs : List MT) (labels : List Codes) :
    M (List Nat × List Nat) := do
  let mut ds : List Nat := []
  let mut cs : List Nat := []
  for m in defs do
    match b with
    | some bi =>
      let (d', c') ← setDef c bi m
      ds := ds ++ d'
      cs := cs ++ c'
    | none =>
      match ← fixedFor c m with
      | some fb => do
        let (d', c') ← setDef c fb m
        ds := ds ++ d'
        cs := cs ++ c'
      | none =>
      match m with
      | .chain lhs ((.defeq, rhs) :: more) => do
        let some key := symKey lhs | fail E.unsupported
        let (v, vty) ← term F [] none rhs
        let i ← addGlob ⟨key, vty, [], false⟩ v
        let x : Tm × Ty := (.glob i, vty)
        let ps ← more.mapM fun (r, y) => do
          if r == .mem then Elab.term.member F [] x y
          else do relTm r x (← term F [] none y)
        let ids ← ps.mapM fun p => emit c p []
        ds := ds ++ [i]
        cs := cs ++ ids
      | _ => fail E.unsupported
  addLabels labels cs true
  pure (ds, cs)

/-- `For $u,v\in A$, set $f(u,v)\coloneqq e$, …`: functions of all the binder's
variables, in their order. Under `u,v\in[0,1]`, `M(u,v)\coloneqq\min\{u,v\}` is a
function on the unit square, like a copula. -/
def multiDefs (bs : List BindInfo) (defs : List MT) (labels : List Codes) (imp : List BindInfo := []) :
    M (List Nat × List Nat) := do
  let mut ds : List Nat := []
  for m in defs do
    match m with
    -- `For $s\in[0,1]$ and $u,v\in[0,1]$, set $S_s(u,v)\coloneqq e$`: a family, indexed by
    -- the first variable, of functions of the others. Inside a result or a proof, the
    -- variables of the result it uses (`imp`) are implicit parameters
    | .chain (.app h args) [(.defeq, rhs)] =>
      if let some (k, p) := familyKey h then
        if bs.head?.map (·.name) == some p then
          let names ← args.mapM fun a => match a with | .id n => pure n | _ => fail E.unsupported
          if names != (bs.drop 1).map (·.name) then fail E.unsupported
          let all := imp ++ bs
          let sc : Scope := (all.map fun b => (b.name, b.ty)).reverse
          let (v, vty) ← term F sc none rhs
          let value := all.foldr (fun b t => Tm.lam b.ty (holdsAt b.pred (.loc 0)) t) v
          let ty := all.foldr (fun b t => Ty.fn b.ty t) vty
          let i ← addGlob ⟨k, ty, all.map (·.pred), true⟩ value
          if !imp.isEmpty then modify fun st => { st with implicits := st.implicits ++ [(i, imp.map (·.name))] }
          ds := ds ++ [i]
          continue
      let names ← args.mapM fun a => match a with | .id n => pure n | _ => fail E.unsupported
      if names != bs.map (·.name) then fail E.unsupported
      let some key := Elab.symKey h | fail E.unsupported
      let sc : Scope := (bs.map fun b => (b.name, b.ty)).reverse
      let (v, vty) ← term F sc none rhs
      let value := bs.foldr (fun b t => Tm.lam b.ty (holdsAt b.pred (.loc 0)) t) v
      let ty := bs.foldr (fun b t => Ty.fn b.ty t) vty
      let i ← addGlob ⟨key, ty, bs.map (·.pred), false⟩ value
      modify fun st => { st with params := st.params ++ [(i, names)] }
      ds := ds ++ [i]
    | _ => fail E.unsupported
  addLabels labels [] true
  pure (ds, [])

/-- `define continuous functions $f,g:A\to\R$ by $f(a)=c$, …, and DISPLAY` with
`f'(x) = …` in the display: `f(x) = c + ∫_a^x f'(t)\,dt` for `x ∈ A` (defined when the
derivative is integrable between `a` and `x`). Where no piece of a piecewise
derivative applies (at finitely many points), the integrand is `0`, which does not
change the integral. Under a binder `p`, `f_p` is a family. -/
def defDeriv (bi : Option BindInfo) (names : List MT) (dom cod : MT) (anchors : List MT)
    (derivs : MT) (labels : List Codes) : M (List Nat × List Nat) := do
  let (aty, apred) ← domainOf true dom
  let (cty, _) ← domainOf true cod
  if aty != .real || cty != .real then fail E.unsupported
  let rows := match derivs with | .conj xs => xs | m => [m]
  let sc0 : Scope := match bi with | some b => [(b.name, b.ty)] | none => []
  let mut ids : List Nat := []
  for n in names do
    let some nk := Elab.symKey n | fail E.unsupported
    let (key, family) ← match n, bi with
      | .sub (.id k) (.id p), some b => if p == b.name then pure (k, true) else fail E.unsupported
      | .id k, none => pure (k, false)
      | _, _ => fail E.unsupported
    -- the value at one point
    let some (a, cv) := anchors.findSome? (fun an => match an with
        | .chain (.app h [a]) [(.eq, cv)] => if Elab.symKey h == some nk then some (a, cv) else none
        | _ => none)
      | fail E.referent nk
    -- the derivative
    let some (x, g) := rows.findSome? (fun r => match r with
        | .chain (.app (.sup h (.id d)) [.id x]) [(.eq, g)] =>
          if d == [39] && Elab.symKey h == some nk then some (x, g) else none
        | _ => none)
      | fail E.referent nk
    let at_ ← asReal (← term F sc0 none a)
    let ct ← asReal (← term F sc0 none cv)
    let gt ← asReal (← term F ((x, .real) :: (w!"", .real) :: sc0) none g)
    let gl := Tm.lam .real .tt (zeroElsewhere gt)
    let a1 := shift 1 0 at_
    let integral := Tm.app (.app (.app (.prim .intervalIntegral) a1) (.loc 0)) gl
    let integrable := Tm.app (.app (.app (.prim .intervalIntegrable) gl) a1) (.loc 0)
    let body := Tm.add (shift 1 0 ct) (.guard integrable integral)
    let fx := Tm.lam .real (holdsAt apred (.loc 0)) body
    let (g, v) : Glob × Tm := match bi with
      | some b => (⟨key, .fn b.ty (.fn .real .real), [b.pred, apred], family⟩, Tm.lam b.ty (holdsAt b.pred (.loc 0)) fx)
      | none => (⟨key, .fn .real .real, [apred], family⟩, fx)
    let i ← addGlob g v
    ids := ids ++ [i]
  addLabels labels [] true
  pure (ids.eraseDups, [])

/-- `For B, let $X_p$ denote NP`. -/
def letDenote (b : BindInfo) (sym : MT) (np : List Chunk) : M (List Nat × List Nat) := do
  let (key, family) ← match sym with
    | .sub (.id k) (.id p) => if p == b.name then pure (k, true) else fail E.unsupported
    -- `\gamma^T`: a family written with a superscript
    | .sup (.id k) (.id p) => if p == b.name then pure (k ++ w!"^", true) else fail E.unsupported
    | .id k => pure (k, false)
    | _ => fail E.unsupported
  let sc : Scope := [(b.name, b.ty)]
  let (val, vty) ← match np with
    -- the law of $(X, f(X))$ for $X$ uniformly distributed on $[0,1]$
    | [.w t, .w l, .w o, .m pair, .w fr, .m [.id x], .w u, .w d, .w on, .m zo] =>
      if [t, l, o, fr, u, d, on] == [w!"the", w!"law", w!"of", w!"for", w!"uniformly", w!"distributed", w!"on"]
          && isUnitInterval (Math.parseFormula zo) then do
        match Math.parseFormula pair with
        | some (.tuple [e1, e2]) => do
          -- λ A. Leb {x : A(e1(x), e2(x))}, with A a measurable subset of [0,1]^2
          let sc' := (x, Ty.unit) :: (w!"", Ty.set2) :: sc
          let a ← coerce (← term F sc' none e1).1 .unit .unit
          let t1 ← term F sc' none e1
          let t2 ← term F sc' none e2
          let a1 ← coerce t1.1 t1.2 .unit
          let a2 ← coerce t2.1 t2.2 .unit
          let _ := a
          let set := Tm.lam .unit .tt (.app (.app (.loc 1) a1) a2)
          let body := Tm.guard (.app (.prim .measurableSet1) set) (.app (.prim .leb) set)
          pure (Tm.lam Ty.set2 (.app (.prim .measurableSet2) (.loc 0)) body, Ty.meas2)
        | _ => fail E.unsupported
      else fail E.noun
    | .w t :: rest =>
      if t != w!"the" then fail E.unsupported
      else do
        let ws := wordsOf rest
        match mathsOf rest with
        | [arg] => do
          let some i := lookupWords (← get).ops ws | fail E.noun ((ws.intersperse [32]).flatten)
          let g := ((← get).globs[i]?).getD default
          let m ← liftO (Math.parseFormula arg) E.unsupported
          let a ← term F sc none m
          applyAll (.glob i) g.ty g.doms [a]
        | _ => fail E.unsupported
    | _ => fail E.unsupported
  let value := Tm.lam b.ty (holdsAt b.pred (.loc 0)) val
  let i ← addGlob ⟨key, .fn b.ty vty, [b.pred], family⟩ value
  pure ([i], [])

/-- `We say that a N $x$ is PHRASE of a M $y$ if φ for all u,v∈A`. -/
def weSay (subj : List Chunk) (phrase : List Codes) (o : List Chunk) (cond : MT) (vs : List Codes) (d : MT) :
    M (List Nat × List Nat) := do
  let s ← nounPhrase subj
  let t ← nounPhrase o
  let bs ← binderInfos (.every vs d)
  let sc := scopeOf ([s, t] ++ bs)
  let body ← prop sc none cond
  let inner := forallBinders (bs.map fun b => (b.name, b.ty, b.pred.map fun p => Tm.app p (.loc 0))) body
  let value := Tm.lam s.ty (holdsAt s.pred (.loc 0)) (.lam t.ty (holdsAt t.pred (.loc 0)) inner)
  let i ← addGlob ⟨[], .fn s.ty (.fn t.ty .prop), [s.pred, t.pred], false⟩ value
  modify fun st => { st with preds := st.preds ++ [(phrase, i)] }
  pure ([i], [])

/-- `let $S$ denote the class of Ns, that is, NP`: `S` is the class described by
the noun phrase `NP`, and `N` (singular) names it. -/
def defClass (sym : MT) (plural : List Codes) (np : List Chunk) : M (List Nat × List Nat) := do
  let key ← match sym with | .id k => pure k | _ => fail E.unsupported
  -- without `that is, NP`, the class is a noun of the vocabulary
  let b ← nounPhrase (if np.isEmpty then plural.map Chunk.w else np)
  if !b.name.isEmpty then fail E.unsupported b.name
  let p := b.pred.getD (.lam b.ty .tt .tt)
  let i ← addGlob ⟨key, .fn b.ty .prop, [none], false⟩ p
  let sing := plural.dropLast ++ (plural.getLast?.map singular).toList
  let names := [sing, (sing.getLast?).toList].eraseDups
  modify fun st => { st with nouns := st.nouns ++ names.map (·, i), classes := st.classes ++ [(plural, i)] }
  pure ([i], [])

/-! ## Inline definitions and notions -/

/-- An inline definition `X\coloneqq e` or `f(y)\coloneqq e` among the binders `bs` of
its context: an argument that is a binder's variable ranges over the binder's
domain, and the binders that `e` uses are implicit parameters, supplied from the
scope at each use. Inside a result or a proof, the definition is local to it. -/
def inlineDef (c : SentCtx) (bs : List BindInfo) (m : MT) : M Nat := do
  match m with
  | .chain lhs [(.defeq, rhs)] =>
    let (hd, args) := match lhs with
      | .app h as => (h, as)
      | _ => (lhs, [])
    let some key := Elab.symKey hd | fail E.unsupported
    let argNames ← args.mapM fun a => match a with | .id n => pure n | _ => fail E.unsupported
    let st ← get
    let ids := freeIds 64 argNames rhs
    let used := ids ++ implicitVars st ids
    let imp := bs.filter fun b => used.contains b.name && !argNames.contains b.name
    let argInfo : List BindInfo := argNames.map fun n => match bs.find? (·.name == n) with
      | some b => b
      | none => ⟨n, .real, none⟩
    let all := imp ++ argInfo
    let (v, vty) ← term F (scopeOf all) none rhs
    let value := all.foldr (fun b acc => Tm.lam b.ty (holdsAt b.pred (.loc 0)) acc) v
    let ty := all.foldr (fun b acc => Ty.fn b.ty acc) vty
    let i ← addGlob ⟨key, ty, all.map (·.pred), false⟩ value
    if !imp.isEmpty then modify fun st => { st with implicits := st.implicits ++ [(i, imp.map (·.name))] }
    match c.ctx.kind with
    | .text => pure ()
    | _ => modify fun st => { st with locals := st.locals ++ [(i, c.ctx.env)] }
    pure i
  | _ => fail E.unsupported

/-- Make the definitions of a clause: those after it (`where`) and those inside a
comparison (`the geometric mean $G\coloneqq\sqrt{ab}$`), which become their symbols. -/
def inlineClause (c : SentCtx) (bs : List BindInfo) (defs : List MT) (k : Clause) : M Clause := do
  for d in defs do discard <| inlineDef c bs d
  let side (m : MT) : M MT := match m with
    | .chain lhs [(.defeq, _)] => do discard <| inlineDef c bs m; pure lhs
    | _ => pure m
  match k with
  | .compare l r rr => pure (.compare (← side l) r (← side rr))
  | _ => pure k

/-- `x\mapsto e` (with its domain, `x\mapsto e,\ x\in D`) is non-increasing, …:
`∀ s t ∈ D, s ≤ t → e(t) ≤ e(s)`. -/
def monoTm (sc : Scope) (m : MT) (mono : Mono) : M Tm := do
  let (x, e, dom) ← match m with
    | .mapsto (.id x) e => pure (x, e, none)
    | .conj [.mapsto (.id x) e, .chain (.id y) [(.mem, d)]] =>
      if x == y then pure (x, e, some d) else fail E.unsupported
    | _ => fail E.unsupported
  let (ty, p) ← match dom with
    | some d => domainOf true d
    | none => pure (.real, none)
  if ty != .real then fail E.unsupported
  let et ← asReal (← term F ((x, ty) :: (w!"", ty) :: sc) none e)
  let es ← asReal (← term F ((w!"", ty) :: (x, ty) :: sc) none e)
  let (pre, concl) : Tm × Tm := match mono with
    | .nonincreasing => (.le (.loc 1) (.loc 0), .le et es)
    | .nondecreasing => (.le (.loc 1) (.loc 0), .le es et)
    | .increasing => (.lt (.loc 1) (.loc 0), .lt es et)
    | .decreasing => (.lt (.loc 1) (.loc 0), .lt et es)
  pure (.all ty (.imp (holdsAt p (.loc 0)) (.all ty (.imp (holdsAt p (.loc 0)) (.imp pre concl)))))

/-- The condition of a notion, about its subject (`loc 0` of `sc`). -/
def notionBody (sc : Scope) (cond : NotionCond) : M Tm := do
  match cond with
  | .formula f binds =>
    let bs := (← bindersInfos binds)
    pure (wrap bs (← prop (scopeOf bs ++ sc) none f))
  | .mono binds m mono =>
    let bs := (← bindersInfos binds)
    pure (wrap bs (← monoTm (scopeOf bs ++ sc) m mono))

/-- `We call a copula $C$ NAME (ABBR) if COND.`: the notion `λ C, COND`, named by
`NAME` and `ABBR`. -/
def defNotion (subj : List Chunk) (name abbr : List Codes) (cond : NotionCond) :
    M (List Nat × List Nat) := do
  let s ← match subj with
    | [.m [.id v]] => match (← get).notionSubject with
      | some b => if b.name == v then pure b else fail E.free v
      | none => fail E.free v
    | np => nounPhrase np
  if s.name.isEmpty then fail E.unsupported
  let body ← notionBody (scopeOf [s]) cond
  let i ← addGlob ⟨[], .fn s.ty .prop, [s.pred], false⟩ (.lam s.ty (holdsAt s.pred (.loc 0)) body)
  let names := [name] ++ (if abbr.isEmpty then [] else [abbr])
  modify fun st => { st with notions := st.notions ++ names.map (·, i), notionSubject := some s }
  pure ([i], [])

/-- `A NP $f$ belongs to $\mathcal M_\alpha$ if $φ$ for every B`: the class `\mathcal M_\alpha`
(a family over the parameter `α` of its subscript). The generic constants of `φ` are
placed by their conventions. When `φ` uses quantities that depend on a parameter `ℓ`
(`\varepsilon` set for every positive integer `ℓ`) and a constant of `φ` is uniform in
`ℓ`, the class consists of families `ℓ ↦ f_ℓ`: `f` in `φ` is the member at `ℓ`, and `ℓ`
is bound after the constants. -/
def defMember (subj : List Chunk) (cls : MT) (cond : MT) (binds : List Grammar.Bind) :
    M (List Nat × List Nat) := do
  let (key, param) ← match cls with
    | .sub (.id k) (.id p) => pure (k, some p)
    | .id k => pure (k, none)
    | _ => fail E.unsupported
  -- the member: a noun phrase (`function $f:\mathbb R^2\to\mathbb R$` as a map)
  let subj := match subj with
    | .w w :: rest => if w == w!"function" then .w w!"map" :: rest else subj
    | _ => subj
  let s ← nounPhrase subj
  if s.name.isEmpty then fail E.unsupported
  let st ← get
  -- `\forall I\in A\ \exists C_I: φ`: the constants are placed by their conventions
  let isGen (k : Codes) : Bool := st.genericConsts.any fun g =>
    k == g.base || k.take (g.base.length + 1) == g.base ++ [95]
  let (cond, binds) := match cond with
    | .quant true vs dom (.quant false gs _ body) =>
      if !gs.isEmpty && gs.all isGen then (body, binds ++ [Grammar.Bind.every vs dom]) else (cond, binds)
    | .quant false gs _ body => if !gs.isEmpty && gs.all isGen then (body, binds) else (cond, binds)
    | _ => (cond, binds)
  let pScope : List BindInfo := match param with
    | some p => [⟨p, .real, none⟩]
    | none => []
  let cbs ← bindersInfos binds
  let bound := (pScope ++ [s] ++ cbs).map (·.name)
  -- the parameters of the quantities `φ` uses (`ℓ` of `\varepsilon`), with their domains
  let ids := (freeIds 64 bound cond).eraseDups
  let params := ((implicitVars st ids).eraseDups.filter (!bound.contains ·))
  let domOf (p : Codes) : Option Tm := (st.implicits.findSome? fun (i, ns) =>
      match ns.idxOf? p with
      | some j => (st.globs[i]?).bind fun g => (g.doms[j]?).join
      | none => none)
  let pbs : List BindInfo := params.map fun p => ⟨p, .real, domOf p⟩
  -- the generic constants of `φ`
  let bases := st.genericConsts.map (·.base)
  let gens := (genericsOf bases 64 cond).filter (fun (k, _) => !(st.globs.any (·.key == k)) && !bound.contains k)
  let gens := gens.foldl (fun acc g => if acc.any (·.1 == g.1) then acc else acc ++ [g]) []
  let convOf (k : Codes) : GenericConst :=
    ((st.genericConsts.filter fun g => k == g.base || k.take (g.base.length + 1) == g.base ++ [95]).getLast?).getD {base := k}
  let gbs : List (BindInfo × GenSpec) := gens.map fun (k, idx) =>
    let g := convOf k
    let pred : Option Tm := if g.sign == 1 then some (.lam .real .tt (.lt (.num 0) (.loc 0)))
      else if g.sign == 2 then some (.lam .real .tt (.le (.num 0) (.loc 0))) else none
    (⟨k, .real, pred⟩, { allowed := idx ++ g.deps, fixedOk := g.fixedOk, uniform := g.uniform, strict := g.strict })
  -- a class of families when a constant is uniform in a parameter
  let family := !pbs.isEmpty && gbs.any fun (_, sp) => pbs.any fun p => !sp.allowed.contains p.name
  if !pbs.isEmpty && !family then fail E.unsupported (params.headD [])
  let some order := placeGenerics gbs (cbs ++ pbs) [] | fail E.unsupported
  let m := order.length
  let fTy : Ty := if family then .fn .real s.ty else s.ty
  -- the scope of `φ`: the parameter, the member (or the family), the binders in order, and
  -- (for a family) the member at `ℓ`
  let outer : Scope := (pScope.map fun b => (b.name, b.ty)).reverse
  let fam : Scope := [(if family then w!"@F" else s.name, fTy)]
  let mid : Scope := (order.map fun (b, _) => (b.name, b.ty)).reverse
  let inner : Scope := if family then [(s.name, s.ty)] else []
  let ψ ← prop (inner ++ mid ++ fam ++ outer) none cond
  let body ← if family then do
      let some (_, ℓ) := pbs.head?.map (fun b => ((), b)) | fail E.unsupported
      let some li := order.findIdx? (fun (b, _) => b.name == ℓ.name) | fail E.unsupported
      -- `(λ f. ψ) (F ℓ)`
      pure (Tm.app (.lam s.ty .tt ψ) (.app (.loc m) (.loc (m - 1 - li))))
    else pure ψ
  let body := wrapMixed order body
  -- the member's own condition (for a family: at every `ℓ`)
  let memberOk : Tm := match s.pred, family, pbs.head? with
    | some q, true, some ℓ =>
      .all .real (.imp (holdsAt ℓ.pred (.loc 0)) (.app (shift 2 0 q) (.app (.loc 1) (.loc 0))))
    | some q, false, _ => .app (shift 1 0 q) (.loc 0)
    | _, _, _ => .tt
  let pred := Tm.lam fTy .tt (if memberOk == .tt then body else .and memberOk body)
  let (value, ty) := match param with
    | some _ => (Tm.lam .real .tt pred, Ty.fn .real (.fn fTy .prop))
    | none => (pred, Ty.fn fTy .prop)
  let i ← addGlob ⟨key, ty, (if param.isSome then [none, none] else [none]), param.isSome⟩ value
  pure ([i], [])

/-- A notion of the article applied to a term. -/
def notionApp (x : Tm × Ty) (name : List Codes) : M Tm := do
  let st ← get
  let some i := st.notions.lookup name | fail E.prose name.flatten
  let some g := st.globs[i]? | fail E.noun ((name.intersperse [32]).flatten)
  let (t, _) ← applyAll (.glob i) g.ty g.doms [x]
  pure t

/-- Does a phrase of the vocabulary, or a noun of the article, start with the first
word of `np` (after `a`, `an`, `the`)? Otherwise the words are prose. -/
def knownStart (st : St) (np : List Chunk) : Bool :=
  let V := st.vocab
  let cs := (kw [w!"a"] np <|> kw [w!"an"] np <|> kw [w!"the"] np).getD np
  match cs with
  | .w w :: _ =>
    let starts (p : Phrase) : Bool := p.head? == some (.w w)
    V.nouns.any (fun n => starts n.sing || starts n.plural) || V.mods.any (fun m => starts m.phrase) ||
      V.notions.any (fun n => starts n.name) || st.nouns.any (fun (ws, _) => ws.head? == some w)
  | _ => false

/-- The chunks of a name (a hyphen as `-`). -/
def nameChunks (name : List Codes) : List Chunk :=
  name.map fun w => if w == w!"-" then Chunk.p 45 else .w w

/-- `[a|an] NP` or `ADJ[, ADJ] [and ADJ]` about the term `x`: a noun of the vocabulary
(with its modifiers), or prenominal modifiers alone. The type of `x` decides between
modifiers with the same words. -/
def vocabPredicate (sc : Scope) (x : Tm × Ty) (cs : List Chunk) : M Tm := do
  let V := (← get).vocab
  let cs := (kw [w!"a"] cs <|> kw [w!"an"] cs <|> kw [w!"the"] cs).getD cs
  let np ← tryCatch (some <$> nounPhrase cs) fun e =>
    if e.code == E.ambiguous then throw e else pure none
  -- a notion with its arguments: `$X$ is the Poisson distribution with mean $\lambda$`
  let notion ← if np.isSome then pure none else do
    let cands := V.notions.filterMap fun n => (Notation.matchSlots n.name cs []).map fun a => ((n, a), [])
    match ← theMeaning (fun (na : Notion × List (List MTok)) => (na.1.ty, na.1.value)) (·.1.field) cs cands with
    | some ((n, args), _) => do
      let ts ← args.mapM fun a => do
        let some m := Math.parseFormula a | fail E.unsupported
        term F sc none m
      let (v, vty) ← applyAll n.value n.ty n.doms ts
      if vty != x.2 then fail E.type
      if vty == .real then pure (some (Tm.eq x.1 v))
      else if vty == .fn .real .real then
        pure (some (Tm.all .real (.eq (.app (shift 1 0 x.1) (.loc 0)) (.app (shift 1 0 v) (.loc 0)))))
      else fail E.type
    | none => pure none
  match np, notion with
  | _, some p => pure p
  | some b, _ =>
    if !b.name.isEmpty then fail E.unsupported b.name
    if b.ty != x.2 then fail E.type
    pure (holdsAt b.pred x.1)
  | none, none =>
    let rec adjs : Nat → List Chunk → List Tm → M (List Tm)
      | 0, _, _ => fail E.unsupported
      | _ + 1, [], acc => pure acc.reverse
      | f + 1, cs, acc => do
        let cs := ((punct 44 cs).bind fun r => (kw [w!"and"] r).getD r |> some).getD cs
        let cs := (kw [w!"and"] cs).getD cs
        if cs.isEmpty then pure acc.reverse else
        let cands := V.mods.filterMap fun m => if m.prenominal && m.ty == x.2 then
            (matchPhrase m.phrase cs).bind fun (v, r) => if v.isNone then some (m, r) else none
          else none
        match ← theMeaning (fun (m : Modifier) => m.pred) (·.field) cs cands with
        | some (m, r) => adjs f r (Tm.app m.pred x.1 :: acc)
        | none => fail E.noun ((wordsOf cs).intersperse [32]).flatten
    let ps ← adjs (cs.length + 1) cs []
    pure (conjAll ps)

def disjAll : List Tm → Tm
  | [] => .not .tt
  | [p] => p
  | p :: ps => .or p (disjAll ps)

/-! ## Standard adjectives -/

/-- `∀ x, A x → D x`: the domain `A` named by `on $A$` lies in the domain `D` of a
definition (the property of the function on `A` is then about its defined values). -/
def within (ty : Ty) (a d : Tm) : Tm :=
  .all ty (.imp (.app (shift 1 0 a) (.loc 0)) (.app (shift 1 0 d) (.loc 0)))

/-- `ADJ [on $A$]` about a term `t` of type `ty`: a property of a number, of a set of
points of the plane, of a real function (on its domain or on `A`), of a quantity of
functions on the unit square (on the class of its definition, or on `A`), or of a
class of such functions. -/
def adjectiveTm (sc : Scope) (t : Tm) (ty : Ty) (defDom : Option Tm) (a : List Codes)
    (on : Option MT) : M Tm := do
  let u := [w!"with", w!"respect", w!"to", w!"uniform", w!"convergence"]
  if ty == .real then
    if on.isSome then fail E.unsupported
    if a == [w!"positive"] then pure (.lt (.num 0) t)
    else if a == [w!"negative"] then pure (.lt t (.num 0))
    else if a == [w!"nonnegative"] then pure (.le (.num 0) t)
    else if a == [w!"nonpositive"] then pure (.le t (.num 0))
    else fail E.type
  else if ty == .fn .real (.fn .real .prop) then
    if on.isSome then fail E.unsupported
    if a == [w!"compact"] then pure (Tm.app (.prim .compact2) t)
    else if a == [w!"convex"] then pure (Tm.app (.prim .convex2) t)
    else if a == [w!"centrally", w!"symmetric"] then pure (Tm.app (.prim .symm2) t)
    else if a == [w!"closed"] then pure (Tm.app (.prim (.setProp .closed)) t)
    else if a == [w!"open"] then pure (Tm.app (.prim (.setProp .isOpen)) t)
    else if a == [w!"bounded"] then pure (Tm.app (.prim (.setProp .bounded)) t)
    else if a == [w!"connected"] then pure (Tm.app (.prim (.setProp .connected)) t)
    else fail E.type
  else if ty == .fn .real .real then
    let p : Option Prim :=
      if a == [w!"continuous"] then some .continuousOn
      else if a == [w!"concave"] then some .concaveOn
      else if a == [w!"strictly", w!"increasing"] then some .strictMonoOn
      else ([([w!"convex"], FnProp.convex), ([w!"strictly", w!"convex"], .strictConvex),
          ([w!"strictly", w!"concave"], .strictConcave), ([w!"strictly", w!"decreasing"], .strictAnti),
          ([w!"nondecreasing"], .monotone), ([w!"nonincreasing"], .antitone), ([w!"bounded"], .bounded),
          ([w!"nonnegative"], .nonneg), ([w!"positive"], .pos), ([w!"differentiable"], .differentiable),
          ([w!"continuously", w!"differentiable"], .contDiff), ([w!"injective"], .injective),
          ([w!"lower", w!"semicontinuous"], .lowerSemicont), ([w!"upper", w!"semicontinuous"], .upperSemicont),
          ([w!"lipschitz"], .lipschitz)].lookup a).map Prim.fnProp
    let some p := p | fail E.type
    let own := defDom.getD (.lam .real .tt .tt)
    match on with
    | none => pure (Tm.app (.app (.prim p) t) own)
    | some m => do
      let (_, d) ← domainOf true m sc
      let d := d.getD (.lam .real .tt .tt)
      let body := Tm.app (.app (.prim p) t) d
      pure (match defDom with | some dd => .guard (within .real d dd) body | none => body)
  else if ty == .fn Ty.sq .real then
    let p : Option SqProp := [([w!"convex"], SqProp.convex), ([w!"concave"], .concave),
      ([w!"lower", w!"semicontinuous"] ++ u, .lowerUniform), ([w!"upper", w!"semicontinuous"] ++ u, .upperUniform),
      ([w!"continuous"] ++ u, .contUniform)].lookup a
    let some p := p | fail E.type
    match on with
    | none =>
      let some d := defDom | fail E.unsupported
      pure (Tm.app (.app (.prim (.sqProp p)) t) d)
    | some m => do
      let (d, dty) ← Elab.term 100000 sc none m
      if dty != .fn Ty.sq .prop then fail E.type
      let body := Tm.app (.app (.prim (.sqProp p)) t) d
      pure (match defDom with | some dd => .guard (within Ty.sq d dd) body | none => body)
  else if ty == .fn Ty.sq .prop then
    if on.isSome then fail E.unsupported
    let p : Option ClassProp := [([w!"convex"], ClassProp.convex), ([w!"compact"] ++ u, .compactUniform),
      ([w!"closed"] ++ u, .closedUniform)].lookup a
    let some p := p | fail E.type
    pure (Tm.app (.prim (.classProp p)) t)
  else fail E.type

/-! ## Claim sentences -/

mutual
/-- One clause; `rest` are the following clauses of the sentence (for scopes). -/
def clauseTm (c : SentCtx) (sc : Scope) (onVar : Option BindInfo) (lastRhs : Option MT) :
    Clause → M Tm
  | .fact f | .holds f => prop sc none f
  | .extremaOver items f noun v cond => do
    -- the class: the noun as written, or its singular
    let sing := noun.dropLast ++ (noun.getLast?.map singular).toList
    let nouns := (← get).nouns
    let some ni := (lookupWords nouns noun).orElse (fun _ => lookupWords nouns sing)
      | fail E.noun ((noun.intersperse [32]).flatten)
    let gty : Option Ty := ((← get).globs[ni]?).map (·.ty)
    let ty ← match gty with
      | some (.fn a .prop) => pure a
      | _ => fail E.type
    let p := Tm.glob ni
    -- `F` and `φ` about one element (`loc 0`), and about a second one (`loc 0`, the first `loc 1`)
    let sx := (v, ty) :: sc
    let fx ← asReal (← term F sx none f)
    let cx ← prop sx none cond
    let sy := (v, ty) :: (w!"", ty) :: sc
    let fy ← asReal (← term F sy none f)
    let cy ← prop sy none cond
    let parts ← items.mapM fun (isMax, x) => do
      let xv ← asReal (← term F sc none x)
      let x1 := shift 1 0 xv
      let x2 := shift 2 0 xv
      let bound := Tm.all ty (.imp (.app p (.loc 0)) (.imp cx (if isMax then .le fx x1 else .le x1 fx)))
      let uniq := Tm.all ty (.imp (.app p (.loc 0)) (.imp cy (.imp (.eq fy x2) (.eq (.loc 0) (.loc 1)))))
      pure (Tm.and bound (.ex ty (Elab.conjAll [.app p (.loc 0), cx, .eq fx x1, uniq])))
    pure (Elab.conjAll parts)
  | .every vs d body => do
    let bs ← binderInfos.everyIn sc vs d
    let p ← prop (scopeOf bs ++ sc) none body
    recordBounds bs body
    pure (wrap bs p)
  | .scoped f vs d eq => do
    let bs ← match d with
      | some d => binderInfos.everyIn sc vs d
      | none => pure []
    let sc' := scopeOf bs ++ sc
    let p ← prop sc' none f
    if !bs.isEmpty && (inequality f).isSome then modify fun st => { st with lastIneq := some (bs, f) }
    let p ← match eq with
      | some at_ => do
        let ineq ← liftO (inequality f) E.unsupported
        let e ← prop sc' none ineq
        let a ← prop sc' none at_
        pure (Tm.and p (.imp e a))
      | none => pure p
    pure (wrap bs p)
  | .extremum isMax fv s rels => do
    match fv with
    | .chain fm [(.eq, value)] => do
      let st ← subjectTm sc s
      let (core, ty, _) ← extremumTm sc isMax fm value st
      let s' ← coerce st.1 st.2 ty
      let extra ← rels.mapM fun r => match r with
        | .has m => prop sc (some (s', ty)) m
        | .pred ph o => predicate sc (s', ty) ph o
      modify fun st' => { st' with
        extrema := st'.extrema ++ [(c.ctx.env, ⟨isMax, fm, value⟩)], subject := some (s', ty) }
      pure (conjAll (core :: extra))
    | _ => fail E.unsupported
  | .increases (.mapsto pat body) a b => do
    let (aty, apred) ← domainOf false a
    let (bty, bpred) ← domainOf false b
    if bty != .real then fail E.unsupported
    let (fn, _) ← Elab.lam F sc pat [aty] (some .real) body
    let fn := onDomain apred fn
    let fx : Tm := .app (shift 1 0 fn) (.loc 0)
    let into := Tm.all aty (Tm.mkImp (holdsAt apred (.loc 0)) (holdsAt bpred fx))
    let fxx : Tm := .app (shift 2 0 fn) (.loc 1)
    let fyy : Tm := .app (shift 2 0 fn) (.loc 0)
    let ltA : Tm := if aty == .unit then .lt (.ofUnit (.loc 1)) (.ofUnit (.loc 0)) else .lt (.loc 1) (.loc 0)
    let mono := Tm.all aty (.all aty (Tm.mkImp (holdsAt apred (.loc 1)) (Tm.mkImp (holdsAt apred (.loc 0))
      (.imp ltA (.lt fxx fyy)))))
    let onto := Tm.all .real (Tm.mkImp (holdsAt bpred (.loc 0)) (.ex aty (Tm.mkAnd (holdsAt apred (.loc 0))
      (.eq (.app (shift 2 0 fn) (.loc 0)) (.loc 1)))))
    pure (conjAll [into, mono, onto])
  | .deriv d positive cond => do
    let some v := onVar | fail E.referent
    let some rhs := lastRhs | fail E.referent
    let some ip := v.pred | fail E.unsupported
    let (g, _) ← Elab.lam F sc (.id v.name) [.real] (some .real) rhs
    let g := match g with | .lam t _ b => Tm.lam t (.app ip (.loc 0)) b | g => g
    let dt ← asReal (← term F sc none d)
    let ct ← prop sc none cond
    let hd := Tm.app (.app (.app (.app (.prim .hasDerivWithin) g) ip) (.loc 0)) dt
    let sign := if positive then Tm.lt (.num 0) dt else Tm.lt dt (.num 0)
    pure (.and hd (.imp ct sign))
  | .noOther noun x isMax => do
    let ex ← findExtremum c.target isMax
    let some ni := lookupWords (← get).nouns noun | fail E.noun ((noun.intersperse [32]).flatten)
    let xt ← term F sc none x
    let u ← attainsOnly sc ex xt false
    match u with
    | .all ty (.imp p rest) =>
      if p == .app (.glob ni) (.loc 0) then pure u
      else pure (.all ty (.imp (.and (.app (.glob ni) (.loc 0)) p) rest))
    | u => pure u
  | .onlyAttains x => do
    let isMax ← match (← get).topic with
      | .maximum => pure true | .minimum => pure false | .none => fail E.referent
    let ex ← findExtremum c.target isMax
    let xt ← term F sc none x
    attainsOnly sc ex xt true
  | .sends (.mapsto (.id v) body) fm gm => do
    let some (ty, p) ← pfDomain 16 fm | fail E.unsupported
    let sc' := (v, ty) :: sc
    let (mt, mty) ← term F sc' none body
    let mt ← coerce mt mty ty
    let lhs ← asReal (← term F sc' (some (mt, ty)) fm)
    let rhs ← asReal (← term F sc' (some (.loc 0, ty)) gm)
    pure (.all ty (.imp (holdsAt p (.loc 0)) (.eq lhs rhs)))
  | .pred s ph o => do
    let st ← subjectTm sc s
    predicate sc st ph o
  | .onlyWith s noun conds var => do
    let some ni := lookupWords (← get).nouns noun | fail E.noun ((noun.intersperse [32]).flatten)
    let (st, sty) ← subjectTm sc s
    -- with a variable, the conditions are about it; otherwise about the subject
    let sc' := (var.getD w!"", sty) :: sc
    let ay ← conds.mapM fun c => match var with
      | some _ => prop sc' none c
      | none => prop sc' (some (.loc 0, sty)) c
    let atS ← conds.mapM fun c => match var with
      | some _ => do pure (Tm.app (.lam sty .tt (← prop sc' none c)) st)
      | none => prop sc (some (st, sty)) c
    let uniq := Tm.all sty (.imp (.app (.glob ni) (.loc 0)) (.imp (conjAll ay) (.eq (.loc 0) (shift 1 0 st))))
    pure (conjAll ([Tm.app (.glob ni) st] ++ atS ++ [uniq]))
  | .everyNP np body inner => do
    let mb := match np with
      | [.m ts] => Grammar.binderMath ts
      | _ => none
    let bs ← match mb with
      -- `every $(x,z)\in[0,1]^2$ satisfies φ`
      | some (vs, d) => binderInfos (.every vs d)
      | none => do
        let b ← nounPhrase np
        if b.name.isEmpty then fail E.unsupported
        pure [b]
    -- `… for all $u,v\in A$`, inside
    let ibs := (← inner.mapM binderInfos).flatten
    let p ← prop (scopeOf ibs ++ scopeOf bs ++ sc) none body
    recordBounds (bs ++ ibs) body
    pure (wrap bs (wrap ibs p))
  | .sharp => do
    let some (bs, ms) := (← get).lastBounds | fail E.referent
    let k := bs.length
    -- for every ε > 0 (`loc k` under the binders), some element has `larger - smaller < ε`
    let sc' := scopeOf bs ++ (w!"", .real) :: sc
    let parts ← ms.mapM fun m => do
      let some (a, b) := ineqSides m | fail E.unsupported
      let at_ ← asReal (← term F sc' none a)
      let bt ← asReal (← term F sc' none b)
      let body := Tm.lt (.sub bt at_) (.loc k)
      let exs := bs.foldr (fun bi acc => Tm.ex bi.ty (Tm.mkAnd (holdsAt bi.pred (.loc 0)) acc)) body
      pure (Tm.all .real (.imp (.lt (.num 0) (.loc 0)) exs))
    pure (conjAll parts)
  | .equalityOn s => do
    let some (bs, ineq) := (← get).lastIneq | fail E.referent
    let some e := inequality ineq | fail E.referent
    let sc' := scopeOf bs ++ sc
    let ep ← prop sc' none e
    let (st, sty) ← term F sc' none s
    let k := bs.length
    let rec memb : Tm → Ty → List (Tm × Ty) → M Tm
      | t, .prop, [] => pure t
      | t, .fn a r, (x, xt) :: xs => do memb (.app t (← coerce x xt a)) r xs
      | _, _, _ => fail E.type
    let mem ← memb st sty ((List.range k).reverse.zip (bs.map (·.ty)) |>.map fun (j, t) => (Tm.loc j, t))
    pure (wrap bs (.iff ep mem))
  | .equalityWhen φ => do
    let some (bs, ineq) := (← get).lastIneq | fail E.referent
    let some e := inequality ineq | fail E.referent
    let sc' := scopeOf bs ++ sc
    let ep ← prop sc' none e
    let q ← prop sc' none φ
    pure (wrap bs (.iff ep q))
  | .ifThen cond cl => do
    let h ← prop sc none cond
    let p ← clauseTm c sc onVar lastRhs cl
    pure (.imp h p)
  | .notions s names disj => do
    let st ← get
    unless names.all (fun n => (st.notions.lookup n).isSome || knownStart st (nameChunks n)) do fail E.prose
    let x ← term F sc none s
    -- a name the article does not define is an adjective of the vocabulary
    let notions := (← get).notions
    let ps ← names.mapM fun n =>
      if (notions.lookup n).isSome then notionApp x n else
      tryCatch (vocabPredicate sc x (nameChunks n)) fun e =>
        if e.code == E.ambiguous then throw e else fail E.prose n.flatten
    pure (if disj then disjAll ps else conjAll ps)
  | .thereIs b cl => do
    let bs ← binderInfos b
    let p ← clauseTm c (scopeOf bs ++ sc) onVar lastRhs cl
    pure (bs.foldr (fun b acc => Tm.ex b.ty (match b.pred with
      | some q => .and (.app q (.loc 0)) acc
      | none => acc)) p)
  | .existsNP np unique cl => do
    let b ← match ← pdeNoun np with
      | some [b] => pure b
      | _ => nounPhrase np sc
    if b.name.isEmpty then fail E.unsupported
    -- `P x`: the noun phrase and the clause about `x`
    let inner ← match cl with
      | some cl => clauseTm c ((b.name, b.ty) :: sc) onVar lastRhs cl
      | none => pure .tt
    let P := Tm.lam b.ty .tt (.and (holdsAt b.pred (.loc 0)) inner)
    let body := if unique then
        Tm.and (.app (shift 1 0 P) (.loc 0))
          (.all b.ty (.imp (.app (shift 2 0 P) (.loc 0)) (.eq (.loc 0) (.loc 1))))
      else Tm.app (shift 1 0 P) (.loc 0)
    pure (.ex b.ty body)
  | .existsNPs nps cls => do
    -- the objects, each NP after the ones before it
    let mut bs : List BindInfo := []
    for np in nps do
      let outer := (bs.map fun b => (b.name, b.ty)).reverse ++ sc
      match ← pdeNoun np with
      | some more => bs := bs ++ more
      | none =>
        -- a noun phrase that is not the vocabulary's makes the sentence prose
        let b ← tryCatch (nounPhrase np outer) fun e =>
          if e.code == E.noun || e.code == E.unsupported then fail E.prose else throw e
        bs := bs ++ [b]
    let sc' := (bs.map fun b => (b.name, b.ty)).reverse ++ sc
    let ps ← clauseTms c sc' onVar lastRhs cls
    -- (the predicate of each object refers to the objects before it)
    pure (bs.foldr (fun b acc => Tm.ex b.ty (match b.pred with
      | some q => .and (.app (shift 1 0 q) (.loc 0)) acc
      | none => acc)) (Elab.conjAll ps))
  | .noneExist cl => do pure (.not (← clauseTm c sc onVar lastRhs cl))
  | .forEveryNP cl np => do
    let b ← nounPhrase np sc
    if b.name.isEmpty then fail E.unsupported
    let p ← clauseTm c (scopeOf [b] ++ sc) onVar lastRhs cl
    pure (wrap [b] p)
  | .isA s np neg => do
    -- words with which no phrase of the vocabulary starts are prose
    unless knownStart (← get) np do fail E.prose
    let x ← term F sc none s
    -- words that are not the vocabulary's are prose
    let p ← tryCatch (vocabPredicate sc x np) fun e =>
      if e.code == E.noun || e.code == E.unsupported then fail E.prose e.detail else throw e
    pure (if neg then .not p else p)
  | .everyIs np names disj => do
    let b ← nounPhrase np
    let ps ← names.mapM (notionApp (.loc 0, b.ty))
    pure (wrap [b] (if disj then disjAll ps else conjAll ps))
  | .iff p q => do pure (.iff (← prop sc none p) (← prop sc none q))
  | .compare l r rr => do relTm r (← term F sc none l) (← term F sc none rr)
  | .adjectives s adjs => do
    let (t, ty) ← term F sc none s
    -- a function's domain is the one its definition states
    let defDom : Option Tm ← match Elab.symKey s with
      | some k => do
        match ← lookupGlob k with
        | some (_, g) => pure (g.doms.head?).join
        | none => pure none
      | none => pure none
    let ps ← adjs.mapM fun (a, on) =>
      -- the standard adjectives, else the vocabulary's (`even` of an integer)
      tryCatch (adjectiveTm sc t ty defDom a on) fun e =>
        if on.isSome then throw e else
        tryCatch (vocabPredicate sc (t, ty) (nameChunks a)) fun e' =>
          if e'.code == E.ambiguous then throw e' else throw e
    pure (conjAll ps)
  | .extremumOf isMax value f s at_ rels => do
    let fm ← match f with
      | some fm => pure fm
      | none => match (← get).lastExtremum with
        | some fm => pure fm
        | none => fail E.referent
    let st ← subjectTm sc s
    let (core, ty, _) ← extremumTm sc isMax fm value st
    let s' ← coerce st.1 st.2 ty
    let atP ← match at_ with
      | some a => do pure [← prop sc (some (s', ty)) a]
      | none => pure []
    let extra ← rels.mapM fun r => match r with
      | .has m => prop sc (some (s', ty)) m
      | .pred ph o => predicate sc (s', ty) ph o
    modify fun st' => { st' with
      extrema := st'.extrema ++ [(c.ctx.env, ⟨isMax, fm, value⟩)], subject := some (s', ty),
      lastExtremum := some fm }
    pure (conjAll (core :: atP ++ extra))
  | .increasing maps => do
    let mut parts := []
    let mut infos := []
    for m in maps do
      match m with
      | .mapsto (.id v) body => do
        let some b := (← get).envBinders.find? (·.name == v) | fail E.free v
        let (fn, _) ← Elab.lam F sc (.id v) [b.ty] (some .real) body
        let fn := onDomain b.pred fn
        let fxx : Tm := .app (shift 2 0 fn) (.loc 1)
        let fyy : Tm := .app (shift 2 0 fn) (.loc 0)
        let ltA : Tm := if b.ty == .unit then .lt (.ofUnit (.loc 1)) (.ofUnit (.loc 0)) else .lt (.loc 1) (.loc 0)
        parts := parts ++ [Tm.all b.ty (.all b.ty (Tm.mkImp (holdsAt b.pred (.loc 1))
          (Tm.mkImp (holdsAt b.pred (.loc 0)) (.imp ltA (.lt fxx fyy)))))]
        infos := infos ++ [(v, body)]
      | _ => fail E.unsupported
    modify fun st => { st with lastMaps := infos }
    pure (conjAll parts)
  | _ => fail E.unsupported

/-- Several clauses in the same scope (structural, so that the kernel evaluates it). -/
def clauseTms (c : SentCtx) (sc : Scope) (onVar : Option BindInfo) (lastRhs : Option MT) :
    List Clause → M (List Tm)
  | [] => pure []
  | cl :: rest => do
    let p ← clauseTm c sc onVar lastRhs cl
    pure (p :: (← clauseTms c sc onVar lastRhs rest))
end

/-- `for $v\in D$, the k-th ranges over $B$`: the image of `D` under the `k`-th map
of the preceding sentence is `B`. -/
def rangesTm (sc : Scope) (k : Nat) (bind : BindInfo) (target : MT) : M Tm := do
  let some (v, body) := (← get).lastMaps[k]? | fail E.referent
  if v != bind.name then fail E.referent v
  let (fn, _) ← Elab.lam F sc (.id v) [bind.ty] (some .real) body
  let fn := onDomain bind.pred fn
  let fv : Tm := .app (shift 1 0 fn) (.loc 0)
  let inner ← Elab.term.member F ((v, bind.ty) :: sc) (fv, .real) target
  let into := Tm.all bind.ty (Tm.mkImp (holdsAt bind.pred (.loc 0)) inner)
  let inB ← Elab.term.member F ((w!"", .real) :: sc) (.loc 0, .real) target
  let onto := Tm.all .real (.imp inB (.ex bind.ty (Tm.mkAnd (holdsAt bind.pred (.loc 0))
    (.eq (.app (shift 2 0 fn) (.loc 0)) (.loc 1)))))
  pure (.and into onto)

def rhsOf : Clause → Option MT
  | .fact (.chain _ rs) | .scoped (.chain _ rs) _ _ _ => rs.getLast?.map (·.2)
  | _ => none

def citesOf (cl : CClause) : List Codes := cl.cites

/-- The claims of one sentence. `exactly one` takes the following clauses into its scope. -/
def claimSentence (c : SentCtx) (topic : Topic) (binds : List Bind) (cls : List CClause) : M (List Nat) := do
  modify fun st => { st with topic := if topic == .none then st.topic else topic }
  -- `If $φ$, …` about variables that are already bound (by the result or a fixed
  -- variable) is a hypothesis: of the first clause when a later clause has its own,
  -- otherwise of every clause
  let st0 ← get
  let known := st0.envBinders.map (·.name) ++ (st0.fixed.filter (·.1 == c.ctx.sec)).map (·.2.name)
  let isHyp (b : Bind) : Bool := match b with
    | .ifCond φ =>
      let fr := ((freeIds 64 [] φ).filter fun n => !(st0.globs.any fun g => g.key == n && !g.family)).eraseDups
      !fr.isEmpty && fr.all known.contains
    | _ => false
  let hyps := binds.filter isHyp
  let binds := binds.filter (!isHyp ·)
  let laterIf := (cls.drop 1).any fun cl => match cl.clause with | .ifThen .. => true | _ => false
  let cls := hyps.foldr (fun h acc => match h with
    | .ifCond φ =>
      if laterIf then match acc with
        | cl :: rest => { cl with clause := Clause.ifThen φ cl.clause } :: rest
        | [] => []
      else acc.map fun cl => { cl with clause := Clause.ifThen φ cl.clause }
    | _ => acc) cls
  let bs ← bindersInfos binds
  -- `On I,`: the sentence's single free variable ranges over I
  let onVar ← match binds.find? (fun b => match b with | .on _ => true | _ => false) with
    | some (.on d) => do
      let (_, p) ← domainOf true d
      let known := (scopeOf bs).map (·.1)
      let st ← get
      let free := (cls.flatMap (fun cl => (clauseMaths cl.clause).flatMap (freeIds 64 known))).eraseDups
      let free := free.filter fun n => !(st.globs.any (·.key == n))
      match free with
      | [v] => pure (some (⟨v, .real, p⟩ : BindInfo))
      | _ => fail E.free free.flatten
    | _ => pure none
  -- variables bound by the opening binders of the current result carry over to
  -- its later sentences (`For $w\in[0,1]$, … . In particular, … w …`), and a
  -- variable introduced in a proof (`Let $x\in A$.`) to the proof's later steps
  let st ← get
  let inResult := match c.ctx.kind with | .result _ => true | _ => false
  let inScope := match c.ctx.kind with | .result _ | .proof => true | _ => false
  let inherited ← if inScope && !st.envBinders.isEmpty then do
      let known := (scopeOf (bs ++ onVar.toList)).map (·.1)
      let clBound := cls.flatMap fun cl => (cl.binds.flatMap fun b => match b with
        | .every vs _ => vs | _ => []) ++ (match cl.clause with
          | .scoped _ vs _ _ | .every vs _ _ => vs | _ => [])
      let free := (cls.flatMap (fun cl => clauseFree st (known ++ clBound) cl)).eraseDups
      -- a variable of the result shadows a definition of the same name
      let free := free.filter fun n => st.envBinders.any (·.name == n) || !(st.globs.any fun g => g.key == n && !g.family)
      pure (usedBinders st.envBinders free)
    else pure []
  if inResult && !bs.isEmpty then
    modify fun st => { st with envBinders := bs ++ st.envBinders.filter fun b => !(bs.any (·.name == b.name)) }
  let allBs := inherited ++ bs ++ onVar.toList
  let sc := scopeOf allBs
  let rec go : Nat → List CClause → Option MT → M (List Nat)
    | 0, _, _ => pure []
    | _ + 1, [], _ => pure []
    | g + 1, cl :: rest, last =>
      match cl.clause with
      | .exactlyOne noun v cond sat => do
        let some ni := lookupWords (← get).nouns noun | fail E.noun ((noun.intersperse [32]).flatten)
        let gty : Option Ty := ((← get).globs[ni]?).map (·.ty)
        let ty ← match gty with
          | some (.fn a .prop) => pure a
          | _ => fail E.type
        let sx := (v, ty) :: sc
        let cx ← prop sx none cond
        let sx' ← prop sx none sat
        let sy := (v, ty) :: sx
        let cy ← prop sy none cond
        let sy' ← prop sy none sat
        let uniq := Tm.all ty (.imp (.app (.glob ni) (.loc 0)) (.imp cy (.imp sy' (.eq (.loc 0) (.loc 1)))))
        modify fun st => { st with subject := some (.loc 0, ty) }
        -- the remaining clauses are in the scope of the unique element
        let inner ← rest.mapM fun cl' => clauseTm c sx none none cl'.clause
        let body := Tm.ex ty (conjAll ([Tm.app (.glob ni) (.loc 0), cx, sx', uniq] ++ inner))
        let id ← emit c (wrap allBs body) (cl.cites ++ rest.flatMap (·.cites))
        pure [id]
      | .ranges k target => do
        -- the binder of the map's variable (of the clause, or of the sentence) restricts
        -- the map's domain
        let some (v, _) := (← get).lastMaps[k]? | fail E.referent
        let cbs := (← bindersInfos cl.binds)
        let some b := (cbs ++ allBs).find? (·.name == v) | fail E.referent v
        let outer := (if cbs.isEmpty then allBs else inherited).filter (·.name != v)
        let p ← rangesTm (scopeOf outer) k b target
        let id ← emit c (wrap outer p) cl.cites
        let ids ← go g rest last
        pure (id :: ids)
      | k => do
        -- the variables of the clause's own binders, and the domains they range over
        let cbVars := cl.binds.flatMap fun b => match b with
          | .every vs _ => vs
          | .many bs => bs.flatMap fun b => match b with | .every vs _ => vs | _ => []
          | _ => []
        let cbDoms := cl.binds.flatMap fun b => match b with
          | .every _ d => [d]
          | .many bs => bs.filterMap fun b => match b with | .every _ d => some d | _ => none
          | _ => []
        -- a clause with its own binder is not in the scope of the sentence's opening
        -- binders; inherited binders bind the variables the clause uses
        let own := match k with | .scoped _ vs _ _ | .every vs _ _ => vs | _ => []
        -- `equality holds …` binds the variables of the inequality it refers to
        let stNow ← get
        let own := own ++ (if usesIneq k then ((stNow.lastIneq.map (·.1.map (·.name))).getD []) else [])
        let free := clauseFree stNow ((scopeOf bs).map (·.1) ++ cbVars ++ own) cl
        -- a domain of the clause's binders may use a variable of the result (`for every $v\in[0,s]$`)
        let domFree := (cbDoms.flatMap (freeIds 64 [])).filter fun n => !(stNow.globs.any (·.key == n))
        let inh := usedBinders inherited (free ++ domFree)
        let hasOwn := !cl.binds.isEmpty
        let outer := if hasOwn then inh else inh ++ bs ++ onVar.toList
        let cbs := (← bindersInfos cl.binds outer)
        -- definitions inside the clause (`the mean $G\coloneqq\sqrt{ab}$`) and after it
        -- (`…, where $d\coloneqq …$`), in the scope of its binders
        let k ← inlineClause c (outer ++ cbs) cl.defs k
        -- `\forall I\in A\ \exists C_I: φ` with `C_I` a generic constant: the convention
        -- places the constant (after `I`, before the variables it is uniform in)
        let stG ← get
        let isGen (key : Codes) : Bool := stG.genericConsts.any fun g =>
          key == g.base || key.take (g.base.length + 1) == g.base ++ [95]
        let k := match k with
          | .fact (.quant true vs dom (.quant false gs _ body)) | .holds (.quant true vs dom (.quant false gs _ body))
          | .scoped (.quant true vs dom (.quant false gs _ body)) [] none none =>
            if !gs.isEmpty && gs.all isGen then Clause.scoped body vs (some dom) none else k
          | .fact (.quant false gs _ body) | .holds (.quant false gs _ body)
          | .scoped (.quant false gs _ body) [] none none =>
            if !gs.isEmpty && gs.all isGen then Clause.fact body else k
          | _ => k
        -- generic constants (`C_m`): existential, after the binders of their indices
        let bases := stG.genericConsts.map (·.1)
        let gens := if bases.isEmpty then [] else
          ((clauseMaths k).flatMap (genericsOf bases 64)).filter (fun (key, _) =>
            !(stG.globs.any (·.key == key)) && !((outer ++ cbs).any (·.name == key)))
        let gens := gens.foldl (fun acc g => if acc.any (·.1 == g.1) then acc else acc ++ [g]) []
        -- the convention of a constant: the latest for its letter
        let convOf (key : Codes) : GenericConst :=
          ((stG.genericConsts.filter fun g => key == g.base || key.take (g.base.length + 1) == g.base ++ [95]).getLast?).getD {base := key}
        let gbs : List (BindInfo × GenSpec) := gens.map fun (key, idx) =>
          let g := convOf key
          let pred : Option Tm := if g.sign == 1 then some (.lam .real .tt (.lt (.num 0) (.loc 0)))
            else if g.sign == 2 then some (.lam .real .tt (.le (.num 0) (.loc 0))) else none
          (⟨key, .real, pred⟩, { allowed := idx ++ g.deps, fixedOk := g.fixedOk, uniform := g.uniform, strict := g.strict })
        -- a clause's own binder that a constant may depend on (its index: `… for every
        -- integer $m\ge0$`) binds before the constant: it becomes a binder of the claim
        let mayDepend (vs : List Codes) : Bool := gbs.any fun (_, s) => s.allowed.any vs.contains
        let (k, ownBs) ← match k with
          | .scoped f vs (some d) eq =>
            if mayDepend vs then do
              let bis ← binderInfos.everyIn (scopeOf (outer ++ cbs)) vs d
              pure (Clause.scoped f [] none eq, bis)
            else pure (k, [])
          | .forEveryNP c' np => do
            if gens.isEmpty then pure (k, []) else
            let b ← nounPhrase np (scopeOf (outer ++ cbs))
            if mayDepend [b.name] then pure (c', [b]) else pure (k, [])
          | _ => pure (k, [])
        let fixedNames := stG.fixed.map (·.2.name)
        let some order := placeGenerics gbs (outer ++ cbs ++ ownBs) fixedNames
          | fail E.unsupported
        let p ← clauseTm c (scopeOf (order.map (·.1))) onVar last k
        -- an inequality about the bound variables is the referent of a later
        -- `equality holds exactly when …`
        match k with
        | .fact f | .holds f | .scoped f [] none _ =>
          if !(outer ++ cbs).isEmpty && (inequality f).isSome then
            modify fun st => { st with lastIneq := some (outer ++ cbs, f) }
        | _ => pure ()
        let id ← emit c (if gens.isEmpty then wrap (outer ++ cbs) p else wrapMixed order p) cl.cites
        let ids ← go g rest (match rhsOf k with | some r => some r | none => last)
        pure (id :: ids)
  go 16 cls none

/-- A convention of the article: a noun the article names (`By a distribution we mean
a probability distribution on $\mathbb{N}_0$.`), which is a class like the article's
own, or words that stand for other words in the following sentences (`Throughout,
increasing means non-decreasing.`). -/
def meaningDef (ws : List Codes) (rhs : List Chunk) (noun : Bool) : M (List Nat × List Nat) := do
  if noun then
    let b ← nounPhrase rhs
    if !b.name.isEmpty then fail E.unsupported b.name
    let p := b.pred.getD (.lam b.ty .tt .tt)
    let i ← addGlob ⟨[], .fn b.ty .prop, [none], false⟩ p
    let plural := ws.dropLast ++ (ws.getLast?.map (· ++ [115])).toList
    modify fun st => { st with nouns := st.nouns ++ [(ws, i), (plural, i)], classes := st.classes ++ [(ws, i)] }
    pure ([i], [])
  else
    let toks ← rhs.mapM fun c => match c with
      | .w w => pure (Tok.word w)
      | .p c => pure (Tok.punct c)
      | _ => fail E.unsupported
    modify fun st => { st with wordAliases := st.wordAliases ++ [(ws, toks)] }
    pure ([], [])

/-- Compile one sentence: definitions and claims, or a reason it has none. -/
def sentence (c : SentCtx) (s : Sent) : M (List Nat × List Nat) := do
  match s with
  | .defClass sym plural np => defClass sym plural np
  | .defIs b items => do
    let bs ← binderInfos b
    let [bi] := bs | fail E.unsupported
    -- `the X and the Y are DISPLAY` with one definition each
    let items := items.flatMap fun it => match it.defn with
      | .conj xs =>
        let parts := (it.name.splitOn w!"and").map fun ws => ws.filter (· != w!"the")
        if parts.length == xs.length then (xs.zip parts).map fun (x, n) => ({ it with defn := x, name := n } : DefItem)
        else xs.map fun x => ({ it with defn := x } : DefItem)
      | _ => [it]
    let rs ← items.mapM (defItem c bi)
    pure (rs.flatMap (·.1), rs.flatMap (·.2))
  | .constDefs b defs labels => do
    match b with
    | some bd => do
      -- inside a result or a proof (`For $v\in[0,s]$ and $w\in[0,1-s]$, set $g_v(w)\coloneqq…$`
      -- with `s` bound by the result), the variables it uses are implicit parameters
      let env := (← get).envBinders
      let maths := defs ++ (match bd with
        | .every _ d => [d]
        | .many bs => bs.filterMap fun b => match b with | .every _ d => some d | _ => none
        | _ => [])
      -- a variable of the result (it shadows a definition of the same name)
      let used := (maths.flatMap (freeIds 64 [])).eraseDups.filter fun n => env.any (·.name == n)
      let imp := if c.ctx.kind == .text then [] else usedBinders env used
      let bis ← match bd with
        | .many bs => bindersInfos (bs.map id) imp
        | .every vs d => bindersInfos [.every vs d] imp
        | bd => binderInfos bd
      let binderNames := bis.map (·.name)
      let imp := imp.filter fun b => !binderNames.contains b.name
      match bis with
      | [bi] => if imp.isEmpty then constDefs c (some bi) defs labels else multiDefs bis defs labels imp
      | _ :: _ :: _ => multiDefs bis defs labels imp
      | [] => fail E.unsupported
    | none => constDefs c none defs labels
  | .defByFamily b sg pieces labels => do
    let [bi] ← binderInfos b | fail E.unsupported
    defByFamily c bi sg pieces labels
  | .defReads b _ sg disp labels => do
    let [bi] ← binderInfos b | fail E.unsupported
    defReads c bi sg disp labels
  | .defBy sg pieces labels obs => defBy c sg pieces labels obs
  | .denotedBy name sym => denotedBy name sym
  | .letDenote b sym np => do
    let [bi] ← binderInfos b | fail E.unsupported
    letDenote bi sym np
  | .weSay sb ph o cond vs d => weSay sb ph o cond vs d
  | .defSteps b sets sym np whereDef => do
    let [bi] ← binderInfos b | fail E.unsupported
    let mut ds := []
    let mut cs := []
    for m in sets do
      let (d', c') ← setDef c bi m
      ds := ds ++ d'
      cs := cs ++ c'
    if let some (sg, disp, ls) := whereDef then
      let (d', c') ← defReads c bi sg disp ls
      ds := ds ++ d'
      cs := cs ++ c'
    let (d', c') ← letDenote bi sym np
    pure (ds ++ d', cs ++ c')
  | .claims topic binds cls => do
    -- definitions made inside the sentence (`where`, `the mean $G\coloneqq …$`)
    let n0 := (← get).globs.length
    let ids ← claimSentence c topic binds cls
    let n1 := (← get).globs.length
    pure ((List.range (n1 - n0)).map (n0 + ·), ids)
  | .fix b defs labels => do
    let [bi] ← binderInfos b | fail E.unsupported
    modify fun st => { st with fixed := (c.ctx.sec, bi) :: st.fixed.filter (·.2.name != bi.name) }
    if defs.isEmpty then pure ([], []) else constDefs c (some bi) defs labels
  | .defNotion subj name abbr cond => defNotion subj name abbr cond
  | .defMember subj cls cond binds => defMember subj cls cond binds
  | .notionSubject subj => do
    -- only the running text introduces the subject of later notions
    if c.ctx.kind != .text then fail E.prose
    let s ← tryCatch (nounPhrase subj) fun _ => fail E.prose
    if s.name.isEmpty then fail E.prose
    modify fun st => { st with notionSubject := some s }
    pure ([], [])
  | .assumeAll binds defs => do
    let bs := (← bindersInfos binds)
    match c.ctx.kind with
    | .text =>
      modify fun st => { st with fixed := bs.map (c.ctx.sec, ·) ++ st.fixed.filter fun (_, x) => !(bs.any (·.name == x.name)) }
    | _ =>
      modify fun st => { st with envBinders := bs ++ st.envBinders.filter fun x => !(bs.any (·.name == x.name)) }
    let st ← get
    let scope := match c.ctx.kind with
      | .text => (st.fixed.filter (·.1 == c.ctx.sec)).map (·.2)
      | _ => st.envBinders
    let ds ← defs.mapM (inlineDef c scope)
    pure (ds, [])
  | .assume b => do
    let bs ← binderInfos b
    match c.ctx.kind with
    | .text =>
      modify fun st => { st with fixed := bs.map (c.ctx.sec, ·) ++ st.fixed.filter fun (_, x) => !(bs.any (·.name == x.name)) }
    | _ =>
      modify fun st => { st with envBinders := bs ++ st.envBinders.filter fun x => !(bs.any (·.name == x.name)) }
    pure ([], [])
  | .notation .. => fail E.unsupported
  | .meaning ws rhs noun => meaningDef ws rhs noun
  | .generic ms deps uni => do
    let bases ← ms.mapM fun (m, sign) => match m with
      | .id k => pure (k, sign)
      | .sub (.id k) _ => pure (k, sign)
      | _ => fail E.unsupported
    -- the variables of the formulas of a list (`$j,I$`)
    let varsOf (tss : List (List MTok)) : M (List Codes) := do
      let parts := tss.flatMap fun ts => (Grammar.topCommas (ts.length + 1) 0 [] ts []).filter (!·.isEmpty)
      parts.mapM fun p => do
        let some m := Math.parseFormula p | fail E.unsupported
        let some k := Elab.symKey m | fail E.unsupported
        pure k
    -- the dependencies: variables, and the fixed data (a phrase with `fixed`); a phrase
    -- that names neither is not read
    let (strict, depVars, fixedOk) ← match deps with
      | some (ms', ws) => do
        if ws.any (fun w => !w.contains w!"fixed") then fail E.dependence ((ws.find? (fun w => !w.contains w!"fixed")).getD [] |>.intersperse [32] |>.flatten)
        pure (true, ← varsOf ms', !ws.isEmpty)
      | none => pure (false, [], true)
    -- uniform in: variables; phrases only beside the list of dependencies (which already
    -- excludes them)
    if !strict && !uni.2.isEmpty then fail E.dependence ((uni.2.headD []).intersperse [32] |>.flatten)
    let uniVars ← varsOf uni.1
    if uniVars.any depVars.contains then fail E.unsupported
    let gcs : List GenericConst := bases.map fun (b, sign) =>
      { base := b, sign, deps := depVars, strict, fixedOk, uniform := uniVars }
    modify fun st => { st with genericConsts := st.genericConsts.filter (fun g => !bases.any (·.1 == g.base)) ++ gcs }
    pure ([], [])
  | .defDeriv b sets names dom cod anchors derivs labels => do
    let bi ← match b with
      | some bd => do
        let [bi] ← binderInfos bd | fail E.unsupported
        pure (some bi)
      | none =>
        -- the variable of the names' subscripts, fixed earlier in the section
        match names.head? with
        | some (.sub (.id _) (.id p)) => do
          match (← get).fixed.find? (fun (s, x) => s == c.ctx.sec && x.name == p) with
          | some (_, x) => pure (some x)
          | none => fail E.free p
        | _ => pure none
    let (d1, c1) ← match bi, sets with
      | _, [] => pure ([], [])
      | some x, _ => constDefs c (some x) sets []
      | none, _ => fail E.unsupported
    let (d2, c2) ← defDeriv bi names dom cod anchors derivs labels
    pure (d1 ++ d2, c1 ++ c2)

/-- `We write $T$ for $F$`, `We write $T$ if $F$`: the template `T` stands for the
formula `F` (in braces). `We write $T$ for the NAME`: a notion of the vocabulary,
whose variables are those of `T`, or `the set of NOUNS`, a class; it becomes a
definition of the article, and `T` stands for it. -/
def notationDef (toks : List PTok) (kind : Nat) (rhs : List Chunk) : M (List Nat × List Nat) := do
  let fs := Notation.formulas (toks.length + 1) toks []
  let some pat := fs.head? | fail E.unsupported
  let st ← get
  let push (tpl : Template) : M Unit := do
    if !tpl.pat.any (fun it => match it with | .fixed _ => true | _ => false) then fail E.unsupported
    modify fun st => { st with templates := st.templates ++ [tpl] }
  if kind == 2 then
    let key : Codes := w!"@n" ++ (toString st.templates.length).toList.map Char.toNat
    let V := st.vocab
    let cands := V.notions.filterMap fun n => (Notation.matchSlots n.name rhs []).map fun a => ((n, a), [])
    match ← theMeaning (fun (na : Notion × List (List MTok)) => (na.1.ty, na.1.value)) (·.1.field) rhs cands with
    | some ((n, args), _) => do
      -- each argument is a variable of the pattern, or a fixed value
      -- (`We write $NF$ for the derivative of $F$ in the direction $(\sqrt2-1,1)$.`)
      let fixedArgs ← args.mapM fun a => match Notation.varTok a with
        | some _ => pure none
        | none => do
          let some m := Math.parseFormula a | fail E.unsupported
          let (v, vty) ← term F [] none m
          pure (some (v, vty))
      let ts := (args.zip fixedArgs).filterMap fun (a, c) => if c.isSome then none else Notation.varTok a
      let rec argTys : Ty → List Ty
        | .fn a b => a :: argTys b
        | _ => []
      let tys := argTys n.ty
      let k := ts.length
      let varTys : List Ty := ((tys.zip fixedArgs).filter (fun (p : Ty × Option (Tm × Ty)) => p.2.isNone)).map (·.1)
      let allDoms : List (Option Tm) := n.doms ++ List.replicate tys.length none
      let varDoms : List (Option Tm) := ((allDoms.zip fixedArgs).filter
        (fun (p : Option Tm × Option (Tm × Ty)) => p.2.isNone)).map (·.1)
      -- the arguments in order: the pattern's variables as locals, the fixed values as given
      let rec place : Nat → List (Option (Tm × Ty)) → List Ty → List (Tm × Ty)
        | _, [], _ => []
        | j, none :: cs, t :: tys => (.loc (k - 1 - j), t) :: place (j + 1) cs tys
        | j, some c :: cs, _ :: tys => c :: place j cs tys
        | _, _, [] => []
      let (body, resTy) ← applyAll n.value n.ty n.doms (place 0 fixedArgs tys)
      let value := varTys.foldr (fun t b => Tm.lam t .tt b) body
      let gty := varTys.foldr (fun t r => Ty.fn t r) resTy
      let pat' := Notation.items ts (pat.map (·.tok))
      let key := match Notation.symbolOf pat' with
        | some k => if st.globs.any (·.key == [92] ++ k) then key else k
        | none => key
      -- a notation that starts with a letter (`N\varphi`) is that letter
      let letter : Option Nat := match pat' with
        | .fixed (.mvar c) :: .slot _ :: _ => if st.globs.any (·.key == [c]) then none else some c
        | _ => none
      let gkey := match letter with | some c => [c] | none => [92] ++ key
      let i ← addGlob ⟨gkey, gty, varDoms, false⟩ (if fixedArgs.all (·.isNone) then n.value else value)
      let slots := (List.range ts.length).map TItem.slot
      let call : List TItem := if slots.isEmpty then [] else
        [.fixed (.msym 40)] ++ (slots.intersperse (.fixed (.msym 44))) ++ [.fixed (.msym 41)]
      push ⟨pat', .fixed (match letter with | some c => .mvar c | none => .cmd key) :: call⟩
      pure ([i], [])
    | none =>
      -- `the set|class of NOUNS`
      let rest ← match rhs with
        | .w a :: .w b :: r => if (a == w!"set" || a == w!"class") && b == w!"of" then pure r else fail E.noun (((wordsOf rhs).intersperse [32]).flatten)
        | _ => fail E.noun (((wordsOf rhs).intersperse [32]).flatten)
      let cands := V.nouns.filterMap fun n => match matchPhrase n.plural rest with
        | some (_, []) => some (n, [])
        | _ => none
      match ← theMeaning (fun (n : Noun) => (n.ty, n.pred)) (·.field) rest cands with
      | some (n, _) => do
        let pat' := pat.map (TItem.fixed ·.tok)
        let key := match Notation.symbolOf pat' with
          | some k => if st.globs.any (·.key == [92] ++ k) then key else k
          | none => key
        let i ← addGlob ⟨[92] ++ key, .fn n.ty .prop, [], false⟩ n.pred
        push ⟨pat.map (TItem.fixed ·.tok), [.fixed (.cmd key)]⟩
        pure ([i], [])
      | none => fail E.noun (((wordsOf rest).intersperse [32]).flatten)
  else
    let some repl := fs[1]? | fail E.unsupported
    let tpl := Notation.template pat repl
    match tpl.pat, tpl.repl with
    -- `We write $A\subset B$ if $A\subseteq B$`: one relation symbol for another, in
    -- place (the arguments are whatever stands on either side)
    | [.slot a, .fixed t, .slot b], [.slot a', .fixed t', .slot b'] =>
      if a == a' && b == b' && a != b then push ⟨[.fixed t], [.fixed t']⟩
      else push { tpl with repl := .fixed .lbrace :: tpl.repl ++ [.fixed .rbrace] }
    | _, _ => push { tpl with repl := .fixed .lbrace :: tpl.repl ++ [.fixed .rbrace] }
    pure ([], [])

end Compile

/-- The state of the compiler between sentences. -/
structure CState where
  st : St
  /-- Index of the next sentence. -/
  idx : Nat := 0
  /-- Outcomes of the sentences read so far, latest first. -/
  outcomesRev : List Outcome := []
  proofs : List ProofInfo := []
  deriving Inhabited, Lean.ToExpr

/-- Environment index of each result, by label (for proofs that name their result). -/
def envTable (ss : List Sentence) : List (Codes × Nat) :=
  ss.filterMap fun s => match s.ctx.kind with
    | .result _ => some (s.ctx.label, s.ctx.env)
    | _ => none

open Compile in
/-- Compile one sentence. A failing sentence leaves no trace in the state. -/
def compileOne (envs : List (Codes × Nat)) (c : CState) (s : Sentence) : CState :=
  -- entering a new environment resets proof-local state
  let st0 := c.st
  let proved : Option Nat := match s.ctx.kind with
    | .proof => envs.lookup s.ctx.proves
    | _ => none
  -- a proof starts with the variables of the result it proves
  let inheritedBinders : List BindInfo := match proved with
    | some e => (st0.resultBinders.lookup e).getD []
    | none => []
  let st0 := if st0.proofEnv != s.ctx.env then
      { st0 with proofEnv := s.ctx.env, proofCites := [], proofSteps := [], topic := Topic.none, envBinders := inheritedBinders }
    else st0
  -- definitions local to a result are visible in it and in its proof
  let st0 := { st0 with curEnv := s.ctx.env, curProved := proved }
  let ps := match s.ctx.kind with
    | .proof => if c.proofs.any (·.env == s.ctx.env) then c.proofs
      else c.proofs ++ [({ env := s.ctx.env, proves := s.ctx.proves, steps := [], cites := [], complete := true } : ProofInfo)]
    | _ => c.proofs
  let incomplete (ps : List ProofInfo) : List ProofInfo :=
    ps.map fun p => if p.env == s.ctx.env then { p with complete := false } else p
  -- `satisfying \eqref{l}`, with `l` a display of the same sentence: that display
  let expanded := Notation.expandRefs (Notation.labelledDisplays (s.toks.length + 1) s.toks [])
    (s.toks.length + 1) s.toks
  let s := { s with toks := expanded }
  -- the article's notations, in the formulas of later sentences
  let toks0 := s.toks
  let s := if st0.templates.isEmpty || Notation.declares s.toks then s
    else { s with toks := Notation.rewriteAll st0.templates s.toks }
  let s := if st0.wordAliases.isEmpty then s
    else { s with toks := Notation.rewriteWords st0.wordAliases (s.toks.length + 1) none s.toks }
  match Grammar.parseSentence s with
  | none => { c with st := st0, idx := c.idx + 1, outcomesRev := .prose :: c.outcomesRev, proofs := incomplete ps }
  | some sent =>
    let sc : SentCtx := ⟨s.ctx, (envs.lookup s.ctx.proves).getD 0, c.idx⟩
    let labelled : M (List Nat × List Nat) := do
      let (ds, cs) ← match sent with
        | .notation k rhs => Compile.notationDef toks0 k rhs
        | _ => Compile.sentence sc sent
      match sent with
      | .claims _ _ _ =>
        -- labels of displays in the sentence, and of the enclosing result, name its claims
        let ls := s.toks.filterMap fun p => match p.tok with | .ref .label l => some l | _ => none
        let ls := match s.ctx.kind with
          | .result _ => if s.ctx.label.isEmpty then ls else s.ctx.label :: ls
          | _ => ls
        Compile.addLabels ls cs false
      | .defNotion .. =>
        -- the displays of a notion's definition: citing them cites the definition
        let ls := s.toks.filterMap fun p => match p.tok with | .ref .label l => some l | _ => none
        Compile.addLabels ls [] true
      | _ => pure ()
      pure (ds, cs)
    let (r, st) := labelled.run.run st0
    match r with
    | .ok (ds, cs) =>
      let ps := ps.map fun p => if p.env == s.ctx.env then
        { p with steps := st.proofSteps, cites := st.proofCites } else p
      let saved := (s.ctx.env, st.envBinders) :: st.resultBinders.filter (·.1 != s.ctx.env)
      let st := match s.ctx.kind with
        | .result _ => { st with resultBinders := saved }
        | _ => st
      -- the subject of an unread notion is kept, and the sentence stays prose
      let o : Outcome := match sent with
        | .notionSubject _ => .prose
        | _ => .compiled ds cs
      { st, idx := c.idx + 1, outcomesRev := o :: c.outcomesRev, proofs := ps }
    | .error e =>
      let o : Outcome := if e.code == E.prose then .prose else .failed e
      { c with st := st0, idx := c.idx + 1, outcomesRev := o :: c.outcomesRev, proofs := incomplete ps }

/-- Compile a list of sentences, starting from a compiler state. -/
def compileAll (envs : List (Codes × Nat)) (c : CState) (ss : List Sentence) : CState :=
  ss.foldl (compileOne envs) c

theorem compileAll_append (envs : List (Codes × Nat)) (c : CState) (a b : List Sentence) :
    compileAll envs c (a ++ b) = compileAll envs (compileAll envs c a) b := by
  simp [compileAll, List.foldl_append]

/-- Results whose printed proof compiled completely: the proof is their premise. -/
def closeProofs (ss : List Sentence) (claims : List Claim) (ps : List ProofInfo) : List Claim :=
  claims.map fun cl =>
    match cl.role with
    | .statement env =>
      let label := (ss.find? (fun s => s.ctx.env == env)).map (·.ctx.label) |>.getD []
      match ps.find? (fun p => p.proves == label && p.complete && !p.steps.isEmpty) with
      | some p => { cl with premises := (p.steps ++ p.cites).eraseDups }
      | none => cl
    | _ => cl

def beginDocument (ts : List PTok) : List PTok :=
  match ts.findIdx? (fun t => t.tok == .begin w!"document") with
  | some i => ts.drop (i + 1)
  | none => ts

/-- The document of a compiled article, from the final compiler state. -/
def finish (ss : List Sentence) (c : CState) : Doc :=
  let st := c.st
  let claims := closeProofs ss st.claims c.proofs
  ⟨st.globs, st.values, claims, ss.map (fun s => (s.ctx, s.start, s.stop)), c.outcomesRev.reverse,
    st.labels, c.proofs, st.preds ++ st.named ++ st.ops ++ st.classes ++ st.notions⟩

/-- Compile the sentences of an article into its document. -/
def assemble (V : Vocab) (ss : List Sentence) : Doc :=
  finish ss (compileAll (envTable ss) { st := { vocab := V } } ss)

def isBeginDocument (l : Codes) : Bool := l.take 16 == w!"\\begin{document}"

/-- Lex and segment the paragraph blocks in order: the completed sentences, the
final math-mode stack and the segmentation state. -/
def lexSeg (ms : Macros) : List (Nat × List Codes) → List Bool → Segment.St →
    Option (List Sentence × List Bool × Segment.St)
  | [], m, s => some ([], m, s)
  | (p, ls) :: bs, m, s =>
    match lexBlock ms (joinLines ls) m with
    | none => none
    | some (t, m') =>
      let r := segBlock p (t ++ blockBreak m') s
      match lexSeg ms bs m' r.2 with
      | none => none
      | some (rest, m'', s'') => some (r.1 ++ rest, m'', s'')

theorem lexSeg_nil (ms : Macros) (m : List Bool) (s : Segment.St) : lexSeg ms [] m s = some ([], m, s) := rfl

theorem lexSeg_cons (ms : Macros) (p : Nat) (ls : List Codes) (b : Codes) (bs : List (Nat × List Codes))
    (m m' m'' : List Bool) (s s' s'' : Segment.St) (t : List PTok) (ss rest : List Sentence)
    (h0 : joinLines ls = b) (h1 : lexBlock ms b m = some (t, m')) (h2 : segBlock p (t ++ blockBreak m') s = (ss, s'))
    (h3 : lexSeg ms bs m' s' = some (rest, m'', s'')) :
    lexSeg ms ((p, ls) :: bs) m s = some (ss ++ rest, m'', s'') := by
  simp [lexSeg, h0, h1, h2, h3]

/-- The complete compilation of an article from its source lines, with the
vocabulary `V`: the preamble supplies the macros, the paragraphs after
`\begin{document}` the sentences. -/
def compileArticle (V : Vocab) (src : Source) : Option Doc := do
  let k ← src.findIdx? isBeginDocument
  let ms ← macrosOf (joinLines (src.take k))
  let bs := blocksOf (src.drop (k + 1)) (linesOffset (src.take (k + 1))) none []
  let (ss, _, s) ← lexSeg ms bs [] {}
  some (assemble V (ss ++ segFinish s))

/-- Staged kernel certificates compose to the compilation of the whole source. -/
theorem compileArticle_eq {V : Vocab} {src : Source} {k : Nat} {ms : Macros} {bs : List (Nat × List Codes)}
    {ss ss' : List Sentence} {m : List Bool} {s : Segment.St} {d : Doc}
    (h0 : src.findIdx? isBeginDocument = some k)
    (h1 : macrosOf (joinLines (src.take k)) = some ms)
    (h2 : blocksOf (src.drop (k + 1)) (linesOffset (src.take (k + 1))) none [] = bs)
    (h3 : lexSeg ms bs [] {} = some (ss, m, s)) (h4 : ss ++ segFinish s = ss') (h5 : assemble V ss' = d) :
    compileArticle V src = some d := by
  simp [compileArticle, h0, h1, h2, h3, h4, h5]

end Leanify
