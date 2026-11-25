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

/-- An atom with none, one, two, … of the scripts after it: each with the rest. -/
def scriptSteps : Nat → List PTok → List PTok → List (List PTok × List PTok)
  | 0, acc, ts => [(acc, ts)]
  | f + 1, acc, ts => (acc, ts) :: (match ts with
    | t :: r =>
      if t.tok == .msym 95 || t.tok == .msym 94 then
        match unit r with
        | some (u, r') => scriptSteps f (acc ++ [t] ++ u) r'
        | none => []
      else if t.tok == .msym 39 then scriptSteps f (acc ++ [t]) r
      else []
    | [] => [])

/-- A symbol (with a font: `\mathbf{x}`, `\mathcal P`, or the digits of a number) or a
group, without its scripts. -/
def atomBase (ts : List PTok) : Option (List PTok × List PTok) :=
  match ts with
  | t :: r =>
    match t.tok with
    | .cmd n => if Math.wFonts.contains n then (unit r).map fun (u, r') => (t :: u, r') else some ([t], r)
    | .mnum _ =>
      let ds := r.takeWhile fun p => match p.tok with | .mnum _ => true | _ => false
      some (t :: ds, r.drop ds.length)
    | _ => unit ts
  | [] => none

/-- An atom: a symbol or a group (`atomBase`), with its scripts. -/
def atom (ts : List PTok) : Option (List PTok × List PTok) := do
  let (base, rest) ← atomBase ts
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
  -- an argument in a subscript or a superscript is one token or one group, as in TeX:
  -- `r_k^{1/k}` is `r_k` to the power `1/k`
  | f + 1, .fixed t :: .slot k :: is, u :: ts, acc =>
    if u.tok != t then none
    else if t == .msym 95 || t == .msym 94 then do
      let (arg, r) ← unit ts
      matchItems f is r (← bind k arg acc)
    else matchItems f (.slot k :: is) ts acc
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
  -- `x^+` with the argument `x`: the symbol before the script, with as few of its own
  -- scripts as the notation leaves (`x_1^+` is `x_1` with the script `^+`)
  | .slot k :: .fixed t :: rest =>
    if t == .msym 95 || t == .msym 94 then do
      let (base, r) ← atomBase ts
      (scriptSteps (r.length + 1) base r).findSome? fun (arg, r') =>
        matchItems f (.fixed t :: rest) r' [(k, arg)]
    else do
      let (arg, r) ← atom ts
      matchItems f (.fixed t :: rest) r [(k, arg)]
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

/-- What a notation stands for, with each bound variable among `clash` renamed to a
letter that is not `used` (none if the letters run out). -/
def renameBound : List Tok → List Tok → List TItem → Option (List TItem)
  | [], _, repl => some repl
  | b :: bs, used, repl =>
    let letters : List Tok := ((List.range 26).map fun i => Tok.mvar (122 - i)) ++
      (List.range 26).map fun i => Tok.mvar (90 - i)
    match letters.find? (!used.contains ·) with
    | some fresh =>
      -- (not the letter of a name set in a font: `\mathcal{C}`)
      let toks : List Tok := repl.map fun it => match it with | .fixed u => u | .slot _ => .par
      let mask := fontMask (toks.length + 1) toks ++ List.replicate toks.length false
      renameBound bs (fresh :: used) ((repl.zip mask).map fun (it, inFont) =>
        if !inFont && it == .fixed b then .fixed fresh else it)
    | none => none

/-- Marks a notation that was not applied, before the variable it would capture. -/
def captureMark : Tok := .cmd w!"@captured"

/-- Replace every match of a template in the formulas of a token list. -/
def rewrite (tpl : Template) : Nat → List PTok → List PTok
  | 0, ts => ts
  | _ + 1, [] => []
  | f + 1, t :: ts =>
    if !t.math then t :: rewrite tpl f ts else
    match matchAt tpl.pat (t :: ts) with
    | some (args, rest) =>
      if rest.length < ts.length + 1 then
        -- an argument that uses a variable the notation binds: the bound variable gets
        -- another letter, so that it does not capture the argument's (`\ell_\beta(\beta(C))`
        -- with `\ell_A(x)` for `\min\{R(C) : …, A(C)=x\}`)
        let clash := tpl.binds.filter fun b => args.any fun (_, ps) => ps.any (·.tok == b)
        let used : List Tok := (t :: ts).map (·.tok) ++ tpl.repl.filterMap fun it =>
          match it with | .fixed u => some u | .slot _ => none
        match renameBound clash used tpl.repl with
        | some repl => substitute repl args t.pos ++ rewrite tpl f rest
        | none =>
          match args.findSome? fun (_, ps) => ps.find? fun p => tpl.binds.contains p.tok with
          | some p => ⟨captureMark, t.pos, true⟩ :: { p with pos := t.pos } :: t :: rewrite tpl f ts
          | none => substitute tpl.repl args t.pos ++ rewrite tpl f rest
      else t :: rewrite tpl f ts
    | none => t :: rewrite tpl f ts

/-- The variable of a notation that an argument would capture, if `rewrite` marked one. -/
def captured : List PTok → Option Tok
  | [] => none
  | a :: rest => if a.tok == captureMark then rest.head?.map (·.tok) else captured rest

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

/-- The formulas and displays of a sentence, each as its tokens. -/
def mathSegs : List PTok → List PTok → Bool → List (List PTok) → List (List PTok)
  | [], cur, inM, acc => (if inM then cur.reverse :: acc else acc).reverse
  | t :: ts, cur, inM, acc =>
    match t.tok with
    | .mopen => mathSegs ts [] true acc
    | .mclose => mathSegs ts [] false (cur.reverse :: acc)
    | .begin e =>
      if Lex.wDisplayEnvs.contains e then mathSegs ts [] true acc
      else mathSegs ts (if inM then t :: cur else cur) inM acc
    | .finish e =>
      if Lex.wDisplayEnvs.contains e then mathSegs ts [] false (cur.reverse :: acc)
      else mathSegs ts (if inM then t :: cur else cur) inM acc
    | _ => mathSegs ts (if inM then t :: cur else cur) inM acc

/-- The letter of a symbol with a subscript that a formula defines (`h_t(u,v)\coloneqq …`). -/
def definedLetter : List PTok → Option Nat
  | a :: b :: rest =>
    match a.tok, b.tok with
    | .mvar ch, .msym 95 => if rest.any (·.tok == .cmd w!"coloneqq") then some ch else none
    | _, _ => none
  | _ => none

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
  { pat := items args ptoks, repl := items args (repl.map (·.tok)) }

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

/-- The ending of an ordinal after a formula (`$n$th`, also written `$n$-th`). -/
def ordinalSuffix (w : Codes) : Bool := w == w!"th" || w == w!"st" || w == w!"nd" || w == w!"rd"

/-- The variables of a phrase, in order, as formulas of the sentence. -/
def matchSlots : Phrase → List Chunk → List (List MTok) → Option (List (List MTok))
  | [], [], acc => some acc.reverse
  | .w [45] :: ps, .p 45 :: cs, acc => matchSlots ps cs acc
  | .w [44] :: ps, .p 44 :: cs, acc => matchSlots ps cs acc
  | .w [47] :: ps, .p 47 :: cs, acc => matchSlots ps cs acc
  | .w w :: ps, .p 45 :: .w v :: cs, acc => if v == w && ordinalSuffix w then matchSlots ps cs acc else none
  | .w w :: ps, .w v :: cs, acc => if v == w then matchSlots ps cs acc else none
  | .m t :: ps, .m u :: cs, acc => if t == u then matchSlots ps cs acc else none
  | .f segs :: ps, .m u :: cs, acc => do
    let args ← splitSegs segs u
    matchSlots ps cs (args.reverse ++ acc)
  | .v :: ps, .m u :: cs, acc => matchSlots ps cs (u :: acc)
  | _, _, _ => none

/-- A phrase at the start of `cs`, with the formulas of its variables and what follows
(`on $v$ vertices` against `on $n+1$ vertices and …`). -/
def matchPrefix : Phrase → List Chunk → List (List MTok) → Option (List (List MTok) × List Chunk)
  | [], cs, acc => some (acc.reverse, cs)
  | .w [45] :: ps, .p 45 :: cs, acc => matchPrefix ps cs acc
  | .w [44] :: ps, .p 44 :: cs, acc => matchPrefix ps cs acc
  | .w [47] :: ps, .p 47 :: cs, acc => matchPrefix ps cs acc
  | .w w :: ps, .p 45 :: .w v :: cs, acc => if v == w && ordinalSuffix w then matchPrefix ps cs acc else none
  | .w w :: ps, .w v :: cs, acc => if v == w then matchPrefix ps cs acc else none
  | .m t :: ps, .m u :: cs, acc => if t == u then matchPrefix ps cs acc else none
  | .f segs :: ps, .m u :: cs, acc => do
    let args ← splitSegs segs u
    matchPrefix ps cs (args.reverse ++ acc)
  | .v :: ps, .m u :: cs, acc => matchPrefix ps cs (u :: acc)
  | _, _, _ => none

/-- A phrase with variables (`on $v$ vertices`, `$v\times v$`): a modifier of this kind
takes their values first. -/
def hasSlots (p : Phrase) : Bool := p.any fun i => match i with | .v | .f _ => true | _ => false

/-- `f a₁ … aₙ`, β-reduced where `f` is a closed λ without a domain (the predicate of a
modifier with variables, applied to their values and to the object). -/
def betaApply : Tm → List Tm → Tm
  | .lam _ .tt b, a :: as => betaApply (Tm.subst a 0 b) as
  | f, as => as.foldl .app f

/-- The head of a term applied to arguments, β-reduced where it is a λ without a domain, through
the guards of the arguments (`(λ m n. [m = n] I_n) x x` is `[x = x] I_x`): what a notation that
fixes or repeats arguments of a notion stands for. -/
def headBeta : Nat → Tm → Tm
  | 0, t => t
  | f + 1, .app g a =>
    match headBeta f g with
    | .lam _ .tt b => headBeta f (Tm.subst a 0 b)
    | .guard c g' => .guard c (headBeta f (.app g' a))
    | g' => .app g' a
  | f + 1, .guard c e => .guard c (headBeta f e)
  | _, t => t

/-- The types of the first `k` arguments of a predicate (its leading λs): those of the
variables of a modifier (`$v$-regular`: a number; `orthogonal to $v$`: a vector). -/
def slotTys : Nat → Tm → List Ty
  | 0, _ => []
  | k + 1, .lam t _ b => t :: slotTys k b
  | k + 1, _ => .real :: slotTys k .tt

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
  -- (an accent before its argument, `\overline{A}`: the accent; a subscript keeps its brace,
  -- `\phi_{\mu,v}` and `\phi` being two symbols)
  let toks := match toks.reverse with
    | .lbrace :: .cmd c :: rest => (Tok.cmd c :: rest).reverse
    | _ => toks
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

/-- `On the event $φ$, [we have] $ψ$`: for all values of the sample, `φ` implies `ψ`
(the formula `\@onevent{φ}{ψ}`, which the vocabulary of the unit square reads with the two
sequences `U`, `V` of a sample). The words become `we have` before that formula. -/
def onEvent : Nat → List PTok → List PTok
  | 0, ts => ts
  | _ + 1, [] => []
  | f + 1, t :: ts =>
    let isW (p : PTok) (w : Codes) : Bool := !p.math && (match p.tok with | .word v => Grammar.lower v == w | _ => false)
    let hit : Option (List PTok × List PTok × List PTok) :=
      match ts with
      | a :: b :: o :: rest =>
        if isW t w!"on" && isW a w!"the" && isW b w!"event" && o.tok == .mopen then
          let phi := rest.takeWhile (·.tok != .mclose)
          let r1 := rest.drop (phi.length + 1)
          let r1 := match r1 with | c :: r => if c.tok == .punct 44 then r else r1 | [] => r1
          let r1 := match r1 with
            | x :: y :: r => if isW x w!"we" && isW y w!"have" then r else r1
            | _ => r1
          match r1 with
          | o2 :: r2 =>
            if o2.tok == .mopen then
              let psi := r2.takeWhile (·.tok != .mclose)
              if phi.isEmpty || psi.isEmpty || psi.length == r2.length then none
              else some (phi, psi, r2.drop (psi.length + 1))
            else none
          | [] => none
        else none
      | _ => none
    match hit with
    | some (phi, psi, rest) =>
      let m (k : Tok) : PTok := ⟨k, t.pos, true⟩
      [⟨.word w!"we", t.pos, false⟩, ⟨.word w!"have", t.pos, false⟩, ⟨.mopen, t.pos, false⟩, m (.cmd w!"@onevent"), m .lbrace] ++
        phi ++ [m .rbrace, m .lbrace] ++ psi ++ [m .rbrace, ⟨.mclose, t.pos, false⟩] ++ onEvent f rest
    | none => t :: onEvent f ts

end Notation

namespace Compile


def intervalPred (lo hi : Tm) : Tm := .lam .real .tt (Elab.interval lo hi (.loc 0))

/-- A closed constant bound (numerals and their negations). -/
def constTm : MT → Option Tm
  | .num n => some (.num n)
  | .neg (.num n) => some (.neg (.num n))
  | .frac (.num a) (.num b) => some (.div (.num a) (.num b))
  | _ => none

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

/-- The name of a variable chunk: a letter, a command (`\gamma`), `\hat x`, or a letter
with a subscript that is a letter or a number (`d_0`, `n_k`: the name a bound on it
binds, as in `$d_0\ge1$`). -/
def varName : List MTok → Option Codes
  | [.id v] => some v
  | [.cmd c] => some ([92] ++ c)
  | ts => match Grammar.hatName ts with
    | some (v, []) => some v
    | _ => Grammar.subNameOf ts

/-- Match a vocabulary phrase at the start of `cs`. The variable slot matches a
variable chunk (returned) or nothing. -/
def matchPhrase : Phrase → List Chunk → Option (Option (List MTok) × List Chunk)
  | [], cs => some (none, cs)
  | .w [45] :: ps, .p 45 :: cs => matchPhrase ps cs
  | .w [44] :: ps, .p 44 :: cs => matchPhrase ps cs
  | .w [47] :: ps, .p 47 :: cs => matchPhrase ps cs
  -- (`$n$-th` for `$n$th`)
  | .w w :: ps, .p 45 :: .w v :: cs => if v == w && Notation.ordinalSuffix w then matchPhrase ps cs else none
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

/-- `theMeaning`, where the entries with the words that the type of their arguments does
not fit are left out first (`fits` elaborates them; nothing it changes is kept): `the
inverse of $A$` is the inverse of a matrix for a matrix `A` and of a permutation for a
permutation, in a vocabulary that has both. Several meanings that fit are an error. -/
def theMeaningBy {α β : Type} [BEq β] (key : α → β) (field : α → Codes) (fits : α → M Unit)
    (cs : List Chunk) (cands : List (α × List Chunk)) (defn : Bool := false) : M (Option (α × List Chunk)) := do
  match (cands.map (·.2.length)).min? with
  | none => pure none
  | some k =>
    let best := cands.filter (·.2.length == k)
    let distinct := best.foldl (fun acc c => if acc.any (fun d => key d.1 == key c.1) then acc else acc ++ [c]) []
    match distinct with
    | [c] => pure (some c)
    | _ =>
      let st ← get
      let fit ← distinct.filterM fun c => do
        let ok ← tryCatch (do fits c.1; pure true) fun _ => pure false
        set st
        pure ok
      match fit with
      | [c] => pure (some c)
      | [] =>
        let ws := wordsOf (cs.take (cs.length - k))
        -- (a definition whose letters have no type yet: the noun before a letter gives it)
        if defn then
          fail E.finding (quoted ws ++ w!" has a meaning for each kind of argument (in " ++
            fieldsText (distinct.map (field ·.1)) ++
            w!"): say the kind of the argument with a noun before its letter (… of a permutation $\\sigma$)")
        else
          fail E.ambiguous (quoted ws ++ w!" has several meanings (in " ++
            fieldsText (distinct.map (field ·.1)) ++ [41])
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

/-- The words at the front of a phrase that the article or its vocabulary know: the
modifiers before a noun and the noun (`finite set` in `finite set with at least two
elements`). The result is these words, whether a noun is among them, and the words
after them. A finding names a noun as unknown only if it is. -/
def knownHead (V : Vocab) (own : List (List Codes × Nat)) (ws : List Codes) :
    List Codes × Bool × List Codes :=
  let shortest (rs : List (List Chunk)) : Option (List Chunk) :=
    rs.foldl (fun best r => match best with
      | some b => if r.length < b.length then some r else some b
      | none => some r) none
  -- (the longest noun at the front: of the article, or of the vocabulary)
  let nounAt (cs : List Chunk) : Option (List Chunk) :=
    shortest (((matchWords own cs).map (·.2)).toList ++ V.nouns.filterMap fun n =>
      ((matchPhrase n.sing cs) <|> (matchPhrase n.plural cs)).bind fun (_, r) =>
        if r.length < cs.length then some r else none)
  let modAt (cs : List Chunk) : Option (List Chunk) :=
    match cs with
    | .w w :: r => if w == w!"fixed" then some r else
      shortest (V.mods.filterMap fun m => if m.prenominal then
          (matchPhrase m.phrase cs).bind fun (v, r) =>
            if v.isNone && r.length < cs.length then some r else none
        else none)
    | _ => none
  let rec go : Nat → List Chunk → Bool × List Chunk
    | 0, cs => (false, cs)
    | f + 1, cs =>
      match nounAt cs with
      | some r => (true, r)
      | none =>
        match modAt cs with
        | some r => go f r
        | none => (false, cs)
  let (noun, rest) := go 6 (ws.map Chunk.w)
  (ws.take (ws.length - rest.length), noun, wordsOf rest)

/-- The finding for a phrase that was not read as a noun phrase. If its noun is known,
the noun is not what stopped the sentence: the finding says which words were read and
which were not. -/
def nounFinding (V : Vocab) (own : List (List Codes × Nat)) (e : Err) : Err :=
  let ws := (e.detail.splitOn 32).filter (!·.isEmpty)
  let (head, noun, rest) := knownHead V own ws
  if head.isEmpty then e
  else if noun && rest.isEmpty then
    ⟨E.nounWords, quoted head ++ w!" is a noun of the vocabulary, but this use of it is not read"⟩
  else if noun then
    ⟨E.nounWords, quoted head ++ w!" is read, but not the words after it (" ++ quoted rest ++ [41]⟩
  else if rest.isEmpty then
    ⟨E.nounWords, quoted head ++ w!" has no noun here: say what it qualifies (every positive integer $n$)"⟩
  else e

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
  -- an interval that is a type of the article's vocabulary (`[0,1]` in `unitsquare`)
  if let some iv ← (if calculus then pure none else Elab.intervalType d) then return (iv.ty, none)
  match d with
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
      -- an open interval, whose ends may use the variables bound before (`(0,c)`)
      let l ← if Elab.isInfty false lo then pure none else some <$> closedBound lo sc
      let h ← if Elab.isInfty true hi then pure none else some <$> closedBound hi sc
      pure (.real, some (.lam .real .tt (Elab.rayTm (l.map (shift 1 0)) (h.map (shift 1 0)) true true (.loc 0))))
    | .id n => do
      -- the real numbers, and all the elements of a vocabulary's type (`\mathbb{C}`)
      if n == w!"\\mathbb{R}" then pure (.real, none) else
      if let some s := (← get).vocab.symbols.find? (fun s => s.sym == n && s.const.isNone) then
        pure (s.ty, none) else
      -- (a set that a sentence binds: `Let $U$ be an open set`, then `there is $x\in U$`)
      if let some (i, .fn a .prop) := Elab.lookupLocal sc n then pure (a, some (.loc i)) else
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

/-- The predicate of a sequence whose terms, for the integers from `l` to `h`, satisfy
`p`: `fun x => ∀ i, i ∈ ℤ ∧ l ≤ i ≤ h → p (x i)`. `l` and `h` are shifted by `k` into
the scope of `i` (2 for terms of the scope the predicate is stated in, 3 for terms of the
scope outside its variable); `p` is a term of that scope or the predicate of an element
stated where its variable is bound. -/
def seqPred (k : Nat) (l h : Tm) (p : Option Tm) : Tm :=
  let i := Tm.loc 0
  let range := Tm.and (.app (.prim .isInt) i) (.and (.le (shift k 0 l) i) (.le i (shift k 0 h)))
  let elem := match p with
    | some p => Tm.app (shift 2 0 p) (.app (.loc 1) i)
    | none => .tt
  .lam (.fn .real .real) .tt (.all .real (.imp range elem))

/-- The type and predicate of the domain of the variables `vs` of a binder: `domainOf`,
or, for a sequence (`x_1,\ldots,x_n\in A`, `@seq lo hi A`), a real function whose terms
`x_i`, for the integers `i` from `lo` to `hi`, are in `A`. The sequences are recorded
(and the other variables forgotten as sequences). -/
def binderDomain (vs : List Codes) (d : MT) (sc : Scope := []) : M (Ty × Option Tm) := do
  match d with
  | .app (.id s) [lo, hi, d'] =>
    if s != w!"@seq" then domainOf false d sc else do
    let (ty, p) ← domainOf true d' sc
    if ty != .real then fail E.unsupported
    let l ← closedBound lo sc
    let h ← closedBound hi sc
    modify fun st => { st with seqs := vs.map (·, lo, hi) ++ st.seqs.filter fun e => !vs.contains e.1 }
    pure (.fn .real .real, some (seqPred 2 l h p))
  | _ => do
    modify fun st => { st with seqs := st.seqs.filter fun e => !vs.contains e.1 }
    domainOf false d sc

def lamWrap : List Ty → Tm → Tm
  | [], b => b
  | t :: ts, b => .lam t .tt (lamWrap ts b)

/-- Functions of arguments with the given domains (a predicate each, or none). -/
def lamWrapD : List (Ty × Option Tm) → Tm → Tm
  | [], b => b
  | (t, p) :: ts, b => .lam t (match p with | some p => .app p (.loc 0) | none => .tt) (lamWrapD ts b)

/-! ### Natural domains

`T_w(x)\coloneqq\begin{cases}…\end{cases}` and `\Delta(x,z)\coloneqq\varphi(x)+\psi(z)-c(x,z)`
say nothing about `x` and `z`. An argument without a stated domain ranges over the values
at which the definition says something: where one of its cases applies, and where the
functions on its right side are defined. -/

/-- The conditions of a definition by cases without an `otherwise`. -/
def caseConds : Tm → Option (List Tm)
  | .cases c _ rest => (caseConds rest).map (c :: ·)
  | .undef _ => some []
  | _ => none

/-- What the body of a definition asks of its arguments. -/
def naturalConds (v : Tm) : List Tm :=
  match caseConds v with
  | some (c :: cs) => [cs.foldl (fun acc q => Tm.or acc q) c]
  | _ => (Tm.conjuncts (Tm.defined v)).filter fun c => match c with
      | .imp _ _ | .all _ _ | .not .tt => false
      | _ => true

/-- Remove the `l` innermost variables from a term that does not mention them. -/
def lowerBy : Nat → Tm → Tm
  | 0, t => t
  | l + 1, t => lowerBy l (Tm.subst (.num 0) 0 t)

/-- The natural domains of the `n` innermost variables of the body `v` (the arguments of a
definition, the last one innermost), for those that have none in `given`: a condition of
`v` is a condition on the last argument that it mentions. -/
def naturalPreds (given : List (Ty × Option Tm)) (v : Tm) : List (Ty × Option Tm) :=
  let n := given.length
  let conds := naturalConds v
  given.zipIdx.map fun ((ty, p), j) =>
    match p with
    | some _ => (ty, p)
    | none =>
      if ty != .real then (ty, none) else
      let l := n - 1 - j
      let mine := conds.filterMap fun c =>
        let low := lowerBy l c
        -- (it mentions none of the later arguments, and it mentions this one)
        if Tm.shift l 0 low == c && Tm.shift 1 0 (Tm.subst (.num 0) 0 low) != low then some low else none
      if mine.isEmpty then (ty, none)
      else (ty, some (.lam ty .tt (Tm.shift 1 1 (Elab.conjAll mine))))

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
def varChunk (ts : List MTok) (outer : Scope := []) : M (Codes × Option (Ty × Option Tm)) := do
  match varName ts with
  | some v => pure (v, none)
  | none =>
    match Grammar.binderMath ts with
    -- (the bound may use the variables bound outside: `every integer $b\ge b_0$`; like
    -- the conditions after `with`, its predicate is stated where the variable is bound,
    -- one binder further in than `outer`)
    | some ([v], dom) => do
      let (ty, p) ← domainOf false dom outer
      pure (v, some (ty, p.map (shift 1 0)))
    | _ => fail E.unsupported

/-- `$φ$ [and $ψ$]`: the conditions after `with` in a noun phrase. -/
def condsOf : Nat → List Chunk → List MT → List MT × List Chunk
  | 0, cs, acc => (acc.reverse, cs)
  | f + 1, cs, acc =>
    match Grammar.formula cs with
    | some (m, r) =>
      -- `$φ$, $ψ$, or $χ$`: one of them
      match Grammar.orTail 6 r [] with
      | some (tl, r') =>
        let ms := tl.filterMap fun c => match c with
          | .m ts => Grammar.formula [.m ts] |>.map (·.1)
          | _ => none
        ((ms.foldl (fun a b => MT.lor a b) m :: acc).reverse, r')
      | none =>
      match r with
      | .w w :: r' => if w == w!"and" then condsOf f r' (m :: acc) else ((m :: acc).reverse, r)
      | _ => ((m :: acc).reverse, r)
    | none => (acc.reverse, cs)

/-- Read a noun phrase (without its determiner). -/
def nounPhrase1Core (np : List Chunk) (outer : Scope := []) : M BindInfo := do
  -- `fixed` before a noun phrase marks a parameter: the binder is the same without it
  -- (`for every fixed real $c>0$`)
  let np := match np with
    | .w w :: c :: rest => if w == w!"fixed" then c :: rest else np
    | _ => np
  -- `every $x\in[0,1]$` in a list of binders (`for every positive integer $n$ and every
  -- $x\in[0,1]$`): a variable and its domain
  match np with
  | [.m ts] =>
    match Grammar.binderMath ts with
    | some ([v], d) => do
      -- (the predicate is stated where the variable is bound)
      let (ty, p) ← binderDomain [v] d outer
      return ⟨v, ty, p.map (shift 1 0)⟩
    | _ => pure ()
  | _ => pure ()
  -- `Let $M$ be the midpoint of $A$ and $B$` (the binder `@the midpoint of $A$ and $B$ $M$`):
  -- the variable is the value of a notion of the vocabulary, with its arguments
  match np with
  | .w w :: rest =>
    if w == w!"@the" then
      let some (.m vts) := rest.getLast? | fail E.unsupported
      let some v := varName vts | fail E.unsupported
      let cs := rest.dropLast
      let V := (← get).vocab
      let cands := V.notions.filterMap fun n => (Notation.matchSlots n.name cs []).map fun a => ((n, a), [])
      let elabArgs (args : List (List MTok)) : M (List (Tm × Ty)) := args.mapM fun a => do
        let some m := Math.parseFormula a | fail E.unsupported
        Elab.term 100000 outer none m
      let fits (na : Notion × List (List MTok)) : M Unit := do
        let _ ← applyAll na.1.value na.1.ty na.1.doms (← elabArgs na.2)
      match ← theMeaningBy (fun (na : Notion × List (List MTok)) => (na.1.ty, na.1.value)) (·.1.field) fits cs cands with
      | some ((n, args), _) =>
        let ts ← elabArgs args
        let (val, vty) ← applyAll n.value n.ty n.doms ts
        -- (the value is in the scope of the variables before this one)
        let k := if outer.isEmpty then 1 else 2
        -- a number or an object of a field's type; a function or a set, value by value
        let ptwise (a : Ty) (isSet : Bool) : Tm :=
          let l := Tm.app (.loc 1) (.loc 0)
          let r := Tm.app (shift (k + 1) 0 val) (.loc 0)
          Tm.all a (if isSet then .iff l r else .eq l r)
        let body? : Option Tm :=
          if vty == .real || Elab.isBase vty then some (Tm.eq (.loc 0) (shift k 0 val)) else
          match vty with
          | .fn a .prop => some (ptwise a true)
          -- (a function of two points, `let $C$ be the copula associated with $\gamma$`)
          | .fn a (.fn a2 b2) =>
            if b2 == .real || Elab.isBase b2 then
              some (Tm.all a (Tm.all a2 (Tm.eq (.app (.app (.loc 2) (.loc 1)) (.loc 0))
                (.app (.app (shift (k + 2) 0 val) (.loc 1)) (.loc 0)))))
            else none
          | .fn a b => if b == .real || Elab.isBase b then some (ptwise a false) else none
          | _ => none
        let some body := body? | fail E.unsupported
        return ⟨v, vty, some (Tm.lam vty .tt body)⟩
      | none => fail E.noun ((wordsOf cs).intersperse [32]).flatten
  | _ => pure ()
  -- `every $M_r$`, `for every fixed $l$`: no noun says what the variable ranges over
  if (wordsOf np).isEmpty then
    fail E.finding w!"a variable without a noun or a domain: say what it ranges over (every integer $n$, every $x\\in A$)"
  -- `every such $\gamma$`: the conditions are in an earlier sentence
  if (wordsOf np).head? == some w!"such" then
    fail E.finding w!"`such` refers to conditions stated earlier: state them here (every $x$ with …)"
  -- `a small $\zeta>0$`: how small is not said
  if (wordsOf np).head? == some w!"small" || (wordsOf np).head? == some w!"large" then
    fail E.finding w!"`small` and `large` alone are not read: say `sufficiently small` (`large`), or give a bound"
  let st ← get
  let V := st.vocab
  -- `a set of measure zero $S$` (as `Let $S$ be a set of measure zero` is read): a modifier
  -- that follows its noun stands after the variable
  let rec hoist : Nat → List Chunk → List Chunk
    | 0, np => np
    | f + 1, np =>
      match np.getLast? with
      | some (.m v) =>
        let ws := np.dropLast
        let words (cs : List Chunk) : Bool := cs.all fun c => match c with | .w _ | .p 45 => true | _ => false
        -- (a modifier with formulas, `a vector in $\mathbb{R}^n$ $x$`: the shortest ending of
        -- the words that is one, after words only)
        if !words ws then
          let hitS := (List.range ws.length).findSome? fun k0 =>
            let k := k0 + 1
            if k ≥ ws.length then none else
            let head := ws.take (ws.length - k)
            let tail := ws.drop (ws.length - k)
            if !words head then none else
            if V.mods.any (fun m => !m.prenominal && Notation.hasSlots m.phrase &&
                (Notation.matchSlots m.phrase tail []).isSome) then some k else none
          match hitS with
          | some k => hoist f (ws.take (ws.length - k) ++ [.m v]) ++ ws.drop (ws.length - k)
          | none => np
        else
        -- (a noun with a hyphen, `right-hand side Lipschitz in the second variable`)
        let hit := V.mods.findSome? fun m =>
          if m.prenominal || Notation.hasSlots m.phrase || m.phrase.length ≥ ws.length then none else
          let tail := ws.drop (ws.length - m.phrase.length)
          match matchPhrase m.phrase tail with
          | some (none, []) => some m.phrase.length
          | _ => none
        match hit with
        | some k => hoist f (ws.take (ws.length - k) ++ [.m v]) ++ ws.drop (ws.length - k)
        | none => np
      | _ => np
  let np := hoist 3 np
  -- prenominal modifiers
  -- (each is the list of the vocabulary's modifiers with those words: the noun's type
  -- decides between them)
  let rec pre : Nat → List Chunk → List (List Chunk × List Modifier) → List (List Chunk × List Modifier) × List Chunk
    | 0, cs, acc => (acc.reverse, cs)
    | f + 1, cs, acc =>
      let cands := V.mods.filterMap (fun m => if m.prenominal then
          if Notation.hasSlots m.phrase then (Notation.matchPrefix m.phrase cs []).map fun (_, r) => (m, r) else
          (matchPhrase m.phrase cs).bind fun (v, r) => if v.isNone then some (m, r) else none
        else none)
      match (cands.map (·.2.length)).min? with
      | some k => pre f (cs.drop (cs.length - k)) ((cs, (cands.filter (·.2.length == k)).map (·.1)) :: acc)
      | none => (acc.reverse, cs)
  let (pmAll, rEnd) := pre 4 np []
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
  -- the head: an article class, a vocabulary noun, or a variable with a signature
  -- (the article's own classes take precedence over the vocabulary's nouns)
  -- (`implicit`: adjectives of numbers came before, so a variable alone is a real number)
  let headOf (r00 : List Chunk) (implicit : Bool) : M ((Ty × List Tm × Option (List MTok) × List Chunk) × List Nat) := do
    let (nms, r0) := preN 4 r00 []
    let h : Ty × List Tm × Option (List MTok) × List Chunk ← do
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
        -- (`a function $A:\CC\to\mathbb{R}$`: the signature says what the function is a
        -- function of, whatever noun `function` a field has)
        let sigAhead : Bool := match r0 with
          | .w w :: .m ts :: _ =>
            (w == w!"map" || w == w!"function" || w == w!"maps" || w == w!"functions") && (Math.parseSig ts).isSome
          | _ => false
        let cands := if sigAhead then [] else V.nouns.filterMap (fun n =>
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
            -- `every positive $a\in J$`, `a rational $s\in(a,b)$`: after adjectives of
            -- numbers, a real variable (its domain, if written, says more)
            if implicit && r1.length == r0.length && (Math.parseSig ts).isNone then
              -- (a formula that is no variable, `a symmetric $2\times2$ matrix`: the
              -- adjectives belong to a noun after it)
              let relation := match Math.parseFormula ts with
                | some (.chain _ (_ :: _)) => true
                | _ => false
              let numeral := match ts.head? with | some (.digit _) => true | _ => false
              if !relation && (numeral || ts.contains (.cmd w!"times")) then fail E.type
              -- (`every positive $n$`: an index name is usually an integer; without a
              -- domain, what it ranges over is not said)
              let stI ← get
              let index := match ts.head? with
                | some (.id v) => Elab.isIndex stI v
                | _ => false
              if index && !ts.contains (.cmd w!"in") then
                fail E.finding w!"adjectives without a noun before an index name: say what it ranges over (every positive integer $n$)"
              return ((.real, [], some ts, r), nms)
            let sg ← liftO (Math.parseSig ts) E.noun (((wordsOf np).intersperse [32]).flatten)
            match sg with
            | .sig (.id f) d c => do
              -- a field (`u:\mathbb{R}^3\times[0,1)\to\mathbb{R}^3`)
              -- (a function on a power of an interval type of the vocabulary, `c:[0,1]^2\to\mathbb{R}`
              -- with the field `unitsquare`, is a function of its points, not a field)
              let onPoints := (← tryCatch (do
                  let ds ← domainsOf false d
                  pure (!ds.isEmpty && ds.all fun (t, p) => Elab.isBase t && p.isNone)) fun _ => pure false)
              match ← (if onPoints then pure none else fieldSig d c) with
              | some (info, ty) =>
                modify fun st => { st with fields := (f, info) :: st.fields }
                pure (ty, [], some [.id f], r)
              | none =>
              let ds ← domainsOf false d
              let (ct, cp) ← domainOf false c
              -- `a function $A:\mathcal C\to\mathbb{R}$` on a class of the article: a
              -- function of the objects of its type, whose values are asked for at the
              -- members of the class only
              match ds, cp with
              | [(dt, some (.glob gi))], none =>
                modify fun st => { st with varDoms := (st.curEnv, f, .glob gi) :: st.varDoms }
                pure (Ty.fn dt ct, [], some [.id f], r)
              | _, _ =>
              if ds.any (·.2.isSome) || cp.isSome then fail E.unsupported
              pure (tyWrap (ds.map (·.1)) ct, [], some [.id f], r)
            | _ => fail E.unsupported
          | _ => fail E.noun (((wordsOf np).intersperse [32]).flatten)
    pure (h, nms)
  -- the longest noun first: the words of a modifier may begin a noun (`prime number`,
  -- `composite number`); otherwise the modifiers before the noun (`odd prime`)
  let restAt (k : Nat) : List Chunk := match pmAll[k]? with
    | some (cs, _) => cs
    | none => rEnd
  let rec tryK : Nat → Nat → M (Nat × (Ty × List Tm × Option (List MTok) × List Chunk) × List Nat)
    | 0, k => do
      let (h, nms) ← headOf (restAt k) (k > 0)
      pure (k, h, nms)
    | f + 1, k =>
      if pmAll.length ≤ k then do
        let (h, nms) ← headOf rEnd (pmAll.length > 0)
        pure (pmAll.length, h, nms)
      else tryCatch (do let (h, nms) ← headOf (restAt k) (k > 0); pure (k, h, nms)) fun _ => tryK f (k + 1)
  let (k, (ty, preds, var, r1), nms) ← tryK (pmAll.length + 1) 0
  let pmGroups := pmAll.take k
  -- (a modifier with variables, `on $v$ vertices`: its predicate of their values, which are
  -- formulas in the scope of the binder, as the conditions below)
  let slotPred (m : Modifier) (cs : List Chunk) : M Tm := do
    if !Notation.hasSlots m.phrase then return m.pred
    let some (args, _) := Notation.matchPrefix m.phrase cs [] | fail E.type
    let sc : Scope := [([], ty)] ++ (if outer.isEmpty then [] else [([], ty)]) ++ outer
    let ts ← (args.zip (Notation.slotTys args.length m.pred)).mapM fun (a, t) => do
      let some mt := Math.parseFormula a | fail E.unsupported
      let v ← Elab.term 100000 sc none mt
      if t == .real then Elab.asReal v else if v.2 == t then pure v.1 else fail E.type
    pure (Tm.lam ty .tt (Notation.betaApply m.pred (ts ++ [.loc 0])))
  let pms ← pmGroups.mapM fun (cs, ms) => do
    let ms := ms.filter (·.ty == ty)
    if ms.isEmpty then fail E.type
    match ← theMeaning (fun (m : Modifier) => m.pred) (·.field) cs (ms.map (·, [])) with
    | some (m, _) => slotPred m cs
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
          if Notation.hasSlots m.phrase then (Notation.matchPrefix m.phrase cs []).map fun (_, r) => (m, r) else
          (matchPhrase m.phrase cs).bind fun (v, r) => if v.isNone then some (m, r) else none
        else none)
      match ← theMeaning (fun (m : Modifier) => m.pred) (·.field) cs cands with
      | some (m, r) => post f r ((← slotPred m cs) :: acc)
      | none => pure (acc.reverse, cs)
  let (qms, r2) ← post 4 r1 []
  -- `a copula $C$ with maximal correlation $R=R(C)$`: the value of a function at the
  -- variable, named by the function's letter for the rest of the result. The words are
  -- the name under which the article introduced the function.
  let r2 ← match r2 with
    | .w w :: r =>
      let ws := r.takeWhile fun c => match c with | .w v => v != w!"and" | _ => false
      match (if w == w!"with" then r.drop ws.length else []) with
      | .m ts :: rest =>
        match Math.parseFormula ts with
        | some (.chain (.id x) [(.eq, .app (.id y) args)]) =>
          let keys := args.filterMap fun a => match a with | .id k => some k | _ => none
          if x != y || keys.length != args.length || args.isEmpty then pure r2 else
          match ← lookupGlob x with
          | some (gi, _) =>
            let words := (wordsOf ws).map Grammar.lower
            let known := ((st.named ++ st.ops).filter (·.2 == gi)).map (·.1)
            if !words.isEmpty && !known.contains words then
              fail E.finding (w!"the words before $" ++ x ++ w!"=" ++ x ++ w!"(…)$ are the name under which the article introduced " ++ x ++
                w!" (We write $" ++ x ++ w!"(C)$ for the maximal correlation of a copula $C$.); without them, write: with $" ++ x ++ w!"=" ++ x ++ w!"(…)$")
            modify fun st => { st with abbrevs := (st.curEnv, x, keys) :: st.abbrevs }
            pure rest
          | none => pure r2
        | _ => pure r2
      | _ => pure r2
    | _ => pure r2
  -- `a copula $C$ with $\rho(C)=0$ [and $\beta(C)=0$]`: conditions on the variable
  let (conds, r2) := match r2 with
    | .w w :: r => if w == w!"with" then condsOf 4 r [] else ([], r2)
    | _ => ([], r2)
  if !r2.isEmpty then fail E.noun (((wordsOf np).intersperse [32]).flatten)
  let (name, member) ← match var with
    | some ts => do let (v, d) ← varChunk ts outer; pure (v, d)
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
    -- (the members of a class: the condition is meaningful for the object, and holds)
    let p := if (← get).strongConds then Tm.mkAnd (Tm.defined p) p else p
    pure (Tm.lam ty .tt p)
  -- (a noun that says nothing beyond its type, `real number`, adds no condition)
  let all := ((preds ++ pms ++ qms ++ memberPred ++ notionPreds ++ condPreds).filter
    (· != Tm.lam ty .tt .tt)).eraseDups
  pure ⟨name, ty, conjPreds ty all⟩

/-- `nounPhrase1Core`; and where words stand between the noun and its variable that are a
modifier of the noun (`an integer coprime $a$ to $n$`, as `Let $a$ be an integer coprime to
$n$` is read: the variable is put before the last preposition), the phrase with the
variable further left, after the noun. -/
def nounPhrase1 (np : List Chunk) (outer : Scope := []) : M BindInfo := do
  let st0 ← get
  tryCatch (nounPhrase1Core np outer) fun e => do
    if !(e.code == E.nounWords || e.code == E.noun) then throw e
    let k := (np.takeWhile fun c => match c with | .w _ => true | _ => false).length
    match np[k]? with
    | some (.m v) =>
      if k < 2 || !(match np[k + 1]? with | some (.w _) => true | _ => false) then throw e
      let rec tryAt : Nat → M BindInfo
        | 0 => throw e
        | j + 1 => do
          set st0
          tryCatch (nounPhrase1Core (np.take (j + 1) ++ [.m v] ++ (np.take k).drop (j + 1) ++ np.drop (k + 1)) outer)
            fun _ => tryAt j
      tryAt (k - 1)
    | _ => throw e

/-- Read a noun phrase (without its determiner). A plural noun with a sequence
(`positive integers $a_1,\ldots,a_n$`, `integers $a_1,\ldots,a_n\ge1$`) binds the
sequence `a`, each of whose terms `a_i`, for the integers `i` from the first index to the
last, is as the noun phrase says of a single variable. -/
def nounPhrase (np : List Chunk) (outer : Scope := []) : M BindInfo := do
  let seq : Option (List Chunk × Codes × List MTok × List MTok × MT × MT) := match np.reverse with
    | .m ts :: rest => (Grammar.seqBound ts).bind fun (list, bound) =>
        (Grammar.seqVars list).map fun (x, name, lo, hi) => (rest.reverse, x, name, bound, lo, hi)
    | _ => none
  match seq with
  | some (pre, x, name, bound, lo, hi) => do
    let b ← nounPhrase1 (pre ++ [.m (name ++ bound)]) outer
    if b.ty != .real then fail E.unsupported
    let l ← closedBound lo outer
    let h ← closedBound hi outer
    modify fun st => { st with seqs := (x, lo, hi) :: st.seqs.filter (·.1 != x) }
    -- (the predicate is stated where the sequence is bound)
    pure ⟨x, .fn .real .real, some (seqPred 3 l h b.pred)⟩
  | none => do
    let b ← nounPhrase1 np outer
    modify fun st => { st with seqs := st.seqs.filter (·.1 != b.name) }
    pure b

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

/-- The bases of the subscripted symbols of a formula (`x` of `x_i`). -/
def subBases : Nat → MT → List Codes
  | 0, _ => []
  | f + 1, m =>
    (match m with | .sub (.id k) _ => [k] | _ => []) ++ (mtChildren m).flatMap (subBases f)

/-- The names with a letter as subscript in a formula (`x_k`, as one name). -/
def subKeys : Nat → MT → List Codes
  | 0, _ => []
  | f + 1, m =>
    (match m with | .sub (.id k) (.id i) => [k ++ [95] ++ i] | _ => []) ++ (mtChildren m).flatMap (subKeys f)

/-- The variables of the result or the proof that a formula uses under a name with a
letter as subscript: after `Let $x_k>0$.`, a later `$x_k$` is that variable (a name with
a number as subscript, `x_1`, is among the free identifiers already). Only a name that
is bound is found: `S_s` of a family `S` stays the family at `s`. -/
def envSubKeys (st : St) (bound : List Codes) (m : MT) : List Codes :=
  (subKeys 64 m).eraseDups.filter fun n =>
    !bound.contains n && (st.envBinders.any (·.name == n) || st.fixed.any (·.2.name == n))

/-- The variables of the result or the proof that a formula uses as the base of a subscript,
when no family of the article has that name: a kernel `F` in its component `F_S`. -/
def subBaseVars (st : St) (bound : List Codes) (m : MT) : List Codes :=
  (subBases 64 m).eraseDups.filter fun k =>
    !bound.contains k && st.envBinders.any (fun b => b.name == k && match b.ty with | .fn _ _ => true | _ => false) &&
      !(st.globs.any fun g => g.key == k && g.family)

/-- The free identifiers `free` of a condition `m` (with repetitions) without the letters
that occur in it only as the subscript of a name that the scope binds (`k` in `x_k`,
after `Let $x_k>0$.`): such a letter is part of the name, not a variable. -/
def dropBoundIndices (st : St) (m : MT) (free : List Codes) : List Codes :=
  let keys := (subKeys 64 m).filter fun n =>
    st.envBinders.any (·.name == n) || st.fixed.any (·.2.name == n)
  -- (the letter of a symbol with a numeral as superscript, `\Phi` of `\Phi^2`, is no variable)
  let free := free.filter fun i => !(st.globs.any fun g => Elab.powerName g.key == some i)
  -- (a family at a numeral, `Q_1` of the family `Q_t`, is no variable)
  let famAt (i : Codes) : Bool :=
    let ds := i.reverse.takeWhile fun c => 48 ≤ c && c ≤ 57
    let rest := i.reverse.drop ds.length
    match rest with
    | 95 :: k => !ds.isEmpty && st.globs.any fun g => g.family && g.key == k.reverse
    | _ => false
  let free := free.filter fun i => !famAt i
  free.filter fun i =>
    let asIndex := (keys.filter fun n =>
      i.length < n.length && n.drop (n.length - i.length - 1) == [95] ++ i).length
    asIndex == 0 || asIndex < (free.filter (· == i)).length

/-- `x_3` as the term of a sequence `x` among the binders `bs` (a variable whose values are
functions of a real number into a type of the vocabulary): the name `x`. -/
def termOfSeq (bs : List BindInfo) (n : Codes) : Option Codes :=
  (bs.find? fun b =>
    (match b.ty with | .fn .real (.base _) => true | _ => false) &&
    n.length > b.name.length + 1 && n.take (b.name.length + 1) == b.name ++ [95] &&
    (n.drop (b.name.length + 1)).all fun c => 48 ≤ c && c ≤ 57).map (·.name)

/-- The sequences of the scope among the free identifiers `ids` of a formula `m`: the
term `x_1` of a sequence `x` is `x`; and the variables of the scope whose name has a
letter as subscript. -/
def seqFree (st : St) (bound : List Codes) (m : MT) (ids : List Codes) : List Codes :=
  -- (`x_1` of a variable `x` of the scope that is a sequence of points of a vocabulary's
  -- type, `Let $x$ be a sequence in $[0,1]$`, is its term: the variable is `x`)
  let ids := ids.map fun n => (termOfSeq (st.envBinders ++ st.fixed.map (·.2)) n).getD n
  let seqs := (subBases 64 m).filter fun k => st.seqs.any (·.1 == k) && !bound.contains k
  ids.filter (fun n => !seqs.any fun k => k ++ [95] == n.take (k.length + 1)) ++ seqs ++
    envSubKeys st bound m

/-- A standard constant is not a variable of a condition (`If $x=\frac{\pi}{2}$`, `for
every $x\in\mathbb{R}$`). -/
def constName (n : Codes) : Bool := (Elab.builtinConst n).isSome || n == w!"\\infty"

/-- Free identifiers of a formula (for `On I,`). -/
def freeIds : Nat → List Codes → MT → List Codes
  | 0, _, _ => []
  | f + 1, bound, m =>
    match m with
    | .id n => if bound.contains n || n == [42] then [] else [n]
    | .num _ => []
    -- the base of `e_b` is a symbol, not a variable; `a_0` may be a variable
    | .sub (.id k) i =>
      -- (`x_1` of a bound sequence `x` is its term)
      let key : List Codes := match i with
        | .num n => if bound.contains k then [] else [k ++ [95] ++ (Nat.toDigits 10 n).map Char.toNat]
        | _ => []
      key.filter (!bound.contains ·) ++ freeIds f bound i
    | .sub b i => freeIds f bound b ++ freeIds f bound i
    -- a starred name is a symbol of its own (`\tau^*`)
    | .sup (.id k) (.id [42]) => if bound.contains (k ++ [94, 42]) then [] else [k ++ [94, 42]]
    | .sup b e => freeIds f bound b ++ freeIds f bound e
    -- `\hat x` is the name `\hat{x}`, or `\widehat` applied to `x`
    | .hat (.id k) =>
      let v := [92] ++ w!"hat{" ++ k ++ [125]
      (if bound.contains v then [] else [v]) ++ (if bound.contains k then [] else [k])
    | .hat x | .neg x | .abs x => freeIds f bound x
    -- (the operations on sets are no identifiers: `A\cup(N\times[0,1])`)
    | .app (.id op) [x, y] =>
      (if op == w!"\\cup" || op == w!"\\cap" || op == w!"\\times" || op == w!"\\setminus" then []
        else freeIds f bound (.id op)) ++ freeIds f bound x ++ freeIds f bound y
    | .app h as => freeIds f bound h ++ (as.flatMap (freeIds f bound))
    | .add x y | .minus x y | .mul x y | .div x y | .frac x y => freeIds f bound x ++ freeIds f bound y
    | .minm xs | .maxm xs | .tuple xs | .conj xs => xs.flatMap (freeIds f bound)
    | .int lo hi b v => freeIds f bound lo ++ freeIds f bound hi ++ freeIds f (v :: bound) b
    | .interval a b => freeIds f bound a ++ freeIds f bound b
    | .chain x rs => freeIds f bound x ++ rs.flatMap (fun r => freeIds f bound r.2)
    | .mapsto p b => freeIds f (freeIds f [] p ++ bound) b
    | .ival a b _ _ => freeIds f bound a ++ freeIds f bound b
    | .setOf p d cs => freeIds f bound d ++ cs.flatMap (freeIds f (freeIds f [] p ++ bound))
    | .setCond p cs => cs.flatMap (freeIds f (freeIds f [] p ++ bound))
    | .image e v d => freeIds f bound d ++ freeIds f (v :: bound) e
    | .cases rows => rows.flatMap fun (a, b) => freeIds f bound a ++ freeIds f bound b
    | .equiv x y | .land x y | .lor x y | .limp x y | .liff x y =>
      freeIds f bound x ++ freeIds f bound y
    | .lnot x | .extr _ x | .bound _ x => freeIds f bound x
    | .finset xs => xs.flatMap (freeIds f bound)
    | .bigop _ v lo hi b => freeIds f bound lo ++ freeIds f bound hi ++ freeIds f (v :: bound) b
    -- (the domain may be a condition on the variables, `\varepsilon>0`)
    | .quant _ vs d b => freeIds f (vs ++ bound) d ++ freeIds f (vs ++ bound) b
    | .limit v t b => freeIds f bound t ++ freeIds f (v :: bound) b
    | .sig .. | .text _ => []

/-- The variables that a formula binds: of its sets, integrals, sums, limits, maps and
quantifiers. -/
def boundIds : Nat → MT → List Codes
  | 0, _ => []
  | f + 1, m =>
    let all (xs : List MT) := xs.flatMap (boundIds f)
    match m with
    | .id _ | .num _ | .sig .. | .text _ => []
    | .sub x y | .sup x y | .add x y | .minus x y | .mul x y | .div x y | .frac x y
    | .interval x y | .ival x y _ _ | .equiv x y | .land x y | .lor x y | .limp x y | .liff x y => all [x, y]
    | .hat x | .neg x | .abs x | .lnot x | .extr _ x | .bound _ x => boundIds f x
    | .app h as => all (h :: as)
    | .minm xs | .maxm xs | .tuple xs | .conj xs | .finset xs => all xs
    | .int lo hi b v => v :: all [lo, hi, b]
    | .chain x rs => all (x :: rs.map (·.2))
    | .mapsto p b => freeIds 64 [] p ++ boundIds f b
    | .setOf p d cs => freeIds 64 [] p ++ all (d :: cs)
    | .setCond p cs => freeIds 64 [] p ++ all cs
    | .image e v d => v :: all [e, d]
    | .cases rows => rows.flatMap fun (a, b) => all [a, b]
    | .bigop _ v lo hi b => v :: all [lo, hi, b]
    | .quant _ vs d b => vs ++ all [d, b]
    | .limit v t b => v :: all [t, b]

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

/-- A letter the article declares to be an integer (`Throughout, $p$ denotes an
integer.`) is one wherever it is bound: the condition joins its domain. -/
def declaredInts (bs : List BindInfo) : M (List BindInfo) := do
  let st ← get
  let isInt : Tm := .app (.prim .isInt) (.loc 0)
  pure (bs.map fun b =>
    if b.ty != .real || !st.letters.contains b.name then b else
    match b.pred with
    | none => { b with pred := some (.lam .real .tt isInt) }
    -- (already joined, when the binder was read by a binder that calls this one)
    | some (.lam _ _ (.and (.app (.prim .isInt) (.loc 0)) _)) => b
    | some q => { b with pred := some (.lam .real .tt (.and isInt (.app (shift 1 0 q) (.loc 0)))) })

/-- The condition that the variable `v` lies in the domain `d` of a binder, as a formula:
an interval by its bounds (`$b\ge0$` is the binder of `b` over `[0,\infty)`, and the
condition `b\ge0`), another domain by membership. -/
def condOfDomain (v : Codes) (d : MT) : MT :=
  let isInf (m : MT) : Bool := match m with | .id n => n == w!"\\infty" | _ => false
  match d with
  | .ival lo hi lopen hopen =>
    let lower : Option (Rel × MT) := match lo with
      | .neg m => if isInf m then none else some (if lopen then .gt else .ge, lo)
      | _ => some (if lopen then .gt else .ge, lo)
    let upper : Option (Rel × MT) := if isInf hi then none else some (if hopen then .lt else .le, hi)
    match lower, upper with
    | some (r, a), some (r', b) => .conj [.chain (.id v) [(r, a)], .chain (.id v) [(r', b)]]
    | some l, none => .chain (.id v) [l]
    | none, some u => .chain (.id v) [u]
    | none, none => .chain (.id v) [(.mem, d)]
  | _ => .chain (.id v) [(.mem, d)]

/-- A condition on variables bound before it in the same binder (`with $a\ge0$`): it joins
the domain of the last of them that it mentions (the last variable, if it mentions none of
them), not simply the last one: in `Let $a$, $b$ and $c$ be real numbers with $a\ge0$`, the
condition on `a` must not ride on `c`, which the claim may leave unused. `φ` is read in the
scope of `before` and of the variables of `out` up to that one. -/
def attachCond (before out : List BindInfo) (φ : MT) : M (List BindInfo) := do
  if out.isEmpty then fail E.unsupported
  let mentioned := freeIds 64 [] φ
  let j := ((out.zipIdx.filter fun (b, _) => mentioned.contains b.name).map (·.2)).getLast?.getD (out.length - 1)
  let some last := out[j]? | fail E.unsupported
  let sc : Scope := ((before ++ out.take (j + 1)).map fun b => (b.name, b.ty)).reverse
  let (p, pty) ← Elab.term 100000 sc none φ
  if pty != .prop then fail E.type
  let pred := match last.pred with
    | some q => Tm.lam last.ty .tt (.and (.app (shift 1 0 q) (.loc 0)) (shift 1 0 p))
    | none => Tm.lam last.ty .tt (shift 1 0 p)
  pure (out.take j ++ [{ last with pred := some pred }] ++ out.drop (j + 1))

def binderInfosRaw (b : Bind) (before : List BindInfo := []) : M (List BindInfo) :=
  let outer : Scope := (before.map fun b => (b.name, b.ty)).reverse
  match b with
  -- (a multi-index `I\in\mathbb{N}_0^n`: its components `I_1`, …, `I_n`)
  | .every vs d => everyIn outer vs d
  | .noun np => do pure [← nounPhrase np outer]
  | .hyp b => binderInfosRaw b before
  | .on _ => pure []
  | .ifCond φ => do
    -- the free variables of φ range over ℝ; φ is the domain of the last one. The
    -- variables bound before (of the result: `Let $n\ge1$. If $x\in[0,n]$, …`) are not
    -- bound again
    let st ← get
    let free := ((dropBoundIndices st φ (freeIds 64 [] φ)).filter fun n => !(st.globs.zipIdx.any fun (g, i) => g.key == n && !g.family && Elab.visibleIn st i) && !constName n).eraseDups
    -- (a symbol of an earlier sentence that Leanify did not read is an object of the
    -- article, not a variable: `If $q>2-s$` about the `q` and `s` introduced in words)
    -- (not a variable that the result or the sentence has bound: `Let $T$ be …. If
    -- $K\subseteq\{…T(x)…\}$, …`)
    if let some v := free.find? (fun n => st.unreadIds.contains n && !before.any (·.name == n)) then
      fail E.undefined v
    -- (`U_1` of a sequence `U` bound before is its term, not a variable)
    let free := free.filter fun n => (termOfSeq before n).isNone
    let free := (seqFree st [] φ free).filter fun n => !before.any (·.name == n)
    -- (a term `x_1` of a sequence is not a variable of its own)
    if let some x := free.find? fun n => st.seqs.any (·.1 == n) then
      fail E.finding (w!"a condition on the terms of the sequence " ++ x ++ w!" together with new variables: state it where " ++ x ++ w!" is introduced (with $…$)")
    match free.reverse with
    | [] => fail E.unsupported
    | last :: _ =>
      let sc : Scope := free.reverse.map (·, Ty.real) ++ outer
      let (p, pty) ← Elab.term 100000 sc none φ
      if pty != .prop then fail E.type
      -- the predicate is applied to the last variable where all of them are bound,
      -- so `φ` is shifted past its own (unused) argument
      pure (free.map fun v => (⟨v, .real, if v == last then some (.lam .real .tt (shift 1 0 p)) else none⟩ : BindInfo))
  | .many bs => do
    let mut out : List BindInfo := []
    for b in bs do
      match b with
      | .every vs d => out := out ++ (← everyAfter (before ++ out) vs d)
      -- `For every $x\in A$ with $φ$`: a condition on the variables bound before it,
      -- part of the domain of the last one
      | .ifCond φ => out ← attachCond before out φ
      -- `For every positive integer $n$ and every $x\in[0,1]$`: a noun phrase, whose
      -- condition may use the variables bound before it
      | .noun np => do
        let b ← nounPhrase np ((before ++ out).map fun b => (b.name, b.ty)).reverse
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
    let (ty, p) ← binderDomain vs d sc
    let (bis, _) := vs.foldl (fun (acc, j) v =>
      (acc ++ [(⟨v, ty, p.map (shift (j + 1) 0)⟩ : BindInfo)], j + 1)) (([] : List BindInfo), 0)
    pure bis

/-- The binders among `bs` whose variables are `used`, in their order. A used binder
whose domain uses the binders before it (`e\in[0,x]`) keeps them all. -/
def binderInfos (b : Bind) (before : List BindInfo := []) : M (List BindInfo) := do
  declaredInts (← binderInfosRaw b before)

def usedBinders (bs : List BindInfo) (used : List Codes) : List BindInfo :=
  let dependent (b : BindInfo) : Bool := b.pred.any fun p => shift 1 0 p != p
  let lastDep := ((bs.zipIdx.filter fun (b, _) => used.contains b.name && dependent b).map (·.2)).getLast?
  (bs.zipIdx.filter fun (b, i) => used.contains b.name || lastDep.any (i ≤ ·)).map (·.1)

/-- The variables of a list of binders, each domain in the scope of the variables
before it (`For $x\in(0,1]$ and $e\in[0,x]$`). -/
def bindersInfos (binds : List Bind) (before : List BindInfo := []) : M (List BindInfo) := do
  let mut out : List BindInfo := []
  let st ← get
  -- (a binder or a condition after others of the same sentence, about variables that they
  -- already bind, is a condition on them: `Let $a$ and $b$ be real numbers with $a\ge0$,
  -- $b\ge0$ and $|b|<1$` does not bind `b` again)
  let restates (out : List BindInfo) (φ : MT) : Bool :=
    let fr := ((dropBoundIndices st φ (freeIds 64 [] φ)).filter fun n =>
      !(st.globs.zipIdx.any fun (g, i) => g.key == n && !g.family && Elab.visibleIn st i) && !constName n).eraseDups
    -- (it may also use the variables bound before: `Let $c>0$. Let $v$ be a real number
    -- with … and $|v|<c$.`)
    fr.any (fun n => out.any (·.name == n)) && fr.all fun n => out.any (·.name == n) || before.any (·.name == n)
  for b in binds do
    match b with
    | .every vs d =>
      if !vs.isEmpty && vs.all (fun n => out.any (·.name == n)) then
        let cs := vs.map fun v => condOfDomain v d
        out ← attachCond before out (match cs with | [c] => c | _ => .conj cs)
      else out := out ++ (← binderInfosRaw.everyAfter (before ++ out) vs d)
    | .noun np => out := out ++ [← nounPhrase np ((before ++ out).map fun b => (b.name, b.ty)).reverse]
    | .ifCond φ => if restates out φ then out ← attachCond before out φ else out := out ++ (← binderInfosRaw b (before ++ out))
    | b => out := out ++ (← binderInfosRaw b (before ++ out))
  declaredInts out

def scopeOf (bs : List BindInfo) : Scope := (bs.map fun b => (b.name, b.ty)).reverse

def wrap (bs : List BindInfo) (body : Tm) : Tm :=
  forallBinders (bs.map fun b => (b.name, b.ty, b.pred.map fun p => Tm.app p (.loc 0))) body

/-- The implicit parameters of the definitions named among `ids` (visible here). A
definition whose name has a letter as subscript (`\delta_n`, defined among the variables
of a result) is not among the free identifiers of a formula, where `n` alone is one: the
callers name it by `subKeys`. -/
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
  | .monoFns fs d _ => d :: fs.map fun f => match f with
    | .app g args => .app g (args.filter fun a => match a with | .id n => n != w!"\\cdot" | _ => true)
    | _ => f
  | .forCond f c => [f, c]
  | .ranges _ b => [b]
  | .extremaOver items f _ _ cond => items.map (·.2) ++ [f, cond]
  | .increases f a b => [f, a, b]
  | .sends m f g => [m, f, g]
  | .every _ d b => [d, b]
  | .equalityOn s => [s]
  | .equalityWhen φ => [φ]
  | .ifThen c cl => c :: clauseMaths cl
  | .ifClause h cl => clauseMaths h ++ clauseMaths cl
  | .adjectives s adjs => (match s with
    | .app g args => .app g (args.filter fun a => match a with | .id n => n != w!"\\cdot" | _ => true)
    | _ => s) :: adjs.filterMap (·.2)
  | .notions s _ _ => [s]
  | .isA s np _ => s :: (mathsOf np).filterMap Math.parseFormula
  | .thereIs _ c => clauseMaths c
  | .aliased _ c => clauseMaths c
  | .both cs => clauseMathsAll cs
  | .iffC p q => clauseMaths p ++ clauseMaths q
  | .orC p q => clauseMaths p ++ clauseMaths q
  | .infinitelyMany np (some c) => clauseMaths c ++ (mathsOf np).filterMap Math.parseFormula
  | .infinitelyMany np none => (mathsOf np).filterMap Math.parseFormula
  | .under _ c => clauseMaths c
  | .forEveryNP c np => clauseMaths c ++ (mathsOf np).filterMap Math.parseFormula
  | .existsNP np _ (some c) => clauseMaths c ++ (mathsOf np).filterMap Math.parseFormula
  | .existsNP np _ none => (mathsOf np).filterMap Math.parseFormula
  | .existsNPs nps cs => clauseMathsAll cs ++ (nps.flatMap mathsOf).filterMap Math.parseFormula
  | .noneExist c => clauseMaths c
  | .iff p q => [p, q]
  | .compare l _ r => [l, r]
  | .stmtAt e => [e]
  | .inst _ e hs cs => e :: clauseMathsAll hs ++ clauseMathsAll cs
  | .fixesConsts op => [op]
  | .mapsInto op d e n => [op, d, e] ++ (n.map (·.2)).toList
  | .timesId op k d => [op, k, d]
  | .dependsFirst g m => [g, m]
  | .hasProps sm _ ms => sm :: ms
  | .firstObs g m => [g, m]
  -- (`$x$ is a minimizer of $f$`: the subject and the object)
  | .pred s _ o => (match s with | .math m => [m] | _ => []) ++ (match o with | .math m => [m] | _ => [])
  | _ => []

/-- The formulas of several clauses (structural, so that the kernel evaluates it). -/
def clauseMathsAll : List Clause → List MT
  | [] => []
  | c :: cs => clauseMaths c ++ clauseMathsAll cs
end

/-- The generic constants of a formula (`C`, `C_m`, `C_{j,I}`): their names and the
variables of their indices. -/
def genericsOf (bases : List Codes) : Nat → MT → List (Codes × List Codes)
  | 0, _ => []
  | f + 1, m =>
    -- the implied constant of `\ll`, `\gg` and `O(…)` (`@ll`)
    let implied : List (Codes × List Codes) := match m with
      | .chain _ rs =>
        if bases.contains w!"@ll" && rs.any (fun (r, y) => r == .ll || r == .gg || r == .asymp ||
            (match y with | .app (.id [79]) [_] => true | _ => false)) then [(w!"@ll", [])] else []
      | _ => []
    implied ++
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
  | .ifClause _ cl => usesIneq cl
  | _ => false

/-- The free variables of the latest inequality that a clause refers to. -/
def ineqFree (st : St) (cl : Clause) : List Codes :=
  if usesIneq cl then
    match st.lastIneq with
    | some (bs, m) => freeIds 64 (bs.map (·.name)) m
    | none => []
  else []

/-- The names of a formula that occur other than as the function of an application. -/
def bareIds : Nat → MT → List Codes
  | 0, _ => []
  | f + 1, m => match m with
    | .id n => [n]
    | .app (.id _) args => args.flatMap (bareIds f)
    | _ => (mtChildren m).flatMap (bareIds f)

/-- The domains of the binders inside a clause (`there is $x\in U$ such that …`,
`… for every $x\in U$`): a domain may be a set that the result binds. -/
def innerDoms : Clause → List MT
  | .thereIs b c | .under b c =>
    (match b with
      | .every _ d => [d]
      | .many bs => bs.filterMap fun b' => match b' with | .every _ d => some d | _ => none
      | _ => []) ++ innerDoms c
  | .scoped _ _ (some d) _ => [d]
  | _ => []

/-- Does a formula speak of the random pair of the result: an expectation `\mathbb{E}[…]`
or a condition that holds almost surely? -/
def usesRandomPair : Nat → MT → Bool
  | 0, _ => false
  | f + 1, m =>
    (match m with
      | .app (.id n) _ => n == w!"@rexp" || n == w!"@rae"
      | _ => false) || (mtChildren m).any (usesRandomPair f)

/-- The joint law of the random pair of the result, as a variable that formulas use: where
they speak of the pair (`\mathbb{E}[…]`, `almost surely`) or of the distribution function of
its first variable. -/
def lawIds (st : St) (ms : List MT) (ids : List Codes) : List Codes :=
  match st.randomPair with
  | some (_, _, _, df, _, _) =>
    if ms.any (usesRandomPair 64) || (match df with | some d => ids.contains d | none => false)
    then [w!"\\mathbb{P}"] else []
  | none => []

/-- The free variables of a clause, its trailing definitions and the implicit
parameters of the definitions it uses (for the binders it inherits). -/
def clauseFree (st : St) (bound : List Codes) (cl : CClause) : List Codes :=
  let ms := clauseMaths cl.clause ++ cl.defs ++
    -- (only a letter that is a set bound before: the other domains are as they were)
    (innerDoms cl.clause).filter (fun d => match d with | .id n => n.length == 1 | _ => false)
  let ids := ms.flatMap fun m => seqFree st bound m (freeIds 64 bound m)
  -- (`R` for `R(C)`, after `a copula $C$ with maximal correlation $R=R(C)$`, uses `C`; not
  -- the function `R` applied, `R(M_r)`)
  let abbrKeys := (ms.flatMap (bareIds 64)).eraseDups.flatMap fun n =>
    if !ids.contains n then [] else
    ((st.abbrevs.find? fun (e, k, _) => k == n && (e == st.curEnv || st.curProved == some e)).map (·.2.2)).getD []
  let law := lawIds st ms ids
  ids ++ law ++ abbrKeys ++ implicitVars st (ids ++ ms.flatMap (subKeys 64)) ++ ineqFree st cl.clause ++
    (ms.flatMap (subBaseVars st bound))

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
      let i ← addGlob ⟨[], tty, [], false, 1⟩ t
      modify fun st => { st with named := st.named ++ [(name, i)] }
      pure (.glob i)
    | _ => fail E.type
  | _ => fail E.unsupported

/-- `$x$ is [a|an] PHRASE of $y$` with a modifier of the vocabulary whose phrase is
`PHRASE of $v$` (`$x$ is a local minimizer of $f$`, of the field `optimization`): its
predicate of `y` and `x`. -/
def vocabOf (sc : Scope) (s : Tm × Ty) (phrase : List Codes) (o : Obj) : M Tm := do
  let ws := match phrase with
    | a :: r => if a == w!"a" || a == w!"an" then r else phrase
    | [] => []
  -- `$a$ is a solution of the Fibonacci recurrence`: a modifier whose phrase goes on with
  -- the words of the object (and its formula, if it has one)
  if let .named nws om := o then
    let target : Phrase := ws.map PItem.w ++ [.w w!"of", .w w!"the"] ++ nws.map PItem.w ++ (if om.isSome then [.v] else [])
    let cands := (← get).vocab.mods.filter fun m => !m.prenominal && m.ty == s.2 && m.phrase == target
    let cs : List Chunk := (ws ++ [w!"of", w!"the"] ++ nws).map Chunk.w
    match ← theMeaning (fun (m : Modifier) => m.pred) (·.field) cs (cands.map (·, [])) with
    | some (m, _) =>
      match om with
      | none => return Tm.app m.pred s.1
      | some mt =>
        let t := (Notation.slotTys 1 m.pred).headD .real
        let v ← term F sc none mt
        let a ← if t == .real then Elab.asReal v else if v.2 == t then pure v.1 else fail E.type
        return Notation.betaApply m.pred [a, s.1]
    | none => pure ()
  let target : Phrase := ws.map PItem.w ++ [.w w!"of", .v]
  let cands := (← get).vocab.mods.filter fun m => !m.prenominal && m.ty == s.2 && m.phrase == target
  let cs : List Chunk := ws.map Chunk.w
  match ← theMeaning (fun (m : Modifier) => m.pred) (·.field) cs (cands.map (·, [])) with
  | some (m, _) =>
    let .math mt := o | fail E.noun ((phrase.intersperse [32]).flatten)
    let t := (Notation.slotTys 1 m.pred).headD .real
    let v ← term F sc none mt
    let a ← if t == .real then Elab.asReal v else if v.2 == t then pure v.1 else fail E.type
    pure (Notation.betaApply m.pred [a, s.1])
  | none => fail E.noun ((phrase.intersperse [32]).flatten)

def predicate (sc : Scope) (s : Tm × Ty) (phrase : List Codes) (o : Obj) : M Tm := do
  let some i := lookupWords (← get).preds phrase | vocabOf sc s phrase o
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
  | none => if st.defLabels.contains l || l.head? == some 167 then pure [] else fail E.label l

def addLabels (ls : List Codes) (claims : List Nat) (isDef : Bool) : M Unit := do
  for l in ls do
    modify fun st =>
      let st := if isDef then { st with defLabels := st.defLabels ++ [l] } else st
      match st.labels.lookup l with
      | some cs => { st with labels := st.labels.map fun (k, v) => if k == l then (k, cs ++ claims) else (k, v) }
      | none => { st with labels := st.labels ++ [(l, claims)] }

/-- A proposition that says nothing: `⊤`, and conjunctions of it. -/
def saysNothing : Tm → Bool
  | .tt => true
  | .and p q => saysNothing p && saysNothing q
  | _ => false

/-- A proposition that says only that objects of declared kinds exist, whatever is
given: `∃ x ∈ K, ⊤` after quantifiers and hypotheses. It holds as soon as the kinds
have elements. -/
def existsOnly (declared : Nat → Bool) : Tm → Bool
  | .all _ b => existsOnly declared b
  | .imp _ q => existsOnly declared q
  | .ex (.base k) b => declared k && (saysNothing b || existsOnly declared b)
  | _ => false

/-- Record a claim of the current sentence (with premises for proof steps). A sentence
that says only that an object of a noun exists which the article does not define
(`There is a graph $G$.`, `For every graph $G$ there is a tree $T$.`) is not a claim:
such a kind is assumed to have an element, so the sentence would be verified by the
assumption. -/
def emit (c : SentCtx) (body : Tm) (cites : List Codes) : M Nat := do
  let st ← get
  if existsOnly (fun k => st.vocab.typeLean[k]?.any fun (n, _) => Vocab.isDeclaredName n) body then
    fail E.finding w!"that such an object exists is not checked: a noun that the article does not define is assumed to have an element"
  match c.ctx.kind with
  | .proof => do
    let cited ← cites.mapM citeClaims
    let allCites := (st.proofCites ++ cited.flatten).eraseDups
    let premises := (allCites ++ st.proofSteps).eraseDups
    let refuted := st.envHyps.any (·.contra)
    let id ← addClaim { sent := c.idx, body := body, role := .step c.ctx.env, cites := cites, premises := premises, refuted := refuted }
    modify fun st => { st with proofCites := allCites, proofSteps := st.proofSteps ++ [id], hypUsed := true }
    pure id
  | _ => do
    discard <| cites.mapM citeClaims
    modify fun st => { st with hypUsed := true }
    let refuted := st.envHyps.any (·.contra)
    addClaim { sent := c.idx, body := body, role := claimRole c, cites := cites, premises := [], refuted := refuted }

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
    -- (`C_1^*(u,v)`: a decoration with a number below)
    | .sup (.sub (.id x) (.num n)) (.id d) =>
      if x == binder then pure (w!"^" ++ d ++ w!"_" ++ (Nat.toDigits 10 n).map Char.toNat, false, names)
      else fail E.unsupported
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
  -- `For a copula $C$, Spearman's rho is DISPLAY` with `\rho(C)=…` for a symbol `\rho`
  -- that is not defined: the display defines it
  let st0 ← get
  let defn := match it.defn with
    | .chain (.app (.id f) args) ((.eq, rhs) :: more) =>
      if !args.isEmpty && args.all (fun a => match a with | .id _ => true | _ => false) &&
          !(st0.globs.any fun g => g.key == f) && (Elab.builtinConst f).isNone
      then MT.chain (.app (.id f) args) ((.defeq, rhs) :: more) else it.defn
    | d => d
  match defn with
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
    let i ← addGlob ⟨key, ty, b.pred :: ats.map (fun _ => none), family, 1⟩ value
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
    let i ← addGlob ⟨[], .fn bty lty, [b.pred], false, 1⟩ value
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
      let ie ← addGlob ⟨e, .fn .real .real, [epred], true, 1⟩ (.lam .real (holdsAt epred (.loc 0)) hv)
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
        let i ← addGlob ⟨f, tyWrap (ds.map (·.1)) cty, ds.map (·.2), false, 1⟩ value
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
    let i ← addGlob ⟨f, .fn aty cty, [apred], false, 1⟩ value
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
    let i ← addGlob ⟨f, .fn b.ty (.fn aty cty), [b.pred, apred], true, 1⟩ value
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
    let i ← addGlob ⟨f, .fn b.ty (.fn aty cty), [b.pred, apred], true, 1⟩ value
    let cs ← chainClaims sc rhs more
    let ids ← cs.mapM fun q => emit c (wrap [b, ⟨x, aty, apred⟩] q) []
    addLabels labels ids true
    pure ([i], ids)
  | _, _ => fail E.unsupported

/-- `NAME is denoted by $S$`: binds the symbol `S` to a named notion of the
vocabulary (`Lebesgue measure on $[0,1]$`). -/
def denotedBy (name : List Chunk) (sym : MT) : M (List Nat × List Nat) := do
  let key ← match sym with | .id k => pure k | _ => fail E.finding w!"the symbol a sentence defines is a name ($X$, $d_0$, $\\Gamma$) or a function of variables ($f(x,y)$)"
  let V := (← get).vocab
  let cands := V.notions.filterMap fun n => match matchPhrase n.name name with
    | some (none, []) => some (n, [])
    | _ => none
  match ← theMeaning (fun (n : Notion) => (n.ty, n.value)) (·.field) name cands with
  | some (n, _) => do
    let i ← addGlob ⟨key, n.ty, [], false, 1⟩ n.value
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
    let i ← addGlob ⟨key, .fn b.ty vty, [b.pred], family, 1⟩ (.lam b.ty (holdsAt b.pred (.loc 0)) v)
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
  -- `For a NOUN $C$, set $C^\top(u,v)\coloneqq C(v,u)$`: an operation on the binder's
  -- variable, as `the transpose of $C$ is …`
  let onBinder : MT → Bool := fun h => match h with
    | .sup (.id x) (.id _) | .hat (.id x) | .sup (.sub (.id x) (.num _)) (.id _) => x == b.name
    | _ => false
  match m with
  | .chain (.app h _) ((.defeq, _) :: _) =>
    if onBinder h then defItem c b ⟨[], m, []⟩ else setDefMain m
  | .chain h ((.defeq, _) :: _) =>
    if onBinder h then defItem c b ⟨[], m, []⟩ else setDefMain m
  | _ => setDefMain m
where setDefMain (m : MT) : M (List Nat × List Nat) := do
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
    let argDoms := naturalPreds (ats.map (·, none)) v
    let value := Tm.lam b.ty (holdsAt b.pred (.loc 0)) (lamWrapD argDoms v)
    let i ← addGlob ⟨key, .fn b.ty (tyWrap ats vty), b.pred :: argDoms.map (·.2), family, 1⟩ value
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

/-- The type of a sequence of points of the vocabulary's interval (`U`, `V` of a sample). -/
def seqTy : M (Option Ty) := do
  pure (((← get).vocab.intervals.find? (·.sampleExp.isSome)).map fun iv => Ty.fn .real iv.ty)

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
    -- `F(x_1,x_2)\coloneqq e`: a kernel, a function of the sequence `x`
    let seqArg : Option (Codes × Ty) ← match Elab.kernelPattern args, ← seqTy with
      | some x, some t => pure (some (x, t))
      | _, _ => pure none
    let args := match seqArg with
      | some (x, _) => [MT.id x]
      | none => args
    let argNames ← args.mapM fun a => match a with | .id n => pure n | _ => fail E.unsupported
    let st ← get
    let ids := freeIds 64 argNames rhs
    let used := ids ++ implicitVars st (ids ++ subKeys 64 rhs) ++ lawIds st [rhs] ids
    -- A variable whose domain uses the variables before it (`x\in[0,n]`) needs them all,
    -- in their order: the definition takes them too, so that the domain is a condition on
    -- its own parameters.
    -- (a domain names its own variable by `loc 0` and the variables before it by the
    -- locals above: `Let $a$ and $c$ be real numbers with $c>0$` does not use `a`)
    let dependent (b : BindInfo) : Bool := b.pred.any fun p => shift 1 1 p != p
    let lastDep := ((bs.zipIdx.filter fun (b, _) =>
      (used.contains b.name || argNames.contains b.name) && dependent b).map (·.2)).getLast?
    let imp := (bs.zipIdx.filter fun (b, i) =>
      !argNames.contains b.name && (used.contains b.name || lastDep.any (i < ·))).map (·.1)
    let argInfo : List BindInfo := argNames.map fun n => match bs.find? (·.name == n) with
      | some b => b
      | none => match seqArg with
        | some (x, t) => if x == n then ⟨n, t, none⟩ else ⟨n, .real, none⟩
        | none => ⟨n, .real, none⟩
    let all := imp ++ argInfo
    match lastDep with
    | some l =>
      if (all.take (l + 1)).map (·.name) != (bs.take (l + 1)).map (·.name) then
        fail E.finding (w!"the domain of a variable of this definition depends on a variable before it, and the arguments of " ++ key ++ w!" are not in that order: define it without arguments (Set $" ++ key ++ w!"\\coloneqq …$), or state the variables with it")
    | none => pure ()
    let (v, vty) ← term F (scopeOf all) none rhs
    -- (an argument that no binder introduces has its natural domain)
    let argInfo : List BindInfo :=
      let nat := naturalPreds (argInfo.map fun b => (b.ty, if (bs.any (·.name == b.name)) then some (b.pred.getD (.lam b.ty .tt .tt)) else b.pred)) v
      (argInfo.zip nat).map fun (b, (_, p)) => if bs.any (·.name == b.name) then b else { b with pred := p }
    let all := imp ++ argInfo
    let value := all.foldr (fun b acc => Tm.lam b.ty (holdsAt b.pred (.loc 0)) acc) v
    let ty := all.foldr (fun b acc => Ty.fn b.ty acc) vty
    let i ← addGlob ⟨key, ty, all.map (·.pred), false, 1⟩ value
    if !imp.isEmpty then modify fun st => { st with implicits := st.implicits ++ [(i, imp.map (·.name))] }
    if !all.isEmpty then modify fun st => { st with telescopes := st.telescopes ++ [(i, all)] }
    match c.ctx.kind with
    | .text => pure ()
    | _ => modify fun st => { st with locals := st.locals ++ [(i, c.ctx.env)] }
    pure i
  | _ => fail E.unsupported


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
      -- a definition that uses variables of the result or proof (of the section, in the
      -- running text) takes them as implicit parameters
      let st ← get
      let scope : List BindInfo := match c.ctx.kind with
        | .text => (st.fixed.filter (·.1 == c.ctx.sec)).map (·.2)
        | _ => st.envBinders
      let usesScope := match m with
        | .chain _ [(.defeq, rhs)] =>
          let ids := freeIds 64 [] rhs
          (ids ++ implicitVars st (ids ++ subKeys 64 rhs)).any fun n => scope.any (·.name == n)
        | _ => false
      if usesScope then
        let i ← inlineDef c scope m
        ds := ds ++ [i]
      else
      match m with
      -- `Define $f(x,y)\coloneqq e$.` without a binder: a function of real variables
      | .chain (.app h args) [(.defeq, _)] => do
        if (symKey h).isNone || (!args.all (fun a => match a with | .id _ => true | _ => false) && (Elab.kernelPattern args).isNone) then
          fail E.finding w!"the left side of a definition is a symbol ($X$, $d_0$) or a function of variables ($f(x,y)$)"
        let i ← inlineDef c [] m
        ds := ds ++ [i]
      | .chain lhs ((.defeq, rhs) :: more) => do
        let some key := symKey lhs
          | fail E.finding w!"the left side of a definition is a symbol ($X$, $d_0$) or a function of variables ($f(x,y)$); for a family ($A_{ij}$), say what its indices range over (For $i,j\\in\\{1,2\\}$, set …)"
        let (v, vty) ← term F [] none rhs
        let i ← addGlob ⟨key, vty, [], false, 1⟩ v
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
def multiDefs (bs0 : List BindInfo) (defs : List MT) (labels : List Codes) (imp : List BindInfo := []) :
    M (List Nat × List Nat) := do
  let mut ds : List Nat := []
  -- (`For $t\in[0,1]$ and $u,v\in[0,1]$, let $f_t(v)\coloneqq …$ and $Q_t(u,v)\coloneqq …$`:
  -- a definition takes the variables of the binder that its arguments name, in the
  -- binder's order; a variable it leaves out has no condition)
  let pick (names : List Codes) : List BindInfo :=
    let kept := bs0.filter fun b => names.contains b.name
    let dropped := bs0.filter fun b => !names.contains b.name
    let laterKept := (bs0.dropWhile fun b => names.contains b.name).filter fun b => names.contains b.name
    if kept.map (·.name) == names && dropped.all (·.pred.isNone) && laterKept.all (·.pred.isNone) then kept else bs0
  for m in defs do
    let bs : List BindInfo := match m with
      | .chain (.app h args) [(.defeq, _)] =>
        let names := args.filterMap fun a => match a with | .id n => some n | _ => none
        match familyKey h with
        | some (_, p) => if bs0.head?.map (·.name) == some p then pick (p :: names) else pick names
        | none => pick names
      | _ => bs0
    match m with
    -- `For $r\in[0,1]$ and $g\in[-r,r]$, set $C_{r,g}\coloneqq e$`: a family with the
    -- binder's variables, all of them and in their order, as its subscripts
    | .chain (.sub (.id k) (.tuple idx)) [(.defeq, rhs)] =>
      let names ← idx.mapM fun a => match a with | .id n => pure n | _ => fail E.unsupported
      if names != bs.map (·.name) then
        fail E.finding (w!"the subscripts of the family " ++ k ++ w!" are the variables of the binder before it, all of them and in its order (For $r\\in[0,1]$ and $g\\in[-r,r]$, set $C_{r,g}\\coloneqq …$)")
      let all := imp ++ bs
      let sc : Scope := (all.map fun b => (b.name, b.ty)).reverse
      let (v, vty) ← term F sc none rhs
      let value := all.foldr (fun b t => Tm.lam b.ty (holdsAt b.pred (.loc 0)) t) v
      let ty := all.foldr (fun b t => Ty.fn b.ty t) vty
      let i ← addGlob { key := k, ty, doms := all.map (·.pred), family := true, indices := names.length } value
      if !imp.isEmpty then modify fun st => { st with implicits := st.implicits ++ [(i, imp.map (·.name))] }
      ds := ds ++ [i]
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
          let i ← addGlob ⟨k, ty, all.map (·.pred), true, 1⟩ value
          if !imp.isEmpty then modify fun st => { st with implicits := st.implicits ++ [(i, imp.map (·.name))] }
          ds := ds ++ [i]
          continue
      let names ← args.mapM fun a => match a with | .id n => pure n | _ => fail E.unsupported
      if names != bs.map (·.name) then fail E.unsupported
      let some key := Elab.symKey h | fail E.unsupported
      let all := imp ++ bs
      let sc : Scope := (all.map fun b => (b.name, b.ty)).reverse
      let (v, vty) ← term F sc none rhs
      let value := all.foldr (fun b t => Tm.lam b.ty (holdsAt b.pred (.loc 0)) t) v
      let ty := all.foldr (fun b t => Ty.fn b.ty t) vty
      let i ← addGlob ⟨key, ty, all.map (·.pred), false, 1⟩ value
      if !imp.isEmpty then modify fun st => { st with implicits := st.implicits ++ [(i, imp.map (·.name))] }
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
      | some b => (⟨key, .fn b.ty (.fn .real .real), [b.pred, apred], family, 1⟩, Tm.lam b.ty (holdsAt b.pred (.loc 0)) fx)
      | none => (⟨key, .fn .real .real, [apred], family, 1⟩, fx)
    let i ← addGlob g v
    ids := ids ++ [i]
  addLabels labels [] true
  pure (ids.eraseDups, [])

/-- `For B, let $X_p$ denote NP`. -/
def letDenote (b : BindInfo) (sym : MT) (np : List Chunk) : M (List Nat × List Nat) := do
  let (key, family) ← match sym with
    | .sub (.id k) (.id p) => if p == b.name then pure (k, true) else
        fail E.finding (w!"a family defined under a binder carries the binder's variable " ++ b.name ++ w!" as its subscript ($D_c$ for every $c$)")
    -- `\gamma^T`: a family written with a superscript
    | .sup (.id k) (.id p) => if p == b.name then pure (k ++ w!"^", true) else
        fail E.finding (w!"a family defined under a binder carries the binder's variable " ++ b.name ++ w!" as its subscript ($D_c$ for every $c$)")
    | .id k => pure (k, false)
    | _ => fail E.finding w!"the symbol a sentence defines is a name ($X$, $d_0$, $\\Gamma$) or a function of variables ($f(x,y)$)"
  let sc : Scope := [(b.name, b.ty)]
  let (val, vty) ← match np with
    -- the law of $(X, f(X))$ for $X$ uniformly distributed on $[0,1]$
    -- (the interval is a type of the article's vocabulary, with its Lebesgue measure)
    | [.w t, .w l, .w o, .m pair, .w fr, .m [.id x], .w u, .w d, .w on, .m zo] =>
      let iv? ← match Math.parseFormula zo with
        | some zm => Elab.intervalType zm
        | none => pure none
      match iv? with
      | none => fail E.noun
      | some iv =>
      if [t, l, o, fr, u, d, on] == [w!"the", w!"law", w!"of", w!"for", w!"uniformly", w!"distributed", w!"on"] then do
        match Math.parseFormula pair with
        | some (.tuple [e1, e2]) => do
          -- λ A. Leb {x : A(e1(x), e2(x))}, with A a measurable subset of the square
          let set2 : Ty := .fn iv.ty (.fn iv.ty .prop)
          let sc' := (x, iv.ty) :: (w!"", set2) :: sc
          let t1 ← term F sc' none e1
          let t2 ← term F sc' none e2
          let a1 ← coerce t1.1 t1.2 iv.ty
          let a2 ← coerce t2.1 t2.2 iv.ty
          let set := Tm.lam iv.ty .tt (.app (.app (.loc 1) a1) a2)
          let body := Tm.guard (.app (.const iv.measurable1) set) (.app (.const iv.lebesgue) set)
          pure (Tm.lam set2 (.app (.const iv.measurable2) (.loc 0)) body, .fn set2 .real)
        | _ => fail E.unsupported
      else fail E.noun
    | .w t :: rest =>
      if t != w!"the" then fail E.unsupported
      else do
        let ws := wordsOf rest
        -- a notion of the vocabulary with its arguments (`the copula associated with
        -- $\gamma_{T_w}$`)
        let vocabNotion : M (Tm × Ty) := do
          let V := (← get).vocab
          let cands := V.notions.filterMap fun n => (Notation.matchSlots n.name rest []).map fun a => ((n, a), [])
          let elabArgs (args : List (List MTok)) : M (List (Tm × Ty)) := args.mapM fun a => do
            let some m := Math.parseFormula a | fail E.unsupported
            term F sc none m
          let fits (na : Notion × List (List MTok)) : M Unit := do
            let _ ← applyAll na.1.value na.1.ty na.1.doms (← elabArgs na.2)
          match ← theMeaningBy (fun (na : Notion × List (List MTok)) => (na.1.ty, na.1.value)) (·.1.field) fits rest cands with
          | some ((n, args), _) =>
            let ts ← elabArgs args
            applyAll n.value n.ty n.doms ts
          | none => fail E.noun ((ws.intersperse [32]).flatten)
        match mathsOf rest with
        | [arg] => do
          match lookupWords (← get).ops ws with
          | some i =>
            let g := ((← get).globs[i]?).getD default
            let m ← liftO (Math.parseFormula arg) E.unsupported
            let a ← term F sc none m
            applyAll (.glob i) g.ty g.doms [a]
          | none => vocabNotion
        | _ => vocabNotion
    | _ => fail E.unsupported
  let value := Tm.lam b.ty (holdsAt b.pred (.loc 0)) val
  let i ← addGlob ⟨key, .fn b.ty vty, [b.pred], family, 1⟩ value
  pure ([i], [])

/-- `Let DISPLAY denote the NAME, NAME, and NAME NOUNS.`, `Let $f(x)\coloneqq e$ denote the
NAME NOUN.`: each definition, named by one of the names (words that are not read), of an
object of the noun. The variables of a definition `f(x,y)\coloneqq e` range over the
arguments of the noun's objects, in order (with the field `unitsquare`, the points of
`[0,1]` for a copula), and that `f` is such an object is a claim of the sentence. The
noun is the longest end of the last name that is a noun of the article or of its
vocabulary and leaves a name before it. -/
def defsNamed (c : SentCtx) (defs : List MT) (labels : List Codes) (np : List Chunk) :
    M (List Nat × List Nat) := do
  -- the names, separated by `,` and `and`
  let rec split : List Chunk → List Chunk → List (List Chunk) → List (List Chunk)
    | [], cur, acc => (cur.reverse :: acc).reverse
    | ch :: rest, cur, acc =>
      match ch with
      | .p 44 => split rest [] (cur.reverse :: acc)
      | .w w => if w == w!"and" then split rest [] (cur.reverse :: acc) else split rest (ch :: cur) acc
      | _ => split rest (ch :: cur) acc
  let items := (split np [] []).filter (!·.isEmpty)
  if items.length != defs.length then
    fail E.finding w!"after `denote the`, a name for each definition, in their order, and the noun after the last name (the comonotonicity and independence copulas)"
  let last := items.getLast?.getD []
  let st0 ← get
  let mut found : Option BindInfo := none
  for l in ((List.range last.length).filter (· ≥ 1)).reverse do
    if found.isNone then
      found ← tryCatch (some <$> nounPhrase (last.drop (last.length - l))) fun _ => do
        set st0
        pure none
  let some bi := found | fail E.noun (((wordsOf last).intersperse [32]).flatten)
  let mut ds : List Nat := []
  let mut cs : List Nat := []
  for m in defs do
    let ids ← match m with
      | .chain (.app _ args) [(.defeq, _)] => do
        let names ← args.mapM fun a => match a with | .id n => pure n | _ => fail E.unsupported
        let tys := argTypes bi.ty names.length
        if tys.length != names.length then fail E.type
        let bis : List BindInfo := (names.zip tys).map fun (n, t) => ⟨n, t, none⟩
        pure (← multiDefs bis [m] [] []).1
      | _ => pure (← constDefs c none [m] []).1
    for i in ids do
      let g := ((← get).globs[i]?).getD default
      if g.ty != bi.ty then fail E.type
      if let some p := bi.pred then
        let id ← emit c (.app p (.glob i)) []
        cs := cs ++ [id]
    ds := ds ++ ids
  addLabels labels [] true
  pure (ds, cs)

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
  let i ← addGlob ⟨[], .fn s.ty (.fn t.ty .prop), [s.pred, t.pred], false, 1⟩ value
  modify fun st => { st with preds := st.preds ++ [(phrase, i)] }
  pure ([i], [])

/-- `let $S$ denote the class of Ns, that is, NP`: `S` is the class described by
the noun phrase `NP`, and `N` (singular) names it. -/
def defClass (sym : MT) (plural : List Codes) (np : List Chunk) : M (List Nat × List Nat) := do
  let key ← match sym with | .id k => pure k | _ => fail E.unsupported
  -- without `that is, NP`, the class is a noun of the vocabulary
  modify fun st => { st with strongConds := plural.isEmpty }
  let st0 ← get
  -- (a gloss that is not read, `that is, distribution functions on $[0,1]^2$ with uniform
  -- marginals, and we refer to …`, when the class itself is a noun of the vocabulary: the
  -- noun is the definition)
  let b ← tryCatch (nounPhrase (if np.isEmpty then plural.map Chunk.w else np)) fun e => do
    if np.isEmpty || plural.isEmpty then throw e
    set { st0 with strongConds := false }
    tryCatch (nounPhrase (plural.map Chunk.w)) fun _ => throw e
  modify fun st => { st with strongConds := false }
  -- (a noun phrase with a variable describes the members: `the class of functions
  -- $f:[0,1]\to\mathbb{R}$ with $φ$`; the class then has its symbol only)
  -- (`the set of couplings, that is, probability measures $\gamma$ on $[0,1]^2$ with …`: a
  -- gloss with a variable, for a class that is a noun of the vocabulary)
  let b ← if !b.name.isEmpty && !plural.isEmpty then
      tryCatch (do set st0; nounPhrase (plural.map Chunk.w)) fun _ => fail E.unsupported b.name
    else pure b
  if !b.name.isEmpty && !plural.isEmpty then fail E.unsupported b.name
  let p := b.pred.getD (.lam b.ty .tt .tt)
  let i ← addGlob ⟨key, .fn b.ty .prop, [none], false, 1⟩ p
  if plural.isEmpty then return ([i], [])
  let sing := plural.dropLast ++ (plural.getLast?.map singular).toList
  let names := [sing, (sing.getLast?).toList].eraseDups
  modify fun st => { st with nouns := st.nouns ++ names.map (·, i), classes := st.classes ++ [(plural, i)] }
  pure ([i], [])

/-! ## Inline definitions and notions -/

/-- The variables a noun phrase binds: the variables of its formulas (`$m$`, `$1\le m\le n$`). -/
def npVars (np : List Chunk) : List Codes :=
  (mathsOf np).flatMap fun ts => match varName ts with
    | some v => [v]
    | none => ((Grammar.binderMath ts).map (·.1)).getD []

/-- A noun phrase without the formulas that are values of the variables of its modifiers
(`$n$` in `a graph $G$ on $n$ vertices`): those are not variables that it binds. -/
def withoutSlotArgs (V : Vocab) (np : List Chunk) : List Chunk := Id.run do
  -- (`@the midpoint of $A$ and $B$ $M$`: the variable is the last formula)
  if (match np.head? with | some (.w w) => w == w!"@the" | _ => false) then
    return (match np.getLast? with | some c => [c] | none => [])
  let mods := V.mods.filter fun m => Notation.hasSlots m.phrase
  if mods.isEmpty then return np
  let mut drop : List Nat := []
  for k in List.range np.length do
    let suffix := np.drop k
    for m in mods do
      if let some (_, rest) := Notation.matchPrefix m.phrase suffix [] then
        drop := drop ++ (List.range (suffix.length - rest.length)).map (k + ·)
  pure ((np.zipIdx.filter fun (c, i) => match c with | .m _ => !drop.contains i | _ => true).map (·.1))

/-- The variables a binder binds, as its words name them; a condition `If $φ$` binds the
free variables of `φ` other than those of `env` (the variables of the result) and the
terms of sequences. -/
def bindNames1 (st : St) (env : List Codes) : Bind → List Codes
  | .every vs _ => vs
  | .noun np => (mathsOf (withoutSlotArgs st.vocab np)).flatMap fun ts =>
    match (Grammar.seqBound ts).bind fun (l, _) => Grammar.seqVars l with
    | some (x, _, _, _) => [x]
    | none => npVars [.m ts]
  | .ifCond φ =>
    let free := ((dropBoundIndices st φ (freeIds 64 [] φ)).filter fun n => !(st.globs.zipIdx.any fun (g, i) => g.key == n && !g.family && Elab.visibleIn st i) && !constName n).eraseDups
    (seqFree st [] φ free).filter (!env.contains ·)
  | .hyp b => bindNames1 st env b
  | _ => []

def bindNames (st : St) (env : List Codes) (bs : List Bind) : List Codes :=
  bs.flatMap fun b => match b with
    | .many bs => bs.flatMap (bindNames1 st env)
    | .hyp (.many bs) => bs.flatMap (bindNames1 st env)
    | b => bindNames1 st env b

/-- The formulas of a binder's domain and conditions (the ends of a sequence's indices). -/
def bindMaths1 : Bind → List MT
  | .every _ d => [d]
  | .noun np => (mathsOf np).flatMap fun ts =>
    match (Grammar.seqBound ts).bind fun (l, b) => (Grammar.seqVars l).map (·, b) with
    | some ((_, name, lo, hi), bound) => [lo, hi] ++ (Math.parseFormula (name ++ bound)).toList
    | none => (Math.parseFormula ts).toList
  | .ifCond φ => [φ]
  | .hyp b => bindMaths1 b
  | _ => []

def bindMaths (bs : List Bind) : List MT :=
  bs.flatMap fun b => match b with
    | .many bs => bs.flatMap bindMaths1
    | .hyp (.many bs) => bs.flatMap bindMaths1
    | b => bindMaths1 b

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
  let i ← addGlob ⟨[], .fn s.ty .prop, [s.pred], false, 1⟩ (.lam s.ty (holdsAt s.pred (.loc 0)) body)
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
  let params := ((implicitVars st (ids ++ subKeys 64 cond)).eraseDups.filter (!bound.contains ·))
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
  let i ← addGlob ⟨key, ty, (if param.isSome then [none, none] else [none]), param.isSome, 1⟩ value
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
  -- (`$1$-Lipschitz`, `$2$-regular`: a modifier that starts with its variable)
  | .m _ :: _ => V.mods.any fun m => match m.phrase.head? with | some .v | some (.f _) => true | _ => false
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
    let elabArgs (args : List (List MTok)) : M (List (Tm × Ty)) := args.mapM fun a => do
      let some m := Math.parseFormula a | fail E.unsupported
      term F sc none m
    let fits (na : Notion × List (List MTok)) : M Unit := do
      let (_, vty) ← applyAll na.1.value na.1.ty na.1.doms (← elabArgs na.2)
      if vty != x.2 then fail E.type
    match ← theMeaningBy (fun (na : Notion × List (List MTok)) => (na.1.ty, na.1.value)) (·.1.field) fits cs cands with
    | some ((n, args), _) => do
      let ts ← elabArgs args
      let (v, vty) ← applyAll n.value n.ty n.doms ts
      if vty != x.2 then fail E.type
      if vty == .real then pure (some (Tm.eq x.1 v))
      else if vty == .fn .real .real then
        pure (some (Tm.all .real (.eq (.app (shift 1 0 x.1) (.loc 0)) (.app (shift 1 0 v) (.loc 0)))))
      -- (an object of a vocabulary's type: `$G$ is the complete graph on $5$ vertices`)
      else if Elab.isBase vty then pure (some (Tm.eq x.1 v))
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
        -- (a modifier that follows its noun is stated too: `$x$ is orthogonal to $y$`, `$S$ is of measure zero`)
        let cands := V.mods.filterMap fun m => if m.ty == x.2 then
            if Notation.hasSlots m.phrase then (Notation.matchPrefix m.phrase cs []).map fun (_, r) => (m, r) else
            (matchPhrase m.phrase cs).bind fun (v, r) => if v.isNone then some (m, r) else none
          else none
        match ← theMeaning (fun (m : Modifier) => m.pred) (·.field) cs cands with
        | some (m, r) =>
          -- (`$G$ is $3$-regular`: a modifier with variables, of their values)
          let some (args, _) := (if Notation.hasSlots m.phrase then Notation.matchPrefix m.phrase cs [] else some ([], r))
            | fail E.type
          let ts ← (args.zip (Notation.slotTys args.length m.pred)).mapM fun (a, t) => do
            let some mt := Math.parseFormula a | fail E.unsupported
            let v ← term F sc none mt
            if t == .real then Elab.asReal v else if v.2 == t then pure v.1 else fail E.type
          adjs f r ((if Notation.hasSlots m.phrase then Notation.betaApply m.pred (ts ++ [x.1]) else Tm.app m.pred x.1) :: acc)
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
def adjectiveTmCore (sc : Scope) (t : Tm) (ty : Ty) (defDom : Option Tm) (a : List Codes)
    (on : Option MT) : M Tm := do
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
  else
    -- an adjective of the vocabulary, about objects of this type
    let st ← get
    let found := st.vocab.adjectives.filter fun e => e.ty == ty && e.words == a
    match found with
    | [] => fail E.type
    | [e] =>
      if !e.onDomain then
        if on.isSome then fail E.unsupported
        pure (Tm.app e.pred t)
      else
        let dty : Ty := match ty with
          | .fn x _ => .fn x .prop
          | _ => .prop
        let dom : Ty := match ty with
          | .fn x _ => x
          | _ => .prop
        match on with
        | none =>
          let some d := defDom | fail E.unsupported
          pure (Tm.app (.app e.pred t) d)
        | some m => do
          let (d, dt) ← Elab.term 100000 sc none m
          if dt != dty then fail E.type
          let body := Tm.app (.app e.pred t) d
          pure (match defDom with | some dd => .guard (within dom d dd) body | none => body)
    | _ => fail E.ambiguous ((a.intersperse [32]).flatten)


/-- `adjectiveTmCore`, and where the core language has no such property of the type, the
modifier of the vocabulary with these words (`compact` of a set of real numbers in the
field `realsets`, `even` of a real function in `realfunctions`). -/
def adjectiveTm (sc : Scope) (t : Tm) (ty : Ty) (defDom : Option Tm) (a : List Codes)
    (on : Option MT) : M Tm := do
  let st0 ← get
  tryCatch (adjectiveTmCore sc t ty defDom a on) fun e => do
    if on.isSome then throw e
    let m? := st0.vocab.mods.find? fun m => m.ty == ty && !Notation.hasSlots m.phrase &&
      m.phrase == a.map PItem.w
    match m? with
    | some m => set st0; pure (Tm.app m.pred t)
    | none => throw e

/-! ## Claim sentences -/

/-- `if $n$ is sufficiently large` about a variable bound before (`bound`): its threshold would
come after it and say nothing; refused. -/
def checkThreshold (bound : List Codes) (bs : List BindInfo) : M Unit := do
  for b in bs do
    if b.name.take 2 == w!"@N" || b.name.take 2 == w!"@d" then
      let v := b.name.drop 2
      if bound.contains v then
        fail E.finding (v ++ w!" is bound before it is said to be sufficiently large or small: say so where it is introduced (for all sufficiently large $" ++ v ++ w!"$)")

/-- `there is $Q=Q(\nu)$ such that …`: `Q` is chosen after the variables its name lists
(bound in `sc`), and after no other. -/
def checkDependence (sc : Scope) (cl : Clause) : M Unit := do
  if let .aliased ps _ := cl then
    let outer := (sc.map (·.1)).filter fun n => !n.isEmpty && n.head? != some 64
    for (al, nm) in ps do
      let deps := match al with
        | .app _ args => args.filterMap Elab.symKey
        | _ => []
      for d in deps do
        if !outer.contains d then fail E.undefined d
      let name := (Elab.symKey nm).getD []
      match outer.find? (!deps.contains ·) with
      | some v => fail E.finding (name ++ w!" is chosen after " ++ v ++ w!", but its name says it depends only on " ++
          ((deps.intersperse w!", ").flatten) ++ w!": list every variable it may depend on, or move the binder of " ++ v ++
          w!" after the constant")
      | none => pure ()

/-- The points of the functions an operator of the field `hilbert` acts on (the interval, or
the sequences of it for an operator on kernels), and the norm and the class `L^2` there. -/
def opParts (iv : IntervalType) (ty : Ty) : M (Ty × Nat × Nat) := do
  let fn1 := Ty.fn iv.ty .real
  let seqT := Ty.fn .real iv.ty
  let kern := Ty.fn seqT .real
  if ty == Ty.fn fn1 fn1 then
    pure (iv.ty, ← liftO iv.norm1 E.unsupported, ← liftO iv.memL2 E.unsupported)
  else if ty == Ty.fn kern kern then
    pure (seqT, ← liftO iv.normSeq E.unsupported, ← liftO iv.isKernel E.unsupported)
  else fail E.type

/-- A class of functions as the object of an operator's phrase: a set (`L^2_0`), or the
subspace of the component `F_S` of a kernel (`H_S`). -/
def opSet (sc : Scope) (m : MT) (fnTy : Ty) : M Tm := do
  let iv ← liftO (← Elab.hilbertIv) E.unsupported
  match m with
  | .app (.id n) [x] =>
    if n == w!"@hsub" then
      match ← term F sc none x with
      | (.app (.app (.const h) _) st, _) =>
        if some h != iv.hoeff then fail E.unsupported
        pure (.app (.const (← liftO iv.hspace E.unsupported)) st)
      | _ => fail E.finding w!"the subspace of a component $F_S$ of a kernel"
    else do
      let (t, ty) ← term F sc none m
      if ty != Ty.fn fnTy .prop then fail E.type
      pure t
  | _ => do
    let (t, ty) ← term F sc none m
    if ty != Ty.fn fnTy .prop then fail E.type
    pure t

mutual
/-- One clause; `rest` are the following clauses of the sentence (for scopes). -/
def clauseTm (c : SentCtx) (sc : Scope) (onVar : Option BindInfo) (lastRhs : Option MT) :
    Clause → M Tm
  | .fact f | .holds f => prop sc none f
  | .absurd => pure (.not .tt)
  -- (`the statement holds for $E$` is given its clauses before it is read: `expandStmt`)
  | .stmtAt _ | .stmtBelow _ => fail E.unsupported
  | .inst v e hyps stmt => do
    let st ← get
    let some j := sc.findIdx? (·.1 == v) | fail E.undefined v
    let ty := ((sc[j]?).map (·.2)).getD .real
    let same : Bool := match e with
      | .id n => n == v
      | _ => false
    if same then
      -- about the variable itself: the statement as it stands (its hypotheses hold here)
      pure (conjAll (← clauseTms c sc onVar lastRhs stmt))
    else
      let (eT, ety) ← term F sc none e
      if ety != ty then fail E.type
      -- the statement about a new variable of the same name, which is then replaced by `E`:
      -- the domain of the variable, the hypotheses of the result about it, and the claims
      let sc' := (v, ty) :: sc
      let bv : Option BindInfo := ((st.resultBinders.lookup c.target).getD []).find? fun b => b.name == v
      let dom : List Tm := match bv.bind (fun b => b.pred) with
        | some p => [Tm.app (shift (j + 2) 0 p) (.loc 0)]
        | none => []
      let hs ← clauseTms c sc' none none hyps
      let ps ← clauseTms c sc' none none stmt
      pure (Tm.subst eT 0 ((dom ++ hs).foldr Tm.imp (conjAll ps)))
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
    let bs ← declaredInts (← binderInfosRaw.everyIn sc vs d)
    let p ← prop (scopeOf bs ++ sc) none body
    recordBounds bs body
    pure (wrap bs p)
  | .scoped f vs d eq => do
    let bs ← match d with
      | some d => do declaredInts (← binderInfosRaw.everyIn sc vs d)
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
    -- (of an interval type: the order of the numbers)
    let ltA : Tm ← if (← Elab.intervalOf aty).isSome then
        pure (Tm.lt (← coerce (.loc 1) aty .real) (← coerce (.loc 0) aty .real))
      else pure (Tm.lt (.loc 1) (.loc 0))
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
  -- the phrases of an operator (the field `hilbert`)
  | .fixesConsts op => do
    let iv ← liftO (← Elab.hilbertIv) E.unsupported
    let (t, ty) ← term F sc none op
    let (pt, nrm, mem) ← opParts iv ty
    -- for every number `c`: `\lVert T(c)-c\rVert = 0`
    let cst := Tm.lam pt .tt (.loc 1)
    let diff := Tm.lam pt .tt (.sub (.app (.app (shift 2 0 t) (shift 1 0 cst)) (.loc 0)) (.loc 1))
    pure (.all .real (.guard (.app (.const mem) diff) (.eq (.app (.const nrm) diff) (.num 0))))
  | .mapsInto op dom cod norm => do
    let iv ← liftO (← Elab.hilbertIv) E.unsupported
    let (t, ty) ← term F sc none op
    let (pt, _, _) ← opParts iv ty
    let fnTy := Ty.fn pt .real
    let d ← opSet sc dom fnTy
    let e ← opSet sc cod fnTy
    let into := Tm.all fnTy (.imp (.app (shift 1 0 d) (.loc 0)) (.app (shift 1 0 e) (.app (shift 1 0 t) (.loc 0))))
    match norm with
    | none => pure into
    | some (atMost, k) => do
      let kt ← asReal (← term F sc none k)
      let onC ← liftO (if pt == iv.ty then iv.opNorm1 else iv.opNormSeq) E.unsupported
      let n := Tm.app (.app (.const onC) t) d
      pure (.and into (if atMost then .le n kt else .eq n kt))
  | .timesId op k dom => do
    let iv ← liftO (← Elab.hilbertIv) E.unsupported
    let (t, ty) ← term F sc none op
    let (pt, nrm, mem) ← opParts iv ty
    let fnTy := Ty.fn pt .real
    let d ← opSet sc dom fnTy
    let kt ← asReal (← term F sc none k)
    -- for every `g` of the set: `\lVert Tg-kg\rVert = 0`
    let diff := Tm.lam pt .tt (.sub (.app (.app (shift 2 0 t) (.loc 1)) (.loc 0)) (.mul (shift 2 0 kt) (.app (.loc 1) (.loc 0))))
    pure (.all fnTy (.imp (.app (shift 1 0 d) (.loc 0)) (.guard (.app (.const mem) diff) (.eq (.app (.const nrm) diff) (.num 0)))))
  | .hasProps sm fromL ms => do
    -- (the definitions of the cited result are visible here)
    if let some l := fromL then
      if let some e := (← get).resultEnvs.lookup l then
        modify fun st => { st with imports := (st.curEnv, e) :: st.imports }
    let (s', ty) ← term F sc none sm
    let ps ← ms.mapM fun m => prop sc (some (s', ty)) m
    pure (conjAll ps)
  | .firstObs g m => do
    let some iv := (← get).vocab.intervals.find? (·.firstObs.isSome) | fail E.unsupported
    let dc ← liftO iv.firstObs E.unsupported
    let (gt, gty) ← term F sc none g
    if gty != Ty.fn (Ty.fn .real iv.ty) (Ty.fn (Ty.fn .real iv.ty) .real) then fail E.type
    let mt ← asReal (← term F sc none m)
    pure (.app (.app (.const dc) gt) mt)
  | .dependsFirst g m => do
    let iv ← liftO (← Elab.hilbertIv) E.unsupported
    let dc ← liftO iv.dependsFirst E.unsupported
    let (gt, gty) ← term F sc none g
    if gty != Ty.fn (Ty.fn .real iv.ty) .real then fail E.type
    let mt ← asReal (← term F sc none m)
    pure (.app (.app (.const dc) gt) mt)
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
  | .ifClause hyp cl => do
    let h ← clauseTm c sc onVar lastRhs hyp
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
    -- (the domains may use the variables bound outside: `there are
    -- $\varepsilon_1,\ldots,\varepsilon_N\in\{-1,1\}$`)
    let bs ← binderInfos b (sc.reverse.map fun (n, t) => ⟨n, t, none⟩)
    checkDependence sc cl
    let p ← clauseTm c (scopeOf bs ++ sc) onVar lastRhs cl
    pure (bs.foldr (fun b acc => Tm.ex b.ty (match b.pred with
      | some q => .and (.app q (.loc 0)) acc
      | none => acc)) p)
  | .under b cl => do
    -- the domains may use the variables bound outside (`for every integer $b\ge b_0$`):
    -- each predicate is about the scope outside, applied under its own binder and those
    -- before it
    let items : List (BindInfo × Nat) ← match b with
      | .every vs d => do
        let (ty, p) ← binderDomain vs d sc
        pure ((vs.zip (List.range vs.length)).map fun (v, j) => (⟨v, ty, p⟩, j + 1))
      | .noun np => do pure [(← nounPhrase np sc, 0)]
      | _ => do pure ((← binderInfos b (sc.reverse.map fun (n, t) => ⟨n, t, none⟩)).map (·, 0))
    let bs := items.map (·.1)
    checkThreshold (sc.map (·.1)) bs
    let p ← clauseTm c (scopeOf bs ++ sc) onVar lastRhs cl
    -- (a threshold `@…` of `sufficiently large` is existential)
    pure (items.foldr (fun (bi, k) acc =>
      if bi.name.head? == some 64 then Tm.ex bi.ty (match bi.pred with
        | some q => .and (.app (shift k 0 q) (.loc 0)) acc
        | none => acc)
      else Tm.all bi.ty (match bi.pred with
        | some q => .imp (.app (shift k 0 q) (.loc 0)) acc
        | none => acc)) p)
  | .existsNP np unique cl => do
    let b ← match ← pdeNoun np with
      | some [b] => pure b
      | _ => nounPhrase np sc
    if b.name.isEmpty then fail E.unsupported
    if let some cl := cl then checkDependence sc cl
    -- `P x`: the noun phrase and the clause about `x`, where `x` is bound (the
    -- predicate of a noun phrase is stated there)
    let inner ← match cl with
      | some cl => clauseTm c ((b.name, b.ty) :: sc) onVar lastRhs cl
      | none => pure .tt
    let px := Tm.and (holdsAt b.pred (.loc 0)) inner
    -- (`exactly one`: every `y` with `P y` is `x`; `P y` under one more binder)
    let body := if unique then
        Tm.and px (.all b.ty (.imp (shift 1 1 px) (.eq (.loc 0) (.loc 1))))
      else px
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
        let np := (kw [w!"a"] np <|> kw [w!"an"] np).getD np
        let b ← tryCatch (nounPhrase np outer) fun e =>
          if e.code == E.noun || e.code == E.unsupported then fail E.prose else throw e
        bs := bs ++ [b]
    let sc' := (bs.map fun b => (b.name, b.ty)).reverse ++ sc
    for cl in cls do checkDependence sc cl
    let ps ← clauseTms c sc' onVar lastRhs cls
    -- (the predicate of each object refers to the objects before it, stated where the
    -- object is bound)
    pure (bs.foldr (fun b acc => Tm.ex b.ty (match b.pred with
      | some q => .and (.app q (.loc 0)) acc
      | none => acc)) (Elab.conjAll ps))
  | .noneExist cl => do pure (.not (← clauseTm c sc onVar lastRhs cl))
  | .infinitelyMany np cl => do
    let b ← nounPhrase np sc
    if b.ty != .real then fail E.type
    let inner ← match cl with
      | some cl => do
        if b.name.isEmpty then fail E.unsupported
        clauseTm c ((b.name, b.ty) :: sc) onVar lastRhs cl
      | none => pure .tt
    -- the set of the numbers described is not finite (it has no number of elements)
    let set := Tm.lam .real .tt (.and (holdsAt b.pred (.loc 0)) inner)
    pure (.not (.ex .real (.app (.app (.prim .cardIs) (shift 1 0 set)) (.loc 0))))
  | .both cls => do
    let ps ← cls.mapM (clauseTm c sc onVar lastRhs)
    pure (Elab.conjAll ps)
  | .iffC p q => do
    pure (.iff (← clauseTm c sc onVar lastRhs p) (← clauseTm c sc onVar lastRhs q))
  | .orC p q => do
    pure (.or (← clauseTm c sc onVar lastRhs p) (← clauseTm c sc onVar lastRhs q))
  | .aliased ps cl => do
    -- `Q(\nu)` stands for `Q` in the clause
    let saved := (← get).aliases
    let keyed := ps.filterMap fun (al, nm) => match al with
      | .app h args => do
        let k ← Elab.symKey h
        let ks ← args.mapM Elab.symKey
        some (k, ks, nm)
      | _ => none
    modify fun st => { st with aliases := keyed ++ st.aliases }
    let p ← clauseTm c sc onVar lastRhs cl
    modify fun st => { st with aliases := saved }
    pure p
  | .forEveryNP cl np => do
    let b ← nounPhrase np sc
    if b.name.isEmpty then fail E.unsupported
    let p ← clauseTm c (scopeOf [b] ++ sc) onVar lastRhs cl
    pure (wrap [b] p)
  | .isA s np neg => do
    -- words with which no phrase of the vocabulary starts are prose
    unless knownStart (← get) np do fail E.prose
    let x ← term F sc none s
    -- (a plural after `are`, `$x$ and $y$ are binary words of length $3$`: the phrase in the
    -- singular, with its article, one plural word at a time)
    let singulars : List (List Chunk) := match np with
      | .w a :: _ =>
        if a == w!"a" || a == w!"an" then [] else
        (List.range np.length).filterMap fun i => match (np[i]? : Option Chunk) with
          | some (Chunk.w w) =>
            if w.length > 2 && w.getLast? == some 115 && w.dropLast.getLast? != some 115 then
              some (Chunk.w w!"a" :: np.set i (Chunk.w w.dropLast))
            else none
          | _ => none
      | _ => []
    let st0 ← get
    -- words that are not the vocabulary's are prose
    let p ← tryCatch (vocabPredicate sc x np) fun e => do
      let mut res : Option Tm := none
      for np' in singulars do
        if res.isNone then
          set st0
          res ← tryCatch (some <$> vocabPredicate sc x np') fun _ => pure none
      match res with
      | some p => pure p
      | none =>
        if !singulars.isEmpty then set st0
        if e.code == E.noun || e.code == E.unsupported then fail E.prose e.detail else throw e
    pure (if neg then .not p else p)
  | .everyIs np names disj => do
    let b ← nounPhrase np
    let st1 ← get
    -- (notions of the article; or adjectives and nouns of the vocabulary, `Every cyclic group
    -- $G$ is abelian`)
    let ps ← tryCatch (names.mapM (notionApp (.loc 0, b.ty))) fun e => do
      set st1
      tryCatch (names.mapM fun nm => vocabPredicate ((b.name, b.ty) :: sc) (.loc 0, b.ty) (nameChunks nm))
        fun _ => throw e
    pure (wrap [b] (if disj then disjAll ps else conjAll ps))
  | .iff p q => do pure (.iff (← prop sc none p) (← prop sc none q))
  | .compare l r rr => do relTm r (← term F sc none l) (← term F sc none rr)
  | .adjectives s adjs => do
    -- `$h_t(u,\cdot)$`: the function of the placeholder
    let isDot (a : MT) : Bool := match a with | .id n => n == w!"\\cdot" | _ => false
    let monoOf (a : List Codes) : Option Mono :=
      if a == [w!"nondecreasing"] || a == [w!"non", w!"decreasing"] then some .nondecreasing
      else if a == [w!"nonincreasing"] || a == [w!"non", w!"increasing"] then some .nonincreasing
      else if a == [w!"strictly", w!"increasing"] then some .increasing
      else if a == [w!"strictly", w!"decreasing"] then some .decreasing
      else none
    match s with
    | .app g args =>
      if args.any isDot then
        -- monotone on a domain: the map of the placeholder
        let x : Codes := w!"\\@dotvar"
        let body := MT.app g (args.map fun a => if isDot a then MT.id x else a)
        let ps ← adjs.mapM fun (a, on) => do
          let some mono := monoOf a | fail E.unsupported
          let some d := on | fail E.unsupported
          monoTm sc (.conj [.mapsto (.id x) body, .chain (.id x) [(.mem, d)]]) mono
        return conjAll ps
      else pure ()
    -- `the map $\theta\mapsto e$ is continuous on $[0,1]$`: a real function of `θ` on the
    -- domain, whose values there are defined
    | .mapsto (.id v) body =>
      if adjs.all (fun (_, on) => on.isSome) then
        let ps ← adjs.mapM fun (a, on) => do
          let some d := on | fail E.unsupported
          let (_, pd) ← domainOf true d sc
          let (fn, _) ← Elab.lam F sc (.id v) [.real] (some .real) body
          let fn := onDomain pd fn
          adjectiveTm sc fn (.fn .real .real) (some (pd.getD (.lam .real .tt .tt))) a on
        return conjAll ps
      else pure ()
    | _ => pure ()
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
        let ltA : Tm ← if (← Elab.intervalOf b.ty).isSome then
            pure (Tm.lt (← coerce (.loc 1) b.ty .real) (← coerce (.loc 0) b.ty .real))
          else pure (Tm.lt (.loc 1) (.loc 0))
        parts := parts ++ [Tm.all b.ty (.all b.ty (Tm.mkImp (holdsAt b.pred (.loc 1))
          (Tm.mkImp (holdsAt b.pred (.loc 0)) (.imp ltA (.lt fxx fyy)))))]
        infos := infos ++ [(v, body)]
      | _ => fail E.unsupported
    modify fun st => { st with lastMaps := infos }
    pure (conjAll parts)
  | .forCond f cond => do
    let before : List BindInfo := (sc.map fun (n, t) => (⟨n, t, none⟩ : BindInfo)).reverse
    let bs ← tryCatch (binderInfosRaw (.ifCond cond) before) fun _ => pure []
    if bs.isEmpty then
      pure (Tm.imp (← prop sc none cond) (← prop sc none f))
    else
      pure (wrap bs (← prop (scopeOf bs ++ sc) none f))
  | .monoFns fs d mono => do
    -- each function, applied to a fresh variable of the domain
    let x : Codes := w!"\\@monovar"
    let parts ← fs.mapM fun f =>
      -- (`$h_t(u,\cdot)$`: the placeholder is the variable)
      let body := match f with
        | .app g args =>
          let isDot (a : MT) : Bool := match a with | .id n => n == w!"\\cdot" | _ => false
          if args.any isDot then MT.app g (args.map fun a => if isDot a then MT.id x else a)
          else MT.app f [MT.id x]
        | _ => .app f [.id x]
      monoTm sc (.conj [.mapsto (.id x) body, .chain (.id x) [(.mem, d)]]) mono
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

/-- Does the local `j` occur in the term? -/
def usesLoc (j : Nat) (t : Tm) : Bool := Tm.subst (.num 0) j t != Tm.subst (.num 1) j t

/-- `t`, written in another scope: its local `k` becomes the term `targets[k]` of that
scope, all at once (`targets` covers the scope of `t`). `none` if `t` uses a local that
has no target. -/
def relocate (targets : List (Option Tm)) (t : Tm) : Option Tm :=
  let n := targets.length
  -- at step `k` the locals `k, …, n-1` of `t` are `0, …, n-1-k`, and what has been put
  -- in lies above them: it comes down by one with each later step
  targets.zipIdx.foldl (fun acc (tgt, k) => acc.bind fun t =>
    match tgt with
    | some s => some (Tm.subst (shift (n - 1 - k) 0 s) 0 t)
    | none => if usesLoc 0 t then none else some (Tm.subst (.num 0) 0 t)) (some t)

/-- `the statement holds for $E$`, in the proof of a result: the clauses of the statement,
for the variable of the induction (`We argue by induction on $n$.`; without that
sentence, `E` is the variable itself). The variable is one that the result introduces,
and no other variable of the result may depend on it: the statement is then a statement
about it. -/
def stmtInst (c : SentCtx) (e : MT) (var : Option Codes := none) : M Clause := do
  if c.ctx.kind != .proof then fail E.prose
  let st ← get
  let rbs := (st.resultBinders.lookup c.target).getD []
  let some (some stmt) := st.resultStmts.lookup c.target
    | fail E.finding w!"`the statement` needs a statement about the variables of the result: state the claims of the result without binders of their own inside a clause, and without `the minimum` or `the maximum` as their topic"
  if stmt.isEmpty then fail E.prose
  let named : Option Codes := var <|> match st.inductionVar with
    | some (env, n) => if env == c.ctx.env then some n else none
    | none => none
  let v ← match named, e with
    | some n, _ => pure n
    | none, .id n =>
      if rbs.any (·.name == n) then pure n
      else fail E.finding w!"the statement for a value of which variable? Say so before (We argue by induction on $n$.); the variable is one that the result introduces (Let $n$ be a positive integer. Then …)"
    | none, _ => fail E.finding w!"the statement for a value of which variable? Say so before (We argue by induction on $n$.)"
  let some iv := rbs.findIdx? (·.name == v)
    | fail E.finding w!"an induction on a variable that the result does not introduce: introduce it in the result (Let $n$ be a positive integer. Then …), so that the statement is a statement about it"
  -- (a later variable of the result whose domain uses the variable)
  if (rbs.zipIdx.any fun (b, i) => i > iv && (match b.pred with
      | some p => usesLoc (i - 1 - iv) p
      | none => false)) then
    fail E.finding w!"another variable of the result depends on the variable of the induction: the statement for another value of it is not determined; write the hypothesis out (Assume that $…$.)"
  let hyps := (((st.resultHyps.lookup c.target).getD []).filter fun h =>
    h.item == 0 && !h.contra && (clauseMaths h.clause).any fun m => (freeIds 64 [] m ++ subKeys 64 m).contains v).map (·.clause)
  pure (.inst v e hyps stmt)

/-- A clause with `the statement holds for …` given its clauses. -/
def expandStmt (c : SentCtx) : Clause → M Clause
  | .stmtAt e => stmtInst c e
  | .under b (.stmtAt e) => do pure (.under b (← stmtInst c e))
  -- `for all smaller values`: for every `m<n`, with a name `m` that no article uses
  | .stmtBelow named => do
    let st ← get
    let ind : Option Codes := match st.inductionVar with
      | some (env, n) => if env == c.ctx.env then some n else none
      | none => none
    let n ← match ind, named with
      | some n, some v => if v == n then pure n else
          fail E.finding (w!"the induction is on " ++ n ++ w!": the statement for smaller values of another variable is not its hypothesis; write it out (Assume that $…$ for all $m<" ++ n ++ w!"$.)")
      | some n, none => pure n
      | none, some v => pure v
      | none, none => fail E.finding w!"smaller values of which variable? Say so before (We argue by induction on $n$.), or name it (for all smaller values of $n$)"
    let m := n ++ w!"@below"
    pure (.under (.every [m] (.ival (.neg (.id w!"\\infty")) (.id n) true true)) (← stmtInst c (.id m) (some n)))
  | cl => pure cl

/-- A definition made under hypotheses (`Assume that $x\ne0$. Set $y\coloneqq\frac1x$.`)
is made for the values of its variables for which the hypotheses can hold: that becomes
part of the domain of its last parameter. So the definition is well defined if its formula
is meaningful there (`∀ x, x ≠ 0 → x ≠ 0`), and each use of it asks for it.

* A hypothesis that speaks only about the variables of the definition is taken as it is.
* A hypothesis that also speaks about other variables of the result or proof (`Assume
  that $xz\ne0$.` says something about `x` and about `z`, and `\frac1x` uses `x` alone)
  is taken as what it says about the definition's variables: that there are such other
  variables, in their domains and with the hypotheses about them alone (`∃ z, xz ≠ 0`).
  The definition does not become a function of `z`.

A hypothesis that is left out only makes the domain larger: the definition then has to
be meaningful on more values, never on fewer. -/
def defsUnderHyps (c : SentCtx) (ds : List Nat) : M Unit := do
  if c.ctx.kind == .text then return
  for i in ds do
    let st ← get
    let some all := st.telescopes.lookup i | continue
    let some g := st.globs[i]? | continue
    let some v := st.values[i]? | continue
    let names := all.map (·.name)
    let envNames := st.envBinders.map (·.name)
    -- the variables of the result or proof that a hypothesis in force speaks about
    let about (h : Hyp) : List Codes :=
      (((clauseMaths h.clause).flatMap fun m => freeIds 64 [] m ++ subKeys 64 m).filter envNames.contains).eraseDups
    -- about parameters of the definition only
    let own := st.envHyps.filter fun h => !(about h).isEmpty && (about h).all names.contains
    -- about parameters and other variables
    let mixed := st.envHyps.filter fun h => (about h).any names.contains && !(about h).all names.contains
    -- the other variables, and those that their domains use (`c\in[0,n]` brings `n`)
    let bs := st.envBinders
    let needs (b : BindInfo) (j : Nat) : List Codes := match b.pred with
      | some p => (List.range j).filterMap fun m =>
          if usesLoc (m + 1) p then (bs[j - 1 - m]?).map (·.name) else none
      | none => []
    let rec close : Nat → List Codes → List Codes
      | 0, e => e
      | f + 1, e =>
        let more := (((bs.zipIdx.filter fun (b, _) => e.contains b.name).flatMap fun (b, j) => needs b j).filter
          fun n => !names.contains n && !e.contains n).eraseDups
        if more.isEmpty then e else close f (e ++ more)
    let others := close bs.length ((mixed.flatMap about).filter fun n => !names.contains n).eraseDups
    let otherBinds := bs.filter fun b => others.contains b.name
    -- about those other variables alone
    let side := if mixed.isEmpty then [] else
      st.envHyps.filter fun h => !(about h).isEmpty && (about h).all others.contains
    if own.isEmpty && mixed.isEmpty then continue
    let sc := scopeOf all
    let ps ← own.mapM fun h => clauseTm c sc none none h.clause
    -- `∃ z, …`: the other variables, their domains, and the hypotheses
    let proj : List Tm ← if mixed.isEmpty then pure [] else do
      let inner := all ++ otherBinds
      let scE := scopeOf inner
      let qs ← (side ++ mixed).mapM fun h => clauseTm c scE none none h.clause
      -- where a variable is in the scope of the `∃`s
      let place (n : Codes) : Option Tm :=
        (inner.findIdx? (·.name == n)).map fun q => Tm.loc (inner.length - 1 - q)
      -- the domain of each, written there (it was written where the variable and the
      -- variables before it are bound)
      let doms := bs.zipIdx.filterMap fun (b, j) =>
        if !others.contains b.name then none else do
          let p ← b.pred
          let self ← place b.name
          let p' ← relocate ((List.range (j + 1)).map fun m => (bs[j - m]?).bind fun b' => place b'.name) p
          some (Tm.app p' self)
      pure [otherBinds.foldr (fun b acc => Tm.ex b.ty acc) (Elab.conjAll (doms ++ qs))]
    let hyp := Elab.conjAll (ps ++ proj)
    -- the domain of the last parameter, in the value and among the domains of the arguments
    let rec under : Nat → Tm → Tm
      | 0, t => t
      | 1, .lam t d b => .lam t (Tm.mkAnd d hyp) b
      | k + 1, .lam t d b => .lam t d (under k b)
      | _, t => t
    let some last := all.getLast? | continue
    let dom : Tm := match last.pred with
      | some p => .lam last.ty .tt (.and (.app (shift 1 0 p) (.loc 0)) (shift 1 1 hyp))
      | none => .lam last.ty .tt (shift 1 1 hyp)
    let doms := g.doms.take (all.length - 1) ++ [some dom] ++ g.doms.drop all.length
    set { st with
      globs := st.globs.set i { g with doms := doms },
      values := st.values.set i (under all.length v) }

/-- A later clause of the sentence has its own hypothesis (`If $φ$, A, and if $ψ$, B`). -/
def laterIfC (cls : List CClause) : Bool :=
  (cls.drop 1).any fun cl => match cl.clause with | .ifThen .. | .ifClause .. => true | _ => false

/-- The claims of one sentence. `exactly one` takes the following clauses into its scope. -/
def claimSentenceCore (c : SentCtx) (topic : Topic) (binds : List Bind) (cls : List CClause) : M (List Nat) := do
  modify fun st => { st with topic := if topic == .none then st.topic else topic }
  -- (`Hence the statement holds for $n+1$.`)
  let cls ← cls.mapM fun cl => do pure { cl with clause := ← expandStmt c cl.clause }
  -- `If CLAUSE, then A and B`: the hypothesis that the grammar read with the first clause is
  -- one of every later clause too, unless a later clause has its own (as for a hypothesis
  -- written as a binder below)
  let cls := match cls with
    | first :: rest =>
      if laterIfC cls then cls else
      match first.clause with
      | .ifClause h _ => first :: rest.map fun cl => { cl with clause := Clause.ifClause h cl.clause }
      | .ifThen φ _ => first :: rest.map fun cl => { cl with clause := Clause.ifThen φ cl.clause }
      | _ => cls
    | [] => []
  -- `If $φ$, …` about variables that are already bound (by the result or a fixed
  -- variable) is a hypothesis: of the first clause when a later clause has its own,
  -- otherwise of every clause
  let st0 ← get
  let known := st0.envBinders.map (·.name) ++ (st0.fixed.filter (·.1 == c.ctx.sec)).map (·.2.name)
  -- (also about the variables of the sentence's binders before it: `For every real $x$,
  -- if $x>0$, then …`)
  let isHyp (known : List Codes) (b : Bind) : Bool := match b with
    | .ifCond φ =>
      let fr := ((dropBoundIndices st0 φ (freeIds 64 [] φ)).filter fun n => !(st0.globs.zipIdx.any fun (g, i) => g.key == n && !g.family && Elab.visibleIn st0 i) && !constName n).eraseDups
      let fr := seqFree st0 [] φ fr
      -- (`U_1` of a known `U` is a term of that sequence)
      let fr := fr.map fun n =>
        let base := n.takeWhile (· != 95)
        if base.length + 1 < n.length && known.contains base && !known.contains n &&
            (n.drop (base.length + 1)).all (fun c => 48 ≤ c && c ≤ 57) then base else n
      !fr.isEmpty && fr.all known.contains
    | _ => false
  let knownAt (k : Nat) : List Codes := known ++ bindNames st0 known (binds.take k)
  let hyps := binds.zipIdx.filterMap fun (b, k) => if isHyp (knownAt k) b then some b else none
  let binds := binds.zipIdx.filterMap fun (b, k) => if isHyp (knownAt k) b then none else some b
  -- `If $n$ is an even integer,`, `If $a$ and $b$ are positive,` about variables that are
  -- already bound (by the result, or by a binder before it): a hypothesis about them;
  -- otherwise binders
  let hypNoun (known : List Codes) (b : Bind) : Option Clause := match b with
    | .noun np => match np.reverse with
      | .m ts :: rest =>
        -- (a sequence `x_1,\ldots,x_n` of the result: each of its terms)
        match Grammar.seqVars ts with
        | some (x, _, _, _) => if known.contains x then Grammar.seqEach ts rest.reverse else none
        | none => do
          let m ← Math.parseFormula ts
          let v ← Elab.symKey m
          if known.contains v then some (Clause.isA m rest.reverse false) else none
      | _ => none
    | .ifCond φ => some (.fact φ)
    | _ => none
  let asHyp (known : List Codes) (b : Bind) : Option Clause := match b with
    | .hyp (.many bs) => do
      let cs ← bs.mapM (hypNoun known)
      -- (a condition alone is not a binder written as a hypothesis)
      if cs.all (fun c => match c with | .fact _ => true | _ => false) then none else
      some (.both cs)
    | .hyp b => hypNoun known b
    | _ => none
  let (hypCls, keep) := binds.zipIdx.foldl (fun (hs, ks) (b, k) =>
      match asHyp (known ++ bindNames st0 known (binds.take k)) b with
      | some h => (hs ++ [h], ks)
      | none => (hs, ks ++ [b])) (([] : List Clause), ([] : List Bind))
  let binds := keep
  let cls := hypCls.foldr (fun h acc =>
    if laterIfC cls then match acc with
      | cl :: rest => { cl with clause := Clause.ifClause h cl.clause } :: rest
      | [] => []
    else acc.map fun cl => { cl with clause := Clause.ifClause h cl.clause }) cls
  let laterIf := (cls.drop 1).any fun cl => match cl.clause with | .ifThen .. => true | _ => false
  let cls := hyps.foldr (fun h acc => match h with
    | .ifCond φ =>
      if laterIf then match acc with
        | cl :: rest => { cl with clause := Clause.ifThen φ cl.clause } :: rest
        | [] => []
      else acc.map fun cl => { cl with clause := Clause.ifThen φ cl.clause }
    | _ => acc) cls
  -- the hypotheses of the result or proof (`Assume that …`, the heading of a case): every
  -- claim is made under them, the first hypothesis outermost
  let cls := match c.ctx.kind with
    | .text => cls
    | _ => st0.envHyps.foldr (fun h acc => acc.map fun cl =>
        { cl with clause := Clause.ifClause h.clause cl.clause }) cls
  -- variables bound by the opening binders of the current result carry over to
  -- its later sentences (`For $w\in[0,1]$, … . In particular, … w …`), and a
  -- variable introduced in a proof (`Let $x\in A$.`) to the proof's later steps; the
  -- domains of the sentence's binders may use them (`If $x_1,\ldots,x_n$ are …`)
  let st ← get
  let inResult := match c.ctx.kind with | .result _ => true | _ => false
  let inScope := match c.ctx.kind with | .result _ | .proof => true | _ => false
  let envNames := st.envBinders.map (·.name)
  let bNames := bindNames st (if inScope then envNames else []) binds
  -- `On I,`: the sentence's single free variable ranges over I
  let onVar ← match binds.find? (fun b => match b with | .on _ => true | _ => false) with
    | some (.on d) => do
      let (_, p) ← domainOf true d
      let free := (cls.flatMap (fun cl => (clauseMaths cl.clause).flatMap (freeIds 64 bNames))).eraseDups
      let free := free.filter fun n => !(st.globs.zipIdx.any fun (g, i) => g.key == n && Elab.visibleIn st i)
      match free with
      | [v] => pure (some (⟨v, .real, p⟩ : BindInfo))
      | _ => fail E.free free.flatten
    | _ => pure none
  let isGlob (n : Codes) : Bool := st.globs.zipIdx.any fun (g, i) => g.key == n && !g.family && Elab.visibleIn st i
  let domEnv := if inScope then ((bindMaths binds).flatMap fun m => seqFree st bNames m (freeIds 64 bNames m)).filter
      fun n => envNames.contains n else []
  -- (binders whose domains use variables of the result come after all of them)
  let inherited := if !domEnv.isEmpty then st.envBinders
    else if inScope && !st.envBinders.isEmpty then
      let known := bNames ++ onVar.toList.map (·.name)
      let clBound := cls.flatMap fun cl => (cl.binds.flatMap fun b => match b with
        | .every vs _ => vs | _ => []) ++ (match cl.clause with
          | .scoped _ vs _ _ | .every vs _ _ => vs | _ => [])
      let free := (cls.flatMap (fun cl => clauseFree st (known ++ clBound) cl)).eraseDups
      -- a variable of the result shadows a definition of the same name
      let free := free.filter fun n => envNames.contains n || !isGlob n
      usedBinders st.envBinders (free ++ domEnv)
    else []
  -- (the binders' domains are in the scope of the inherited binders)
  let bs ← bindersInfos binds inherited
  checkThreshold known bs
  if inResult && !bs.isEmpty then
    -- (a binder is in the scope of those before it in the list: new binders that use
    -- variables of the result come after them)
    if domEnv.isEmpty then
      modify fun st => { st with envBinders := bs ++ st.envBinders.filter fun b => !(bs.any (·.name == b.name)) }
    else modify fun st => { st with envBinders := st.envBinders ++ bs }
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
        let domFree := (cbDoms.flatMap (freeIds 64 [])).filter fun n => !(stNow.globs.zipIdx.any fun (g, i) => g.key == n && Elab.visibleIn stNow i)
        let inh := usedBinders inherited (free ++ domFree)
        let hasOwn := !cl.binds.isEmpty
        -- (the sentence's binders may depend on any inherited binder)
        let outer := if hasOwn then inh else (if domEnv.isEmpty then inh else inherited) ++ bs ++ onVar.toList
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
              let bis ← declaredInts (← binderInfosRaw.everyIn (scopeOf (outer ++ cbs)) vs d)
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

def claimSentence (c : SentCtx) (topic : Topic) (binds : List Bind) (cls : List CClause) : M (List Nat) := do
  -- definitions of the sentence (`… for $F(x)=e$`): made first; a later sentence may
  -- define the same symbol again (`Similarly, … for $F(x)=e'$`), and then means that one
  let fds := cls.flatMap (·.forDefs)
  for d in fds do
    let key := match d with
      | .chain (.app h _) _ | .chain h _ => (Elab.symKey h).getD []
      | _ => []
    let st ← get
    let old := st.forGlobs.filter fun i => (st.globs[i]?).any (·.key == key) && Elab.visibleIn st i
    -- (the earlier one is no longer visible: its environment is one that never is current)
    modify fun st => { st with locals := st.locals.map fun (i, e) => if old.contains i then (i, 1000000000) else (i, e) }
    let n0 := (← get).globs.length
    discard <| inlineDef c [] d
    let n1 := (← get).globs.length
    -- (in the running text, the definition is local to its section's text: as in a proof)
    modify fun st => { st with forGlobs := st.forGlobs ++ (List.range (n1 - n0)).map (n0 + ·) }
    if c.ctx.kind == .text then
      modify fun st => { st with locals := st.locals ++ (List.range (n1 - n0)).map fun k => (n0 + k, c.ctx.env) }
  claimSentenceCore c topic binds cls

/-- The number of quantities that the article has introduced without defining them:
the definitions whose value is a constant after those of the vocabulary. -/
def undefinedCount (st : St) : Nat :=
  (st.values.filter fun v => match v with
    | .const j => st.vocab.consts.length ≤ j
    | _ => false).length

/-- `Let $\chi(G)$ denote the chromatic number of a graph $G$.`: the symbol `\chi` for a
quantity that neither the article nor its vocabulary defines. Its arguments are the
variables of the noun phrases, in the order of the left side, and its values are of the
kind that its name says: a `number` (`constant`, `value`, `quantity`) is a real number, and
a name that ends with a noun (`complement graph`) is an object of that noun's type. No
property of the values is assumed. The symbol is a definition of the article whose
value is a constant without a meaning (`#leanify_semantics` declares it `opaque`): what
is proved about it holds whatever it is. -/
def undefinedDef (c : SentCtx) (lhs : MT) (words : List Codes) (args : List (List Chunk)) :
    M (List Nat × List Nat) := do
  if c.ctx.kind != .text then fail E.prose
  let st ← get
  let V := st.vocab
  -- the kind of its values: the last word before an `of` of the name
  let head := words.takeWhile (· != w!"of")
  let resTy ← match head.getLast? with
    | none => fail E.unsupported
    | some w =>
      if [w!"number", w!"constant", w!"value", w!"quantity"].contains w then pure Ty.real else
      let cs : List Chunk := head.map Chunk.w
      -- the noun at its end, the longest first
      let noun := (List.range head.length).findSome? fun p =>
        V.nouns.findSome? fun n => match matchPhrase n.sing (cs.drop p) with
          | some (none, []) => some n.ty
          | _ => none
      match noun with
      | some t => pure t
      | none => fail E.finding (quoted head ++ w!" does not say what kind of object it is: the name of a quantity that the article does not define ends with a word for a number (the chromatic number of a graph $G$), with a noun of the article (the line graph of a graph $G$), or with a word that the preamble declares, as a noun (\\usepackage[notions={" ++ (head.getLast?.getD []) ++ w!"}]{leanify}) or as the name of a number (\\usepackage[quantities={" ++ (head.getLast?.getD []) ++ w!"}]{leanify})")
  -- the left side: a symbol, or a symbol applied to the variables of the arguments
  let (key, vars) ← match lhs with
    | .app h as => do
      let some k := Elab.symKey h | fail E.unsupported
      let vs ← as.mapM fun a => match Elab.symKey a with
        | some v => pure v
        | none => fail E.unsupported
      pure (k, vs)
    | m => do
      let some k := Elab.symKey m | fail E.unsupported
      pure (k, [])
  let bs ← args.mapM fun np => nounPhrase np
  if vars.eraseDups.length != vars.length || vars.length != bs.length ||
      !(vars.all fun v => bs.any (·.name == v)) then
    fail E.finding (w!"the arguments of " ++ key ++ w!" are the variables of the noun phrases after its name, each once (Let $\\chi(G)$ denote the chromatic number of a graph $G$.)")
  let ordered := vars.filterMap fun v => bs.find? (·.name == v)
  if (← lookupGlob key).isSome then fail E.redefined key
  let j := V.consts.length + undefinedCount st
  let i ← addGlob ⟨key, tyWrap (ordered.map (·.ty)) resTy, ordered.map (·.pred), false, 1⟩ (.const j)
  modify fun st => { st with named := st.named ++ [(words, i)] }
  pure ([i], [])

/-- The definition of `L` (`j(n)`) by a description: the least (greatest) number that the
noun phrase and the clause describe, defined only when there is one; or how many numbers
they describe, defined only when finitely many. The variables of `L` range as the
binders `bs` before it say (the real numbers otherwise); the variables of the result or
section the description uses are implicit parameters. -/
def descDef (c : SentCtx) (bs : List BindInfo) (lhs : MT) (kind : DescKind) (np : List Chunk)
    (cond : Option Clause) : M (List Nat × List Nat) := do
  let (hd, args) := match lhs with
    | .app h as => (h, as)
    | _ => (lhs, [])
  let some key := Elab.symKey hd | fail E.finding w!"the symbol a sentence defines is a name ($X$, $d_0$, $\\Gamma$) or a function of variables ($f(x,y)$)"
  let argNames ← args.mapM fun a => match a with | .id n => pure n | _ => fail E.finding w!"the symbol a sentence defines is a name ($X$, $d_0$, $\\Gamma$) or a function of variables ($f(x,y)$)"
  let st ← get
  -- the variables the description uses, apart from its own
  let own := npVars np
  let maths := (mathsOf np).filterMap Math.parseFormula ++ (cond.map clauseMaths).getD []
  let ids := (maths.flatMap (freeIds 64 [])).filter (!own.contains ·)
  let used := ids ++ implicitVars st (ids ++ maths.flatMap (subKeys 64))
  let imp := bs.filter fun b => used.contains b.name && !argNames.contains b.name
  let argInfo : List BindInfo := argNames.map fun n => match bs.find? (·.name == n) with
    | some b => b
    | none => ⟨n, .real, none⟩
  let all := imp ++ argInfo
  let sc := scopeOf all
  let b ← nounPhrase np sc
  if b.ty != .real then fail E.type
  let inner ← match cond with
    | some cl => do
      if b.name.isEmpty then fail E.unsupported
      clauseTm c ((b.name, b.ty) :: sc) none none cl
    | none => pure .tt
  -- `P x`: the noun phrase and the clause about `x`, where `x` is bound
  let px := match cond with
    | some _ => Tm.and (holdsAt b.pred (.loc 0)) inner
    | none => holdsAt b.pred (.loc 0)
  let v := match kind with
    | .least => Tm.the .real (.and px (.all .real (.imp (shift 1 1 px) (.le (.loc 1) (.loc 0)))))
    | .greatest => Tm.the .real (.and px (.all .real (.imp (shift 1 1 px) (.le (.loc 0) (.loc 1)))))
    | .count => Elab.cardTm (.lam .real .tt px)
  let value := all.foldr (fun b acc => Tm.lam b.ty (holdsAt b.pred (.loc 0)) acc) v
  let ty := all.foldr (fun b acc => Ty.fn b.ty acc) Ty.real
  let i ← addGlob ⟨key, ty, all.map (·.pred), false, 1⟩ value
  if !imp.isEmpty then modify fun st => { st with implicits := st.implicits ++ [(i, imp.map (·.name))] }
  match c.ctx.kind with
  | .text => pure ()
  | _ => modify fun st => { st with locals := st.locals ++ [(i, c.ctx.env)] }
  pure ([i], [])

/-- `Let B, …, and let DEFS.`: variables of the rest of the result or proof (of the section,
in the running text), and definitions local to it. -/
def assumeIn (c : SentCtx) (binds : List Bind) (defs : List MT) : M (List Nat × List Nat) := do
  -- (a domain may use the variables of the result: `Let $n\ge1$. Let $x_1,\ldots,x_n$ be
  -- real numbers.`; these binders come after all of them)
  let st0 ← get
  let envNames := match c.ctx.kind with | .text => [] | _ => st0.envBinders.map (·.name)
  let bNames := bindNames st0 envNames binds
  let domEnv := ((bindMaths binds).flatMap fun m => seqFree st0 bNames m (freeIds 64 bNames m)).filter envNames.contains
  let bs := (← bindersInfos binds (if domEnv.isEmpty then [] else st0.envBinders))
  match c.ctx.kind with
  | .text =>
    modify fun st => { st with fixed := bs.map (c.ctx.sec, ·) ++ st.fixed.filter fun (_, x) => !(bs.any (·.name == x.name)) }
  | _ =>
    if domEnv.isEmpty then
      modify fun st => { st with envBinders := bs ++ st.envBinders.filter fun x => !(bs.any (·.name == x.name)) }
    else modify fun st => { st with envBinders := st.envBinders ++ bs }
  let st ← get
  let scope := match c.ctx.kind with
    | .text => (st.fixed.filter (·.1 == c.ctx.sec)).map (·.2)
    | _ => st.envBinders
  let ds ← defs.mapM (inlineDef c scope)
  pure (ds, [])

/-! ## Hypotheses of a result or a proof -/

/-- A hypothesis is a statement about the variables of the result or proof: it is read
once where it is made, so that a hypothesis without a reading fails there and not in
every sentence after it. -/
def checkHyp (c : SentCtx) (h : Clause) : M Unit := do
  let st ← get
  let fixedNames := (st.fixed.filter (·.1 == c.ctx.sec)).map (·.2.name)
  let r ← tryCatch (do discard <| clauseTm c (scopeOf st.envBinders) none none h; pure none)
    fun e => pure (some e)
  set st
  match r with
  | some e => if e.code == E.undefined && fixedNames.contains e.detail then pure () else throw e
  | none => pure ()

/-- `Assume that …`, `Suppose …`: hypotheses of the following sentences of the result or
proof, or of the list item the sentence is in. They last until the proof or the item
ends, until a contradiction refutes them, or until another case takes their place:

* an assumption after another is added to it (`Assume that $y>0$.` after `Assume that
  $x>0$.`), and ends on its own;
* `Assume further that …` belongs to the assumption before it: the two end together;
* `Assume now that …` (`next`, `instead`, `conversely`) begins another case: it takes the
  place of the latest assumption of the proof (of the item).

A formula with a new variable (`Assume $c>0$.`, `Suppose $x\in A$.`) binds it, as `Let`
does. -/
def supposeIn (c : SentCtx) (hyps : List Clause) (additive caseLike contra : Bool) (asBinder : Option Bind) :
    M (List Nat × List Nat) := do
  if c.ctx.kind == .text then fail E.prose
  let st ← get
  let known := st.envBinders.map (·.name) ++ (st.fixed.filter (·.1 == c.ctx.sec)).map (·.2.name)
  let newVars (b : Bind) : Bool := (bindNames st known [b]).any (!known.contains ·)
  -- (a symbol that the article or the result has defined is no new variable: `Suppose that
  -- $K\subseteq A$.` about the set `K` defined before is a hypothesis)
  let defined ← match asBinder with
    | some (.every vs _) => vs.allM fun v => do pure (← Elab.lookupGlob v).isSome
    | _ => pure false
  match asBinder with
  | some b => if !contra && !defined && newVars b then return ← assumeIn c [b] [] else pure ()
  | none => pure ()
  let item := c.ctx.items.headD 0
  -- the assumptions of this proof (of this item), not the headings of its cases
  let own (h : Hyp) : Bool := h.item == item && h.env == c.ctx.env && !h.heading
  let latest : Option Hyp := (st.envHyps.filter own).getLast?
  -- another case: the latest assumption ends
  if caseLike then
    match latest with
    | some l => modify fun st => { st with envHyps := st.envHyps.filter fun h => !(own h && h.group == l.group) }
    | none => pure ()
  let group : Nat := if additive then (latest.map (·.group)).getD c.idx else c.idx
  for h in hyps do
    -- a condition with a new variable binds it (`Assume $c>0$.`, as `Let $c>0$.`)
    let cond : Option Bind := match h with
      | .fact φ => if newVars (.ifCond φ) then some (.ifCond φ) else none
      | _ => none
    match cond with
    | some b =>
      if contra then fail E.finding w!"a hypothesis for contradiction about a variable it introduces: say that there is one (Suppose, for contradiction, that there is $c>0$ such that …)"
      discard <| assumeIn c [b] []
    | none =>
      let h ← expandStmt c h
      checkHyp c h
      modify fun st => { st with
        envHyps := st.envHyps ++ [({ item, contra, heading := false, env := c.ctx.env, sent := c.idx, clause := h, group } : Hyp)],
        hypUsed := false }
  pure ([], [])

/-- The heading of a case, `\item \emph{$x\ge0$.}`: a hypothesis of the sentences of its
item. Outside a result or a proof, or outside a list, it is prose. -/
def caseIn (c : SentCtx) (hyps : List Clause) : M (List Nat × List Nat) := do
  if c.ctx.kind == .text then fail E.prose
  let item :: _ := c.ctx.items | fail E.prose
  for h in hyps do
    checkHyp c h
    modify fun st => { st with
      envHyps := st.envHyps ++ [({ item, contra := false, heading := true, env := c.ctx.env, sent := c.idx, clause := h, group := c.idx } : Hyp)],
      hypUsed := false }
  pure ([], [])

/-- `This is a contradiction.`, `…, a contradiction.`: the claims of the sentence, and
then the false statement, under the hypotheses made. It refutes the latest hypothesis
made for contradiction, which ends here with the hypotheses made after it; without one,
the latest assumption of the proof (with what `Assume further` added to it). The claims
made under what it refutes are marked: their hypotheses are not meant to hold together. -/
def contradictionIn (c : SentCtx) (topic : Topic) (binds : List Bind) (cls : List CClause) (cites : List Codes) :
    M (List Nat × List Nat) := do
  if c.ctx.kind == .text then fail E.prose
  let st ← get
  if st.envHyps.isEmpty then
    fail E.finding w!"a contradiction without a hypothesis: say what is assumed (Suppose, for contradiction, that …)"
  -- the assumptions of this result or proof (not its cases, not the hypotheses of the result)
  let own := st.envHyps.zipIdx.filter fun (h, _) => h.env == c.ctx.env && !h.heading
  let from? : Option Nat := match (own.filter (·.1.contra)).getLast? with
    | some (_, k) => some k
    | none =>
      match own.getLast? with
      | some (l, _) => (own.find? fun (h, _) => h.group == l.group).map (·.2)
      | none => none
  -- where what it refutes begins: that hypothesis, or else the heading of the case, or
  -- else the proof
  let start : Nat := match from? with
    | some k => ((st.envHyps[k]?).map (·.sent)).getD c.idx
    | none => (((st.envHyps.filter fun h => h.env == c.ctx.env).getLast?).map (·.sent)).getD 0
  let n0 := (← get).globs.length
  let ids ← if cls.isEmpty then pure [] else claimSentence c topic binds cls
  let ids' ← claimSentence c .none [] [⟨cites, .absurd, [], [], []⟩]
  let inEnv (cl : Claim) : Bool := match cl.role with
    | .step e | .statement e => e == c.ctx.env
    | _ => false
  modify fun st => { st with
    envHyps := match from? with | some k => st.envHyps.take k | none => st.envHyps,
    claims := st.claims.map fun cl => if inEnv cl && start ≤ cl.sent then { cl with refuted := true } else cl,
    hypUsed := false }
  let n1 := (← get).globs.length
  pure ((List.range (n1 - n0)).map (n0 + ·), ids ++ ids')

/-- A convention of the article: a noun the article names (`By a distribution we mean
a probability distribution on $\mathbb{N}_0$.`), which is a class like the article's
own, or words that stand for other words in the following sentences (`Throughout,
increasing means non-decreasing.`). -/
def meaningDef (ws : List Codes) (rhs : List Chunk) (noun : Bool) : M (List Nat × List Nat) := do
  if noun then
    let b ← nounPhrase rhs
    if !b.name.isEmpty then fail E.unsupported b.name
    let p := b.pred.getD (.lam b.ty .tt .tt)
    let i ← addGlob ⟨[], .fn b.ty .prop, [none], false, 1⟩ p
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
      let used := (maths.flatMap fun m => freeIds 64 [] m ++ subKeys 64 m).eraseDups.filter fun n => env.any (·.name == n)
      let used := used ++ lawIds (← get) maths (maths.flatMap fun m => freeIds 64 [] m)
      let imp := if c.ctx.kind == .text then [] else usedBinders env used
      let bis ← match bd with
        | .many bs => bindersInfos (bs.map id) imp
        | .every vs d => bindersInfos [.every vs d] imp
        | bd => binderInfos bd
      let binderNames := bis.map (·.name)
      let imp := imp.filter fun b => !binderNames.contains b.name
      -- `For $b\in(0,\frac12)$ and $x\in(1-b,1]$, set $z_-(x)\coloneqq…$`: the first variables
      -- of the binder that no defined symbol shows are implicit parameters of the
      -- definitions, supplied from the scope where the symbols are used
      let shown := (defs.flatMap fun m => match m with
        | .chain l _ => freeIds 64 [] l ++ subKeys 64 l
        | _ => []).eraseDups
      let hidden := bis.takeWhile fun b => !shown.contains b.name
      let (bis, imp) :=
        if !hidden.isEmpty && hidden.length < bis.length &&
            (bis.drop hidden.length).all (fun b => shown.contains b.name)
        then (bis.drop hidden.length, imp ++ hidden) else (bis, imp)
      let res ← match bis with
        | [bi] => if imp.isEmpty then constDefs c (some bi) defs labels else multiDefs bis defs labels imp
        | _ :: _ :: _ => multiDefs bis defs labels imp
        | [] => fail E.finding w!"`On $D$, put …`: a definition under `On $D$` is a function of a variable of $D$; name it (For $x\\in D$, set $f(x)\\coloneqq …$)"
      -- a function or a family defined inside a result or a proof is local to it, like a
      -- constant defined there
      if c.ctx.kind != .text then
        modify fun st => { st with locals := st.locals ++
          (res.1.filter fun i => (st.locals.lookup i).isNone).map fun i => (i, c.ctx.env) }
      -- in the statement of a result, the parameter of a family it defines stays bound in
      -- its later sentences and its proof (`For $t\in[0,1]$, let $Q_t(u,v)\coloneqq …$.
      -- Then $Q_t$ is a copula.`)
      if c.ctx.kind matches .result _ then
        let idx := defs.filterMap fun m => match m with
          | .chain (.app h _) _ | .chain h _ => match h with
            | .sub (.id _) (.id p) => some p
            | _ => (familyKey h).map (·.2)
          | _ => none
        let keep := bis.filter fun b => idx.contains b.name
        unless keep.isEmpty do
          modify fun st => { st with envBinders := keep ++ st.envBinders.filter fun x => !(keep.any (·.name == x.name)) }
      pure res
    | none =>
      -- `We set $B_{1/2}\coloneqq A_{1/2}$.` for a family `B` of the article: the family at
      -- one further parameter (`addGlob` joins it to the family on its domain)
      let atPoint : Option (Codes × MT × MT) := match defs with
        | [.chain (.sub (.id k) e) [(.defeq, rhs)]] => if (freeIds 64 [] e).isEmpty then some (k, e, rhs) else none
        | _ => none
      match atPoint with
      | some (k, e, rhs) =>
        match ← Elab.lookupFam k with
        | some (_, old) =>
          match old.ty with
          | .fn t cod => do
            let (et, ety) ← term F [] none e
            let et ← Elab.coerce et ety t
            let (rt, rty) ← term F [] none rhs
            let rt ← Elab.coerce rt rty cod
            let p := Tm.lam t .tt (.eq (.loc 0) (shift 1 0 et))
            let i ← addGlob ⟨k, old.ty, some p :: old.doms.drop 1, true, 1⟩ (Tm.lam t (.app (shift 1 0 p) (.loc 0)) (shift 1 0 rt))
            pure ([i], [])
          | _ => constDefs c none defs labels
        | none => constDefs c none defs labels
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
  | .defsNamed defs labels np => defsNamed c defs labels np
  -- the random pair of a result: its joint law is a variable of the result, a probability
  -- measure on `ℝ × [0,1]` whose second coordinate is uniform (see `St.randomPair`)
  | .randomVar y integ df cont => do
    if c.ctx.kind == .text then fail E.prose
    modify fun st => { st with randomPair := some (st.curEnv, y, none, df, integ, cont) }
    pure ([], [])
  | .uniformVar z dom => do
    if c.ctx.kind == .text then fail E.prose
    let st ← get
    let some (e, y, none, df, integ, cont) := st.randomPair | fail E.prose
    if e != st.curEnv then fail E.prose
    let some iv ← Elab.intervalType dom | fail E.unsupported
    let (some pl, some pu, some pi, some pd) := (iv.pairLaw, iv.pairUniform, iv.pairInt, iv.pairDf) | fail E.unsupported
    let lawTy : Ty := .fn (.fn .real (.fn iv.ty .prop)) .real
    let law := Tm.loc 0
    let conds := [Tm.app (.const pl) law, Tm.app (.const pu) law] ++
      (if integ then [Tm.app (.app (.const pi) law) (Tm.lam .real .tt (Tm.lam iv.ty .tt (.loc 1)))] else []) ++
      (if cont && df.isSome then
        [Tm.app (.app (.prim .continuousOn) (Tm.app (.const pd) law)) (Tm.lam .real .tt .tt)] else [])
    let bi : BindInfo := ⟨w!"\\mathbb{P}", lawTy, some (Tm.lam lawTy .tt (conjAll conds))⟩
    modify fun st => { st with envBinders := st.envBinders ++ [bi], randomPair := some (e, y, some z, df, integ, cont) }
    pure ([], [])
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
    -- in a result or a proof, `Fix $c>0$.` is `Let $c>0$.`
    if c.ctx.kind != .text then assumeIn c [b] defs else
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
  | .defDesc b lhs kind np cond _ => do
    -- the variables of the section or result, then those of the binder before it
    let st ← get
    let ctx : List BindInfo := match c.ctx.kind with
      | .text => (st.fixed.filter (·.1 == c.ctx.sec)).map (·.2)
      | _ => st.envBinders
    let own ← match b with
      | some bd => binderInfos bd
      | none => pure []
    let bs := ctx.filter (fun x => !own.any (·.name == x.name)) ++ own
    descDef c bs lhs kind np cond
  | .assumeAll binds defs => assumeIn c binds defs
  | .letSuchThatNP np hyp => do
    -- the object, then the property it is chosen with
    let (d1, c1) ← assumeIn c [.noun np] []
    let (d2, c2) ← supposeIn c [hyp] false false false none
    pure (d1 ++ d2, c1 ++ c2)
  | .letSuchThat v hyp defs => do
    -- the variable, then the property it is chosen with, then the definitions
    let (d1, c1) ← assumeIn c [.every [v] (.id w!"\\mathbb{R}")] []
    let (d2, c2) ← supposeIn c [hyp] false false false none
    let (d3, c3) ← if defs.isEmpty then pure ([], []) else assumeIn c [] defs
    pure (d1 ++ d2 ++ d3, c1 ++ c2 ++ c3)
  | .assume b => assumeIn c [b] []
  | .suppose hyps additive caseLike contra asBinder => supposeIn c hyps additive caseLike contra asBinder
  | .caseOf hyps => caseIn c hyps
  | .contradiction cites => contradictionIn c .none [] [] cites
  | .claimsContra topic binds cls => contradictionIn c topic binds cls []
  -- (it organizes a proof; elsewhere it is prose)
  | .organizes => if c.ctx.kind == .proof then pure ([], []) else fail E.prose
  | .usesFrom l φ => do
    if c.ctx.kind != .proof then fail E.prose
    let some e := (← get).proofEnvs.lookup l | fail E.prose
    modify fun st => { st with imports := (st.curEnv, e) :: st.imports }
    match φ with
    | some m =>
      let ids ← claimSentence c .none [] [{ cites := [], clause := .fact m }]
      pure ([], ids)
    | none => pure ([], [])
  | .undefined lhs words args => undefinedDef c lhs words args
  | .letters vs => do
    modify fun st => { st with letters := st.letters ++ vs.filter (!st.letters.contains ·) }
    pure ([], [])
  | .inductionOn v => do
    if c.ctx.kind != .proof then fail E.prose
    unless (((← get).resultBinders.lookup c.target).getD []).any (·.name == v) do
      fail E.finding w!"an induction on a variable that the result does not introduce: introduce it in the result (Let $n$ be a positive integer. Then …), so that the statement is a statement about it"
    modify fun st => { st with inductionVar := some (c.ctx.env, v) }
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
    -- (`if $C^\top(u,v)\coloneqq C(v,u)$ denotes the transpose of $C$`: a formula that defines
    -- the symbol itself is the article's definition, whatever notion of the vocabulary has
    -- these words)
    if toks.any (·.tok == .cmd w!"coloneqq") then fail E.unsupported
    let key : Codes := w!"@n" ++ (toString st.templates.length).toList.map Char.toNat
    let V := st.vocab
    -- `We write $\operatorname{ord}(\sigma)$ for the order of a permutation $\sigma$`: a
    -- noun before a letter gives its type, which decides between notions with these words
    -- (of a permutation, of a group); the letter stays the argument
    let rec typed : Nat → List Chunk → List Chunk × List (List MTok × Ty)
      | 0, cs => (cs, [])
      | _ + 1, [] => ([], [])
      | f + 1, c :: cs =>
        let art := match c with | .w a => a == w!"a" || a == w!"an" | _ => false
        let hit := if !art then none else V.nouns.findSome? fun n =>
          match matchPhrase n.sing cs with
          | some (none, .m ts :: rest) => if (Notation.varTok ts).isSome then some (ts, n.ty, rest) else none
          | _ => none
        match hit with
        | some (ts, ty, rest) => let (r, acc) := typed f rest; (.m ts :: r, (ts, ty) :: acc)
        | none => let (r, acc) := typed f cs; (c :: r, acc)
    let (rhsT, typedVars) := typed (rhs.length + 1) rhs
    let candsOf (cs : List Chunk) := V.notions.filterMap fun n => (Notation.matchSlots n.name cs []).map fun a => ((n, a), [])
    -- (only where the words with the nouns are a notion of the vocabulary: otherwise they are
    -- read as before, `the maximum degree of a graph $G$` as a quantity of the article)
    let (rhs, typedVars) := if typedVars.isEmpty || (candsOf rhsT).isEmpty then (rhs, []) else (rhsT, typedVars)
    let cands := candsOf rhs
    let rec tysOf : Ty → List Ty
      | .fn a b => a :: tysOf b
      | _ => []
    let fits (na : Notion × List (List MTok)) : M Unit := do
      if typedVars.isEmpty then fail E.type
      let tys := tysOf na.1.ty
      for (ts, ty) in typedVars do
        match na.2.findIdx? (· == ts) with
        | some i => if tys.getD i .prop != ty then fail E.type
        | none => fail E.type
    match ← theMeaningBy (fun (na : Notion × List (List MTok)) => (na.1.ty, na.1.value)) (·.1.field) fits rhs cands true with
    | some ((n, args), _) => do
      -- each argument is a variable of the pattern, or a fixed value
      -- (`We write $NF$ for the derivative of $F$ in the direction $(\sqrt2-1,1)$.`)
      -- (a letter that is not in the pattern is a symbol of the article, a fixed value too:
      -- `We write $K$ for the circle with centre $O$ and radius $5$.`, `O` the origin)
      let fixedOf (a : List MTok) : M (Option (Tm × Ty)) := do
        let some m := Math.parseFormula a | fail E.unsupported
        let (v, vty) ← term F [] none m
        pure (some (v, vty))
      let fixedArgs ← args.mapM fun a => match Notation.varTok a with
        | some t =>
          if pat.any (·.tok == t) then pure none else do
            let st1 ← get
            -- (the symbol as the article's notations have it)
            let toks := Notation.rewriteAll st1.templates [{ tok := t, pos := 0, math := true }]
            let a' := (Math.simplify (toks.length + 1) toks).getD a
            tryCatch (fixedOf a') fun _ => do set st1; pure none
        | none => fixedOf a
      let tsAll := (args.zip fixedArgs).filterMap fun (a, c) => if c.isSome then none else Notation.varTok a
      -- (a variable in several arguments, `$M_n$` for the set of `$n\times n$` matrices: one
      -- argument of the notation)
      let ts := tsAll.eraseDups
      let rec argTys : Ty → List Ty
        | .fn a b => a :: argTys b
        | _ => []
      let tys := argTys n.ty
      let k := ts.length
      let varPos : List (Option Tok) := args.zip fixedArgs |>.map fun (a, c) => if c.isSome then none else Notation.varTok a
      -- (the type and domain of a variable: those of its first argument)
      let firstOf (v : Tok) : Nat := (varPos.findIdx? (· == some v)).getD 0
      let varTys : List Ty := ts.map fun v => tys.getD (firstOf v) .real
      let allDoms : List (Option Tm) := n.doms ++ List.replicate tys.length none
      -- (the domain of a variable speaks about the arguments before it, which the notation
      -- may fix (`We write $N_a$ for the integral mean of $f$ on $[0,a]$.`) or name in another
      -- order: they are put in, as the definition has them; a domain about a variable that
      -- comes later in the notation is left to the guard inside the value)
      let wholeVars := fixedArgs.all (·.isNone) && ts.length == tsAll.length
      let varDoms : List (Option Tm) := ts.zipIdx.map fun (v, j) =>
        let pos := firstOf v
        match allDoms.getD pos none with
        | none => none
        | some p =>
          if wholeVars then some p else
          let rs : List (Option Tm) := (List.range pos).map fun q =>
            match fixedArgs.getD q none, varPos.getD q none with
            | some (c, _), _ => some c
            | none, some t => match ts.idxOf? t with
              | some w => if w < j then some (.loc (j - w)) else none
              | none => none
            | none, none => none
          if rs.any (·.isNone) then none else
          let closed := (List.range (pos + 1)).foldl (fun b _ => Tm.lam .real .tt b) p
          some (Notation.betaApply closed (rs.filterMap id ++ [.loc 0]))
      -- (the domain of a fixed argument that speaks about variables before it, `the integral
      -- mean of $g$ on $[0,1]$` with `g` integrable on `[0,1]`: a condition on the last of
      -- them, which the definition then asks for, instead of a condition for every `g`)
      let varDoms : List (Option Tm) := if wholeVars then varDoms else
        (List.range args.length).foldl (fun (ds : List (Option Tm)) q =>
          match fixedArgs.getD q none, allDoms.getD q none with
          | some (cq, _), some pq =>
            let before := (List.range q).filterMap fun q' => (varPos.getD q' none).bind fun t => ts.idxOf? t
            match before.max? with
            | none => ds
            | some jStar =>
              let rs : List (Option Tm) := (List.range q).map fun q' =>
                match fixedArgs.getD q' none, varPos.getD q' none with
                | some (c, _), _ => some c
                | none, some t => (ts.idxOf? t).map fun w => .loc (jStar - w)
                | none, none => none
              if rs.any (·.isNone) then ds else
              let closed := (List.range (q + 1)).foldl (fun b _ => Tm.lam .real .tt b) pq
              let cond : Tm := .app (Notation.betaApply closed (rs.filterMap id ++ [cq])) cq
              let ty := varTys.getD jStar .real
              let extra : Tm := .lam ty .tt (Tm.shift 1 0 cond)
              ds.set jStar (some (match ds.getD jStar none with
                | some (.lam t d b) => .lam t d (.and b (Tm.shift 1 0 cond))
                | some other => .lam ty .tt (.and (.app (Tm.shift 1 0 other) (.loc 0)) (Tm.shift 1 0 cond))
                | none => extra))
          | _, _ => ds) varDoms
      -- the arguments in order: the pattern's variables as locals, the fixed values as given
      let rec place : List (Option Tok × Option (Tm × Ty)) → List Ty → List (Tm × Ty)
        | [], _ => []
        | (some v, none) :: cs, t :: tys => (.loc (k - 1 - (ts.idxOf v)), t) :: place cs tys
        | (_, some c) :: cs, _ :: tys => c :: place cs tys
        | (none, none) :: cs, _ :: tys => place cs tys
        | _, [] => []
      let (body, resTy) ← applyAll n.value n.ty n.doms (place (varPos.zip fixedArgs) tys)
      let body := if fixedArgs.all (·.isNone) && ts.length == tsAll.length then body else Notation.headBeta 64 body
      -- (the variables range over their domains, so that the definition is well defined
      -- where its uses are)
      let value := (varTys.zip varDoms).foldr (fun (t, d) b => Tm.lam t (if wholeVars then .tt else holdsAt d (.loc 0)) b) body
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
      let whole := fixedArgs.all (·.isNone) && ts.length == tsAll.length
      -- (the notion's value is a function of more arguments than its phrase names, `the moment
      -- generating function of $f$` at `t`: their domains go with the definition, so that
      -- `M_f(t)` asks for the domain of `t` too)
      let moreDoms : List (Option Tm) := if whole then n.doms.drop varPos.length else []
      let i ← addGlob ⟨gkey, gty, varDoms ++ moreDoms, false, 1⟩ (if whole then n.value else value)
      let slots := (List.range ts.length).map TItem.slot
      let call : List TItem := if slots.isEmpty then [] else
        [.fixed (.msym 40)] ++ (slots.intersperse (.fixed (.msym 44))) ++ [.fixed (.msym 41)]
      push ⟨pat', .fixed (match letter with | some c => .mvar c | none => .cmd key) :: call, []⟩
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
        let i ← addGlob ⟨[92] ++ key, .fn n.ty .prop, [], false, 1⟩ n.pred
        push ⟨pat.map (TItem.fixed ·.tok), [.fixed (.cmd key)], []⟩
        pure ([i], [])
      | none => fail E.noun (((wordsOf rest).intersperse [32]).flatten)
  else
    let some repl := fs[1]? | fail E.unsupported
    let tpl := Notation.template pat repl
    -- the variables it binds, other than its arguments
    let bound : List Codes := match (Math.simplify (repl.length + 1) repl).bind Math.parseDisplay with
      | some m => (boundIds 64 m).eraseDups
      | none => []
    let slots : List Tok := (tpl.pat.zip (pat.map (·.tok))).filterMap fun (i, t) =>
      match i with | .slot _ => some t | _ => none
    let binds : List Tok := (bound.filterMap fun n => match n with
      | [c] => some (Tok.mvar c)
      | 92 :: name => some (Tok.cmd name)
      | _ => none).filter (!slots.contains ·)
    let tpl := { tpl with binds }
    match tpl.pat, tpl.repl with
    -- `We write $A\subset B$ if $A\subseteq B$`: one relation symbol for another, in
    -- place (the arguments are whatever stands on either side)
    | [.slot a, .fixed t, .slot b], [.slot a', .fixed t', .slot b'] =>
      if a == a' && b == b' && a != b then push { pat := [.fixed t], repl := [.fixed t'] }
      else push { tpl with repl := .fixed .lbrace :: tpl.repl ++ [.fixed .rbrace] }
    | _, _ => push { tpl with repl := .fixed .lbrace :: tpl.repl ++ [.fixed .rbrace] }
    pure ([], [])

end Compile

/-- Greek letters: names of variables. -/
def greekLetters : List Codes :=
  [w!"alpha", w!"beta", w!"gamma", w!"delta", w!"epsilon", w!"varepsilon", w!"zeta", w!"eta",
   w!"theta", w!"vartheta", w!"iota", w!"kappa", w!"lambda", w!"mu", w!"nu", w!"xi", w!"pi",
   w!"rho", w!"varrho", w!"sigma", w!"tau", w!"upsilon", w!"phi", w!"varphi", w!"chi", w!"psi",
   w!"omega", w!"Gamma", w!"Delta", w!"Theta", w!"Lambda", w!"Xi", w!"Sigma", w!"Phi", w!"Psi",
   w!"Omega", w!"ell"]

/-- The letters and Greek letters of the formulas of a sentence (`e` only where it is not
the base of a power). -/
def symbolsOf (ts : List PTok) : List Codes :=
  let rec go : List PTok → List Codes → List Codes
    | [], acc => acc
    | t :: rest, acc =>
      let add (n : Codes) := if acc.contains n then acc else n :: acc
      match t.tok with
      | .mvar c =>
        if !t.math then go rest acc
        else
          match rest with
          -- (`g_*` is a symbol of its own, not `g`)
          | ⟨.msym 95, _, _⟩ :: _ => go rest acc
          -- (`e^x` is the exponential, not a symbol `e`)
          | ⟨.msym 94, _, _⟩ :: _ => if c == 101 then go rest acc else go rest (add [c])
          | _ => go rest (add [c])
      | .cmd n =>
        if t.math && greekLetters.contains n then go rest (add ([92] ++ n)) else go rest acc
      | _ => go rest acc
  (go ts []).reverse

/-- The symbols a sentence introduces: the left sides of the formulas after `let`, `fix`,
`set`, `put`, `define`, `write`, `denote [by]`, `choose`, `take`, `consider`, `call` or
`where` (`Let $q$ denote the charge`, `define \[X=2U-1,\qquad Y=2V-1\]`), and a single
symbol named by the words before it (`the idempotent $e$`). -/
def introducedSymbols (ts : List PTok) : List Codes :=
  let intro := [w!"let", w!"fix", w!"set", w!"put", w!"define", w!"write", w!"denote", w!"denotes",
    w!"choose", w!"take", w!"consider", w!"call", w!"where", w!"given", w!"suppose", w!"assume"]
  -- words after which a formula is not named by the words before it
  let notName := [w!"of", w!"at", w!"in", w!"on", w!"to", w!"for", w!"by", w!"with", w!"from",
    w!"and", w!"or", w!"is", w!"are", w!"be", w!"was", w!"that", w!"then", w!"if", w!"when",
    w!"every", w!"all", w!"each", w!"any", w!"some", w!"no", w!"as", w!"than", w!"so", w!"hence",
    w!"thus", w!"since", w!"because", w!"over", w!"under", w!"into", w!"equals", w!"has", w!"have",
    w!"gives", w!"satisfies", w!"holds", w!"implies", w!"yields", w!"whenever", w!"unless", w!"not",
    w!"between", w!"through", w!"via", w!"along", w!"after", w!"before", w!"until", w!"while",
    w!"also", w!"only", w!"both", w!"either", w!"neither", w!"but", w!"whether", w!"which", w!"whose"]
  let isRel (t : Tok) : Bool := match t with
    | .msym c => c == 61 || c == 60 || c == 62 || c == 58
    | .cmd n => [w!"le", w!"ge", w!"leq", w!"geq", w!"in", w!"coloneqq", w!"sim", w!"subset",
        w!"subseteq", w!"ne", w!"neq", w!"to", w!"equiv", w!"approx", w!"mapsto"].contains n
    | _ => false
  -- the left sides of the parts of a formula (split at top-level `,` and `\qquad`)
  let rec lhs : List PTok → Int → Bool → List PTok → List PTok
    | [], _, _, acc => acc
    | t :: rest, d, done, acc =>
      let d' : Int := match t.tok with
        | .lbrace | .msym 40 | .msym 91 => d + 1
        | .rbrace | .msym 41 | .msym 93 => d - 1
        | _ => d
      if d == 0 && (t.tok == .msym 44 || t.tok == .cmd w!"qquad" || t.tok == .cmd w!"quad") then lhs rest d' false acc
      else if done then lhs rest d' true acc
      else if d == 0 && isRel t.tok then lhs rest d' true acc
      else lhs rest d' false (t :: acc)
  -- the symbols a formula introduces, given the two words before it (`cur` is reversed)
  let chunkSyms (ws : List Codes) (cur : List PTok) : List Codes :=
    if cur.isEmpty then [] else
    let chunk := cur.reverse
    let w1 := ws.headD []
    let w2 := (ws.drop 1).headD []
    if intro.contains w1 || intro.contains w2 then symbolsOf ((lhs chunk 0 false []).reverse)
    -- (`for every real $x$`: a variable of a binder, not an object)
    else if w1 != [] && !notName.contains w1 &&
        ![w!"every", w!"all", w!"each", w!"any"].contains w2 then
      -- a single symbol named by a noun (`the idempotent $e$`)
      let inner := chunk.filter fun p => match p.tok with | .mopen | .mclose => false | _ => true
      match inner with
      | [⟨.mvar c, _, _⟩] => [[c]]
      | [⟨.cmd n, _, _⟩] => if greekLetters.contains n then [[92] ++ n] else []
      | _ => []
    else []
  -- the chunks of formulas with the two words before each
  let rec go : List PTok → List Codes → List PTok → List Codes → List Codes
    | [], ws, cur, acc => acc ++ chunkSyms ws cur
    | t :: rest, ws, cur, acc =>
      if t.math then go rest ws (t :: cur) acc
      else
        let acc := acc ++ chunkSyms ws cur
        match t.tok with
        | .word w => go rest ((Grammar.lower w :: ws).take 2) [] acc
        | _ => go rest ws [] acc
  go ts [] [] []

/-- The state of the compiler between sentences. -/
structure CState where
  st : St
  /-- Index of the next sentence. -/
  idx : Nat := 0
  /-- Outcomes of the sentences read so far, latest first. -/
  outcomesRev : List Outcome := []
  proofs : List ProofInfo := []
  deriving Inhabited, Lean.ToExpr

/-- The sentence with `, that is,` turned into `; that is,`: no longer read through its
formal restatement. -/
def noThatIs (s : Sentence) : Sentence :=
  let rec go : List PTok → List PTok
    | a :: b :: c :: rest =>
      if a.tok == .punct 44 && b.tok == .word w!"that" && c.tok == .word w!"is"
      then { a with tok := .punct 59 } :: go (b :: c :: rest) else a :: go (b :: c :: rest)
    | l => l
  { s with toks := go s.toks }

/-- Environment index of each result, by label (for proofs that name their result). -/
def envTable (ss : List Sentence) : List (Codes × Nat) :=
  ss.filterMap fun s => match s.ctx.kind with
    | .result _ => some (s.ctx.label, s.ctx.env)
    | _ => none

/-! ## Freer wordings

A sentence that has no reading as it stands is read through sentences of the forms above
that say the same: a definition inside a sentence of prose (`…, if $C^\top(u,v)\coloneqq
C(v,u)$ denotes the transpose of $C$, then …`), definitions after a colon and after
`, where` (`… indexed by $w\in[0,1]$: let $A_w$ be …, where \[T_w(x)\coloneqq…\]`), and
a definition about a letter that an earlier definition introduced (`For a copula $C$, …`). -/
namespace Flex

def isW (p : PTok) (w : Codes) : Bool :=
  match p.tok with | .word v => !p.math && Grammar.lower v == w | _ => false
def isWs (p : PTok) (ws : List Codes) : Bool := ws.any (isW p)
def W (pos : Nat) (w : Codes) : PTok := ⟨.word w, pos, false⟩
def comma (pos : Nat) : PTok := ⟨.punct 44, pos, false⟩
def period (pos : Nat) : PTok := ⟨.punct 46, pos, false⟩
def isP (p : PTok) (c : Nat) : Bool := !p.math && p.tok == .punct c

structure SegSt where
  out : List (Bool × List PTok) := []
  cur : List PTok := []
  mode : Nat := 0
  env : Codes := []

def segStep (s : SegSt) (t : PTok) : SegSt :=
  let flush : List (Bool × List PTok) := if s.cur.isEmpty then s.out else (false, s.cur.reverse) :: s.out
  match s.mode with
  | 0 =>
    match t.tok with
    | .mopen => { out := flush, cur := [t], mode := 1 }
    | .begin e =>
      if Lex.wDisplayEnvs.contains e then { out := flush, cur := [t], mode := 2, env := e }
      else { s with cur := t :: s.cur }
    | _ => { s with cur := t :: s.cur }
  | 1 =>
    if t.tok == .mclose then { out := (true, (t :: s.cur).reverse) :: s.out }
    else { s with cur := t :: s.cur }
  | _ =>
    if t.tok == .finish s.env then { out := (true, (t :: s.cur).reverse) :: s.out }
    else { s with cur := t :: s.cur }

/-- The stretches of words and the formulas of a sentence, in order. -/
def segs (ts : List PTok) : List (Bool × List PTok) :=
  let s := ts.foldl segStep {}
  (if s.cur.isEmpty then s.out else (s.mode != 0, s.cur.reverse) :: s.out).reverse

def unsegs (ss : List (Bool × List PTok)) : List PTok := ss.foldr (fun s acc => s.2 ++ acc) []

def isDefSign (p : PTok) : Bool := p.tok == .cmd w!"coloneqq"
def hasDef (seg : List PTok) : Bool := seg.any isDefSign

/-- The letters of a formula before its first relation sign. -/
def headVars (seg : List PTok) : List Tok :=
  let isRel (t : Tok) : Bool := match t with
    | .msym c => c == 61 | .cmd n => [w!"coloneqq", w!"in", w!"le", w!"ge", w!"to"].contains n | _ => false
  (seg.takeWhile (fun p => !isRel p.tok)).filterMap fun p => match p.tok with
    | .mvar c => some (.mvar c)
    | _ => none

/-- The introduction `For a copula $C$,` or `For $w\in[0,1]$,` that a sentence starts with. -/
def forPrefix (ts : List PTok) : Option (List PTok) :=
  match ts with
  | t :: rest =>
    if isW t w!"for" then
      let pre := rest.takeWhile (fun p => !isP p 44)
      if pre.length == rest.length || pre.any (fun p => isP p 46 || isP p 58 || (match p.tok with | .begin _ => true | _ => false)) then none
      else if !pre.any (fun p => p.tok == .mopen) then none
      else some (t :: pre ++ [comma t.pos])
    else none
  | [] => none

/-- The letters an introduction introduces. -/
def prefixVars (pre : List PTok) : List Tok :=
  ((segs pre).filter (·.1)).flatMap fun s => headVars s.2

/-- The latest introduction of one of the letters `vs`. -/
def stickyFor (pres : List (List PTok)) (vs : List Tok) : List PTok :=
  match pres.find? (fun pre => (prefixVars pre).any vs.contains) with
  | some pre => pre
  | none => []

/-- The latest introduction of a letter of `vs`, or else of `ws`. -/
def stickyFor2 (pres : List (List PTok)) (vs ws : List Tok) : List PTok :=
  let p := stickyFor pres vs
  if p.isEmpty then stickyFor pres ws else p

def startsDef (ts : List PTok) : Bool :=
  match ts with
  | t :: u :: _ => isWs t [w!"let", w!"set", w!"define", w!"put"] ||
      (isW t w!"we" && isWs u [w!"set", w!"define", w!"put", w!"let", w!"write"])
  | [t] => isWs t [w!"let", w!"set", w!"define", w!"put"]
  | [] => false

/-- Split at the words `and let`, `and set`, `and define`, `and put` between formulas. -/
def andParts : List PTok → List PTok → List (List PTok)
  | [], cur => [cur.reverse]
  | t :: rest, cur =>
    match rest with
    | u :: _ =>
      if isW t w!"and" && isWs u [w!"let", w!"set", w!"define", w!"put"] && !cur.isEmpty then
        cur.reverse :: andParts rest []
      else andParts rest (t :: cur)
    | [] => andParts rest (t :: cur)

def dropLast {α : Type} (l : List α) : List α := l.take (l.length - 1)

/-- Words that do not change what a definition says: `the coupling` before the formula
after `associated with`, a reference `from Section 2`. -/
def tidy : List PTok → List PTok
  | a :: b :: c :: d :: e :: rest =>
    if isW a w!"associated" && isW b w!"with" && isW c w!"the" && (match d.tok with | .word _ => !d.math | _ => false) && e.tok == .mopen then
      a :: b :: tidy (e :: rest)
    else if isWs a [w!"from", w!"in", w!"of"] && isWs b [w!"section", w!"lemma", w!"theorem", w!"proposition", w!"corollary", w!"equation", w!"appendix"]
        && (match c.tok with | .ref _ _ => true | _ => false) then tidy (d :: e :: rest)
    else a :: tidy (b :: c :: d :: e :: rest)
  | a :: b :: c :: rest =>
    if isWs a [w!"from", w!"in", w!"of"] && isWs b [w!"section", w!"lemma", w!"theorem", w!"proposition", w!"corollary", w!"equation", w!"appendix"]
        && (match c.tok with | .ref _ _ => true | _ => false) then tidy rest
    else a :: tidy (b :: c :: rest)
  | ts => ts

/-- The definitions in the rows of an aligned display that says more beside them
(`z_-(x)&\coloneqq…,&\quad\text{with probability }&…`). -/
def rowDefs (d : List PTok) : List (List PTok) :=
  if !d.any (fun p => p.tok == .begin w!"aligned") then [] else
  let body := d.filter fun p => match p.tok with | .begin _ | .finish _ | .ref _ _ => false | _ => true
  let rec rows : List PTok → List PTok → List (List PTok)
    | [], cur => [cur.reverse]
    | t :: rest, cur => if t.tok == .csym 92 then cur.reverse :: rows rest [] else rows rest (t :: cur)
  let clean (r : List PTok) : Option (List PTok) :=
    let r : List PTok := r.filter (fun p => p.tok != .msym 38)
    -- (an optional argument of the row break: `\\[0.4ex]`)
    let r : List PTok := match r with
      | o :: r' => if o.tok == .msym 91 then (r'.dropWhile (·.tok != .msym 93)).drop 1 else r
      | [] => r
    let r : List PTok := r.takeWhile fun p => !(p.tok == .cmd w!"quad" || p.tok == .cmd w!"qquad" || p.tok == .cmd w!"text")
    let r : List PTok := match r.getLast? with
      | some l => if l.tok == .msym 44 || l.tok == .msym 46 then dropLast r else r
      | none => r
    if hasDef r then some r else none
  let all := rows body []
  if all.length < 2 then [] else all.filterMap clean

/-- The name in the words before a formula (`the survival copula`, `Spearman's rho,`):
the words from the nearest `the` on, or else up to three words of which the first is
capitalized. The words are given latest first. -/
def nameBefore (rev : List PTok) : List PTok :=
  let rev := match rev with | c :: r => if isP c 44 then r else rev | [] => rev
  let run : List PTok := rev.takeWhile fun p => match p.tok with | .word _ => !p.math | _ => false
  let upTo : List PTok := run.takeWhile (fun p => !isW p w!"the")
  if upTo.length < run.length then (if upTo.isEmpty || upTo.length > 4 then [] else upTo.reverse)
  else
    let cap (p : PTok) : Bool := match p.tok with
      | .word (c :: _) => 65 ≤ c && c ≤ 90
      | _ => false
    match (run.take 3).reverse with
    | a :: r => if cap a && !r.isEmpty && !r.any cap then a :: r
        else (match r with | b :: r' => if cap b && !r'.isEmpty then b :: r' else [] | [] => [])
    | [] => []

/-- The name in the words after a formula (`denotes the transpose of $C$`). -/
def nameAfter (rest : List PTok) : List PTok :=
  match rest with
  | d :: t :: more =>
    if isWs d [w!"denotes", w!"denote"] && isW t w!"the" then
      let nm := more.takeWhile (fun p => !isP p 44 && !(match p.tok with | .begin _ => true | _ => false))
      if nm.isEmpty then [] else t :: nm
    else []
  | _ => []

/-- A formula `f(x)=…` that defines the symbol `f`, which no definition has introduced. -/
def freshEq (known : List Codes) (d : List PTok) : Bool :=
  let inner := d.filter fun p => match p.tok with
    | .begin _ | .finish _ | .ref _ _ | .mopen | .mclose => false | _ => true
  match inner with
  | h :: o :: rest =>
    let key : Codes := match h.tok with | .cmd n => 92 :: n | .mvar c => [c] | _ => []
    let args := rest.takeWhile (fun p => p.tok != .msym 41)
    !key.isEmpty && o.tok == .msym 40 && !known.contains key &&
      args.all (fun p => match p.tok with | .mvar _ | .msym 44 => true | _ => false) &&
      ((rest.drop (args.length + 1)).head?.map (·.tok)) == some (.msym 61)
  | _ => false

/-- `for the function $\Phi$ in (3)`: the reference to a symbol that is defined. -/
def tidyRef : List PTok → List PTok
  | a :: b :: c :: rest =>
    if isW a w!"for" && isW b w!"the" && isWs c [w!"function", w!"map", w!"constant", w!"functions"] then
      match segs rest with
      | (true, m) :: (false, ws) :: more =>
        (match ws with
         | i :: r :: ws' =>
           if m.length == 3 && isWs i [w!"in", w!"from", w!"of"] && (match r.tok with | .ref _ _ => true | _ => false) then
             ws' ++ unsegs more
           else a :: tidyRef (b :: c :: rest)
         | _ => a :: tidyRef (b :: c :: rest))
      | _ => a :: tidyRef (b :: c :: rest)
    else a :: tidyRef (b :: c :: rest)
  | ts => ts

def inner (m : List PTok) : List PTok := m.filter fun p => p.tok != .mopen && p.tok != .mclose

def symKey (t : PTok) : Codes := match t.tok with | .cmd n => 92 :: n | .mvar c => [c] | _ => []

/-- Apply the functionals of a formula (the defined symbols that have no argument) to `x`:
`\nu-\rho` at `C` is `\nu(C)-\rho(C)`. -/
def applyTo (fns : List Codes) (x : List PTok) : List PTok → List PTok
  | [] => []
  | t :: rest =>
    let applied := match rest with
      | u :: _ => u.tok == .msym 40 || u.tok == .msym 95 || u.tok == .msym 94
      | [] => false
    if !(symKey t).isEmpty && fns.contains (symKey t) && !applied then
      t :: ⟨.msym 40, t.pos, true⟩ :: x ++ ⟨.msym 41, t.pos, true⟩ :: applyTo fns x rest
    else t :: applyTo fns x rest

/-- Split a formula at its first `=` outside brackets. -/
def splitEq : List PTok → Nat → List PTok → Option (List PTok × List PTok)
  | [], _, _ => none
  | t :: rest, d, acc =>
    if d == 0 && t.tok == .msym 61 then some (acc.reverse, rest)
    else
      let d' := match t.tok with
        | .lbrace | .msym 40 | .msym 91 => d + 1
        | .rbrace | .msym 41 | .msym 93 => d - 1
        | _ => d
      splitEq rest d' (t :: acc)

/-- Split a formula at its commas outside brackets. -/
def splitCommas : List PTok → Nat → List PTok → List (List PTok)
  | [], _, acc => [acc.reverse]
  | t :: rest, d, acc =>
    if d == 0 && t.tok == .msym 44 then acc.reverse :: splitCommas rest d []
    else
      let d' := match t.tok with
        | .lbrace | .msym 40 | .msym 91 => d + 1
        | .rbrace | .msym 41 | .msym 93 => d - 1
        | _ => d
      splitCommas rest d' (t :: acc)

/-- The operation with the key `key` at `x`: `\widehat{x}`, `x^\top`. -/
def applyOp (key : Codes) (x : List PTok) : Option (List PTok) :=
  match Leanify.lex [] ([36] ++ key ++ [36]) with
  | some ks =>
    let k := (inner ks).map fun p => { p with math := true }
    match key with
    | 92 :: _ => some (k ++ [⟨.lbrace, 0, true⟩] ++ x ++ [⟨.rbrace, 0, true⟩])
    | 94 :: _ => some (x ++ k)
    | _ => none
  | none => none

def wordsOf (ts : List PTok) : List Codes := ts.filterMap fun p => match p.tok with
  | .word w => if p.math then none else some (Grammar.lower w)
  | .punct 44 => some [44]
  | _ => none

/-- `The maximum $\nu-\rho=\frac14$ is attained only by $D_{1/2}$, which has $\rho=0$.`,
`the maximum $a$ of $\nu-\eta$ is attained only by $A$, at which $(\eta,\nu)=(e,n)$, and the
minimum $-a$ only by $A^\top$`, `… only by its survival copula`: the sentences `The maximum
$e=v$ is attained only by $x$.` and the values at `x`. With the object, for `its` in the
next sentence. -/
def attained (fns : List Codes) (ops : List (List Codes × Codes)) (it : List PTok) (toks : List PTok) :
    Option (List (List PTok) × List PTok) :=
  let pos := (toks.head?.map (·.pos)).getD 0
  let body := match toks.getLast? with
    | some l => if isP l 46 then dropLast toks else toks
    | none => toks
  -- (`Both constants are sharp: …`)
  let body :=
    let head := body.takeWhile (fun p => !isP p 58)
    if head.length == body.length || head.any (fun p => p.math) then body else body.drop (head.length + 1)
  let m (ts : List PTok) : List PTok := [⟨.mopen, pos, true⟩] ++ ts ++ [⟨.mclose, pos, true⟩]
  let eq : PTok := ⟨.msym 61, pos, true⟩
  -- (the form `The maximum $e=v$ is attained only by $x$.`)
  let iffSent (mx : Codes) (e v x : List PTok) : List PTok :=
    [W pos w!"The", W pos mx] ++ m (e ++ [eq] ++ v) ++
      [W pos w!"is", W pos w!"attained", W pos w!"only", W pos w!"by"] ++ m x ++ [period pos]
  -- the object after `only by`
  let object (ws : List Codes) (rest : List (Bool × List PTok)) : Option (List PTok × List (Bool × List PTok)) :=
    if ws.isEmpty then
      match rest with
      | (true, x) :: more => some (inner x, more)
      | _ => none
    else
      match ws with
      | i :: name =>
        if i == w!"its" && !it.isEmpty then
          (ops.lookup name).bind fun key => (applyOp key it).map (·, rest)
        else none
      | [] => none
  let isMax (w : Codes) : Bool := w == w!"maximum" || w == w!"minimum"
  let headForm : Option (Codes × List PTok × List PTok × List Codes × List (Bool × List PTok)) :=
    match segs body with
    | (false, w1) :: (true, f1) :: (false, w2) :: rest =>
      (match wordsOf w1 with
       | [t, mx] =>
         if t == w!"the" && isMax mx then
           let ws2 := wordsOf w2
           if ws2.take 4 == [w!"is", w!"attained", w!"only", w!"by"] then
             (splitEq (inner f1) 0 []).map fun (e, v) => (mx, e, v, ws2.drop 4, rest)
           else if ws2 == [w!"of"] then
             match rest with
             | (true, f2) :: (false, w3) :: rest' =>
               let ws3 := wordsOf w3
               if ws3.take 4 == [w!"is", w!"attained", w!"only", w!"by"] then
                 some (mx, inner f2, inner f1, ws3.drop 4, rest')
               else none
             | _ => none
           else none
         else none
       | _ => none)
    | _ => none
  match headForm with
  | none => none
  | some (mx, e, v, ws, rest) =>
    -- (the words after `by` up to a comma name the object; the rest starts the tail)
    let nameWs := ws.takeWhile (· != [44])
    let tailWs := ws.drop nameWs.length
    match object nameWs rest with
    | none => none
    | some (x, rest) =>
      let first := iffSent mx e v x
      let more (x : List PTok) (f : List PTok) : Option (List PTok) :=
        -- `$\rho=0$`, `$(\eta,\nu)=(a,b)$`
        (splitEq (inner f) 0 []).bind fun (l, r) =>
          let strip (ts : List PTok) : List PTok := match ts with
            | o :: r => if o.tok == .msym 40 then dropLast r else ts
            | [] => ts
          let ls := splitCommas (strip l) 0 []
          let rs := if ls.length == 1 then [r] else splitCommas (strip r) 0 []
          if ls.length != rs.length then none else
          let eqs := (ls.zip rs).map fun (a, b) => m (applyTo fns x a ++ [eq] ++ b)
          let joined := eqs.foldl (fun acc q => if acc.isEmpty then q else acc ++ [W pos w!"and"] ++ q) []
          some ([W pos w!"Moreover", comma pos] ++ joined ++ [period pos])
      -- the tail: the words before each further formula
      let rec tail : Nat → List Codes → List (Bool × List PTok) → List PTok → Option (List (List PTok) × List PTok)
        | 0, _, _, _ => none
        | _, [], [], x => some ([], x)
        | f + 1, ws, (true, g) :: rest, x =>
          if ws == [[44], w!"which", w!"has"] || ws == [[44], w!"at", w!"which"] then
            match rest with
            | (false, w') :: rest' => (more x g).bind fun s => (tail f (wordsOf w') rest' x).map fun (ss, y) => (s :: ss, y)
            | [] => (more x g).map fun s => ([s], x)
            | _ => none
          else if ws.take 3 == [[44], w!"and", w!"the"] && ws.length == 4 && isMax (ws.getD 3 []) then
            match rest with
            | (false, w') :: rest' =>
              let ws' := wordsOf w'
              if ws'.take 2 == [w!"only", w!"by"] then
                let nameWs := (ws'.drop 2).takeWhile (· != [44])
                match object nameWs rest' with
                | some (y, rest'') =>
                  (tail f ((ws'.drop 2).drop nameWs.length) rest'' y).map fun (ss, z) => (iffSent (ws.getD 3 []) e (inner g) y :: ss, z)
                | none => none
              else none
            | _ => none
          else none
        | _, _, _, _ => none
      match rest with
      | [] => if tailWs.isEmpty then some ([first], x) else none
      | (false, w') :: rest' =>
        if tailWs.isEmpty then (tail (rest.length + 2) (wordsOf w') rest' x).map fun (ss, y) => (first :: ss, y) else none
      | _ => (tail (rest.length + 2) tailWs rest x).map fun (ss, y) => (first :: ss, y)

/-- The sentences that an unread sentence is read through: without (`sticky = false`) or
with the latest introductions of the letters of its definitions, and with (`named`) or
without the names that the words around a definition give it. -/
def expand (known : List Codes) (pres : List (List PTok)) (sticky named : Bool) (toks : List PTok) :
    Option (List (List PTok)) :=
  let pos := (toks.head?.map (·.pos)).getD 0
  let body := match toks.getLast? with
    | some l => if isP l 46 then dropLast toks else toks
    | none => toks
  let body := tidyRef (tidy body)
  -- the introduction the sentence starts with (`For $w\in[0,1]$, …`); `For $(U,V)\sim C$,`
  -- introduces no letter of a definition
  let (pre0, body) : List PTok × List PTok :=
    match forPrefix body with
    | some p =>
      if p.any (fun t => t.tok == .cmd w!"sim") then ([], body.drop p.length)
      else (p, body.drop p.length)
    | none => ([], body)
  -- after a colon: the definitions the words before it announce
  let (pre, tail) : List PTok × List PTok :=
    let head := body.takeWhile (fun p => !isP p 58)
    if head.length == body.length then (pre0, body) else
    let rest := body.drop (head.length + 1)
    match (segs head).getLast? with
    | some (true, m) =>
      if m.any (fun p => p.tok == .cmd w!"in") then (W pos w!"For" :: m ++ [comma pos], rest)
      else (pre0, body)
    | _ => (pre0, body)
  -- `…, where DISPLAY`
  let ss := segs tail
  let (main, whereDefs) : List PTok × List (List PTok) :=
    match ss.reverse with
    | (true, d) :: (false, ws) :: before =>
      (match ws.reverse with
       | w :: c :: wsr =>
         if isW w w!"where" && isP c 44 && hasDef d then (unsegs before.reverse ++ wsr.reverse, [d])
         else (tail, [])
       | _ => (tail, []))
    | _ => (tail, [])
  let parts := andParts main []
  let close (s : List PTok) : List PTok :=
    match s.getLast? with
    | some l => (match l.tok with | .finish _ => s | _ => s ++ [period pos])
    | none => s
  let preOf (vars : List Tok) : List PTok :=
    if !pre.isEmpty then pre else if sticky then stickyFor pres vars else []
  let withPre (vars : List Tok) (s : List PTok) : List PTok :=
    let p := preOf vars
    let s := match s with
      | t :: rest => if p.isEmpty then s else
          (match t.tok with | .word w => { t with tok := .word (Grammar.lower w) } | _ => t) :: rest
      | [] => s
    close (p ++ s)
  -- a definition inside prose, with the words before and after it
  let defSent (before after d : List PTok) : List PTok :=
    -- (the comma that continues the sentence after a display)
    let d := match d.reverse with
      | e :: c :: r =>
        if (match e.tok with | .finish _ => true | _ => false) then
          if c.tok == .msym 44 then (e :: { c with tok := .msym 46 } :: r).reverse
          else if c.tok == .msym 46 then d
          else (e :: { c with tok := .msym 46 } :: c :: r).reverse
        else d
      | _ => d
    let subject : Bool := match before.getLast? with
      | some l => isWs l [w!"is", w!"are"] && before.all (fun p => !isP p 44) &&
          (match before.head? with | some h => isW h w!"the" | none => false)
      | none => false
    let hasSig : Bool := match ((segs before).filter (·.1)).getLast? with
      | some (_, m) => m.any (fun p => p.tok == .cmd w!"to")
      | none => false
    if named && subject && hasSig then
      -- `the rank map $\zeta_c:[0,1]\to[0,1]$ is DISPLAY`
      close (preOf (headVars (d.filter fun p => match p.tok with | .ref _ _ | .begin _ | .mopen => false | _ => true)) ++
        [W pos w!"define"] ++ dropLast before ++ [W pos w!"by"] ++ d)
    else if named && subject then
      close (preOf (headVars (d.filter fun p => match p.tok with | .ref _ _ | .begin _ | .mopen => false | _ => true)) ++
        (match before with
         | t :: rest => (match t.tok with | .word w => { t with tok := .word (Grammar.lower w) } | _ => t) :: rest
         | [] => []) ++ d)
    else
    let vars := headVars (d.filter fun p => match p.tok with | .ref _ _ | .begin _ | .mopen => false | _ => true)
    let na := nameAfter after
    let nb := nameBefore before.reverse
    if named && !na.isEmpty then withPre vars ([W pos w!"we", W pos w!"write"] ++ d ++ [W pos w!"for"] ++ na)
    else if named && !nb.isEmpty then
      let p := preOf vars
      let ofVar : List PTok := match ((segs p).filter (·.1)).getLast? with
        | some (_, m) => if m.length == 3 then [W pos w!"of"] ++ m else []
        | none => []
      let cap (p : PTok) : Bool := match p.tok with | .word (c :: _) => 65 ≤ c && c ≤ 90 | _ => false
      let the : List PTok := if nb.head?.map cap == some true then [] else [W pos w!"the"]
      let ofVar := if the.isEmpty then [] else ofVar
      close (p ++ the ++ nb ++ ofVar ++ [W pos w!"is"] ++ d)
    else withPre vars (W pos w!"set" :: d)
  let rec partDefs : Nat → List PTok → List (Bool × List PTok) → List (List PTok)
    | 0, _, _ => []
    | _, _, [] => []
    | f + 1, before, (m, d) :: rest =>
      let here := if m && (hasDef d || (named && freshEq known d && !(nameBefore before.reverse).isEmpty &&
          (match d.head? with | some t => (match t.tok with | .begin _ => true | _ => false) | none => false)))
        then (if named || (rowDefs d).isEmpty then [defSent before (unsegs rest) d]
          else (rowDefs d).map fun r =>
            let vars := headVars r ++ r.filterMap fun p => match p.tok with | .mvar c => some (Tok.mvar c) | _ => none
            let p := if !pre.isEmpty then pre else if sticky then stickyFor2 pres (headVars r) vars else []
            p ++ [W pos w!"set", ⟨.mopen, pos, true⟩] ++ r ++ [⟨.mclose, pos, true⟩, period pos]) else []
      here ++ partDefs f (before ++ d) rest
  let partSents (p : List PTok) : Option (List (List PTok)) :=
    if startsDef p then
      let vars := match ((segs p).filter (·.1)).head? with | some (_, m) => headVars m | none => []
      some [withPre vars p]
    else
      let sp := segs p
      let ds := partDefs (sp.length + 1) [] sp
      -- (words before `, where DISPLAY` that define nothing are not read)
      if ds.isEmpty then (if whereDefs.isEmpty then none else some []) else some ds
  match parts.mapM partSents with
  | none => none
  | some pss =>
    let wd := whereDefs.flatMap fun d =>
      if named || (rowDefs d).isEmpty then [withPre (headVars d) (W pos w!"set" :: d)]
      else (rowDefs d).map fun r =>
        withPre (headVars r) ([W pos w!"set", ⟨.mopen, pos, true⟩] ++ r ++ [⟨.mclose, pos, true⟩])
    match pss.reverse with
    | last :: initR => some ((initR.reverse.flatMap id) ++ wd ++ last)
    | [] => none

/-- `…, a normalization that makes $\nu(M)=1$, $\nu(W)=-1$, and $\nu(\Pi)=0$.`: the sentence
before the comma, and the formulas as its consequences. -/
def makesSplit : List PTok → List PTok → Option (List (List PTok))
  | [], _ => none
  | t :: rest, acc =>
    let hit : Option (List PTok) :=
      match rest with
      | a :: rest' =>
        if isP t 44 && isWs a [w!"a", w!"an"] then
          let ws := rest'.takeWhile fun p => match p.tok with | .word _ => !p.math | _ => false
          match ws.reverse with
          | v :: th :: nm =>
            if isWs v [w!"makes", w!"make", w!"gives", w!"yields"] && isW th w!"that" && !nm.isEmpty && nm.length ≤ 3 then
              some (rest'.drop ws.length)
            else none
          | _ => none
        else none
      | [] => none
    match hit with
    | some after =>
      if acc.isEmpty || after.isEmpty then none
      else some [acc.reverse ++ [period t.pos], [W t.pos w!"We", W t.pos w!"have"] ++ after]
    | none => makesSplit rest (t :: acc)

/-- `… with the set $\Gamma$ of all such couplings, …`: the symbol denotes the set. -/
def setOf (known : List Codes) : List (Bool × List PTok) → Option (List (List PTok))
  | (false, w1) :: (true, m) :: (false, w2) :: rest =>
    let pos := (m.head?.map (·.pos)).getD 0
    let hit : Option (List (List PTok)) :=
      match w1.reverse, w2 with
      | k :: th :: _, o :: w2' =>
        if isW th w!"the" && isWs k [w!"set", w!"class", w!"family", w!"collection"] && isW o w!"of" &&
            (inner m).length == 1 && !((inner m).any fun p => known.contains (symKey p)) then
          let w2' := w2'.dropWhile (fun p => isWs p [w!"all", w!"such", w!"the", w!"these"])
          let nm := w2'.takeWhile fun p => match p.tok with | .word _ => !p.math | _ => false
          if nm.isEmpty then none
          else some [[W pos w!"Let"] ++ m ++ [W pos w!"denote", th, k, o] ++ nm ++ [period pos]]
        else none
      | _, _ => none
    match hit with
    | some r => some r
    | none => setOf known ((true, m) :: (false, w2) :: rest)
  | _ :: rest => setOf known rest
  | [] => none

/-- `\mathbb{E}[…]` as `\mathbb{E}_\gamma[…]`. -/
def expUnder (g : PTok) : List PTok → List PTok
  | a :: b :: c :: d :: e :: rest =>
    if a.tok == .cmd w!"mathbb" && b.tok == .lbrace && c.tok == .mvar 69 && d.tok == .rbrace && e.tok == .msym 91 then
      a :: b :: c :: d :: { e with tok := .msym 95 } :: g :: e :: expUnder g rest
    else a :: expUnder g (b :: c :: d :: e :: rest)
  | ts => ts

/-- `If $(X,Z)$ follows the coupling associated with $C\in\mathcal{C}$, then …
\mathbb{E}[XZ] …`: the expectations are those under that coupling. -/
def followsCoupling (toks : List PTok) : Option (List (List PTok)) :=
  match segs toks with
  | (false, [i]) :: (true, _) :: (false, ws) :: (true, m) :: (false, th) :: rest =>
    let pos := i.pos
    let g : PTok := ⟨.cmd w!"gamma", pos, true⟩
    match th with
    | c :: t :: th' =>
      if isW i w!"if" && wordsOf ws == [w!"follows", w!"the", w!"coupling", w!"associated", w!"with"] &&
          isP c 44 && isW t w!"then" && !toks.any (fun p => p.tok == .cmd w!"gamma") &&
          (inner m).any (fun p => p.tok == .cmd w!"in") then
        let v := (inner m).take 1
        some [[W pos w!"Let"] ++ m ++ [comma pos, W pos w!"and", W pos w!"let", ⟨.mopen, pos, true⟩, g, ⟨.mclose, pos, true⟩,
            W pos w!"be", W pos w!"the", W pos w!"coupling", W pos w!"associated", W pos w!"with",
            ⟨.mopen, pos, true⟩] ++ v ++ [⟨.mclose, pos, true⟩, period pos],
          [W pos w!"Then"] ++ expUnder g (th' ++ unsegs rest)]
      else none
    | _ => none
  | _ => none

/-- `[Consequently,] $\rho$, $\nu$, and $\eta$ depend affinely on the copula.`: each of them
is affine. -/
def dependAffinely (toks : List PTok) : Option (List (List PTok)) :=
  let body := match toks.getLast? with
    | some l => if isP l 46 then dropLast toks else toks
    | none => toks
  let body := match body with
    | a :: c :: r => if (match a.tok with | .word _ => true | _ => false) && isP c 44 then r else body
    | _ => body
  let ss := segs body
  match ss.reverse with
  | (false, ws) :: before =>
    let w := wordsOf ws
    if (w.take 4 == [w!"depend", w!"affinely", w!"on", w!"the"] || w.take 4 == [w!"depends", w!"affinely", w!"on", w!"the"]) && w.length ≤ 6 then
      let ok := before.all fun (m, ts) => if m then (inner ts).length == 1 else (wordsOf ts).all fun x => x == [44] || x == w!"and"
      let ms := (before.reverse.filter (·.1)).map (·.2)
      if ok && !ms.isEmpty then
        some (ms.map fun m => m ++ [W 0 w!"is", W 0 w!"affine", period 0])
      else none
    else none
  | _ => none

/-- Replace the tokens `old` by `new` in a formula. -/
def substToks (old new : List Tok) : Nat → List PTok → List PTok
  | 0, ts => ts
  | _, [] => []
  | f + 1, t :: rest =>
    if !old.isEmpty && ((t :: rest).take old.length).map (·.tok) == old then
      new.map (fun k => { t with tok := k }) ++ substToks old new f ((t :: rest).drop old.length)
    else t :: substToks old new f rest

/-- `[In particular,] if some $\gamma^*\in\Gamma$ satisfies $\gamma^*(K)=1$, then the
maximizers of $\gamma\mapsto e$ over $\Gamma$ are exactly the couplings concentrated on $K$.`:
if there is such an object, then `e` is the supremum exactly for the `\gamma` with
`\gamma(K)=1`. -/
def maximizers (toks : List PTok) : Option (List (List PTok)) :=
  let pos := (toks.head?.map (·.pos)).getD 0
  let body := match toks.getLast? with
    | some l => if isP l 46 then dropLast toks else toks
    | none => toks
  let ss := segs body
  let ss := match ss with
    | (false, w) :: rest =>
      (match wordsOf w with
       | [a, b, c, d, e] => if a == w!"in" && b == w!"particular" && c == [44] && d == w!"if" && e == w!"some" then some rest else none
       | [d, e] => if d == w!"if" && e == w!"some" then some rest else none
       | _ => none)
    | _ => none
  match ss with
  | some [(true, m), (false, w1), (true, p), (false, w2), (true, f), (false, w3), (true, a), (false, w4), (true, k)] =>
    let ws2 := wordsOf w2
    let ws4 := wordsOf w4
    let isMaxW := ws2 == [[44], w!"then", w!"the", w!"maximizers", w!"of"]
    let isMinW := ws2 == [[44], w!"then", w!"the", w!"minimizers", w!"of"]
    if wordsOf w1 == [w!"satisfies"] && (isMaxW || isMinW) && wordsOf w3 == [w!"over"] &&
        ws4.take 3 == [w!"are", w!"exactly", w!"the"] && ws4.drop (ws4.length - 2) == [w!"concentrated", w!"on"] then
      let mi := inner m
      let var0 := (mi.takeWhile (fun t => t.tok != .cmd w!"in")).map (·.tok)
      let dom0 := mi.drop (var0.length + 1)
      let fi := inner f
      match fi with
      | v :: arrow :: e =>
        let used (n : Codes) : Bool := body.any fun t => t.tok == .cmd n
        let fresh := [w!"mu", w!"sigma", w!"tau", w!"theta", w!"chi"].filter (!used ·)
        if arrow.tok == .cmd w!"mapsto" && !var0.isEmpty && !dom0.isEmpty && fresh.length ≥ 2 then
          let f1 : Tok := .cmd (fresh.getD 0 [])
          let f2 : Tok := .cmd (fresh.getD 1 [])
          let mt (k : Tok) : PTok := ⟨k, pos, true⟩
          let M (ts : List PTok) : List PTok := [mt .mopen] ++ ts ++ [mt .mclose]
          let ai := inner a
          let sup : Tok := .cmd (if isMaxW then w!"sup" else w!"inf")
          some [[W pos w!"For", W pos w!"every"] ++ M ([v, mt (.cmd w!"in")] ++ ai) ++
            [comma pos, W pos w!"if", W pos w!"there", W pos w!"is"] ++ M ([mt f1, mt (.cmd w!"in")] ++ dom0) ++
            [W pos w!"such", W pos w!"that"] ++ M (substToks var0 [f1] (p.length + 1) (inner p)) ++
            [comma pos, W pos w!"then"] ++
            M (e ++ [mt (.msym 61), mt sup, mt (.msym 95), mt .lbrace, mt f2, mt (.cmd w!"in")] ++ ai ++ [mt .rbrace] ++
              substToks [v.tok] [f2] (e.length + 1) e) ++
            [W pos w!"if", W pos w!"and", W pos w!"only", W pos w!"if"] ++
            M ([v, mt (.msym 40)] ++ inner k ++ [mt (.msym 41), mt (.msym 61), mt (.mnum 1)]) ++ [period pos]]
        else none
      | _ => none
    else none
  | _ => none

/-- The readings of an unread sentence to try, in order, each with the object it says a
value is attained by (for `its` in the next sentence). -/
def variants (known : List Codes) (ops : List (List Codes × Codes)) (pres : List (List PTok))
    (it : List PTok) (s : Sentence) : List (List Sentence × List PTok) :=
  let mk (v : List (List PTok)) : List Sentence := v.map fun ts => { s with toks := ts }
  let vs := [(false, true), (true, true), (false, false), (true, false)].filterMap fun (st, nm) =>
    expand known pres st nm s.toks
  (match attained known ops it s.toks with
   | some (v, x) => [(mk v, x)]
   | none => []) ++
  ([makesSplit s.toks [], setOf known (segs s.toks), followsCoupling s.toks, dependAffinely s.toks,
      maximizers s.toks].filterMap
    fun o => o.map fun v => (mk v, [])) ++
  ((vs.eraseDups.filter (· != [s.toks])).map fun v => (mk v, [])) ++
  -- a statement about a letter that a definition introduced (`For $c\in[0,1]$, …`): about
  -- every such value
  (let base := tidyRef (tidy s.toks)
   let letters : List Tok := (base.filterMap fun p => match p.tok with
     | .mvar c => if p.math then some (Tok.mvar c) else none
     | _ => none).eraseDups
   let lower (ts : List PTok) : List PTok := match ts with
     | t :: rest => (match t.tok with | .word w => { t with tok := .word (Grammar.lower w) } | _ => t) :: rest
     | [] => []
   let withPre : List (List PTok) :=
     if (match s.ctx.kind with | .proof => true | _ => false) || (forPrefix base).isSome then [] else
     ((letters.map fun l => stickyFor pres [l]).filter (!·.isEmpty)).eraseDups.map fun pre => pre ++ lower base
   ((if base != s.toks then [base] else []) ++ withPre.take 3).map fun v => (mk [v], []))

end Flex

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
  -- (the sequences of the result a proof proves, and those fixed in the text, stay)
  let seqs0 := st0.seqs.filter fun e => inheritedBinders.any (·.name == e.1) || st0.fixed.any (·.2.name == e.1)
  -- (and with its hypotheses, other than those of its cases and those it refuted)
  let inheritedHyps : List Hyp := match proved with
    | some e => ((st0.resultHyps.lookup e).getD []).filter fun h => h.item == 0
    | none => []
  let st0 := if st0.proofEnv != s.ctx.env then
      { st0 with proofEnv := s.ctx.env, proofCites := [], proofSteps := [], topic := Topic.none, envBinders := inheritedBinders, seqs := seqs0,
                 envHyps := inheritedHyps, hypUsed := false }
    else st0
  -- the hypothesis of a case ends with its item
  let st0 := { st0 with envHyps := st0.envHyps.filter fun h => h.item == 0 || s.ctx.items.contains h.item }
  -- definitions local to a result are visible in it and in its proof
  -- (in the running text, a value named by its function's letter is for its sentence)
  let st0 := { st0 with curEnv := s.ctx.env, curProved := proved, abbrevs := st0.abbrevs.filter (·.1 != 0) }
  -- (the environment of each proof, for `… from the proof of Theorem~\ref{l}`)
  let st0 := if s.ctx.kind == .proof && !st0.proofEnvs.any (·.2 == s.ctx.env) then
      { st0 with proofEnvs := (s.ctx.proves, s.ctx.env) :: st0.proofEnvs } else st0
  let st0 := match s.ctx.kind with
    | .result _ => if !s.ctx.label.isEmpty && !st0.resultEnvs.any (·.2 == s.ctx.env) then
        { st0 with resultEnvs := (s.ctx.label, s.ctx.env) :: st0.resultEnvs } else st0
    | _ => st0
  let st0 := { st0 with varDoms := st0.varDoms.filter (·.1 != 0) }
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
  -- (a symbol that a result or its proof defines, `h_t`, hides a notation of the article
  -- written with the same letter, `h_C`: in the sentence that defines it and after it)
  let target := (envs.lookup s.ctx.proves).getD 0
  let hidden : List Nat :=
    (Notation.mathSegs s.toks [] false []).filterMap Notation.definedLetter ++
    ((st0.globs.zip (List.range st0.globs.length)).filterMap fun (g, i) =>
      match g.key, st0.locals.lookup i with
      | ch :: rest, some e =>
        if (rest.isEmpty || rest.head? == some 95) && (e == s.ctx.env || (s.ctx.kind == .proof && e == target))
        then some ch else none
      | _, _ => none)
  let templates := st0.templates.filter fun t => match t.pat with
    | .fixed (.mvar ch) :: _ => !hidden.contains ch
    | _ => true
  let toks0 := s.toks
  let s := if templates.isEmpty || Notation.declares s.toks then s
    else { s with toks := Notation.rewriteAll templates s.toks }
  -- `On the event $φ$, we have $ψ$`: one formula about every value of the sample
  let s := { s with toks := Notation.onEvent (s.toks.length + 1) s.toks }
  -- a notation that binds a variable of its argument is not applied: a finding
  let capturedVar := Notation.captured s.toks
  let s := if capturedVar.isSome then { s with toks := toks0 } else s
  let s := if st0.wordAliases.isEmpty then s
    else { s with toks := Notation.rewriteWords st0.wordAliases (s.toks.length + 1) none s.toks }
  -- the symbols this sentence introduces, if it is not read
  let unread : List Codes := introducedSymbols s.toks
  let st0u := { st0 with unreadIds := (st0.unreadIds ++ unread.filter (!st0.unreadIds.contains ·)) }
  -- a symbol for a quantity that the article does not define (`Let $\chi(G)$ denote the
  -- chromatic number of a graph $G$.`), if the sentence has no other reading
  let undefinedAlt : Option Grammar.Sent := match s.ctx.kind with
    | .text => Grammar.undefinedOf s
    | _ => none
  if let some v := capturedVar then
    let name : Codes := match v with | .mvar ch => [ch] | .cmd nm => 92 :: nm | _ => []
    let msg : Codes := w!"a notation of the article binds $" ++ name ++ w!"$, and the formula it is written with here uses $" ++ name ++ w!"$ as well: the notation would capture it. Rename one of the two"
    { c with st := st0u, idx := c.idx + 1, outcomesRev := .failed ⟨E.finding, msg⟩ :: c.outcomesRev, proofs := incomplete ps }
  else
  -- (a sentence of several parts: the sentences it is made of, if it has no other reading,
  -- or if its reading as a whole does not compile)
  let partsOf : Unit → Option (List (Sentence × Grammar.Sent)) := fun _ =>
    (Grammar.partsOf s).bind fun ps => ps.mapM fun p => (Grammar.parseSentence p).map (p, ·)
  let parsed : Option (List (Sentence × Grammar.Sent)) :=
    match (Grammar.parseSentence s).orElse fun _ => undefinedAlt with
    | some sent => some [(s, sent)]
    | none => partsOf ()
  -- (a sentence without a reading, or whose reading does not compile: the sentences of a
  -- freer wording that it is read through)
  let flex : Unit → List (List (Sentence × Grammar.Sent) × List PTok) := fun _ =>
    let ops : List (List Codes × Codes) := st0.ops.filterMap fun (nm, i) => (st0.globs[i]?).map fun g => (nm, g.key)
    (Flex.variants (st0.globs.map (·.key)) ops st0.forPrefixes st0.lastAttained s).filterMap fun (v, x) =>
      (v.mapM fun p => (Grammar.parseSentence p).map (p, ·)).map (·, x)
  let parsed := match parsed with
    | some p => some p
    | none => if (flex ()).isEmpty then none else some []
  match parsed with
  | none => { c with st := st0u, idx := c.idx + 1, outcomesRev := .prose :: c.outcomesRev, proofs := incomplete ps }
  | some parts =>
    let sent : Grammar.Sent := match parts with
      | [(_, sn)] => sn
      | _ => .constDefs none [] []
    let sc : SentCtx := ⟨s.ctx, (envs.lookup s.ctx.proves).getD 0, c.idx⟩
    let one (part : Sentence) (sent : Grammar.Sent) (ptoks0 : List PTok) (alt : Option Grammar.Sent) :
        M (List Nat × List Nat) := do
        let before ← get
        let explicit := ptoks0.any (·.tok == .cmd w!"coloneqq")
        let primary : M (List Nat × List Nat) := match sent with
          | .notation k rhs => Compile.notationDef ptoks0 k rhs
          -- `We write $L$ for the WORDS`: a notation for an operation of the vocabulary, or
          -- else a description
          | .defDesc _ _ _ _ _ (some (k, rhs)) => do
            let st ← get
            -- (`$C^\top(u,v)\coloneqq C(v,u)$ denotes the transpose of $C$`: the article's own
            -- formula comes first, whatever notion of the vocabulary has these words)
            if explicit then
              tryCatch (Compile.sentence sc sent) fun e => do
                set st
                tryCatch (Compile.notationDef ptoks0 k rhs) fun _ => do set st; throw e
            else
            tryCatch (Compile.notationDef ptoks0 k rhs) fun _ => do
              set st
              Compile.sentence sc sent
          | _ => Compile.sentence sc sent
        -- (if no reading of the sentence compiles: the quantity it names, undefined)
        let (ds, cs) ← tryCatch primary fun e =>
          match alt, sent with
          | _, .undefined .. => throw e
          | some alt, _ => do
            set before
            -- (a finding about the quantity says more than the reading that failed)
            tryCatch (Compile.sentence sc alt) fun e' => throw (if e'.code == E.finding then e' else e)
          | none, _ => throw e
        -- a definition made under hypotheses takes those about its variables
        Compile.defsUnderHyps sc ds
        -- the introduction of a definition (`For a copula $C$, …`), for later definitions
        -- about its letters
        if !ds.isEmpty then
          match Flex.forPrefix part.toks with
          | some pre => modify fun st => { st with forPrefixes := pre :: st.forPrefixes }
          | none => pure ()
        match sent with
        | .claims _ _ _ | .claimsContra _ _ _ =>
          -- labels of displays in the sentence, and of the enclosing result, name its claims
          let ls := part.toks.filterMap fun p => match p.tok with | .ref .label l => some l | _ => none
          let ls := match s.ctx.kind with
            | .result _ => if s.ctx.label.isEmpty then ls else s.ctx.label :: ls
            | _ => ls
          Compile.addLabels ls cs false
        | .defNotion .. =>
          -- the displays of a notion's definition: citing them cites the definition
          let ls := part.toks.filterMap fun p => match p.tok with | .ref .label l => some l | _ => none
          Compile.addLabels ls [] true
        | _ => pure ()
        pure (ds, cs)
    -- the parts one after the other, each with the notations of the parts before it
    let runParts (parts : List (Sentence × Grammar.Sent)) : M (List Nat × List Nat) := do
      let n0 := st0.templates.length
      let mut ds : List Nat := []
      let mut cs : List Nat := []
      for (p, sn) in parts do
        let newT := (← get).templates.drop n0
        let (p, sn) := if newT.isEmpty || Notation.declares p.toks then (p, sn) else
          let p' := { p with toks := Notation.rewriteAll newT p.toks }
          match Grammar.parseSentence p' with
          | some sn' => (p', sn')
          | none => (p, sn)
        let (d, cl) ← one p sn p.toks none
        ds := ds ++ d
        cs := cs ++ cl
      pure (ds, cs)
    let tryFlex (e : Err) : M (List Nat × List Nat) := do
      let st ← get
      (flex ()).foldr (fun (v, x) next => do
        set st
        tryCatch (do
          let r ← runParts v
          unless x.isEmpty do modify fun st => { st with lastAttained := x }
          pure r) fun _ => next) (do set st; throw e)
    let labelled : M (List Nat × List Nat) :=
      match parts with
      | [] => tryFlex ⟨E.prose, []⟩
      | [(_, sn)] => do
        let st ← get
        tryCatch (one s sn toks0 (undefinedAlt.orElse fun _ => Grammar.thatIsSentence s)) fun e =>
          match partsOf () with
          | some ps@(_ :: _ :: _) => do
            set st
            tryCatch (runParts ps) fun _ => do
              set st
              tryFlex e
          | _ => do
            set st
            tryFlex e
      | _ => do
        let st ← get
        tryCatch (runParts parts) fun e => do
          set st
          tryFlex e
    let (r, st) := labelled.run.run st0
    match r with
    | .ok (ds, cs) =>
      let ps := ps.map fun p => if p.env == s.ctx.env then
        { p with steps := st.proofSteps, cites := st.proofCites } else p
      let saved := (s.ctx.env, st.envBinders) :: st.resultBinders.filter (·.1 != s.ctx.env)
      let st := match s.ctx.kind with
        | .result _ =>
          let savedHyps := (s.ctx.env, st.envHyps) :: st.resultHyps.filter (·.1 != s.ctx.env)
          -- the statement, for the hypothesis of an induction in the proof: the clauses
          -- of its claims, if they are claims about the variables of the result alone
          -- (the binders of the sentence, `For every positive integer $n$, …`, are variables
          -- of the result; a hypothesis among them, `If $x>0$, …`, is not kept here)
          let rec binder : Nat → Bind → Bool
            | _, .every _ _ | _, .noun _ => true
            | f + 1, .many bs => bs.all (binder f)
            | _, _ => false
          let plain : Option (List Clause) := match sent with
            | .claims topic binds cls =>
              if binds.all (binder 4) && topic == Topic.none && cls.all (fun c => c.binds.isEmpty && c.defs.isEmpty)
              then some (cls.map (·.clause)) else none
            | _ => if cs.isEmpty then some [] else none
          let stmt : Option (List Clause) := match st.resultStmts.lookup s.ctx.env, plain with
            | none, p => p
            | some (some old), some new => some (old ++ new)
            | _, _ => none
          let savedStmts := (s.ctx.env, stmt) :: st.resultStmts.filter (·.1 != s.ctx.env)
          { st with resultBinders := saved, resultHyps := savedHyps, resultStmts := savedStmts }
        | _ => st
      -- the subject of an unread notion is kept, and the sentence stays prose
      let o : Outcome := match sent with
        | .notionSubject _ => .prose
        | _ => .compiled ds cs
      { st, idx := c.idx + 1, outcomesRev := o :: c.outcomesRev, proofs := ps }
    | .error e =>
      -- An inclusion sign that no convention of the article resolves: if the sentence is
      -- read, or stops elsewhere, with `\subseteq` in its place, the sign is what stopped
      -- it, whatever name it stopped at first (`\supp u\subset K`: not `supp`).
      let resolved (sign to : Codes) : Bool :=
        s.toks.any (fun p => p.math && p.tok == .cmd sign) &&
        (let s' := { s with toks := s.toks.map fun p =>
            if p.math && p.tok == .cmd sign then { p with tok := .cmd to } else p }
         match Grammar.parseSentence s' with
         | some sent' =>
           match ((Compile.sentence sc sent').run.run st0).1 with
           | .ok _ => true
           | .error e' => e' != e
         | none => false)
      let e : Err :=
        if e.code == E.prose || e.detail == w!"\\subset" || e.detail == w!"\\supset" then e
        else if resolved w!"subset" w!"subseteq" then ⟨E.undefined, w!"\\subset"⟩
        else if resolved w!"supset" w!"supseteq" then ⟨E.undefined, w!"\\supset"⟩
        else e
      -- A noun that the article or its vocabulary know is not what stopped the sentence.
      let e : Err := if e.code == E.noun then nounFinding st0.vocab st0.nouns e else e
      -- A sentence of the text that is read only through `, that is,` (its formal
      -- restatement) stays prose if that restatement does not compile.
      let isText : Bool := match s.ctx.kind with | .text => true | _ => false
      let thatIsOnly : Bool := isText && (Grammar.parseSentence s).isSome &&
        (Grammar.parseSentence (noThatIs s)).isNone
      -- A step of a proof about a letter that the proof introduces in words (`On this
      -- rectangle, …`), or with a placeholder (`$\Delta(1-w,\cdot)\ge0$`), is not read.
      -- (a letter with an argument, `$t(x)$`, is a symbol that should be defined)
      let applied (c : Nat) (ts : List PTok) : Bool :=
        (ts.zip (ts.drop 1)).any fun (a, b) => a.tok == .mvar c && b.tok == .msym 40
      let proofLocal : Bool := (match s.ctx.kind with | .proof => true | _ => false) &&
        e.code == E.undefined && (e.detail == w!"\\cdot" ||
          (match e.detail with | [c] => !applied c s.toks | _ => false))
      let o : Outcome := if e.code == E.prose || thatIsOnly || proofLocal then .prose else .failed e
      { c with st := st0u, idx := c.idx + 1, outcomesRev := o :: c.outcomesRev, proofs := incomplete ps }

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
