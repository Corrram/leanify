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

/-- Other wordings of what the grammar reads, as authors write them: each is replaced by
the wording of `docs/writing.md` before the sentence is read (`for any` is `for every`,
`so that` is `such that`, `one has` is `we have`). -/
def standardWords : List (List Codes × List Tok) :=
  let w (s : List Codes) : List Tok := s.map Tok.word
  [([w!"so", w!"that"], w [w!"such", w!"that"]),
   ([w!"iff"], w [w!"if", w!"and", w!"only", w!"if"]),
   ([w!"it", w!"holds", w!"that"], w [w!"we", w!"have"]),
   ([w!"we", w!"have", w!"that"], w [w!"we", w!"have"]),
   ([w!"one", w!"has"], w [w!"we", w!"have"]),
   ([w!"one", w!"gets"], w [w!"we", w!"have"]),
   ([w!"one", w!"obtains"], w [w!"we", w!"have"]),
   ([w!"there", w!"is", w!"some"], w [w!"there", w!"is", w!"a"]),
   ([w!"there", w!"exists", w!"some"], w [w!"there", w!"exists", w!"a"]),
   -- (`mapping` for `map`; a `family` or a `collection` of objects is a set of them)
   ([w!"mapping"], w [w!"map"]), ([w!"mappings"], w [w!"maps"]),
   ([w!"family", w!"of"], w [w!"set", w!"of"]), ([w!"families", w!"of"], w [w!"sets", w!"of"]),
   ([w!"collection", w!"of"], w [w!"set", w!"of"]), ([w!"collections", w!"of"], w [w!"sets", w!"of"]),
   ([w!"be", w!"two"], w [w!"be"]), ([w!"be", w!"three"], w [w!"be"]), ([w!"be", w!"four"], w [w!"be"])]

/-- The tokens of a group of a formula up to its closing brace (the opening one read), and
those after it. -/
def groupBody : Nat → Nat → List PTok → List PTok → Option (List PTok × List PTok)
  | 0, _, _, _ => none
  | _ + 1, _, [], _ => none
  | f + 1, d, t :: ts, acc =>
    if t.tok == .rbrace then (if d == 0 then some (acc.reverse, ts) else groupBody f (d - 1) ts (t :: acc))
    else if t.tok == .lbrace then groupBody f (d + 1) ts (t :: acc)
    else groupBody f d ts (t :: acc)

/-- The tokens of a group before and after its `\choose` (at the depth of the group). -/
def splitChoose : Nat → Nat → List PTok → List PTok → Option (List PTok × List PTok)
  | 0, _, _, _ => none
  | _ + 1, _, [], _ => none
  | f + 1, d, t :: ts, acc =>
    if d == 0 && t.tok == .cmd w!"choose" then some (acc.reverse, ts)
    else if t.tok == .lbrace then splitChoose f (d + 1) ts (t :: acc)
    else if t.tok == .rbrace then splitChoose f (d - 1) ts (t :: acc)
    else splitChoose f d ts (t :: acc)

/-- `{n \choose k}` as `\binom{n}{k}`. -/
def chooseBinom : Nat → List PTok → List PTok
  | 0, ts => ts
  | _ + 1, [] => []
  | f + 1, t :: ts =>
    if t.tok == .lbrace then
      match groupBody (ts.length + 1) 0 ts [] with
      | some (inner, rest) =>
        match splitChoose (inner.length + 1) 0 inner [] with
        | some (a, b) =>
          let mk (k : Tok) : PTok := ⟨k, t.pos, t.math⟩
          [mk (.cmd w!"binom"), mk .lbrace] ++ chooseBinom f a ++ [mk .rbrace, mk .lbrace] ++ chooseBinom f b ++
            [mk .rbrace] ++ chooseBinom f rest
        | none => t :: chooseBinom f ts
      | none => t :: chooseBinom f ts
    else t :: chooseBinom f ts

/-- `{\mathcal{G}}` (as `{\cal G}` is lexed) as `\mathcal{G}`: braces around one letter in a
font are no group. -/
def unbraceFont : Nat → List PTok → List PTok
  | 0, ts => ts
  | _ + 1, [] => []
  | f + 1, t :: ts =>
    match t.tok, ts with
    | .lbrace, c :: o :: x :: cl :: cl2 :: rest =>
      let font := match c.tok with
        | .cmd n => [w!"mathcal", w!"mathbb", w!"mathbf", w!"mathfrak", w!"mathscr", w!"mathit", w!"mathrm", w!"mathsf"].contains n
        | _ => false
      let letter := match x.tok with | .mvar _ => true | _ => false
      if font && o.tok == .lbrace && letter && cl.tok == .rbrace && cl2.tok == .rbrace then
        c :: o :: x :: cl :: unbraceFont f rest
      else t :: unbraceFont f ts
    | _, _ => t :: unbraceFont f ts

/-- A token that is a relation of the formula grammar (`=`, `<`, `\le`, `\subseteq`, …). -/
def relationTok (t : Tok) : Bool :=
  match t with
  | .msym c => c == 61 || c == 60 || c == 62
  | .cmd c => [w!"le", w!"leq", w!"ge", w!"geq", w!"ne", w!"neq", w!"subseteq", w!"supseteq", w!"in", w!"sim", w!"equiv",
      w!"subsetneq", w!"supsetneq", w!"coloneqq"].contains c
  | _ => false

/-- `\stackrel{(a)}{\le}`, `\overset{\text{def}}{=}`, `\stackrel{d}{=}`: a relation with an
annotation above it. `def`, `\triangle` or `:` above `=` make it `\coloneqq`; `d`, `D`,
`\mathcal{D}`, `\mathcal{L}`, `law` or `dist` above `=` make it equality in distribution. An
annotation that is a label or a reference (`(a)`, `(2.3)`, `\eqref{…}`, `*`) or a reason
in words (`\text{by (2)}`, `\text{IH}`) is dropped. Any other annotation may change what
the relation says (`a.s.`, `n\to\infty`, `!`), and the notation is then not read. -/
def annotatedRel : Nat → List PTok → List PTok
  | 0, ts => ts
  | _ + 1, [] => []
  | f + 1, t :: ts =>
    let keep := t :: annotatedRel f ts
    if t.tok != .cmd w!"stackrel" && t.tok != .cmd w!"overset" then keep else
    match ts with
    | a :: r1 =>
      if a.tok != .lbrace then keep else
      match groupBody (r1.length + 1) 0 r1 [] with
      | some (above, b :: r3) =>
        -- (the relation in braces, or alone: `\stackrel{d}=`)
        let relOf : Option (PTok × List PTok) :=
          if b.tok != .lbrace then (if relationTok b.tok then some (b, r3) else none) else
          match groupBody (r3.length + 1) 0 r3 [] with
          | some ([rel], r4) => some (rel, r4)
          | _ => none
        match relOf with
        | some (rel, r4) =>
          if !relationTok rel.tok then keep else
          let letters : Codes := above.flatMap fun u => match u.tok with
            | .mvar c => [c]
            | .word w => w
            | _ => []
          let isDef := letters == w!"def" || letters == w!"Def" ||
            (above.length == 1 && (above.head?.any fun u => u.tok == .cmd w!"triangle" || u.tok == .msym 58))
          -- (the letters alone, in any font: `d`, `\mathrm{d}`, `\mathcal{D}`, `\text{law}`)
          let plain := above.all fun u => match u.tok with
            | .mvar _ | .word _ | .lbrace | .rbrace => true
            | .cmd c => [w!"mathrm", w!"mathcal", w!"mathscr", w!"text", w!"textrm", w!"mathit", w!"operatorname", w!"scriptscriptstyle", w!"scriptstyle"].contains c
            | _ => false
          let isLaw := plain && [w!"d", w!"D", w!"L", w!"law", w!"dist", w!"distr"].contains letters
          let isRef := above.any fun u => match u.tok with
            | .cmd c => [w!"ref", w!"eqref", w!"cref", w!"Cref", w!"cite", w!"ast", w!"star", w!"dagger"].contains c
            | .msym 40 | .msym 41 | .msym 42 | .punct 40 | .punct 41 | .punct 42 => true
            | _ => false
          -- (a reason in words: not the abbreviations that say how the relation holds)
          let isWords := !above.isEmpty && !above.any (fun u => match u.tok with | .mvar _ => true | _ => false) &&
            (above.any fun u => match u.tok with | .word _ => true | _ => false) &&
            ![w!"as", w!"ae", w!"a", w!"p", w!"P", w!"prob", w!"wp", w!"d", w!"D", w!"L", w!"law", w!"dist", w!"distr", w!"def", w!"Def"].contains letters
          if isDef && rel.tok == .msym 61 then ⟨.cmd w!"coloneqq", rel.pos, rel.math⟩ :: annotatedRel f r4
          else if isLaw && rel.tok == .msym 61 then ⟨.cmd w!"leanifyeqd", rel.pos, rel.math⟩ :: annotatedRel f r4
          else if isRef || isWords then rel :: annotatedRel f r4
          else keep
        | none => keep
      | _ => keep
    | [] => keep

/-- `one-to-one` as `injective` (not in `one-to-one correspondence`, a bijection). -/
def oneToOne : Nat → List PTok → List PTok
  | 0, ts => ts
  | _ + 1, [] => []
  | f + 1, t :: ts =>
    match Grammar.textWord t, ts with
    | some o1, h1 :: t2 :: h2 :: o2 :: rest =>
      if o1 == w!"one" && h1.tok == .punct 45 && Grammar.textWord t2 == some w!"to" && h2.tok == .punct 45 &&
          Grammar.textWord o2 == some w!"one" && !(rest.head?.any fun u => Grammar.textWord u == some w!"correspondence") then
        ⟨.word w!"injective", t.pos, false⟩ :: oneToOne f rest
      else t :: oneToOne f ts
    | _, _ => t :: oneToOne f ts

/-- The number of letters in the formulas between a `let` and a `be`, from the tokens before
`be` (the latest first); `none` if a token that is not a letter, a comma, `and` or `let`
comes first. -/
def letVarCount : Nat → List PTok → Bool → Int → Nat → Option Nat
  | 0, _, _, _, _ => none
  | _ + 1, [], _, _, _ => none
  | f + 1, t :: ts, inMath, depth, n =>
    if inMath then
      match t.tok with
      | .mopen => letVarCount f ts false 0 (n + 1)
      | .rbrace | .msym 41 | .msym 93 => letVarCount f ts true (depth + 1) n
      | .lbrace | .msym 40 | .msym 91 => letVarCount f ts true (depth - 1) n
      | .msym 44 => letVarCount f ts true depth (if depth == 0 then n + 1 else n)
      | .cmd c => if c == w!"in" || c == w!"subseteq" || c == w!"colon" then none else letVarCount f ts true depth n
      | .msym 58 | .msym 61 | .msym 60 | .msym 62 => none
      | _ => letVarCount f ts true depth n
    else if t.tok == .mclose then letVarCount f ts true 0 n
    else if !t.math && t.tok == .punct 44 then letVarCount f ts false 0 n
    else match Grammar.textWord t with
      | some w => if w == w!"let" then (if n > 0 then some n else none)
        else if w == w!"and" then letVarCount f ts false 0 n else none
      | none => none

/-- The number words of `dropCounts`. -/
def countWords : List (Codes × Nat) := [(w!"two", 2), (w!"three", 3), (w!"four", 4), (w!"five", 5), (w!"six", 6)]

/-- `dropCounts`, with the tokens before (the latest first). -/
def dropCountsAux : List PTok → List PTok → List PTok
  | _, [] => []
  | before, t :: ts =>
    let drop : Bool := match Grammar.textWord t >>= (fun w => List.lookup w countWords), before with
      | some n, b :: bs => Grammar.textWord b == some w!"be" && letVarCount (bs.length + 1) bs false 0 0 == some n
      | _, _ => false
    if drop then dropCountsAux (t :: before) ts else t :: dropCountsAux (t :: before) ts

/-- Without the number word of `let $x$, $y$ be two NOUNS` (`$x,y$`, `$x$ and $y$`) where it
counts the variables: they are such objects, as `let $x$, $y$ be NOUNS` (`two` does not
say that they are distinct; `two distinct` does, and keeps its word). -/
def dropCounts (ts : List PTok) : List PTok := dropCountsAux [] ts

/-- Without the parentheticals that constrain nothing: `(possibly infinite)`, `(not
necessarily commutative)`, `(possibly empty)`. -/
def dropUnconstraining : Nat → List PTok → List PTok
  | 0, ts => ts
  | _, [] => []
  | f + 1, t :: ts =>
    if !t.math && t.tok == .punct 40 then
      let inner := ts.takeWhile fun u => !(u.tok == .punct 41)
      let closes := (ts.drop inner.length).head?.any fun u => u.tok == .punct 41 && !u.math
      let words := inner.filterMap fun u => if u.math then none else match u.tok with
        | .word w => some (Grammar.lower w)
        | _ => none
      let plain := inner.all fun u => !u.math && (match u.tok with
        | .word _ | .punct 45 | .punct 44 => true
        | _ => false)
      let lead := words.take 1 == [w!"possibly"] || words.take 2 == [w!"not", w!"necessarily"]
      if closes && plain && lead && words.length ≥ 2 then dropUnconstraining f (ts.drop (inner.length + 1))
      else t :: dropUnconstraining f ts
    else t :: dropUnconstraining f ts

/-- Is there a determiner before (the tokens before, the latest first), with words, hyphens
and commas between? -/
def detBefore : Nat → List PTok → Bool
  | 0, _ => false
  | _ + 1, [] => false
  | f + 1, u :: us =>
    if u.math then false else
    match Grammar.textWord u with
    | some w => if [w!"a", w!"an", w!"every", w!"each", w!"any", w!"some", w!"all", w!"no"].contains w then true else detBefore f us
    | none => if u.tok == .punct 45 || u.tok == .punct 44 then detBefore f us else false

/-- `adjectiveCommas`, with the tokens before (the latest first). -/
def adjCommasAux (firsts lasts : List Codes) : List PTok → List PTok → List PTok
  | _, [] => []
  | before, t :: ts =>
    let drop : Bool := !t.math && t.tok == .punct 44 && (match before, ts with
      | b :: bs, a :: _ => (match Grammar.textWord b, Grammar.textWord a with
          | some wb, some wa => lasts.contains wb && firsts.contains wa && detBefore (bs.length + 1) bs
          | _, _ => false)
      | _, _ => false)
    if drop then adjCommasAux firsts lasts (t :: before) ts else t :: adjCommasAux firsts lasts (t :: before) ts

/-- Without the commas between the adjectives before a noun: `a compact, connected metric
space` as `a compact connected metric space`. A comma goes where it follows a determiner
(`a`, `an`, `every`, `each`, `any`, `some`, `all`, `no`) and words only, the word before it
ends an adjective and the word after it begins one (of the vocabulary, or a notion of the
article). -/
def adjectiveCommas (V : Vocab) (notions : List (List Codes)) (ts : List PTok) : List PTok :=
  let firsts : List Codes := V.adjectives.filterMap (·.words.head?) ++
    V.mods.filterMap (fun m => match m.phrase.head? with | some (.w w) => some w | _ => none) ++ notions.filterMap (·.head?)
  let lasts : List Codes := V.adjectives.filterMap (·.words.getLast?) ++
    V.mods.filterMap (fun m => match m.phrase.getLast? with | some (.w w) => some w | _ => none) ++ notions.filterMap (·.getLast?)
  adjCommasAux firsts lasts [] ts

/-- Words around a formula that say nothing more than the formula: `$φ$ holds` is `$φ$`,
`the inequality $φ$` is `$φ$`; and `If $φ$ then $ψ$` has its comma, `real $x$` its noun,
`there is … $y$ with $φ$` is `such that $φ$`. `there` says whether `there is|exists` came
before in the sentence, `cond` whether the sentence is inside the condition of an `if`:
there `any` is left alone, since `if $f(x)=0$ for any $x$` asks for one `x` only. -/
def standardForms : Nat → Bool → Bool → Option PTok → List PTok → List PTok
  | 0, _, _, _, ts => ts
  | _ + 1, _, _, _, [] => []
  | f + 1, there, cond, prev, t :: ts =>
    let lw (p : PTok) : Option Codes := match p.tok with
      | .word v => if p.math then none else some (Grammar.lower v)
      | _ => none
    let afterMath := match prev with | some p => p.tok == .mclose | none => false
    let beforeMath := match ts with | n :: _ => n.tok == .mopen | [] => false
    let word (v : Codes) : PTok := ⟨.word v, t.pos, false⟩
    let prevWord := prev.bind lw
    let beforeEnd := match ts with
      | n :: _ => (match n.tok with | .punct _ => true | _ => false)
      | [] => true
    let kinds : List Codes := [w!"inequality", w!"identity", w!"equality", w!"estimate", w!"bound", w!"formula", w!"relation"]
    match lw t with
    | some v =>
      -- `$φ$ holds`
      if (v == w!"holds" || v == w!"hold") && afterMath then standardForms f there cond prev ts
      -- `$(a_n)$ converges to $l$`, `$(a_n)$ converges`, `$(a_n)$ diverges`: the modifiers
      -- `converging to`, `convergent`, `divergent`
      else if v == w!"converges" && afterMath && (match ts with
          | n :: m :: _ => lw n == some w!"to" && m.tok == .mopen
          | _ => false) then
        word w!"is" :: word w!"converging" :: standardForms f there cond (some (word w!"converging")) ts
      -- `$B$ spans $V$`, `$S$ generates $G$`: a spanning or generating set of it
      else if (v == w!"spans" || v == w!"generates") && afterMath && beforeMath then
        word w!"is" :: word w!"a" :: word (if v == w!"spans" then w!"spanning" else w!"generating") :: word w!"set" ::
          word w!"of" :: standardForms f there cond (some (word w!"of")) ts
      -- `$G$ has order $n$`, `$g$ has finite order`, `$K$ has characteristic $p$`: the
      -- modifiers `of order $n$`, `of finite order`, `of characteristic $p$`
      else if (v == w!"has" || v == w!"have") && afterMath && (match ts with
          | n :: m :: _ =>
            let quantity (x : Option Codes) : Bool := match x with
              | some x => [w!"order", w!"characteristic", w!"dimension", w!"index", w!"degree"].contains x
              | none => false
            (quantity (lw n) && m.tok == .mopen) ||
              -- (`has dimension at most $3$`)
              (quantity (lw n) && (lw m == some w!"at") && (match ts.drop 2 with
                | q :: k :: _ => (lw q == some w!"most" || lw q == some w!"least") && k.tok == .mopen
                | _ => false)) ||
              (((lw n).map fun x => [w!"finite", w!"infinite", w!"prime", w!"odd", w!"even", w!"positive"].contains x).getD false &&
                quantity (lw m))
          | _ => false) then
        word (if v == w!"has" then w!"is" else w!"are") :: word w!"of" :: standardForms f there cond (some (word w!"of")) ts
      else if (v == w!"converges" || v == w!"diverges") && afterMath && (beforeEnd || (match ts with
          | n :: _ => ((lw n).map fun x => [w!"if", w!"iff", w!"whenever", w!"since", w!"and", w!"or", w!"but"].contains x).getD false
          | [] => false)) then
        word w!"is" :: word (if v == w!"converges" then w!"convergent" else w!"divergent") ::
          standardForms f there cond (some (word w!"convergent")) ts
      -- `the inequality $φ$`
      else if v == w!"the" && (match ts with
          | k :: n :: _ => ((lw k).map kinds.contains).getD false && n.tok == .mopen
          | _ => false) then standardForms f there cond prev (ts.drop 1)
      -- `Then the sequence $(a_n^2)$ converges`, `the number $n^3-n$ is divisible by $6$`: the
      -- formula (not after `of`: `the limit of the sequence $a$` is a notion's)
      else if v == w!"the" && (prevWord == some w!"then" || prevWord == some w!"that" ||
          prevWord == some w!"and" || prevWord == some w!"if" || (prev.map (·.tok == .punct 44)).getD false ||
          (prev.isNone && (match ts with | k :: _ => lw k == some w!"sequence" || lw k == some w!"series" | _ => false))) && (match ts with
          | k :: n :: _ => (lw k == some w!"sequence" || lw k == some w!"series" || lw k == some w!"number" || lw k == some w!"integer") && n.tok == .mopen
          | _ => false) then standardForms f there cond prev (ts.drop 1)
      -- `If $φ$ then $ψ$`
      else if v == w!"then" && afterMath then
        ⟨.punct 44, t.pos, false⟩ :: t :: standardForms f there cond (some t) ts
      -- `we obtain $φ$`
      else if (v == w!"get" || v == w!"obtain" || v == w!"find") && prevWord == some w!"we" && beforeMath then
        word w!"have" :: standardForms f there cond (some t) ts
      -- `Let $X$ follow a normal distribution with …`, `$X$ has a Poisson distribution with
      -- …`: a random variable with it
      else if (v == w!"follow" || v == w!"follows" || v == w!"have" || v == w!"has") && (match ts with
            | a :: d :: _ => (lw a == some w!"a" || lw a == some w!"an" || lw a == some w!"the") &&
                (lw d).any fun x => [w!"normal", w!"standard", w!"poisson", w!"exponential", w!"uniform", w!"bernoulli", w!"binomial"].contains x
            | _ => false) && afterMath then
        let verb := if v == w!"follow" || v == w!"have" then w!"be" else w!"is"
        word verb :: word w!"a" :: word w!"random" :: word w!"variable" :: word w!"with" ::
          standardForms f there cond (some (word w!"with")) ts
      -- `at least two vertices`: the number `$2$`
      else if (prevWord == some w!"least" || prevWord == some w!"most" || prevWord == some w!"exactly") &&
          ([w!"two", w!"three", w!"four", w!"five", w!"six", w!"seven", w!"eight", w!"nine", w!"ten"].idxOf? v).isSome then
        let k := ([w!"two", w!"three", w!"four", w!"five", w!"six", w!"seven", w!"eight", w!"nine", w!"ten"].idxOf v) + 2
        ⟨.mopen, t.pos, false⟩ :: ⟨.mnum k, t.pos, true⟩ :: ⟨.mclose, t.pos, false⟩ :: standardForms f there cond (some ⟨.mclose, t.pos, false⟩) ts
      -- `$\sum a_n$ converges absolutely`: `… is absolutely convergent`
      else if v == w!"converges" && afterMath && (match ts with
          | a :: e :: _ => lw a == some w!"absolutely" && (match e.tok with | .punct _ => true | _ => false)
          | _ => false) then
        word w!"is" :: word w!"absolutely" :: word w!"convergent" :: standardForms f there cond (some t) (ts.drop 1)
      -- `Let $(a,b)$ be a pair of integers`, `a triple of …`, `an ordered pair of …`: `Let
      -- $a,b$ be integers` (letters and commas only between the parentheses)
      else if v == w!"let" && (match ts with
          | o :: l :: _ => o.tok == .mopen && l.tok == .msym 40
          | _ => false) && (
          let inner := (ts.drop 2).takeWhile (·.tok != .mclose)
          let after := ts.drop (inner.length + 3)
          let after := match after with
            | b :: a :: rest => if lw b == some w!"be" && (lw a == some w!"a" || lw a == some w!"an") then rest else []
            | _ => []
          let after := match after with | o :: rest => if lw o == some w!"ordered" then rest else after | [] => []
          inner.getLast?.map (·.tok) == some (.msym 41) && inner.length ≥ 4 &&
          (inner.dropLast.all fun p => match p.tok with | .mvar _ | .msym 44 | .cmd _ => true | _ => false) &&
          (match after with
            | k :: o :: _ => (lw k).any (fun x => [w!"pair", w!"triple", w!"tuple", w!"quadruple"].contains x) && lw o == some w!"of"
            | _ => false)) then
        let inner := (ts.drop 2).takeWhile (·.tok != .mclose)
        let after := ts.drop (inner.length + 3)
        -- (after `be a [ordered] pair of`)
        let rest := (after.dropWhile fun p => lw p != some w!"of").drop 1
        match ts with
        | o :: _ =>
          t :: o :: inner.dropLast ++ [⟨.mclose, t.pos, false⟩, word w!"be"] ++ standardForms f there cond (some (word w!"be")) rest
        | [] => [t]
      -- `either A or B`: `A or B`
      else if v == w!"either" && ts.any (fun p => lw p == some w!"or") then standardForms f there cond prev ts
      -- `NP can be written as a NP'`, `… can be expressed as …`: `NP is a NP'`
      else if v == w!"can" && (match ts with
          | b :: w :: a :: _ => lw b == some w!"be" && (lw w == some w!"written" || lw w == some w!"expressed" || lw w == some w!"represented") && lw a == some w!"as"
          | _ => false) then
        word w!"is" :: standardForms f there cond (some (word w!"is")) (ts.drop 3)
      -- `a Poisson random variable with parameter $\lambda$` (binomial, exponential, normal,
      -- Gaussian, Bernoulli): `a random variable that is Poisson distributed with …`
      else if (match lw t with
          | some d => [w!"poisson", w!"binomial", w!"exponential", w!"normal", w!"gaussian", w!"bernoulli"].contains d
          | none => false) && (match ts with
          | r :: va :: wi :: _ => lw r == some w!"random" && (lw va == some w!"variable" || lw va == some w!"variables") && lw wi == some w!"with"
          | _ => false) then
        match ts with
        | r :: va :: rest =>
          let d := (lw t).getD []
          let adv : Codes := if d == w!"poisson" then w!"Poisson" else if d == w!"binomial" then w!"binomially"
            else if d == w!"exponential" then w!"exponentially" else if d == w!"bernoulli" then w!"Bernoulli" else w!"normally"
          r :: va :: word w!"that" :: word (if lw va == some w!"variables" then w!"are" else w!"is") :: word adv :: word w!"distributed" ::
            standardForms f there cond (some (word w!"distributed")) rest
        | _ => t :: standardForms f there cond (some t) ts
      -- `φ whenever $ψ$`: `φ for $ψ$` (for every value of the new variables of `ψ`, inside the
      -- clause that `φ` is part of: `there is $\delta>0$ such that … whenever $|x|<\delta$`)
      else if v == w!"whenever" && beforeMath then word w!"for" :: standardForms f there cond (some (word w!"for")) ts
      -- `Let $(X,d)$ be a metric space`: the space `X`, whose distance `d` is the vocabulary's
      -- (`(V,\|\cdot\|)`, a normed space, likewise)
      else if (v == w!"let" || v == w!"and") && (match ts with
          | o :: l :: x :: c :: _ => o.tok == .mopen && l.tok == .msym 40 && (match x.tok with | .mvar _ => true | _ => false) && c.tok == .msym 44
          | _ => false) && (
          let inner := (ts.drop 1).takeWhile (·.tok != .mclose)
          let after := ts.drop (inner.length + 2)
          inner.getLast?.map (·.tok) == some (.msym 41) &&
          (after.take 12).any (fun p => lw p == some w!"space" || lw p == some w!"spaces") &&
          ((after.head? >>= lw) == some w!"be" || (after.head? >>= lw) == some w!"and")) then
        match ts with
        | o :: _ :: x :: rest =>
          let inner := rest.takeWhile (·.tok != .mclose)
          t :: o :: x :: standardForms f there cond (some x) (rest.drop inner.length)
        | _ => t :: standardForms f there cond (some t) ts
      -- `non-abelian`, `non-empty`: one word, `nonabelian` (the negation of the adjective,
      -- where the vocabulary does not name the word itself)
      else if v == w!"non" && (match ts with
          | h :: x :: _ => h.tok == .punct 45 && (lw x).isSome
          | _ => false) then
        match ts with
        | _ :: x :: rest => standardForms f there cond prev (word (w!"non" ++ (lw x).getD []) :: rest)
        | _ => t :: standardForms f there cond (some t) ts
      -- `for all real $x$`
      -- (not before a size and the noun it qualifies, `a real $2\times2$ matrix`, `a real
      -- $n$-vector`)
      else if v == w!"real" && beforeMath && !(match ts.dropWhile (·.tok != .mclose) with
          | _ :: n :: _ => (lw n).any fun x => [w!"matrix", w!"matrices", w!"vector", w!"vectors", w!"polynomial",
              w!"polynomials", w!"function", w!"functions", w!"sequence", w!"sequences", w!"random", w!"symmetric",
              w!"square", w!"diagonal", w!"orthogonal", w!"invertible", w!"array", w!"arrays"].contains x
          | _ => false) then t :: word w!"number" :: standardForms f there cond (some t) ts
      -- `Let $x$ be real.`
      else if v == w!"real" && prevWord == some w!"be" && beforeEnd then
        word w!"a" :: t :: word w!"number" :: standardForms f there cond (some t) ts
      -- `Any real number $x$ satisfies`, `for any $x$`: every one, outside a condition
      -- (not `any two`, which says something of every two of them)
      else if v == w!"any" && !cond && (prev.isNone || prevWord == some w!"for") &&
          !(match ts with | n :: _ => lw n == some w!"two" | [] => false) then
        word w!"every" :: standardForms f there cond (some t) ts
      -- `Given $x>0$, we have`
      else if v == w!"given" && prev.isNone && beforeMath then
        word w!"for" :: standardForms f there cond (some t) ts
      -- `for all $x$ we have $φ$`
      else if v == w!"we" && afterMath && (match ts with | n :: _ => lw n == some w!"have" | [] => false) then
        ⟨.punct 44, t.pos, false⟩ :: t :: standardForms f there cond (some t) ts
      -- `such that for all $x$ we have $φ$`
      else if v == w!"that" && prevWord == some w!"such" &&
          (match ts with | n :: _ => lw n == some w!"for" | [] => false) then
        t :: ⟨.punct 44, t.pos, false⟩ :: standardForms f there cond (some t) ts
      -- `there is a real number $y>0$ with $y<x$`
      else if v == w!"with" && there && afterMath && beforeMath &&
          !(ts.any fun p => lw p == some w!"such") then
        word w!"such" :: word w!"that" :: standardForms f false cond (some t) ts
      else
        let there' := there || ((v == w!"is" || v == w!"exists" || v == w!"exist") &&
          (match prev with | some p => lw p == some w!"there" | none => false))
        let cond' := (cond || v == w!"if") && v != w!"then"
        t :: standardForms f there' cond' (some t) ts
    | none =>
      -- `Then $(X,d)$ is complete.`: the space `X` of `Let $(X,d)$ be a metric space` (the letter
      -- of a space and the vocabulary's distance, before `is`)
      let spaceOf : Option PTok := match t.tok, ts with
        | .mopen, l :: x :: c :: d :: r :: e :: n :: _ =>
          if l.tok == .msym 40 && c.tok == .msym 44 && r.tok == .msym 41 && e.tok == .mclose &&
              (lw n == some w!"is" || lw n == some w!"are") &&
              (match x.tok, d.tok with
                | .mvar u, .mvar k => 65 ≤ u && u ≤ 90 && k == 100
                | _, _ => false) then some x else none
        | _, _ => none
      -- `$a^2\equiv0$ or $a^2\equiv1\pmod4$`: the modulus of the second congruence is also that
      -- of the first
      let sharedMod : Option (List PTok) := do
        if t.tok != .mopen then none
        let body1 := ts.takeWhile (·.tok != .mclose)
        let rest1 := ts.drop body1.length
        if !(body1.any (·.tok == .cmd w!"equiv")) || body1.any (fun p => p.tok == .cmd w!"pmod" || p.tok == .cmd w!"bmod") then none
        -- (the first congruence after it with a modulus, through `or` and `and`: `$x\equiv0$ or
        -- $x\equiv1$ or $x\equiv8\pmod9$`)
        let rec ahead : Nat → List PTok → Option (List PTok)
          | 0, _ => none
          | g + 1, rest =>
            match rest with
            | _ :: conj :: open2 :: more =>
              if !(lw conj == some w!"or" || lw conj == some w!"and") || open2.tok != .mopen then none else
              let body2 := more.takeWhile (·.tok != .mclose)
              if !(body2.any (·.tok == .cmd w!"equiv")) then none else
              match body2.findIdx? (·.tok == .cmd w!"pmod") with
              | some k => some (body2.drop k)
              | none => ahead g (more.drop body2.length)
            | _ => none
        let modToks ← ahead 6 rest1
        some (body1 ++ modToks ++ rest1)
      -- `integers $p$ and $q\ne0$`: the condition of the last name, `integers $p$ and $q$ with
      -- $q\ne0$` (not of both, as `$p,q\ne0$` says)
      let lastCond : Option (List PTok) := do
        if t.tok != .mopen then none
        let pw ← prevWord
        if pw.getLast? != some 115 then none
        let a :: c1 :: andW :: o2 :: more := ts | none
        let .mvar _ := a.tok | none
        if c1.tok != .mclose || lw andW != some w!"and" || o2.tok != .mopen then none
        let body2 := more.takeWhile (·.tok != .mclose)
        let v :: rel :: _ := body2 | none
        let .mvar _ := v.tok | none
        let isRel := match rel.tok with
          | .cmd c => [w!"ne", w!"neq", w!"ge", w!"geq", w!"le", w!"leq", w!"in", w!"notin"].contains c
          | .msym c => c == 60 || c == 62
          | _ => false
        if !isRel then none
        let close2 :: after := more.drop body2.length | none
        let w (x : Codes) : PTok := ⟨.word x, o2.pos, false⟩
        let condToks := [o2] ++ body2 ++ [close2]
        let tail := match after with
          | n :: rest => if lw n == some w!"with" then condToks ++ [w w!"and"] ++ rest else condToks ++ after
          | [] => condToks
        some ([a, c1, andW, o2, v, close2, w w!"with"] ++ tail)
      match spaceOf, sharedMod, lastCond with
      | some x, _, _ => t :: x :: standardForms f there cond (some x) (ts.drop 5)
      | none, some ts', _ => t :: standardForms f there cond (some t) ts'
      | none, none, some ts' => t :: standardForms f there cond (some t) ts'
      | none, none, none => t :: standardForms f there cond (some t) ts

/-- `$x$ satisfies $φ$`: `$φ$` (the variables are bound); `$a,b\in R$ satisfy $φ$`:
`$a,b\in R$ and $φ$`. -/
def satisfiesForm : Nat → List PTok → List PTok
  | 0, ts => ts
  | f + 1, ts =>
    match ts.findIdx? (fun t => !t.math && match t.tok with
        | .word v => v == w!"satisfies" || v == w!"satisfy"
        | _ => false) with
    | none => ts
    | some k =>
      let before := ts.take k
      let after := ts.drop (k + 1)
      let opens := match after.head? with | some t => t.tok == .mopen | none => false
      let closes := match before.getLast? with | some t => t.tok == .mclose | none => false
      if !opens || !closes then before ++ [ts[k]!] ++ satisfiesForm f after else
      -- (the formula before: from its `$`)
      let j := ((List.range (k - 1)).reverse.find? fun i => (ts[i]?.map (·.tok)) == some .mopen).getD 0
      let inner := (ts.take (k - 1)).drop (j + 1)
      let bare := inner.all fun t => match t.tok with
        | .mvar _ | .mnum _ => true
        | .csym c => c == 44 || c == 95
        | .msym c => c == 44 || c == 95
        | _ => false
      let pos := ts[k]!.pos
      -- (after a word that opens a clause; not `the function $u$ satisfies`)
      let opener := j == 0 || match ts[j - 1]? with
        | some t => !t.math && match t.tok with
          | .word w => [w!"if", w!"then", w!"that", w!"and", w!"when", w!"whenever", w!"suppose", w!"assume", w!"if"].contains (Grammar.lower w)
          | .punct _ => true
          | _ => false
        | none => true
      if !opener then before ++ [ts[k]!] ++ satisfiesForm f after else
      if bare then ts.take j ++ satisfiesForm f after
      else before ++ [⟨.word w!"and", pos, false⟩] ++ satisfiesForm f after

/-- `(a_n)_{n\ge1}`, `(a_n)_{n=1}^{\infty}`, `(a_n)_{n\in\mathbb{N}}`: a sequence written by its
term, with the range of its index, is the sequence `(a_n)` (its terms are those at the
natural numbers; the range says no more about the sequence). -/
def seqRanges : Nat → List PTok → List PTok
  | 0, ts => ts
  | _ + 1, [] => []
  | f + 1, t :: ts =>
    -- (skip a group `{…}` or a single token)
    let skipGroup (r : List PTok) : List PTok := match r with
      | ⟨.lbrace, _, _⟩ :: r' =>
        let rec go : Nat → Nat → List PTok → List PTok
          | 0, _, r => r
          | _ + 1, _, [] => []
          | g + 1, d, ⟨.lbrace, _, _⟩ :: r => go g (d + 1) r
          | g + 1, d, ⟨.rbrace, _, _⟩ :: r => if d == 0 then r else go g (d - 1) r
          | g + 1, d, _ :: r => go g d r
        go (r'.length + 1) 0 r'
      | _ :: r' => r'
      | [] => []
    match t.tok, ts with
    | .msym 40, ⟨.mvar a, pa, ma⟩ :: ⟨.msym 95, p9, m9⟩ :: i :: ⟨.msym 41, pc, mc⟩ :: ⟨.msym 95, _, _⟩ :: rest =>
      if !(match i.tok with | .mvar _ => true | _ => false) then t :: seqRanges f ts else
      let rest := skipGroup rest
      let rest := match rest with
        | ⟨.msym 94, _, _⟩ :: r => skipGroup r
        | r => r
      t :: ⟨.mvar a, pa, ma⟩ :: ⟨.msym 95, p9, m9⟩ :: i :: ⟨.msym 41, pc, mc⟩ :: seqRanges f rest
    | _, _ => t :: seqRanges f ts

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

/-- `(a_n)`, `(a_n)_{n\ge1}`, `(a_n)_{n\in\mathbb{N}}`, `(a_n)_{n=1}^{\infty}`: a sequence
written by its term (the name `a`). -/
def seqVarName (ts : List MTok) : Option Codes := do
  let .sym 40 :: rest := ts | none
  let inner := rest.takeWhile (· != .sym 41)
  let after := rest.drop (inner.length + 1)
  match after.head? with
  | none | some (.sym 95) | some (.sym 94) => pure ()
  | _ => none
  match Math.parseFormula inner with
  | some (.sub (.id a) (.id _)) => some a
  | _ => none

/-- The name of a variable chunk: a letter, a command (`\gamma`), `\hat x`, or a letter
with a subscript that is a letter or a number (`d_0`, `n_k`: the name a bound on it
binds, as in `$d_0\ge1$`). -/
def varName : List MTok → Option Codes
  | [.id v] => some v
  | [.cmd c] => some ([92] ++ c)
  | ts => match Grammar.hatName ts with
    | some (v, []) => some v
    | _ => (seqVarName ts) <|> Grammar.subNameOf ts

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
    (cs : List Chunk) (cands : List (α × List Chunk)) (defn : Bool := false) (rethrow : Bool := false) :
    M (Option (α × List Chunk)) := do
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
        -- (none fits: the reason the first one does not, `unknown notation`)
        if rethrow then
          if let some c := distinct.head? then
            fits c.1
            set st
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
    | .w w :: r => if w == w!"fixed" || w == w!"arbitrary" || w == w!"given" then some r else
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
    -- `A\subseteq X` as a binder: the subsets of `X`, a set of numbers or of the elements of a
    -- structure (`Let $X$ be a topological space and let $A\subseteq X$.`)
    | .app (.id sub) [x] =>
      if sub != w!"@subsets" && sub != w!"@psubsets" then do
        let (p, t) ← Elab.term 100000 sc none d
        match t with
        | .fn a .prop => pure (a, some p)
        | _ => fail E.unsupported
      else do
        let (xt, xty) ← Elab.term 100000 sc none x
        let .fn a .prop := xty | fail E.type
        let inside : Tm := .all a (.imp (.app (.loc 1) (.loc 0)) (.app (shift 2 0 xt) (.loc 0)))
        -- (`A\subsetneq X`: a subset other than `X`)
        let body : Tm := if sub == w!"@psubsets" then .and inside (.not (.eq (.loc 0) (shift 1 0 xt))) else inside
        pure (.fn a .prop, some (.lam (.fn a .prop) .tt body))
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
    | .sup (.id r) e =>
      -- `u\in\mathbb{R}^n` with the field `vectors`: the vectors of dimension `n`
      let V := (← get).vocab
      let rn := V.notions.find? fun n =>
        (n.name.filterMap fun p => match p with | .w w => some w | _ => none) == [w!"set", w!"of", w!"vectors", w!"in"]
      match (if r == w!"\\mathbb{R}" then rn else none) with
      | some n =>
        let .fn .real (.fn vt .prop) := n.ty | fail E.unsupported
        let (et, ety) ← Elab.term 100000 sc none e
        if ety != .real then fail E.type
        pure (vt, some (.app n.value et))
      | none => do
        let (p, t) ← Elab.term 100000 sc none d
        match t with
        | .fn a .prop => pure (a, some p)
        | _ => fail E.unsupported
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
def seqPred (k : Nat) (l h : Tm) (p : Option Tm) (et : Ty := .real) : Tm :=
  let i := Tm.loc 0
  let range := Tm.and (.app (.prim .isInt) i) (.and (.le (shift k 0 l) i) (.le i (shift k 0 h)))
  let elem := match p with
    | some p => Tm.app (shift 2 0 p) (.app (.loc 1) i)
    | none => .tt
  .lam (.fn .real et) .tt (.all .real (.imp range elem))

/-- The type and predicate of the domain of the variables `vs` of a binder: `domainOf`,
or, for a sequence (`x_1,\ldots,x_n\in A`, `@seq lo hi A`), a real function whose terms
`x_i`, for the integers `i` from `lo` to `hi`, are in `A`. The sequences are recorded
(and the other variables forgotten as sequences). -/
def binderDomain (vs : List Codes) (d : MT) (sc : Scope := []) : M (Ty × Option Tm) := do
  match d with
  | .app (.id s) [lo, hi, d'] =>
    if s != w!"@seq" then domainOf false d sc else do
    let (ty, p) ← domainOf true d' sc
    -- (numbers, or elements of a structure: `v_1,\ldots,v_n\in V`)
    if ty != .real && !Elab.isBase ty then fail E.unsupported
    let l ← closedBound lo sc
    let h ← closedBound hi sc
    modify fun st => { st with seqs := vs.map (·, lo, hi) ++ st.seqs.filter fun e => !vs.contains e.1 }
    pure (.fn .real ty, some (seqPred 2 l h p ty))
  | _ => do
    modify fun st => { st with seqs := st.seqs.filter fun e => !vs.contains e.1 }
    -- (`f\in C([0,1])`, `f\in C^1(D)`: a function on `D`, as `f\colon D\to\mathbb{R}`; its
    -- adjectives are said on `D`)
    let space? : Option MT := match d with
      | .app (.id c) [dm] => if c == [67] then some dm else none
      | .app (.sup (.id c) (.num 1)) [dm] => if c == [67] then some dm else none
      | .mul (.sup (.id c) (.num 1)) dm => if c == [67] then some dm else none
      | _ => none
    let r ← domainOf false d sc
    if let some dm := space? then
      -- (a set of real numbers as `D`; where `[0,1]` is a type of the vocabulary, the
      -- functions are of that type, and their adjectives are said on it anyway)
      let (dty, dp) ← domainOf false dm sc
      if dty == .real && dp.isNone then fail E.unsupported
      if dty == .real && r.1 == Ty.rfun then
        let st ← get
        let entries : List (Nat × Codes × MT × MT) := vs.map fun v => (st.curEnv, v, dm, MT.id w!"\\mathbb{R}")
        set { st with sigDoms := entries ++ st.sigDoms.filter (fun (e : Nat × Codes × MT × MT) => !vs.contains e.2.1) }
    pure r

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
def fieldSig (d c : MT) (sc : Scope := []) : M (Option (FieldInfo × Ty)) := do
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
  let sds ← domainsOf true sp sc
  let tds ← match tm with
    | some b => domainsOf true b sc
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

/-- `v` is an index of a subscript in the tokens (`a_n`, `a_{n+1}`). -/
def indexedBy (v : Codes) : List MTok → Bool
  | .sym 95 :: .id w :: rest => w == v || indexedBy v rest
  | .sym 95 :: .lb :: rest =>
    let (inner, _) := (rest.span (· != .rb))
    inner.contains (.id v) || indexedBy v rest
  | _ :: rest => indexedBy v rest
  | [] => false

/-- `$φ$ [and $ψ$]`: the conditions after `with` in a noun phrase. -/
def condsOf : Nat → List Chunk → List MT → List MT × List Chunk
  | 0, cs, acc => (acc.reverse, cs)
  | f + 1, cs, acc =>
    -- (`with $φ$ and $ψ$ for all $z\in A$`: both for every value)
    let both : Option (MT × List Chunk) := match cs with
      | .m t1 :: .w a :: .m t2 :: .w fo :: .w q :: .m b :: rest =>
        if a == w!"and" && fo == w!"for" && (q == w!"all" || q == w!"every" || q == w!"each") then
          match Math.parseFormula t1, Math.parseFormula t2, Grammar.binderMath b with
          | some m1, some m2, some (vs, d) => some (.quant true vs d (.conj [m1, m2]), rest)
          | _, _, _ => none
        else none
      | _ => none
    if let some (m, rest) := both then
      match rest with
      | .w w :: r' => if w == w!"and" then condsOf f r' (m :: acc) else ((m :: acc).reverse, rest)
      | _ => ((m :: acc).reverse, rest)
    else
    -- (`with $a_n\to0$ as $n\to\infty$`: the limit along the index of the term)
    let asIdx : Option (MT × List Chunk) := match cs with
      | .m ts :: .w a :: .m [.id v, .cmd t, .cmd i] :: rest =>
        if a == w!"as" && t == w!"to" && i == w!"infty" && indexedBy v ts then
          (Grammar.seqLimitMT ts).map (·, rest)
        else none
      | _ => none
    match asIdx <|> Grammar.formula cs with
    | some (m0, r0) =>
      -- `with $a_n\ge0$ for all $n$`: the condition for every value of the variables
      -- (`for every real number $x$`, `for all integers $n$`: the noun's numbers)
      let nounDom (r : List Chunk) : Option (MT × List Chunk) :=
        let dom (ws : List Codes) (d : Codes) : Option (MT × List Chunk) :=
          (Grammar.kw ws r).map fun r' => (MT.id d, r')
        dom [w!"real", w!"numbers"] w!"\\mathbb{R}" <|> dom [w!"real", w!"number"] w!"\\mathbb{R}" <|>
        dom [w!"integers"] w!"\\mathbb{Z}" <|> dom [w!"integer"] w!"\\mathbb{Z}" <|>
        dom [w!"natural", w!"numbers"] w!"\\mathbb{N}" <|> dom [w!"natural", w!"number"] w!"\\mathbb{N}"
      let r0 : List Chunk := match (Grammar.kw [w!"for", w!"all"] r0 <|> Grammar.kw [w!"for", w!"every"] r0 <|>
          Grammar.kw [w!"for", w!"each"] r0) with
        | some r1 =>
          let domTs (d : MT) : List MTok := match d with | .id n => [.id n] | _ => []
          match nounDom r1 with
          -- (two of them: `for all real numbers $x$ and $y$`, `$x$, $y$`, `$x,y$`)
          | some (d, .m [.id a] :: .w n :: .m [.id b] :: r2) =>
            if n == w!"and" then [.w w!"for", .w w!"all", .m ([.id a, .sym 44, .id b, .cmd w!"in"] ++ domTs d)] ++ r2 else r0
          | some (d, .m [.id a] :: .p 44 :: .m [.id b] :: r2) =>
            [.w w!"for", .w w!"all", .m ([.id a, .sym 44, .id b, .cmd w!"in"] ++ domTs d)] ++ r2
          | some (d, .m [.id a, .sym 44, .id b] :: r2) =>
            [.w w!"for", .w w!"all", .m ([.id a, .sym 44, .id b, .cmd w!"in"] ++ domTs d)] ++ r2
          | some (d, .m [.id v] :: r2) => [.w w!"for", .w w!"all", .m ([.id v, .cmd w!"in"] ++ domTs d)] ++ r2
          | _ => r0
        | none => r0
      let (m, r) : MT × List Chunk := match (Grammar.kw [w!"for", w!"all"] r0 <|> Grammar.kw [w!"for", w!"every"] r0 <|>
          Grammar.kw [w!"for", w!"each"] r0) with
        | some (.m ts :: r1) =>
          match Grammar.binderMath ts with
          | some (vs, d) => (.quant true vs d m0, r1)
          | none => match varName ts with
            -- (an index of a sequence, `a_n` for all `n`, is a natural number)
            | some v =>
              let idx := match cs.head? with
                | some (.m ms) => indexedBy v ms
                | _ => false
              (.quant true [v] (.id (if idx then w!"\\mathbb{N}" else w!"\\mathbb{R}")) m0, r1)
            | none => (m0, r0)
        | _ => (m0, r0)
      -- `$φ$, $ψ$, or $χ$`: one of them
      match Grammar.orTail 6 r [] with
      | some (tl, r') =>
        let ms := tl.filterMap fun c => match c with
          | .m ts => Grammar.formula [.m ts] |>.map (·.1)
          | _ => none
        ((ms.foldl (fun a b => MT.lor a b) m :: acc).reverse, r')
      | none =>
      match r with
      -- (not before another binder with `be` left out, `… and $(b_n)$ a sequence with …`)
      | .w w :: .m _ :: .w a :: _ =>
        if w == w!"and" && (a == w!"a" || a == w!"an") then ((m :: acc).reverse, r)
        else if w == w!"and" then condsOf f (r.drop 1) (m :: acc) else ((m :: acc).reverse, r)
      | .w w :: r' => if w == w!"and" then condsOf f r' (m :: acc) else ((m :: acc).reverse, r)
      | _ => ((m :: acc).reverse, r)
    | none => (acc.reverse, cs)

/-- The vocabulary's type of maps between sets of elements of `dt` and of `ct`, with its
signature predicate (`$\\varphi\\colon G\\to H$` for structures). -/
def mapType (dt ct : Ty) : M (Option (Ty × Tm)) := do
  let st ← get
  let ms := st.vocab.methods.filter (·.op == .sig)
  pure <| ms.findSome? fun m =>
    match (st.vocab.consts[m.const]? : Option Ty) with
    | some (Ty.fn (Ty.fn d Ty.prop) (Ty.fn (Ty.fn c Ty.prop) (Ty.fn t Ty.prop))) =>
      if d == dt && c == ct && t == m.ty then some (m.ty, Tm.const m.const) else none
    | _ => none

/-- The predicate of a map of such a type bound by a signature with the domain and codomain
predicates `dp`, `cp` (of the scope outside the binder): stated where the variable is bound. -/
def mapSigPred (mt dt ct : Ty) (c : Tm) (dp cp : Option Tm) : Tm :=
  let d := (dp.map (shift 2 0)).getD (.lam dt .tt .tt)
  let k := (cp.map (shift 2 0)).getD (.lam ct .tt .tt)
  Tm.lam mt .tt (.app (.app (.app c d) k) (.loc 0))

/-- A map bound by a signature on a set of elements of a vocabulary's type that has numbers
in it (`$\\varphi\\colon G\\to H$`): its value at a number is its value at that element of
the domain (`\\varphi(1)` at the identity of `G`). Stated where the map is bound. -/
def numeralsIn (dt ct : Ty) (dp : Option Tm) : M (List Tm) := do
  let some p := dp | return []
  let st ← get
  let some m := st.vocab.methods.find? (fun m => m.ty == dt && m.op == .ofRealIn) | return []
  let some o := st.vocab.methods.find? (fun m => m.ty == dt && m.op == .ofReal) | return []
  let cty : Ty := .fn dt ct
  -- `fun f => ∀ r, f (ofReal r) = f (ofRealIn D r)`
  let body := Tm.eq (.app (.loc 1) (.app (.const o.const) (.loc 0)))
    (.app (.loc 1) (.app (.app (.const m.const) (shift 3 0 p)) (.loc 0)))
  pure [Tm.lam cty .tt (.all .real body)]

/-- The complement of a noun phrase, `$G$` of `subgroup $H$ of $G$`: the formula after the
first `of` that follows the noun's words. -/
def complementOf (np : List Chunk) : Option (List MTok) :=
  let rec go : List Chunk → Option (List MTok)
    | .w w :: rest =>
      match rest with
      | .m ts :: _ => if w == w!"of" then some ts else go rest
      | _ => go rest
    | .m _ :: rest => go rest
    | .p 45 :: rest => go rest
    | _ => none
  match np with
  | .w _ :: _ => go np
  | _ => none

/-- A standard property of a real function `t` on the domain `dom` (a predicate of real
numbers): `increasing` (Mathlib `MonotoneOn`), `strictly increasing`, `decreasing`,
`monotone`, `bounded`, `positive`, `nonnegative`, `negative`, `continuous`, `convex`,
`concave`, `differentiable`, `Lipschitz`, `injective`, …; `none` for other words. -/
def fnAdjectiveOn (t : Tm) (a : List Codes) (dom : Tm) : Option Tm :=
  let on (p : Prim) : Tm := .app (.app (.prim p) t) dom
  let terms (p : Tm → Tm) : Tm := .all .real (.imp (.app (shift 1 0 dom) (.loc 0)) (p (.app (shift 1 0 t) (.loc 0))))
  let a := a.map Grammar.lower
  -- (`non-decreasing`)
  let a := match a with
    | [n, w] => if n == w!"non" then [n ++ w] else a
    | _ => a
  if a == [w!"increasing"] || a == [w!"nondecreasing"] then some (on (.fnProp .monotone))
  else if a == [w!"decreasing"] || a == [w!"nonincreasing"] then some (on (.fnProp .antitone))
  else if a == [w!"strictly", w!"increasing"] then some (on .strictMonoOn)
  else if a == [w!"strictly", w!"decreasing"] then some (on (.fnProp .strictAnti))
  else if a == [w!"monotone"] then some (.or (on (.fnProp .monotone)) (on (.fnProp .antitone)))
  else if a == [w!"strictly", w!"monotone"] then some (.or (on .strictMonoOn) (on (.fnProp .strictAnti)))
  else if a == [w!"bounded"] then some (on (.fnProp .bounded))
  else if a == [w!"positive"] then some (on (.fnProp .pos))
  else if a == [w!"nonnegative"] then some (on (.fnProp .nonneg))
  else if a == [w!"negative"] then some (terms fun x => .lt x (.num 0))
  else if a == [w!"nonpositive"] then some (terms fun x => .le x (.num 0))
  else if a == [w!"continuous"] then some (on .continuousOn)
  else if a == [w!"concave"] then some (on .concaveOn)
  else if a == [w!"convex"] then some (on (.fnProp .convex))
  else if a == [w!"strictly", w!"convex"] then some (on (.fnProp .strictConvex))
  else if a == [w!"strictly", w!"concave"] then some (on (.fnProp .strictConcave))
  else if a == [w!"differentiable"] then some (on (.fnProp .differentiable))
  else if a == [w!"continuously", w!"differentiable"] then some (on (.fnProp .contDiff))
  else if a == [w!"injective"] || a == [w!"one-to-one"] then some (on (.fnProp .injective))
  else if a == [w!"lipschitz"] || a == [w!"lipschitz", w!"continuous"] then some (on (.fnProp .lipschitz))
  else if a == [w!"lower", w!"semicontinuous"] then some (on (.fnProp .lowerSemicont))
  else if a == [w!"upper", w!"semicontinuous"] then some (on (.fnProp .upperSemicont))
  -- (`uniformly continuous`: for every `ε>0` a `δ>0` with `|f(x)-f(y)|<ε` at points of the
  -- domain closer than `δ`; scope inside: `y`, `x`, `δ`, `ε`)
  else if a == [w!"uniformly", w!"continuous"] then
    let d (x : Tm) : Tm := .app (shift 4 0 dom) x
    let f (x : Tm) : Tm := .app (shift 4 0 t) x
    some (.all .real (.imp (.lt (.num 0) (.loc 0)) (.ex .real (.and (.lt (.num 0) (.loc 0))
      (.all .real (.all .real (.imp (.and (d (.loc 1)) (.and (d (.loc 0)) (.lt (.abs (.sub (.loc 1) (.loc 0))) (.loc 2))))
        (.lt (.abs (.sub (f (.loc 1)) (f (.loc 0)))) (.loc 3)))))))))
  -- (`constant`: the same value at any two points of the domain)
  else if a == [w!"constant"] then
    some (.all .real (.all .real (.imp (.and (.app (shift 2 0 dom) (.loc 1)) (.app (shift 2 0 dom) (.loc 0)))
      (.eq (.app (shift 2 0 t) (.loc 1)) (.app (shift 2 0 t) (.loc 0))))))
  else none

/-- `surjective` (`onto`) and `bijective` of a real function with a signature
`f\colon X\to Y` (domain `dom`, codomain `cod`, predicates of real numbers): every point of `Y`
is the value at a point of `X`; bijective, and injective on `X`. -/
def fnOnto (t : Tm) (a : List Codes) (dom cod : Tm) : Option Tm :=
  let a := a.map Grammar.lower
  let onto := Tm.all .real (.imp (.app (shift 1 0 cod) (.loc 0))
    (.ex .real (.and (.app (shift 2 0 dom) (.loc 0)) (.eq (.app (shift 2 0 t) (.loc 0)) (.loc 1)))))
  if a == [w!"surjective"] || a == [w!"onto"] then some onto
  else if a == [w!"bijective"] then some (.and (.app (.app (.prim (.fnProp .injective)) t) dom) onto)
  else none

/-- `fnAdjectiveOn`, and `nonX` (`non-constant`, `nonconstant`): not `X`, for the words
that it reads other than `positive`, `negative`, `increasing` and `decreasing` (whose `non`
words it reads itself). -/
def fnAdjectiveOnNeg (t : Tm) (a : List Codes) (dom : Tm) : Option Tm :=
  match fnAdjectiveOn t a dom with
  | some p => some p
  | none =>
    match a.map Grammar.lower with
    | [w] =>
      let x := w.drop 3
      if w.take 3 != w!"non" || [w!"positive", w!"negative", w!"increasing", w!"decreasing"].contains x then none
      else (fnAdjectiveOn t [x] dom).map Tm.not
    | _ => none

/-- A property of a sequence `t` of real numbers (a real function whose terms are its values
at the natural numbers), said of its terms: `increasing` (Mathlib `Monotone`), `strictly
increasing` (`StrictMono`), `decreasing`, `monotone`, `bounded`, `positive`, … -/
def seqAdjective (t : Tm) (a : List Codes) : Option Tm :=
  let a' := a.map Grammar.lower
  -- (of its terms only: not the properties of a function of the line)
  if [[w!"continuous"], [w!"convex"], [w!"concave"], [w!"differentiable"], [w!"continuously", w!"differentiable"],
      [w!"strictly", w!"convex"], [w!"strictly", w!"concave"], [w!"lower", w!"semicontinuous"],
      [w!"upper", w!"semicontinuous"]].contains a' then none
  else fnAdjectiveOn t a (.lam .real .tt (.app (.prim .isNat) (.loc 0)))

/-- `of the form $E$` at the start of the chunks: the formula, and the chunks after it. -/
def ofFormOf (cs : List Chunk) : Option (MT × List Chunk) := match cs with
  | .w o :: .w t :: .w fm :: .m ts :: rest =>
    if o != w!"of" || t != w!"the" || fm != w!"form" then none else
    (Math.parseFormula ts).map (·, rest)
  | _ => none

/-- `of the form $E$` (`primes of the form $4k+3$`, `of the form $2^n-1$`): the number `obj`
(bound first in `sc`) is the value of `E` for some values of its letters that nothing else
binds, integers, or natural numbers where they stand in an exponent. -/
def ofFormBody (sc : Scope) (obj : Codes) (e : MT) : M Tm := do
  let rec lets : Nat → Bool → MT → List (Codes × Bool)
    | 0, _, _ => []
    | k + 1, ex, m => match m with
      | .id n => [(n, ex)]
      | .add a b | .minus a b | .mul a b | .div a b | .frac a b => lets k ex a ++ lets k ex b
      | .sup b x => lets k ex b ++ lets k true x
      | .neg a | .abs a => lets k ex a
      | .app _ as => as.flatMap (lets k ex)
      | _ => []
  let letter (n : Codes) : Bool := match n with
    | [ch] => (97 ≤ ch && ch ≤ 122) || (65 ≤ ch && ch ≤ 90)
    | _ => false
  let cand := (lets 32 false e).filter fun (n, _) => letter n && (Elab.lookupLocal sc n).isNone
  let free ← cand.filterM fun (n, _) => do pure (← Elab.lookupGlob n).isNone
  let names := (free.map (·.1)).eraseDups
  if names.isEmpty then fail E.unsupported
  let natural (n : Codes) : Bool := free.any fun (m, ex) => m == n && ex
  let body := names.foldr (fun n acc =>
    MT.quant false [n] (.id (if natural n then w!"\\mathbb{N}" else w!"\\mathbb{Z}")) acc)
    (MT.chain (.id obj) [(.eq, e)])
  let (p, pty) ← Elab.term 100000 sc none body
  if pty != .prop then fail E.type
  pure p

/-- Read a noun phrase (without its determiner). -/
def nounPhrase1Core (np : List Chunk) (outer : Scope := []) : M BindInfo := do
  -- `fixed` before a noun phrase marks a parameter: the binder is the same without it
  -- (`for every fixed real $c>0$`)
  -- (not the word of a noun, `fixed point`)
  let V0 := (← get).vocab
  let np := match np with
    | .w w :: c :: rest =>
      let fixedNoun := match c with
        | .w w' => V0.nouns.any fun n => (n.sing.take 2 == [.w w!"fixed", .w w'] || n.plural.take 2 == [.w w!"fixed", .w w'])
        | _ => false
      if w == w!"fixed" && !fixedNoun then c :: rest
      -- (`an arbitrary element of $G$`, `a given group`: the same noun phrase)
      else if (w == w!"arbitrary" || w == w!"given") && (match c with | .w _ => true | _ => false) then c :: rest
      else np
    | _ => np
  -- `a continuous function $f$ on $[0,1]$`: the function `f\colon[0,1]\to\mathbb{R}`
  -- (not where the vocabulary has a noun `… function on …` with the word before,
  -- `distribution function on $[0,1]^2$`)
  let np :=
    let fixedBefore (prev : Option Codes) : Bool := V0.nouns.any fun n =>
      (List.range n.sing.length).any fun i =>
        n.sing[i]? == some (.w w!"function") &&
        (n.sing[i + 1]? == some (.w w!"on") || (n.sing[i + 1]? == some .v && n.sing[i + 2]? == some (.w w!"on"))) &&
        (i == 0 || match prev with
          | some w => n.sing[i - 1]? == some (.w w)
          | none => false)
    let sig (v d : List MTok) : List MTok := v ++ [.sym 58] ++ d ++ [.cmd w!"to", .id w!"\\mathbb{R}"]
    let single (v : List MTok) : Bool := match v with | [.id _] => true | _ => false
    let rec go : Nat → Option Codes → List Chunk → List Chunk
      | 0, _, cs => cs
      | k + 1, prev, cs => match cs with
        | .w fw :: .m v :: .w o :: .m d :: rest =>
          if (fw == w!"function" || fw == w!"functions") && (o == w!"on" || o == w!"over") && single v && !fixedBefore prev then .w fw :: .m (sig v d) :: rest
          else .w fw :: go k (some fw) (.m v :: .w o :: .m d :: rest)
        | .w fw :: .w o :: .m d :: .m v :: rest =>
          if fw == w!"function" && (o == w!"on" || o == w!"over") && single v && !fixedBefore prev then .w fw :: .m (sig v d) :: rest
          else .w fw :: go k (some fw) (.w o :: .m d :: .m v :: rest)
        | .w fw :: .m v :: .w df :: .w o :: .m d :: rest =>
          if fw == w!"function" && df == w!"defined" && o == w!"on" && single v then .w fw :: .m (sig v d) :: rest
          else .w fw :: go k (some fw) (.m v :: .w df :: .w o :: .m d :: rest)
        -- (`every continuous function on $[a,b]$`: a function without a letter, on a set)
        | .w fw :: .w o :: .m d :: rest =>
          if (fw == w!"function" || fw == w!"functions") && (o == w!"on" || o == w!"over") && !fixedBefore prev
              && (match rest with | .m _ :: _ => false | _ => true) then
            .w fw :: .m (sig [.id w!"\\everyobj"] d) :: rest
          else .w fw :: go k (some fw) (.w o :: .m d :: rest)
        | .w w :: rest => .w w :: go k (some w) rest
        | c :: rest => c :: go k none rest
        | [] => []
    go (np.length + 1) none np
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
      let cs0 := rest.dropLast
      let V := (← get).vocab
      let elabArgs (args : List (List MTok)) : M (List (Tm × Ty)) := args.mapM fun a => do
        let some m := Math.parseFormula a | fail E.unsupported
        Elab.term 100000 outer none m
      let fits (na : Notion × List (List MTok)) : M Unit := do
        let _ ← applyAll na.1.value na.1.ty na.1.doms (← elabArgs na.2)
      let candsOf (cs : List Chunk) := V.notions.filterMap fun n => (Notation.matchSlots n.name cs []).map fun a => ((n, a), ([] : List Chunk))
      -- (`the closure of $A$`, of a subset `A` of `X`: in the space of the complement of `A`,
      -- where no notion with these words fits `A` itself)
      let stc ← get
      let anyFits (cs : List Chunk) : M Bool := do
        let ok ← (candsOf cs).anyM fun c => tryCatch (do fits c.1; pure true) fun _ => pure false
        set stc
        pure ok
      let cs2 : Option (List Chunk) := match cs0.getLast? with
        | some (.m [.id k]) =>
          (stc.complements.find? (fun ((e, n, _) : Nat × Codes × List MTok) => n == k && (e == stc.curEnv || stc.curProved == some e))).map
            fun (_, _, cts) => cs0 ++ [.w w!"@in", .m cts]
        | _ => none
      let cs ← match cs2 with
        | some c2 => do
          if !(candsOf c2).isEmpty && !(← anyFits cs0) then pure c2 else pure cs0
        | none => pure cs0
      let cands := candsOf cs
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
            -- (a set of pairs, `let $E$ be the edge set of $G$`: pair by pair)
            else if b2 == .prop then
              some (Tm.all a (Tm.all a2 (Tm.iff (.app (.app (.loc 2) (.loc 1)) (.loc 0))
                (Notation.headBeta 8 (.app (.app (shift (k + 2) 0 val) (.loc 1)) (.loc 0))))))
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
  modify fun st => { st with sigDom := st.sigDomPreset, sigCod := st.sigCodPreset, pendingSeq := false }
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
        -- (a noun that ends in a fixed formula, `vector space over $\mathbb{R}$ $V$`: as it is)
        let fixedNoun := V.nouns.any fun n => n.sing.any (fun i => match i with | .m _ => true | _ => false) &&
          (List.range ws.length).any fun k => match matchPhrase n.sing (ws.drop k) with
            | some (none, []) => true
            | _ => false
        if fixedNoun then np else
        -- (a modifier with formulas, `a vector in $\mathbb{R}^n$ $x$`: the shortest ending of
        -- the words that is one, after words only)
        if !words ws then
          let hitS := (List.range ws.length).findSome? fun k0 =>
            let k := k0 + 1
            if k ≥ ws.length then none else
            let head := ws.take (ws.length - k)
            let tail := ws.drop (ws.length - k)
            if !words head then none else
            -- (not a noun after a formula, `$p$-group`: the formula is a modifier before it)
            let nounEnd := match tail with
              | [.m _, .p 45, .w w] => V.nouns.any fun n => n.sing == [.w w] || n.plural == [.w w]
              | _ => false
            if !nounEnd && V.mods.any (fun m => !m.prenominal && Notation.hasSlots m.phrase &&
                (Notation.matchSlots m.phrase tail []).isSome) then some k else
            -- (a noun's complement, `subgroup of $G$ $H$`)
            match tail with
            | [.w w, .m _] =>
              if V.nouns.any (fun n => match n.arg with
                | some (ws, _, _) => ws.contains (Grammar.lower w)
                | none => false) then some k else none
            | _ => none
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
  -- a noun's complement (`subgroup of $G$`): the relation to the object it names, as a
  -- predicate of the variable, stated where the variable is bound (as a modifier's)
  let nounArg (n : Noun) (rest : List Chunk) (var : Option (List MTok) := none) : M (List Tm × List Chunk) := do
    -- (a noun that needs a complement, without one: the set of the variable's domain, `Let
    -- $W\subset K$ be a subfield.`, `Let $I\subseteq R$ be an ideal.`)
    let implicit : M (List Tm × List Chunk) := do
      let some (_, aty, rel) := n.arg | fail E.type
      let some ts := var | fail E.type
      let some ([_], d) := Grammar.binderMath ts | fail E.type
      let x := match d with
        | .app (.id s) [x] => if s == w!"@subsets" || s == w!"@psubsets" then x else d
        -- (`a subgroup $H\le G$`: of `G`)
        | .ival (.neg (.id inf)) b true false => if inf == w!"\\infty" && n.ty != .real then b else d
        | _ => d
      let sc : Scope := [([], n.ty)] ++ (if outer.isEmpty then [] else [([], n.ty)]) ++ outer
      let (a, aty') ← Elab.term 100000 sc none x
      if aty' != aty then fail E.type
      let r := Notation.betaApply rel [a, .loc 0]
      -- (the membership that the domain states already, `an element $g\in G$`: nothing more)
      if r == Tm.app a (.loc 0) then return ([], rest)
      pure ([Tm.lam n.ty .tt r], rest)
    -- (a complement that the noun may have: the domain's set, if the variable has one)
    -- (a noun with a complement, `normal subgroup of $G$`, needs it: alone, it would say
    -- less than the noun means)
    let optional : M (List Tm × List Chunk) := do
      if n.needsArg then return ← implicit
      let st0 ← get
      tryCatch implicit fun e => do
        set st0
        -- (a complement that is the membership the variable's domain states, `an element
        -- $g\in G$`: nothing more to say, where the domain is read in another scope)
        let some (ws, _, rel) := n.arg | throw e
        let domainSays : Bool := match var with
          | some ts => (Grammar.binderMath ts).isSome && Notation.betaApply rel [.glob 1000000, .loc 0] == Tm.app (.glob 1000000) (.loc 0)
          | none => false
        if domainSays then return ([], rest)
        let words := n.sing.filterMap fun i => match i with | .w w => some w | _ => none
        let art : Codes := match words.head? >>= List.head? with
          | some ch => if [97, 101, 105, 111, 117].contains ch then w!"an " else w!"a "
          | none => w!"a "
        let phrase := (words.intersperse [32]).flatten
        fail E.finding ([34] ++ phrase ++ w!"\" is read with its complement: say which object it is " ++
          (ws.headD w!"of") ++ w!" (" ++ art ++ phrase ++ [32] ++ (ws.headD w!"of") ++ w!" $X$)")
    match n.arg, rest with
    | some (ws, aty, rel), .w w :: .m ts :: rest' =>
      if !ws.contains (Grammar.lower w) then return ← optional
      let some mt := Math.parseFormula ts | fail E.unsupported
      let sc : Scope := [([], n.ty)] ++ (if outer.isEmpty then [] else [([], n.ty)]) ++ outer
      let (a, aty') ← Elab.term 100000 sc none mt
      let a ← if aty' == aty then pure a else if aty == .real then Elab.asReal (a, aty') else fail E.type
      -- (the domain of the complement's signature, where the relation takes it)
      if n.argOnDomain then
        let stD ← get
        let dom? : Option MT := match mt with
          | .id f => (stD.sigDoms.find? fun (e, g, _, _) => g == f && (e == stD.curEnv || stD.curProved == some e)).map (·.2.2.1)
          | _ => none
        let domTm ← match dom? with
          | some d => do
            let (_, p) ← domainOf false d sc
            pure (p.getD (.lam .real .tt .tt))
          | none => pure (.lam .real .tt .tt)
        return ([Tm.lam n.ty .tt (Notation.betaApply rel [domTm, a, .loc 0])], rest')
      pure ([Tm.lam n.ty .tt (Notation.betaApply rel [a, .loc 0])], rest')
    | some _, _ => optional
    | none, _ => pure ([], rest)
  -- a noun's predicate; a noun of maps meant on a domain takes the domain of the signature
  let nounPred (n : Noun) : M Tm := do
    if !n.onDomain then return n.pred
    let some d := (← get).sigDom
      | fail E.finding (w!"a " ++ ((n.sing.filterMap fun i => match i with | .w w => some w | _ => none).intersperse [32]).flatten ++
          w!" is bound with its domain: $\\varphi\\colon G\\to H$")
    if n.onCodomain then
      let some c := (← get).sigCod | fail E.finding (w!"a map whose noun is about its codomain is bound with it: $\\varphi\\colon G\\to H$")
      return Tm.lam n.ty .tt (Notation.betaApply n.pred [shift 1 0 d, shift 1 0 c, .loc 0])
    pure (Tm.lam n.ty .tt (Notation.betaApply n.pred [shift 1 0 d, .loc 0]))
  -- (the chunks after the noun's variable, if one follows it)
  let afterVar (n : Noun) (v : Option (List MTok)) (r : List Chunk) : List Chunk :=
    match v, r with
    | none, .m ts :: r' =>
      let single := match ts with | [.id _] | [.cmd _] => true | _ => false
      if (Math.parseSig ts).isSome || (!(n.sing.all fun p => p != .v) && !r'.isEmpty && !single) then r else r'
    | _, _ => r
  -- the head: an article class, a vocabulary noun, or a variable with a signature
  -- (the article's own classes take precedence over the vocabulary's nouns)
  -- (`implicit`: adjectives of numbers came before, so a variable alone is a real number)
  let headOf (r00 : List Chunk) (implicit : Bool) : M ((Ty × List Tm × Option (List MTok) × List Chunk) × List Nat) := do
    -- (a noun of the article, `calm group`, is no notion before a noun)
    let (nms, r0) := if (matchWords st.nouns r00).isSome then ([], r00) else preN 4 r00 []
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
        -- (nouns with the same words: their complements' types decide, `subset of $A$`)
        let fitsArg (nvr : Noun × Option (List MTok) × List Chunk) : M Unit := do
          let (n, v, r) := nvr
          -- (nouns of maps of different types: the signature's type decides, `a bijection
          -- $f\colon G\to H$`)
          let sigTs : Option (List MTok) := match v, r with
            | none, .m ts :: _ => if (Math.parseSig ts).isSome then some ts else none
            | some ts, _ => if (Math.parseSig ts).isSome then some ts else none
            | _, _ => none
          if let some ts := sigTs then
            if let some (.sig _ d c) := Math.parseSig ts then
              let ds ← domainsOf false d outer
              let (ct, _) ← domainOf false c outer
              if let [(dt, _)] := ds then
                let want := match ← mapType dt ct with
                  | some (mt, _) => mt
                  | none => Ty.fn dt ct
                if want != n.ty then fail E.type
          -- (a noun of maps meant on a domain needs one: without a signature, another noun)
          else if n.onDomain && (← get).sigDomPreset.isNone then fail E.type
          -- (a variable with a domain, `an element $g\in G$`: the domain's type is the noun's)
          if sigTs.isNone then
            let varTs : Option (List MTok) := match v, r with
              | some ts, _ => some ts
              | none, .m ts :: _ => some ts
              | _, _ => none
            if let some ts := varTs then
              if let some ([_], d) := Grammar.binderMath ts then
                let (dty, _) ← domainOf false d outer
                if dty != n.ty then fail E.type
          -- (a noun without a complement before the complement of another with the same
          -- words, `sequence in $X$`: the other)
          if n.arg.isNone then
            match afterVar n v r with
            | .w w :: .m ts :: _ =>
              -- (only where the complement is of the other's type: `vector in $\mathbb{R}^n$`
              -- is no vector of a vector space)
              let st0 ← get
              let cty : Option Ty ← tryCatch (do
                  let some mt := Math.parseFormula ts | pure none
                  let sc : Scope := [([], n.ty)] ++ (if outer.isEmpty then [] else [([], n.ty)]) ++ outer
                  pure (some (← Elab.term 100000 sc none mt).2)) fun _ => pure none
              set st0
              if cands.any (fun ((n', _), _) => match n'.arg with
                  | some (ws, aty, _) => ws.contains (Grammar.lower w) && cty == some aty
                  | none => false) then fail E.type
            | _ => pure ()
          let varOf : Option (List MTok) := match v, r with
            | some ts, _ => some ts
            | none, .m ts :: _ => some ts
            | _, _ => none
          let _ ← nounArg n (afterVar n v r) varOf
        match ← theMeaningBy (fun (nvr : Noun × Option (List MTok) × List Chunk) => (nvr.1.ty, nvr.1.pred, nvr.2.1))
            (·.1.field) fitsArg r0 (cands.map fun ((n, v), r) => ((n, v, r), r)) (rethrow := true) with
        | some ((n, v, _), r) =>
          -- `a homomorphism $\varphi\colon G\to H$`: a noun of maps, with its signature
          let sigVar : Option (List MTok × List Chunk) := match v, r with
            | none, .m ts :: r' => if (Math.parseSig ts).isSome then some (ts, r') else none
            | some ts, r' => if (Math.parseSig ts).isSome then some (ts, r') else none
            | _, _ => none
          match sigVar, (match n.ty with | .fn _ _ => true | t => Elab.isBase t) with
          | some (ts, r'), true =>
            let some (.sig (.id f) d c) := Math.parseSig ts | fail E.unsupported
            let ds ← domainsOf false d outer
            let (ct, cp) ← domainOf false c outer
            let [(dt, dp)] := ds | fail E.unsupported
            -- (a noun of a vocabulary's type of maps: a map of that type)
            if let some (mt, c) ← mapType dt ct then
              if mt != n.ty then fail E.type
              let (extra, rest) ← nounArg n r'
              return ((n.ty, [n.pred, mapSigPred mt dt ct c dp cp] ++ extra, some [.id f], rest), nms)
            if Ty.fn dt ct != n.ty then fail E.type
            let dom := (dp.map (shift 1 0)).getD (.lam dt .tt .tt)
            let cod := (cp.map (shift 1 0)).getD (.lam ct .tt .tt)
            modify fun st => { st with sigDom := some dom, sigCod := some cod, sigDoms := (st.curEnv, f, d, c) :: st.sigDoms.filter (·.2.1 != f) }
            let inDom : Tm := match dp with
              | some q => .app (shift 3 0 q) (.loc 0)
              | none => .tt
            let into : List Tm := match cp with
              | some p => [Tm.lam n.ty .tt (.all dt (.imp inDom (.app (shift 3 0 p) (.app (.loc 1) (.loc 0)))))]
              | none => []
            let (extra, rest) ← nounArg n r'
            pure (n.ty, [← nounPred n] ++ into ++ (← numeralsIn dt ct dp) ++ extra, some [.id f], rest)
          | _, _ =>
          if n.seq then modify fun st => { st with pendingSeq := true }
          let np0 ← nounPred n
          let (ty, ps, var, rest) : Ty × List Tm × Option (List MTok) × List Chunk := match v, r with
            -- `a copula $C$`: the variable follows a noun without a slot
            | none, .m ts :: r' =>
              let single := match ts with | [.id _] | [.cmd _] => true | _ => false
              if (Math.parseSig ts).isSome || (!(n.sing.all fun p => p != .v) && !r'.isEmpty && !single) then (n.ty, [np0], v, r)
              else (n.ty, [np0], some ts, r')
            | _, _ => (n.ty, [np0], v, r)
          let (extra, rest) ← nounArg n rest var
          pure (ty, ps ++ extra, var, rest)
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
              -- (a formula before a hyphen, `a finite $p$-group`: a modifier of the noun after it)
              if (match r with | .p 45 :: _ => true | _ => false) then fail E.type
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
                  let ds ← domainsOf false d outer
                  pure (!ds.isEmpty && ds.all fun (t, p) => Elab.isBase t && p.isNone)) fun _ => pure false)
              match ← (if onPoints then pure none else fieldSig d c outer) with
              | some (info, ty) =>
                modify fun st => { st with fields := (f, info) :: st.fields }
                pure (ty, [], some [.id f], r)
              | none =>
              let ds ← domainsOf false d outer
              let (ct, cp) ← domainOf false c outer
              -- `a function $A:\mathcal C\to\mathbb{R}$` on a class of the article: a
              -- function of the objects of its type, whose values are asked for at the
              -- members of the class only
              match ds, cp with
              | [(dt, some (.glob gi))], none =>
                modify fun st => { st with varDoms := (st.curEnv, f, .glob gi) :: st.varDoms }
                pure (Ty.fn dt ct, [], some [.id f], r)
              | _, _ =>
              -- `$f\colon A\to B$` with sets `A`, `B` (of numbers, or of the elements of a
              -- structure, `$\varphi\colon G\to H$`): a function of the elements of `A`'s type
              -- that maps `A` into `B` (its values elsewhere are not used)
              match ds, cp with
              | [(dt, dp)], _ =>
                -- (a vocabulary's type of maps between these elements: a map of that type)
                if let some (mt, c) ← mapType dt ct then
                  return ((mt, [mapSigPred mt dt ct c dp cp], some [.id f], r), nms)
                -- (`$a\colon\mathbb{N}\to\mathbb{R}$`: a sequence, whose terms are its values
                -- at the natural numbers, `0` elsewhere)
                let natDom := match d with
                  | .id n => n == w!"\\mathbb{N}" || n == w!"\\mathbb{N}_0"
                  | _ => false
                let seqPreds : List Tm := if natDom && dt == .real && ct == .real then
                    [.lam (.fn .real .real) .tt (.all .real (.imp (.not (.app (.prim .isNat) (.loc 0)))
                      (.eq (.app (.loc 1) (.loc 0)) (.num 0))))]
                  else []
                if !seqPreds.isEmpty then modify fun st => { st with pendingSeq := true }
                let dom := (dp.map (shift 1 0)).getD (.lam dt .tt .tt)
                let cod := (cp.map (shift 1 0)).getD (.lam ct .tt .tt)
                modify fun st => { st with sigDom := some dom, sigCod := some cod, sigDoms := (st.curEnv, f, d, c) :: st.sigDoms.filter (·.2.1 != f) }
                if cp.isNone then pure (Ty.fn dt ct, seqPreds, some [.id f], r) else
                -- (the predicates of the domains are stated where the variable is bound)
                let inDom : Tm := match dp with
                  | some p => .app (shift 3 0 p) (.loc 0)
                  | none => .tt
                let inCod : Tm := match cp with
                  | some p => .app (shift 3 0 p) (.app (.loc 1) (.loc 0))
                  | none => .tt
                pure (Ty.fn dt ct, seqPreds ++ [Tm.lam (.fn dt ct) .tt (.all dt (.imp inDom inCod))] ++ (← numeralsIn dt ct dp), some [.id f], r)
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
      else tryCatch (do
          let st1 ← get
          let (h, nms) ← headOf (restAt k) (k > 0)
          -- (a noun that is also a modifier, `idempotent`: before another noun, the modifier,
          -- `an idempotent element`)
          -- (or a noun after more modifiers, `a real symmetric $n\times n$ matrix`)
          let stops := [w!"that", w!"which", w!"of", w!"with", w!"such", w!"in", w!"on", w!"for", w!"over", w!"whose", w!"and"]
          let lead := h.2.2.2.takeWhile fun c => match c with
            | .w w => !stops.contains w
            | .m _ | .p 45 => true
            | _ => false
          let nounNext := match h.2.2.2 with
            | .w _ :: _ => lead.any fun c => match c with
              | .w w => V.nouns.any (fun n => n.sing.head? == some (.w w) || n.plural.head? == some (.w w)) ||
                -- (`map` and `function` before a signature, `a polynomial map $f\colon…$`)
                ([w!"map", w!"maps", w!"function", w!"functions"].contains w && lead.any fun c => match c with
                  | .m ts => (Math.parseSig ts).isSome
                  | _ => false)
              | _ => false
            | _ => false
          if nounNext && k < pmAll.length then
            let st2 ← get
            set st1
            -- (only where the modifiers before the other noun are of its type)
            tryCatch (do
                let (k', h', nms') ← tryK f (k + 1)
                if !((pmAll.take k').all fun (_, ms) => ms.any (·.ty == h'.1)) then fail E.type
                pure (k', h', nms')) fun _ => do set st2; pure (k, h, nms)
          else pure (k, h, nms)) fun _ => tryK f (k + 1)
  let (k, (ty, preds, var, r1), nms) ← tryK (pmAll.length + 1) 0
  let pmGroups := pmAll.take k
  -- (a modifier with variables, `on $v$ vertices`: its predicate of their values, which are
  -- formulas in the scope of the binder, as the conditions below)
  let slotPred (m : Modifier) (cs : List Chunk) : M Tm := do
    -- (a modifier of maps meant on a domain: the domain of the signature)
    if m.onDomain then
      let some d := (← get).sigDom | fail E.type
      if m.onCodomain then
        let some c := (← get).sigCod | fail E.type
        return Tm.lam ty .tt (Notation.betaApply m.pred [shift 1 0 d, shift 1 0 c, .loc 0])
      return Tm.lam ty .tt (Notation.betaApply m.pred [shift 1 0 d, .loc 0])
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
    -- (of a sequence, `an increasing sequence`: the property of its terms, at the natural
    -- numbers)
    if (← get).pendingSeq && ty == .fn .real .real then
      let words := (ms.head?.map fun m => m.phrase.filterMap fun i => match i with | .w w => some w | _ => none).getD []
      if let some body := seqAdjective (.loc 0) words then return Tm.lam ty .tt body
    -- (of a real function on the domain of its signature, `a continuous function
    -- $f\colon[a,b]\to\mathbb{R}$`: the property on that domain)
    if ty == .fn .real .real then
      let words := (ms.head?.map fun m => m.phrase.filterMap fun i => match i with | .w w => some w | _ => none).getD []
      -- (`a surjective function $f\colon X\to Y$`: onto `Y`)
      if let some c := (← get).sigCod then
        let d := ((← get).sigDom).getD (.lam .real .tt .tt)
        if let some body := fnOnto (.loc 0) words (shift 1 0 d) (shift 1 0 c) then return Tm.lam ty .tt body
      if let some d := (← get).sigDom then
        if d != .lam .real .tt .tt then
          if let some body := fnAdjectiveOnNeg (.loc 0) words (shift 1 0 d) then return Tm.lam ty .tt body
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
  -- (`a set of real numbers that is bounded above [and closed]`: the adjectives after
  -- `that is`, as modifiers after the noun)
  -- (`a polynomial that has no real roots`, `a graph which has a Hamiltonian cycle`: the
  -- modifiers `without real roots`, `with a Hamiltonian cycle`)
  let r1 : List Chunk := match r1 with
    | .w t :: .w h :: rest =>
      if (t == w!"that" || t == w!"which") && (h == w!"has" || h == w!"have" || h == w!"contains") then
        match rest with
        | .w n :: rest' => if n == w!"no" then .w w!"without" :: rest' else .w w!"with" :: rest
        | _ => .w w!"with" :: rest
      else r1
    | _ => r1
  let (rel, r1) : Bool × List Chunk := match r1 with
    | .w t :: .w i :: rest =>
      if (t == w!"that" || t == w!"which") && (i == w!"is" || i == w!"are") then (true, rest) else (false, r1)
    | _ => (false, r1)
  -- postnominal modifiers
  let rec post : Nat → Bool → List Chunk → List Tm → M (List Tm × List Chunk)
    | 0, _, cs, acc => pure (acc.reverse, cs)
    | f + 1, rel, cs, acc => do
      -- (`an integer greater than $1$ that is not prime`: a relative clause after a modifier)
      let (rel, cs) : Bool × List Chunk := if acc.isEmpty then (rel, cs) else match cs with
        | .w t :: .w i :: rest =>
          if (t == w!"that" || t == w!"which") && (i == w!"is" || i == w!"are") then (true, rest) else (rel, cs)
        | _ => (rel, cs)
      let cs := if rel && !acc.isEmpty then (match cs with
          | .w a :: rest => if a == w!"and" then rest else cs
          | .p 44 :: .w a :: rest => if a == w!"and" then rest else cs
          | .p 44 :: rest => rest
          | _ => cs) else cs
      -- (`a graph with $n$ vertices and minimum degree at least $k$`: `and` between the
      -- phrases of `with`)
      let cs := if acc.isEmpty then cs else match cs with
        | .w a :: rest =>
          let alt := Chunk.w w!"with" :: rest
          if a == w!"and" && V.mods.any (fun m => !m.prenominal && m.ty == ty &&
              (if Notation.hasSlots m.phrase then (Notation.matchPrefix m.phrase alt []).isSome
               else ((matchPhrase m.phrase alt).bind fun (v, _) => if v.isNone then some () else none).isSome)) then alt else cs
        | _ => cs
      let cands := V.mods.filterMap (fun m => if (rel || !m.prenominal) && m.ty == ty then
          if Notation.hasSlots m.phrase then (Notation.matchPrefix m.phrase cs []).map fun (_, r) => (m, r) else
          (matchPhrase m.phrase cs).bind fun (v, r) => if v.isNone then some (m, r) else none
        else none)
      -- (several fields with the words: those whose variables the formulas fit)
      let cands ← if (cands.map (·.1.field)).eraseDups.length > 1 then do
          let st ← get
          let fit ← cands.filterM fun (m, _) => do
            let ok ← tryCatch (do let _ ← slotPred m cs; pure true) fun _ => pure false
            set st
            pure ok
          pure (if fit.isEmpty then cands else fit)
        else pure cands
      -- (`a set of real numbers containing $0$`, `an open subset of $X$ containing $K$`: the
      -- object contains it, `x\in S`, or `x\subseteq S` of a set of the same elements)
      let containing : Option (MT × List Chunk) := match cs with
        | .w c :: .m ts :: rest =>
          if c != w!"containing" then none else
          match Math.parseFormula ts with
          | some (.chain _ (_ :: _)) | none => none
          | some x => some (x, rest)
        | _ => none
      if let some (x, rest) := containing then
        let v : Codes := w!"@obj"
        let sc : Scope := [(v, ty)] ++ (if outer.isEmpty then [] else [([], ty)]) ++ outer
        let (p, pty) ← Elab.term 100000 sc none (.app (.id w!"@contains") [.id v, x])
        if pty != .prop then fail E.type
        post f rel rest (Tm.lam ty .tt p :: acc) else
      -- (`a rational number contained in $I$`, `a neighbourhood of $x$ contained in $U$`: the
      -- object is an element, `y\in I`, or a subset, `N\subseteq U`, of it)
      let containedIn : Option (MT × List Chunk) := match cs with
        | .w c :: .w i :: .m ts :: rest =>
          if c != w!"contained" || i != w!"in" then none else
          match Math.parseFormula ts with
          | some (.chain _ (_ :: _)) | none => none
          | some x => some (x, rest)
        | _ => none
      if let some (x, rest) := containedIn then
        let v : Codes := w!"@obj"
        let sc : Scope := [(v, ty)] ++ (if outer.isEmpty then [] else [([], ty)]) ++ outer
        let (p, pty) ← Elab.term 100000 sc none (.app (.id w!"@contains") [x, .id v])
        if pty != .prop then fail E.type
        post f rel rest (Tm.lam ty .tt p :: acc) else
      -- (`primes of the form $4k+3$`, `of the form $2^n-1$`: a number that is the value of the
      -- formula for some values of its letters that nothing else binds, integers, natural numbers
      -- in an exponent)
      if let some (e, rest) := ofFormOf cs then
        if ty != .real then fail E.type
        let v : Codes := w!"@obj"
        let sc : Scope := [(v, ty)] ++ (if outer.isEmpty then [] else [([], ty)]) ++ outer
        post f rel rest (Tm.lam ty .tt (← ofFormBody sc v e) :: acc) else
      -- (`not coprime to $n$`: the negation of a modifier, as `that is not coprime to $n$`)
      let negated : Option (List Chunk) := if !cands.isEmpty then none else match cs with
        | .w n :: rest => if n == w!"not" then some rest else none
        | _ => none
      let neg ← match negated with
        | some cs' =>
          let ncands := V.mods.filterMap (fun m => if (rel || !m.prenominal) && m.ty == ty then
              if Notation.hasSlots m.phrase then (Notation.matchPrefix m.phrase cs' []).map fun (_, r) => (m, r) else
              (matchPhrase m.phrase cs').bind fun (v, r) => if v.isNone then some (m, r) else none
            else none)
          match ← theMeaning (fun (m : Modifier) => m.pred) (·.field) cs' ncands with
          | some (m, r) =>
            let p ← slotPred m cs'
            let np : Tm := match p with
              | .lam t d b => .lam t d (.not b)
              | p => .lam ty .tt (.not (.app (shift 1 0 p) (.loc 0)))
            pure (some (np, r))
          | none => pure none
        | none => pure none
      if let some (np, r) := neg then post f rel r (np :: acc) else
      match ← theMeaning (fun (m : Modifier) => m.pred) (·.field) cs cands with
      | some (m, r) => post f rel r ((← slotPred m cs) :: acc)
      | none =>
        -- (`a subgroup of $G$ of index $2$`: a modifier that ends in `in $v$`, without it,
        -- of the object the noun's complement names)
        let rels : List ((Modifier × List Chunk) × List Chunk) := match complementOf np with
          | some comp =>
            if !(V.nouns.any fun n => n.arg.isSome && n.ty == ty) then [] else
            V.mods.filterMap fun m => if m.prenominal || m.ty != ty then none else
              match m.phrase.reverse with
              | .v :: .w i :: front =>
                if i != w!"in" || !Notation.hasSlots front.reverse && front.isEmpty then none else
                (Notation.matchPrefix front.reverse cs []).map fun (_, r) =>
                  ((m, cs.take (cs.length - r.length) ++ [.w w!"in", .m comp] ++ r), r)
              | _ => none
          | none => []
        match ← theMeaning (fun (mc : Modifier × List Chunk) => mc.1.pred) (·.1.field) cs rels with
        | some ((m, cs2), r) => post f rel r ((← slotPred m cs2) :: acc)
        | none => pure (acc.reverse, cs)
  let (qms, r2) ← post 4 rel r1 []
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
  -- (`a sequence $(a_n)$ such that $a_n\le a_{n+1}$ for all $n$`)
  let (conds, r2) := match conds, r2 with
    | [], .w w :: .w t :: r@(.m _ :: .w f :: _) =>
      if w == w!"such" && t == w!"that" && f == w!"for" then condsOf 4 r [] else (conds, r2)
    | _, _ => (conds, r2)
  if !r2.isEmpty then fail E.noun (((wordsOf np).intersperse [32]).flatten)
  let (name, member) ← match var with
    | some ts => do let (v, d) ← varChunk ts outer; pure (v, d)
    | none => pure ([], none)
  -- (an object of a noun with a complement: adjectives relative to it, `complements`)
  if !name.isEmpty then
    if let some ts := complementOf np then
      if V.nouns.any (fun n => n.arg.isSome && n.ty == ty) then
        modify fun st => { st with complements := (st.curEnv, name, ts) :: st.complements.filter (·.2.1 != name) }
  -- (a sequence: its terms are written `a_n`, also in its conditions)
  if (← get).pendingSeq && !name.isEmpty then
    modify fun st => { st with infSeqs := (st.curEnv, name) :: st.infSeqs.filter (·.2 != name), pendingSeq := false }
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

/-- `set of subgroups $F$ of $G$`, `set of finite subsets $F$ of $\mathbb{R}$` (`family`,
`collection`): the phrase of one of its elements, the plural noun in the singular. -/
def setOfElems (V : Vocab) (np : List Chunk) : Option (List Chunk) := do
  let rest ← Grammar.kw [w!"set", w!"of"] np
  let words := rest.takeWhile fun c => match c with | .w _ | .p 45 => true | _ => false
  -- (the longest plural noun among the words before the variable, the latest start)
  let cands := V.nouns.filterMap fun n =>
    if n.plural == n.sing || n.plural.isEmpty || !(n.plural.all fun i => match i with | .w _ => true | _ => false) then none else
    (List.range words.length).reverse.findSome? fun i =>
      match matchPhrase n.plural (words.drop i) with
      | some (none, []) => some (i, n)
      | _ => none
  let (i, n) ← cands.foldl (fun (best : Option (Nat × Noun)) c => match best with
    | some b => if c.1 < b.1 then some c else some b
    | none => some c) none
  some (rest.take i ++ n.sing.filterMap (fun it => match it with | .w w => some (Chunk.w w) | _ => none) ++ rest.drop words.length)

/-- `vertices of $G$ of odd degree`, `primes less than $n$`: the noun phrase of one of the
objects, its plural noun in the singular (the earliest plural noun of the vocabulary, the
longest there). -/
def singularNP (V : Vocab) (cs : List Chunk) : Option (List Chunk) := do
  let isWords (p : Phrase) : Bool := !p.isEmpty && p.all fun i => match i with | .w _ => true | _ => false
  let cands := V.nouns.filterMap fun n =>
    if n.plural == n.sing || !isWords n.plural || !isWords n.sing then none else
    (List.range cs.length).findSome? fun i =>
      match matchPhrase n.plural (cs.drop i) with
      | some (none, r) => some (i, cs.length - i - r.length, n)
      | _ => none
  let (i, len, n) ← cands.foldl (fun (best : Option (Nat × Nat × Noun)) c => match best with
    | some b => if c.1 < b.1 || (c.1 == b.1 && c.2.1 > b.2.1) then some c else some b
    | none => some c) none
  -- (the words before it are adjectives: no formula among them)
  if (cs.take i).any (fun c => match c with | .w _ | .p 45 => false | _ => true) then none
  some (cs.take i ++ n.sing.filterMap (fun it => match it with | .w w => some (Chunk.w w) | _ => none) ++ cs.drop (i + len))

/-- `sequence of dense open subsets of $X$ $(U_n)$`: the noun phrase of each term, in the singular
and without a variable (`dense open subset of $X$`), and the sequence's variable. -/
def seqOfElems (V : Vocab) (np : List Chunk) : Option (List Chunk × List MTok × List Chunk) := do
  -- (the variable after `sequence`, `sequence $(x_n)$ of points of $X$`: as at the end)
  let np := match np with
    | .w s :: .m vts :: .w o :: r =>
      if s != w!"sequence" || o != w!"of" || r.isEmpty then np else
      let ws := r.takeWhile fun c => match c with
        | .w w => w != w!"with" && w != w!"such"
        | .p 45 => true
        | _ => false
      -- (after the words, before the complement's preposition: `points $(x_n)$ of $X$`)
      let k := match ws.getLast?, r[ws.length]? with
        | some (.w p), some (.m _) => if [w!"of", w!"in", w!"over", w!"on"].contains p then ws.length - 1 else ws.length
        | _, _ => ws.length
      .w s :: .w o :: r.take k ++ [.m vts] ++ r.drop k
    | _ => np
  let rest ← Grammar.kw [w!"sequence", w!"of"] np
  -- (the conditions, after `with` or `such that`)
  let ci := rest.findIdx? fun c => match c with | .w w => w == w!"with" || w == w!"such" | _ => false
  let (rest, conds) := match ci with
    | some i => (rest.take i, ((Grammar.kw [w!"with"] (rest.drop i) <|> Grammar.kw [w!"such", w!"that"] (rest.drop i))).getD [])
    | none => (rest, [])
  if ci.isSome && conds.isEmpty then none
  let words := rest.takeWhile fun c => match c with | .w _ | .p 45 => true | _ => false
  -- (the variable after the words, before a complement, or at the end)
  let (vts, rest) ← match rest.drop words.length with
    | .m vts :: after => some (vts, words ++ after)
    | _ => match rest.getLast? with
      | some (.m vts) => some (vts, rest.dropLast)
      | _ => none
  let cands := V.nouns.filterMap fun n =>
    if n.plural == n.sing || n.plural.isEmpty || !(n.plural.all fun i => match i with | .w _ => true | _ => false) then none else
    (List.range words.length).reverse.findSome? fun i =>
      match matchPhrase n.plural (words.drop i) with
      | some (none, []) => some (i, n)
      | _ => none
  let (i, n) ← cands.foldl (fun (best : Option (Nat × Noun)) c => match best with
    | some b => if c.1 < b.1 then some c else some b
    | none => some c) none
  some (rest.take i ++ n.sing.filterMap (fun it => match it with | .w w => some (Chunk.w w) | _ => none) ++ rest.drop words.length, vts, conds)

/-- `nounPhrase1Core`; and where words stand between the noun and its variable that are a
modifier of the noun (`an integer coprime $a$ to $n$`, as `Let $a$ be an integer coprime to
$n$` is read: the variable is put before the last preposition), the phrase with the
variable further left, after the noun. -/
def nounPhrase1 (np : List Chunk) (outer : Scope := []) : M BindInfo := do
  let st0 ← get
  -- (`$a\in R$ be a unit`, which the grammar reads as `unit element $a$ of $R$`, where that
  -- is not read: a noun of the vocabulary with the variable's domain, `unit $a\in R$`)
  let V0 := st0.vocab
  let asNoun : Option (List Chunk) := match np with
    | .w n :: .w e :: .m [.id v] :: .w o :: .m x :: rest =>
      let isNoun := V0.nouns.any fun nn => nn.sing == [.w n]
      let both := V0.nouns.any fun nn => nn.sing == [.w n, .w e]
      -- (an adjective of the same objects as well, `idempotent element`, is read so)
      let adj := V0.mods.any fun m => m.prenominal && m.phrase == [.w n] &&
        V0.nouns.any fun nn => nn.sing == [.w n] && nn.ty == m.ty
      if isNoun && !both && !adj && o == w!"of" && (e == w!"element" || e == w!"subset") then
        some (.w n :: .m ([.id v, .cmd (if e == w!"element" then w!"in" else w!"subseteq")] ++ x) :: rest)
      else none
    | _ => none
  tryCatch (nounPhrase1Core np outer) fun e => do
    -- (a set of pairs of objects of a noun, `a set $T$ of pairs of subsets of $V$`: both
    -- components of each of its elements are one)
    if let some rest := Grammar.kw [w!"set", w!"of", w!"pairs", w!"of"] np <|>
        Grammar.kw [w!"set", w!"of", w!"ordered", w!"pairs", w!"of"] np then
      if let some np' := setOfElems V0 ([Chunk.w w!"set", Chunk.w w!"of"] ++ rest) then
        set st0
        if let some b ← tryCatch (some <$> nounPhrase1Core np' outer) (fun _ => pure none) then
          let sty : Ty := .fn b.ty (.fn b.ty .prop)
          let each (i : Nat) : Tm := match b.pred with
            | some p => Notation.headBeta 4 (.app (shift 3 0 p) (.loc i))
            | none => .tt
          -- (a noun that says nothing of its objects, `real numbers`: no condition)
          let cond := Tm.mkAnd (each 1) (each 0)
          if cond == .tt then return ⟨b.name, sty, none⟩
          return ⟨b.name, sty, some (.lam sty .tt (.all b.ty (.all b.ty
            (.imp (.app (.app (.loc 2) (.loc 1)) (.loc 0)) cond))))⟩
        set st0
    -- (a set of objects of a noun: each of its elements is one)
    if let some np' := setOfElems V0 np then
      set st0
      if let some b ← tryCatch (some <$> nounPhrase1Core np' outer) (fun _ => pure none) then
        let sty : Ty := .fn b.ty .prop
        let each : Tm := match b.pred with
          | some p => .app (shift 2 0 p) (.loc 0)
          | none => .tt
        return ⟨b.name, sty, some (.lam sty .tt (.all b.ty (.imp (.app (.loc 1) (.loc 0)) each)))⟩
      set st0
    -- (`a finite $A$-module $M$`, `a $K$-vector space`: `a finite module $M$ over $A$`, for a
    -- noun with a complement after `over`; `complete and separable metric space`: adjectives
    -- joined by `and`)
    let overNoun (ws : List Chunk) : Bool := V0.nouns.any fun n =>
      (match n.arg with | some (ps, _, _) => ps.contains w!"over" | none => false) &&
      (match matchPhrase n.sing ws with | some (none, _) => true | _ => false)
    let hyphened : Option (List Chunk) := (List.range np.length).findSome? fun i =>
      match (np[i]? : Option Chunk), (np[i + 1]? : Option Chunk) with
      | some (Chunk.m x), some (Chunk.p 45) =>
        let rest := np.drop (i + 2)
        if !overNoun rest then none else
        let j := (rest.findIdx? fun c => match c with | .m _ => true | _ => false).getD rest.length
        -- (after the noun's variable, or after its words)
        let k := if j < rest.length then j + 1 else rest.length
        some (np.take i ++ rest.take k ++ [.w w!"over", .m x] ++ rest.drop k)
      | _, _ => none
    let noAnd : Option (List Chunk) :=
      let lead := np.takeWhile fun c => match c with | .w _ | .p 45 => true | _ => false
      if lead.any (fun (c : Chunk) => match c with | .w w => w == w!"and" | _ => false) && !(lead.take 1).any (fun (c : Chunk) => match c with | .w w => w == w!"and" | _ => false) then
        some (lead.filter (fun c => !(fun (c : Chunk) => match c with | .w w => w == w!"and" | _ => false) c) ++ np.drop lead.length) else none
    for alt in [hyphened, noAnd, hyphened.bind fun h =>
        let lead := h.takeWhile fun c => match c with | .w _ | .p 45 => true | _ => false
        if lead.any (fun (c : Chunk) => match c with | .w w => w == w!"and" | _ => false) then some (lead.filter (fun c => !(fun (c : Chunk) => match c with | .w w => w == w!"and" | _ => false) c) ++ h.drop lead.length) else none] do
      if let some np' := alt then
        set st0
        if let some b ← tryCatch (some <$> nounPhrase1Core np' outer) (fun _ => pure none) then return b
        set st0
    if let some np' := asNoun then
      set st0
      if let some b ← tryCatch (some <$> nounPhrase1Core np' outer) (fun _ => pure none) then return b
      set st0
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
            -- (read but for a letter that nothing defines: that letter, for the caller to bind)
            fun e' => if e'.code == E.undefined || e'.code == E.free then throw e' else tryAt j
      tryAt (k - 1)
    | _ => throw e

/-- Read a noun phrase (without its determiner). A plural noun with a sequence
(`positive integers $a_1,\ldots,a_n$`, `integers $a_1,\ldots,a_n\ge1$`) binds the
sequence `a`, each of whose terms `a_i`, for the integers `i` from the first index to the
last, is as the noun phrase says of a single variable. -/
def nounPhraseCore (np : List Chunk) (outer : Scope := []) : M BindInfo := do
  -- `Let $S$ be the set of [all] subgroups of $G$.`, `… the class of open subsets of $X$`: the
  -- set of the objects that the noun phrase describes (`x ∈ S` exactly for them)
  let setOf : Option (Codes × List Chunk) := match np with
    | .w t :: rest =>
      if t != w!"@the" then none else
      match rest.getLast? with
      | some (.m vts) =>
        (varName vts).bind fun v =>
          (Grammar.kw [w!"set", w!"of"] rest.dropLast <|> Grammar.kw [w!"class", w!"of"] rest.dropLast).map fun r =>
            (v, (Grammar.kw [w!"all"] r).getD r)
      | _ => none
    | _ => none
  if let some (v, members) := setOf then
    if !members.isEmpty && members.all (fun c => match c with | .p 44 | .p 46 => false | _ => true) then
      let b ← nounPhrase1 members outer
      if !b.name.isEmpty then fail E.unsupported
      let p := b.pred.getD (.lam b.ty .tt .tt)
      -- (the members' predicate is stated under its own binder: under the set's binder, its
      -- argument and the member, the variables of `outer` are two further out)
      let body := Tm.all b.ty (.iff (.app (.loc 1) (.loc 0)) (.app (shift 2 1 p) (.loc 0)))
      return ⟨v, .fn b.ty .prop, some (Tm.lam (.fn b.ty .prop) .tt body)⟩
  -- (the sequence after the noun, or before its complement: `elements $x_1,\ldots,x_n$
  -- of $R$`)
  let seqAt (ts : List MTok) := (Grammar.seqBound ts).bind fun (list, bound) =>
    (Grammar.seqVars list).map fun (x, name, lo, hi) => (x, name, bound, lo, hi)
  let seq : Option (List Chunk × List Chunk × Codes × List MTok × List MTok × MT × MT) :=
    (match np.reverse with
      | .m ts :: rest => (seqAt ts).map fun (x, name, bound, lo, hi) => (rest.reverse, [], x, name, bound, lo, hi)
      | _ => none) <|>
    ((np.zipIdx.findSome? fun (c, i) => match c with
        | .m ts => if i == 0 then none else (seqAt ts).map fun r => (i, r)
        | _ => none).map fun (i, (x, name, bound, lo, hi)) => (np.take i, np.drop (i + 1), x, name, bound, lo, hi))
  -- `Let $N$ be the number of primes less than $n$.`, `the number of vertices of $G$ of odd
  -- degree` (where no notion of the vocabulary has these words): how many objects of the noun
  -- phrase (real numbers) there are, defined when they are finitely many (as `\#\{x : …\}`)
  let Vc := (← get).vocab
  let countOf : Option (Codes × List Chunk) := match np with
    | .w t :: .w n :: .w o :: rest =>
      if t != w!"@the" || n != w!"number" || o != w!"of" then none else
      match rest.getLast? with
      | some (.m vts) => (varName vts).bind fun v => (singularNP Vc rest.dropLast).map (v, ·)
      | _ => none
    | _ => none
  if let some (v, sing) := countOf then
    let st0 ← get
    match ← tryCatch (some <$> nounPhrase1 np outer) (fun e => do set st0; if e.code == E.noun then pure none else throw e) with
    | some b => return b
    | none =>
      let b ← nounPhrase1 sing outer
      if b.ty != .real || !b.name.isEmpty then fail E.unsupported
      let p := b.pred.getD (.lam .real .tt .tt)
      -- (the predicate's object, the dummy of its scope, is the counted object `y`)
      let set := Tm.lam .real .tt (.app (shift 3 1 p) (.loc 0))
      let body := Tm.eq (.loc 0) (.the .real (.app (.app (.prim .cardIs) set) (.loc 0)))
      return ⟨v, .real, some (Tm.lam .real .tt body)⟩
  match seq with
  | some (pre, post, x, name, bound, lo, hi) => do
    let b ← nounPhrase1 (pre ++ [.m (name ++ bound)] ++ post) outer
    -- (numbers, or elements of a structure of the vocabulary: `elements $x_1,\ldots,x_n$ of $R$`)
    if b.ty != .real && !Elab.isBase b.ty then fail E.unsupported
    let l ← closedBound lo outer
    let h ← closedBound hi outer
    modify fun st => { st with seqs := (x, lo, hi) :: st.seqs.filter (·.1 != x) }
    -- (the predicate is stated where the sequence is bound)
    pure ⟨x, .fn .real b.ty, some (seqPred 3 l h b.pred b.ty)⟩
  | none => do
    let b ← nounPhrase1 np outer
    modify fun st => { st with seqs := st.seqs.filter (·.1 != b.name) }
    pure b

/-- `nounPhraseCore`, and an adjective that the vocabulary has relative to a structure only. -/
def nounPhrase0 (np : List Chunk) (outer : Scope := []) : M BindInfo := do
  let st00 ← get
  tryCatch (nounPhraseCore np outer) fun e00 => do
  set st00
  -- `a closed subspace of $X$`, `a dense subset of $X$`: an adjective that the vocabulary has
  -- relative to a structure only (`closed in $X$`), relative to the noun's complement
  let V0 := (← get).vocab
  -- (the leading words of the noun phrase, before its complement `of $X$`)
  let k := (np.findIdx? fun c => match c with | .w w => w == w!"of" | _ => true).getD np.length
  -- (the noun's variable may come before the complement: `closed subspace $Y$ of $X$`)
  let comp : Option (List MTok) := match np.drop k with
    | .w o :: .m x :: _ => if o == w!"of" then some x else none
    | .m [.id _] :: .w o :: .m x :: _ => if o == w!"of" then some x else none
    | _ => none
  let rels : List (Nat × Modifier) := ((np.take k).zipIdx.filterMap fun (c, i) => match c with
    | .w a => (V0.mods.find? fun m => !m.prenominal && m.phrase == [.w a, .w w!"in", .v] &&
        !V0.mods.any (fun m' => m'.prenominal && m'.phrase == [.w a] && m'.ty == m.ty)).map (i, ·)
    | _ => none)
  if let some x := comp then
    if !rels.isEmpty && rels.length < k then
      let st0 ← get
      -- (`closed and bounded subset of $X$`: without the `and` of the adjectives)
      let rest := np.zipIdx.filterMap fun (c, i) => if rels.any (·.1 == i) then none else
        match c with
        | .w w => if w == w!"and" && i < k then none else some c
        | _ => some c
      let r ← tryCatch (do
          let b ← nounPhraseCore rest outer
          let some mx := Math.parseFormula x | fail E.unsupported
          let sc : Scope := [([], b.ty)] ++ (if outer.isEmpty then [] else [([], b.ty)]) ++ outer
          let (a, aty) ← Elab.term 100000 sc none mx
          let ps ← rels.mapM fun (_, m) => do
            if b.ty != m.ty || some aty != (Notation.slotTys 1 m.pred).head? then fail E.type
            pure (Tm.lam b.ty .tt (Notation.betaApply m.pred [a, .loc 0]))
          pure (some { b with pred := conjPreds b.ty (b.pred.toList ++ ps) })) fun _ => do set st0; pure none
      if let some b := r then return b
  throw e00

/-- `function differentiable on $(a,b)$ $f$`, `function $f$ differentiable on $(a,b)$`,
`set $A$ closed in $X$`: words after the noun, with the phrase of a preposition, read before it,
`differentiable function on $(a,b)$ $f$` (the variable after the phrase). -/
def postAdjForm (V : Vocab) (np : List Chunk) : Option (List Chunk) := do
  let isW (c : Chunk) : Bool := match c with | .w _ | .p 45 => true | _ => false
  let isVar (v : List MTok) : Bool := match v with | [.id _] | [.cmd _] => true | _ => Grammar.subName v
  -- (the noun of the vocabulary after the first words: the one that ends last, the longest)
  let cands : List (Nat × Nat) := (List.range np.length).flatMap fun i =>
    if !(np.take i).all isW then [] else
    V.nouns.filterMap fun n =>
      let ws := n.sing.filterMap fun p => match p with | .w x => some x | _ => none
      if ws.isEmpty || ws.length != n.sing.length then none
      else if ((np.drop i).take ws.length).map (fun c => match c with | .w x => some x | _ => none) == ws.map some then
        some (i, ws.length) else none
  let (i, k) ← cands.foldl (fun (acc : Option (Nat × Nat)) (c : Nat × Nat) => match acc with
    | some a => if c.1 + c.2 > a.1 + a.2 || (c.1 + c.2 == a.1 + a.2 && c.2 > a.2) then some c else some a
    | none => some c) none
  let after := np.drop (i + k)
  let (var, after) : Option (List MTok) × List Chunk := match after with
    | .m v :: rest => if isVar v then (some v, rest) else (none, after)
    | _ => (none, after)
  let preps := [w!"on", w!"at", w!"in", w!"over"]
  let adjs := after.takeWhile fun c => match c with
    | .w w => !(preps ++ [w!"with", w!"such", w!"that", w!"which", w!"of", w!"for", w!"whose", w!"where", w!"and"]).contains w
    | .p 45 => true
    | _ => false
  if adjs.isEmpty then none
  let rest := after.drop adjs.length
  -- (`function differentiable $v$ on $(a,b)$`: the variable before the preposition)
  let (var, rest) : Option (List MTok) × List Chunk := match var, rest with
    | none, .m v :: r@(.w _ :: _) => if isVar v then (some v, r) else (none, rest)
    | _, _ => (var, rest)
  let .w p :: .m d :: tail := rest | none
  if !preps.contains p then none
  let (var, tail) : Option (List MTok) × List Chunk := match var, tail with
    | none, .m v :: t => if isVar v then (some v, t) else (none, tail)
    | _, _ => (var, tail)
  let v ← var
  let noun := (np.drop i).take k
  some (np.take i ++ adjs ++ noun ++ [.w p, .m d, .m v] ++ tail)

/-- `subgroup of index $2$ in $G$` as `subgroup of $G$ of index $2$`, `element in $G$` as
`element of $G$`: readings of a noun phrase whose words have no complement, with an object after
`in` at its end, as the noun's complement (the variable after the words, `subgroup $H$ of index
$2$ in $G$`, or before `in`, `subgroup of finite index $H$ in $G$`, stays the variable). -/
def compInForms (np : List Chunk) : List (List Chunk) :=
  let lead := np.takeWhile fun c => match c with
    | .w w => ![w!"of", w!"with", w!"in", w!"on", w!"over", w!"at", w!"to", w!"from", w!"such", w!"that",
        w!"which", w!"whose", w!"satisfying", w!"where"].contains w
    | .p 45 => true
    | _ => false
  if lead.isEmpty || !(lead.any fun c => match c with | .w _ => true | _ => false) then [] else
  let rest := np.drop lead.length
  let (var, rest) : List Chunk × List Chunk := match rest with
    | .m [.id v] :: r => ([.m [.id v]], r)
    | _ => ([], rest)
  -- (a complement already, `subgroup of $G$ …`)
  let hasComp : Bool := match rest with
    | .w o :: .m _ :: _ => o == w!"of"
    | _ => false
  if hasComp then [] else
  match rest.reverse with
  | .m x :: .w i :: mid =>
    if i != w!"in" then [] else
    -- (no other `in` before it, and only words and formulas between)
    if mid.any (fun c => match c with | .w w => w == w!"in" || w == w!"such" || w == w!"that" || w == w!"which" | .p _ => true | _ => false) then [] else
    let first := lead ++ var ++ [.w w!"of", .m x] ++ mid.reverse
    let second : List (List Chunk) := match var, mid with
      | [], .m [.id v] :: m' => [lead ++ [.m [.id v], .w w!"of", .m x] ++ m'.reverse]
      | _, _ => []
    first :: second
  | _ => []

/-- `nounPhrase0`, and `a sequence of dense open subsets of $X$ $(U_n)$`: a function of the
natural numbers whose terms `U_n` are each as the noun phrase says (its values elsewhere are not
used). -/
def nounPhrase (np : List Chunk) (outer : Scope := []) : M BindInfo := do
  let st00 ← get
  -- `continuous $f$` (`Let $f,g$ be continuous.`): words before a letter, without a noun, are of
  -- a number (`every positive $x$`); where they do not fit a number, as `@some` below
  -- (`differentiable $f$ at $x_0$`, `continuous $f$ on $[a,b]$`: the words of a preposition after
  -- the letter, `Let $f,g$ be continuous on $[a,b]$.`)
  let mut np := np
  let ws := np.takeWhile fun c => match c with | .w _ | .p 45 => true | _ => false
  if let .m v :: post := np.drop ws.length then
    let isVar := match v with | [.id _] | [.cmd _] => true | _ => Grammar.subName v
    -- (no word of a noun of the vocabulary among the words)
    let V := (← get).vocab
    let lastWords : List Codes := V.nouns.flatMap fun n =>
      (match n.sing.getLast? with | some (.w x) => [x] | _ => []) ++ (match n.plural.getLast? with | some (.w x) => [x] | _ => [])
    let noNoun (c : Chunk) : Bool := match c with
      | .w w => w != w!"@some" && w != w!"@the" && !lastWords.contains w
      | _ => true
    let postOk := match post with
      | [] => true
      | .w p :: _ => [w!"on", w!"at", w!"in", w!"over", w!"from", w!"to"].contains p
      | _ => false
    if isVar && !ws.isEmpty && postOk && ws.all noNoun && post.all noNoun then
      let r ← tryCatch (do discard <| nounPhrase0 np outer; pure none) (fun e => pure (some e))
      set st00
      if (r.map (·.code)) == some E.type then np := [.w w!"@some", .m v] ++ ws ++ post
  -- `@some $f$ continuous on $[a,b]$` (`Let $f$ be continuous on $[a,b]$.`, words without a
  -- noun): the one kind of object of the vocabulary that the words fit, with its noun (a number
  -- where they fit one)
  if let .w sm :: .m v :: post := np then
    if sm == w!"@some" then
      let V := (← get).vocab
      let bases : List (List Codes) := [[w!"real", w!"number"], [w!"function"], [w!"sequence"], [w!"set"],
        [w!"matrix"], [w!"vector"], [w!"graph"], [w!"permutation"], [w!"complex", w!"number"],
        [w!"random", w!"variable"], [w!"polynomial"]]
      -- (the fields of the words: `odd` of the field `numbers` is said of numbers, of
      -- `realfunctions` of functions; a noun of the core takes the words of every field)
      let firstWord : Option Codes := post.findSome? fun c => match c with | .w w => some w | _ => none
      let wordFields : List Codes := match firstWord with
        | some w =>
          ((V.adjectives.filter fun a => a.words.head? == some w).map (·.field)) ++
          ((V.mods.filter fun m => match m.phrase.head? with | some (.w x) => x == w | _ => false).map (·.field))
        | none => []
      let present := bases.filter fun b => V.nouns.any fun n => n.sing == b.map PItem.w && n.arg.isNone
      let ofWordField (b : List Codes) : Bool := V.nouns.any fun n => n.sing == b.map PItem.w && n.arg.isNone &&
        (wordFields.isEmpty || n.field.isEmpty || wordFields.contains n.field)
      let allWords := post.all fun c => match c with | .w _ | .p 45 => true | _ => false
      -- (the words before a preposition before the noun, the phrase of the preposition after
      -- it: `continuous function on $[a,b]$ $f$`)
      let pre := post.takeWhile fun c => match c with
        | .w w => ![w!"on", w!"at", w!"in", w!"over", w!"from", w!"to", w!"with", w!"of"].contains w
        | .p 45 => true
        | _ => false
      let rest := post.drop pre.length
      let cands : List (List Codes × List Chunk) := present.flatMap fun b =>
        let noun : List Chunk := b.map Chunk.w
        let vm : Chunk := .m v
        ([noun ++ [vm] ++ post] ++ (if allWords then [post ++ noun ++ [vm]] else []) ++
          (if !pre.isEmpty && !rest.isEmpty then [pre ++ noun ++ rest ++ [vm]] else []) ++
          -- (`twice differentiable function $f$ with …`: the variable before the condition)
          (if !pre.isEmpty && (match rest with | .w w :: _ => w == w!"with" | _ => false) then [pre ++ noun ++ [vm] ++ rest] else []) ++
          -- (`continuous function on $[a,b]$ $f$ with …`: after the phrase, before the condition)
          (match rest.findIdx? (fun c => match c with | .w w => w == w!"with" | _ => false) with
            | some k => if !pre.isEmpty && k > 0 then [pre ++ noun ++ rest.take k ++ [vm] ++ rest.drop k] else []
            | none => [])).map (b, ·)
      let mut fits : List (List Codes × List Chunk × BindInfo) := []
      -- (a letter that nothing defines, `on $[a,b]$`: for the caller to bind, then read again)
      let mut undef : Option Err := none
      for (b, c) in cands do
        match ← tryCatch (Sum.inl <$> nounPhrase0 c outer) (fun e => pure (Sum.inr e)) with
        | .inl bi => fits := fits ++ [(b, c, bi)]
        | .inr e => if (e.code == E.undefined || e.code == E.free) && undef.isNone then undef := some e
        set st00
      let kinds := fits.foldl (fun acc (b, c, bi) =>
        if acc.any (fun (_, _, b') => b'.ty == bi.ty && b'.pred == bi.pred) then acc else acc ++ [(b, c, bi)]) []
      -- (a number where the words fit one, as `every positive $x$`)
      let kinds := match kinds.find? (fun (b, _, _) => b == [w!"real", w!"number"]) with
        | some k => [k]
        | none => kinds
      -- (of one type, the general kind: a function, not a sequence or a polynomial, which are
      -- functions of their own kind)
      -- (the kinds of the field of the words, where it has any: `convergent` of the field `series`
      -- is said of sequences, not of the functions of `realfunctions`)
      let inField : List (List Codes × List Chunk × BindInfo) := kinds.filter fun (b, _, _) => ofWordField b
      let kinds : List (List Codes × List Chunk × BindInfo) :=
        if kinds.length < 2 || inField.isEmpty then kinds else inField
      -- (otherwise, of one type, the general kind: `twice differentiable` of the field `calculus`
      -- is said of functions, not of sequences or polynomials, functions of a kind of their own)
      let general (b : List Codes) : Bool := V.nouns.any fun n => n.sing == b.map PItem.w && n.arg.isNone &&
        (match n.pred with | .lam _ _ .tt => true | _ => false)
      let kinds : List (List Codes × List Chunk × BindInfo) := kinds.filter fun (b, _, bi) =>
        general b || !(kinds.any fun (b', _, bi') => bi'.ty == bi.ty && general b')
      match kinds with
      | [(_, c, _)] => return ← nounPhrase0 c outer
      | [] =>
        if let some e := undef then throw e
        fail E.finding (w!"say what kind of object " ++ (varName v |>.getD []) ++ w!" is, with a noun (Let $f$ be a continuous function on $[a,b]$.)")
      | _ =>
        -- (the kinds by their nouns, each once: `a real number or a function`)
        let names := (kinds.map fun (b, _, _) => w!" ".intercalate b).eraseDups
        let art (n : Codes) : Codes := (if [97, 101, 105, 111, 117].contains (n.headD 0) then w!"an " else w!"a ") ++ n
        let arts := names.map art
        let listed := match arts.reverse with
          | last :: more@(_ :: _) => w!", ".intercalate more.reverse ++ w!" or " ++ last
          | _ => w!", ".intercalate arts
        fail E.finding (w!"the words fit several kinds of objects (" ++ listed ++
          w!"): say what kind of object " ++ (varName v |>.getD []) ++ w!" is, with a noun (Let $f$ be a continuous function on $[a,b]$.)")
  -- `Let $f\in K[x]$ be a nonzero polynomial of degree $n$`: a polynomial over the ring of the
  -- coefficients of its domain (not over its domain), read first
  let polyOver : Option (List Chunk) := do
    let k ← np.findSome? fun c => match c with
      | .m [.id _, .cmd i, .id r, .sym 91, .id _, .sym 93] => if i == w!"in" then some r else none
      | _ => none
    let j ← np.findIdx? fun c => match c with | .w w => w == w!"polynomial" || w == w!"polynomials" | _ => false
    if (match np[j + 1]? with | some (.w o) => o == w!"over" | _ => false) then none
    let at_ := if (match np[j + 1]? with | some (.m _) => true | _ => false) then j + 2 else j + 1
    some (np.take at_ ++ [.w w!"over", .m [.id k]] ++ np.drop at_)
  if let some np' := polyOver then
    if let some b ← tryCatch (some <$> nounPhrase0 np' outer) (fun _ => pure none) then return b
    set st00
  -- (`increasing sequence that is bounded above`: the words after `that is` follow the noun,
  -- `increasing sequence bounded above`)
  let relFree : Option (List Chunk) := do
    let i ← (List.range np.length).find? fun i => match (np[i]? : Option Chunk), (np[i + 1]? : Option Chunk), (np[i + 2]? : Option Chunk) with
      | some (.w t), some (.w b), some (.w _) => (t == w!"that" || t == w!"which") && (b == w!"is" || b == w!"are") && i > 0
      | _, _, _ => false
    some (np.take i ++ np.drop (i + 2))
  if let some np' := relFree then
    if let some b ← tryCatch (some <$> nounPhrase0 np' outer) (fun _ => pure none) then return b
    set st00
  -- (`divisor of $n$ $d$ with $d>1$`: the variable after the noun's complement, before more
  -- words, as `divisor $d$ of $n$ with $d>1$`)
  let varAfterComp : Option (List Chunk) := do
    let k ← np.findIdx? fun c => match c with | .w w => w == w!"of" | _ => false
    if k == 0 || !((np.take k).all fun c => match c with | .w _ | .p 45 => true | _ => false) then none
    match np.drop k with
    | .w _ :: .m x :: .m v :: rest@(_ :: _) =>
      let _ ← varName v
      some (np.take k ++ [.m v, .w w!"of", .m x] ++ rest)
    | _ => none
  if let some np' := varAfterComp then
    if let some b ← tryCatch (some <$> nounPhrase0 np' outer) (fun _ => pure none) then return b
    set st00
  -- (`convergent sequence $(a_n)$ of real numbers with …`: a sequence's variable before the
  -- words of its terms, as `convergent sequence of real numbers $(a_n)$ with …`)
  let seqBeforeOf : Option (List Chunk) := do
    let k ← np.findIdx? fun c => match c with | .m _ => true | _ => false
    let .m v :: .w o :: post := np.drop k | none
    if o != w!"of" || !Grammar.seqParenName v then none
    let words := post.takeWhile fun c => match c with
      | .w w => w != w!"with" && w != w!"such" && w != w!"that" && w != w!"which" | .p 45 => true | _ => false
    if words.isEmpty then none
    some (np.take k ++ [.w o] ++ words ++ [.m v] ++ post.drop words.length)
  if let some np' := seqBeforeOf then
    if let some b ← tryCatch (some <$> nounPhrase0 np' outer) (fun _ => pure none) then return b
    set st00
  -- (`with more than $n-1$ edges`: `with at least $\lfloor n-1\rfloor+1$ edges`; `fewer than`,
  -- `less than`: `at most $\lceil k\rceil-1$`, after `with` or `and`; `exactly $k$`: `$k$`)
  let rec counted : Nat → List Chunk → List Chunk
    | 0, cs => cs
    | f + 1, .w a :: .w m :: .w t :: .m k :: rest =>
      if (a == w!"with" || a == w!"and") && t == w!"than" && (m == w!"more" || m == w!"fewer" || m == w!"less") then
        -- (of a number of objects: more than `k` is at least `⌊k⌋+1`, fewer than `k` at most `⌈k⌉-1`)
        if m == w!"more" then .w a :: .w w!"at" :: .w w!"least" :: .m ([.cmd w!"lfloor"] ++ k ++ [.cmd w!"rfloor", .sym 43, .digit 1]) :: counted f rest
        else .w a :: .w w!"at" :: .w w!"most" :: .m ([.cmd w!"lceil"] ++ k ++ [.cmd w!"rceil", .sym 45, .digit 1]) :: counted f rest
      else .w a :: counted f (.w m :: .w t :: .m k :: rest)
    | f + 1, .w a :: .w e :: .m k :: rest =>
      if (a == w!"with" || a == w!"and") && e == w!"exactly" then .w a :: .m k :: counted f rest
      else .w a :: counted f (.w e :: .m k :: rest)
    | f + 1, c :: rest => c :: counted f rest
    | _, [] => []
  let npc := counted (np.length + 1) np
  if np.any (fun c => match c with | .w w => w == w!"than" || w == w!"exactly" | _ => false) then
    if let some b ← tryCatch (some <$> nounPhrase0 npc outer) (fun _ => pure none) then return b
    set st00
  tryCatch (nounPhrase0 np outer) fun e00 => do
  set st00
  -- (`function differentiable on $(a,b)$`: as `differentiable function on $(a,b)$`)
  -- (a letter that nothing defines, `on $(a,b)$`: for the caller to bind, then read again)
  for np' in ([some np, relFree].filterMap id).filterMap (postAdjForm (← get).vocab) do
    match ← tryCatch (Sum.inl <$> nounPhrase0 np' outer) (fun e => pure (Sum.inr e)) with
    | .inl b => return b
    | .inr e => if e.code == E.undefined || e.code == E.free then throw e
    set st00
  if let some (np', vts, condCs) := seqOfElems (← get).vocab np then
    if let some v := varName vts then
      if let some b ← tryCatch (some <$> nounPhrase0 np' outer) (fun _ => pure none) then
        if b.name.isEmpty then
          let each : Tm := match b.pred with
            | some p => .app (shift 2 0 p) (.app (.loc 1) (.loc 0))
            | none => .tt
          modify fun st => { st with infSeqs := (st.curEnv, v) :: st.infSeqs.filter (·.2 != v), pendingSeq := false }
          let sty : Ty := .fn .real b.ty
          -- (`with $A_{n+1}\subseteq A_n$ for all $n$`: conditions on the terms, stated where
          -- the sequence is bound)
          let (ms, left) := condsOf 4 condCs []
          if !left.isEmpty then throw e00
          let cs ← ms.mapM fun m => do
            let (p, pty) ← Elab.term 100000 ((v, sty) :: outer) none m
            if pty != .prop then fail E.type
            pure p
          let terms : List Tm := if each == .tt then [] else [Tm.all .real (.imp (.app (.prim .isNat) (.loc 0)) each)]
          return ⟨v, sty, some (.lam sty .tt (Elab.conjAll (terms ++ cs)))⟩
    set st00
  -- (`subgroup of index $2$ in $G$`: the object after `in` as the noun's complement)
  if !(e00.code == E.undefined || e00.code == E.free) then
    for np' in compInForms np do
      if let some b ← tryCatch (some <$> nounPhrase0 np' outer) (fun _ => pure none) then return b
      set st00
  throw e00

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
    -- (`@the`, `@norm`: markers of the parser, no variables)
    | .id n => if bound.contains n || n == [42] || n == [39] || n.head? == some 64 then [] else [n]
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
      -- (`K[x]`: the letter of the polynomials is no variable)
      if op == w!"@polyring" then freeIds f bound x else
      (if op == w!"\\cup" || op == w!"\\cap" || op == w!"\\times" || op == w!"\\setminus" then []
        else freeIds f bound (.id op)) ++ freeIds f bound x ++ freeIds f bound y
    -- (`\bigcap_n U_n`: the index is bound)
    | .app (.id op) [.id v, lo, hi, b] =>
      if op == w!"@bigcap" || op == w!"@bigcup" then freeIds f bound lo ++ freeIds f bound hi ++ freeIds f (v :: bound) b
      else freeIds f bound (.id op) ++ ([MT.id v, lo, hi, b].flatMap (freeIds f bound))
    | .app h as => freeIds f bound h ++ (as.flatMap (freeIds f bound))
    | .add x y | .minus x y | .mul x y | .div x y | .frac x y => freeIds f bound x ++ freeIds f bound y
    | .minm xs | .maxm xs | .tuple xs | .conj xs => xs.flatMap (freeIds f bound)
    | .int lo hi b v => freeIds f bound lo ++ freeIds f bound hi ++ freeIds f (v :: bound) b
    | .interval a b => freeIds f bound a ++ freeIds f bound b
    -- (`X\sim\mathrm{Bin}(n,p)`: the name of the distribution is no variable)
    | .chain x rs => freeIds f bound x ++ rs.flatMap (fun r =>
        if r.1 == .sim then (match r.2 with
          | .app _ args => args.flatMap (freeIds f bound)
          | .mul _ y => freeIds f bound y
          | .id _ => []
          | d => freeIds f bound d)
        else freeIds f bound r.2)
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
    -- (the sets of a signature, `f\colon A\to B`)
    | .sig _ d c => freeIds f bound d ++ freeIds f bound c
    | .text _ => []

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
    | .app (.id op) [.id v, lo, hi, b] =>
      (if op == w!"@bigcap" || op == w!"@bigcup" then [v] else []) ++ all [lo, hi, b]
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

/-- The conjuncts of a condition (`with $a\ge0$ and $b\ge0$`), each read on its own. -/
def conjunctsOf : Nat → MT → List MT
  | 0, m => [m]
  | f + 1, .conj ms => ms.flatMap (conjunctsOf f)
  | _, m => [m]

/-- A condition on variables bound before it in the same binder (`with $a\ge0$`): it joins
the domain of the last of them that it mentions (the last variable, if it mentions none of
them), not simply the last one: in `Let $a$, $b$ and $c$ be real numbers with $a\ge0$`, the
condition on `a` must not ride on `c`, which the claim may leave unused. `φ` is read in the
scope of `before` and of the variables of `out` up to that one. -/
def attachOne (before out : List BindInfo) (φ : MT) : M (List BindInfo) := do
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

/-- `attachOne` for each conjunct (`with $a\ge0$ and $b\ge0$`: each condition on its own
variable, so that a claim that uses `a` alone keeps `a ≥ 0`). -/
def attachCond (before out : List BindInfo) (φ : MT) : M (List BindInfo) := do
  let mut o := out
  for m in conjunctsOf 8 φ do o ← attachOne before o m
  pure o

/-- `a vector space $V$ over a field $K$`: a complement that introduces its own object (a
preposition, `a` or `an`, words and a variable). The noun phrase of that object, and the
phrase with the variable in place of it. -/
def splitNested (np : List Chunk) : Option (List Chunk × List Chunk) := do
  let preps : List Codes := [w!"of", w!"over", w!"in", w!"on"]
  let i ← (List.range np.length).find? fun i => match (np[i]? : Option Chunk), (np[i + 1]? : Option Chunk) with
    | some (Chunk.w p), some (Chunk.w a) => preps.contains p && (a == w!"a" || a == w!"an")
    | _, _ => false
  let rest := np.drop (i + 2)
  let ws := rest.takeWhile fun (c : Chunk) => match c with | .w _ | .p 45 => true | _ => false
  if ws.isEmpty then none
  let some (Chunk.m ts) := (rest[ws.length]? : Option Chunk) | none
  let _ ← Math.parseFormula ts >>= fun m => match m with | .id _ => some () | _ => none
  -- (the variable at the end, with none before: the object's own, which a `Let` puts
  -- there, `Let $H$ be a subgroup of a cyclic group` as `subgroup of a cyclic group $H$`;
  -- the complement's object has no letter)
  let isMath (c : Chunk) : Bool := match c with | .m _ => true | _ => false
  if (rest.drop (ws.length + 1)).isEmpty && !(np.take i).any isMath then none
  some (ws ++ [.m ts], np.take (i + 1) ++ [.m ts] ++ rest.drop (ws.length + 1))

/-- The binders of a noun phrase: one, or two for a complement that introduces its own
object (`a vector space $V$ over a field $K$` binds `K`, then `V`). -/
def nounBinders (np : List Chunk) (outer : Scope) : M (List BindInfo) := do
  match splitNested np with
  | some (inner, main) =>
    -- (the object bound already, by the phrase before in the same binder: `Let $V$ and $W$
    -- be vector spaces over a field $K$` has one field)
    let innerVar : Option Codes := match inner.getLast? with
      | some (.m [.id v]) => some v
      | _ => none
    if let some v := innerVar then
      if outer.any (·.1 == v) then
        let st0 ← get
        return ← tryCatch (do pure [← nounPhrase main outer]) fun _ => do
          set st0
          pure [← nounPhrase np outer]
    let st0 ← get
    tryCatch (do
        let b1 ← nounPhrase inner outer
        let b2 ← nounPhrase main ((b1.name, b1.ty) :: outer)
        pure [b1, b2]) fun _ => do
      set st0
      pure [← nounPhrase np outer]
  | none => pure [← nounPhrase np outer]

/-- The name with a number below it whose letter is `v0` (`x_0`), where the formulas name the
letter only so (one name, no other number below it, and the letter nowhere alone). -/
def subNameFor (maths : List MT) (v0 : Codes) : Option Codes :=
  let rec subOf : Nat → MT → List Codes
    | 0, _ => []
    | k + 1, m => (match m with
      | .sub (.id b) (.num n) => if b == v0 then [b ++ [95] ++ (Nat.toDigits 10 n).map Char.toNat] else []
      | _ => []) ++ (match m with
        | .sub (.id _) (.num _) => []
        | _ => (mtChildren m).flatMap (subOf k))
  let rec bare : Nat → MT → Bool
    | 0, _ => false
    | k + 1, m => match m with
      | .id b => b == v0
      | .sub (.id _) (.num _) => false
      | _ => (mtChildren m).any (bare k)
  match (maths.flatMap (subOf 64)).eraseDups with
  | [key] => if maths.any (bare 64) then none else some key
  | _ => none

/-- The ends of the intervals that the formulas of a noun phrase name (`[a,b]`, `(a,b]`; `(a,b)`
as the domain of a signature or after `on`, `over`): the left end and the right end. -/
def npIntervalEnds (np : List Chunk) : List (MT × MT) :=
  let rec ends : Nat → Bool → MT → List (MT × MT)
    | 0, _, _ => []
    | f + 1, dom, m =>
      (match m with
        | .interval a b | .ival a b _ _ => [(a, b)]
        | .tuple [a, b] => if dom then [(a, b)] else []
        | _ => []) ++
      (match m with
        | .sig n d c => ends f false n ++ ends f true d ++ ends f false c
        | _ => (mtChildren m).flatMap (ends f false))
  np.zipIdx.flatMap fun (c, i) => match c with
    | .m ts =>
      let dom := i > 0 && (match (np[i - 1]? : Option Chunk) with
        | some (.w w) => w == w!"on" || w == w!"over"
        | _ => false)
      match Math.parseSig ts <|> Math.parseFormula ts with
      | some m => ends 64 dom m
      | none => []
    | _ => []

/-- `nounBinders`; and where a letter that nothing defines stands in a formula of the noun
phrase (`Let $G$ be a graph with $n$ vertices`, `an $n\times n$ matrix`), the letter is a
number bound with it, before it. An end of an interval of the phrase (`a continuous function on
$[a,b]$`, `$f\colon(a,b)\to\mathbb{R}$`) is below the other end, as the notation presupposes. -/
def nounBindersImplicitN (np : List Chunk) : Nat → Scope → M (List BindInfo)
  | 0, outer => nounBinders np outer
  | f + 1, outer => do
    let st0 ← get
    tryCatch (nounBinders np outer) fun e => do
      if e.code != E.undefined && e.code != E.free then throw e
      let v0 := e.detail
      -- (a letter with a number below it, `x_0` in `differentiable at $x_0$`, where the letter
      -- alone is nowhere: the name with its number, one variable)
      let subName := subNameFor (np.filterMap fun c => match c with | .m ts => Math.parseFormula ts | _ => none) v0
      let v := subName.getD v0
      -- (a Latin or Greek letter: `with mean $\mu$ and variance $\sigma^2$`)
      let greek := [w!"alpha", w!"beta", w!"gamma", w!"delta", w!"epsilon", w!"varepsilon", w!"zeta", w!"eta", w!"theta",
        w!"kappa", w!"lambda", w!"mu", w!"nu", w!"xi", w!"rho", w!"sigma", w!"tau", w!"phi", w!"varphi", w!"chi", w!"psi", w!"omega"]
      let isGreek := v.head? == some 92 && greek.contains (v.drop 1)
      let single := isGreek || match v with | [c] => (c ≥ 97 && c ≤ 122) || (c ≥ 65 && c ≤ 90) | _ => false
      let inPhrase := np.any fun c => match c with
        | .m ts => ts.contains (.id v) || (isGreek && (ts.contains (.cmd (v.drop 1)) || ts.contains (.id v)))
        | _ => false
      let varOfNoun := np.any fun c => match c with | .m [.id w] => w == v | _ => false
      if subName.isNone && (!single || !inPhrase) || (outer.any (·.1 == v)) then throw e
      -- (not the prime of a `$p$-group`: a prime that the sentence binds, not any number)
      let pGroupLetter := (List.range np.length).any fun i => match (np[i]? : Option Chunk), (np[i + 1]? : Option Chunk), (np[i + 2]? : Option Chunk) with
        | some (.m [.id u]), some (.p 45), some (.w g) => u == v && [w!"group", w!"groups", w!"subgroup", w!"subgroups"].contains g
        | _, _, _ => false
      if pGroupLetter then throw e
      -- (not the noun's own variable: `a graph $n$`)
      if varOfNoun && (np.filter fun c => match c with | .m _ => true | _ => false).length < 2 then throw e
      set st0
      -- (an end of an interval: below the other end, a number or a real variable bound before;
      -- the predicate is stated where the letter is bound, under its own binder)
      let side (m : MT) : Option Tm := match m with
        | .id p => if p == v then some (.loc 0) else
          (outer.findIdx? fun (n, t) => n == p && t == .real).map fun k => Tm.loc (k + 2)
        | .num n => some (.num n)
        | _ => none
      let conds : List Tm := (npIntervalEnds np).filterMap fun (l, r) =>
        let mentions := (match l with | .id p => p == v | _ => false) || (match r with | .id p => p == v | _ => false)
        if !mentions then none else
        match side l, side r with
        | some a, some b => if a == b then none else some (Tm.lt a b)
        | _, _ => none
      let conds := conds.eraseDups
      let bs ← nounBindersImplicitN np f ((v, .real) :: outer)
      pure ((⟨v, .real, if conds.isEmpty then none else some (.lam .real .tt (Elab.conjAll conds))⟩ : BindInfo) :: bs)

/-- The parts of an object that is named with them (`Let $G=(V,E)$ be a graph`, the noun
phrase `@parts $G$ $V$ $E$` after the binder of `G`): each letter is the value of the notion
that the vocabulary names for that part of the objects of `G`'s kind (`Noun.parts`: `V` is
the vertex set of `G`, `E` its edge set), as `let $V$ be the vertex set of $G$` binds it. -/
def partsBinders (g : List MTok) (ps : List (List MTok)) (outer : Scope) : M (List BindInfo) := do
  let some key := Math.parseFormula g >>= Grammar.nameKey | fail E.unsupported
  let some (_, ty) := Elab.lookupLocal outer key | fail E.undefined key
  let V := (← get).vocab
  let shown : Codes := (ps.map fun _ => w!"…").intersperse [44] |>.flatten
  let some n := V.nouns.find? fun n => n.ty == ty && !n.parts.isEmpty
    | fail E.finding (w!"$" ++ key ++ w!"=(" ++ shown ++ w!")$: the vocabulary names no parts for an object of this kind: introduce $" ++ key ++ w!"$ alone, and each part by what it is (let $V$ be the …)")
  if n.parts.length != ps.length then
    let names : Codes := (n.parts.map fun ph => ((ph.filterMap fun i => match i with | .w w => some w | _ => none).takeWhile (· != w!"of")).intersperse [32] |>.flatten).intersperse w!", " |>.flatten
    fail E.finding (w!"$" ++ key ++ w!"=(" ++ shown ++ w!")$: the parts of such an object are the " ++ names)
  let mut out : List BindInfo := []
  for (ph, p) in n.parts.zip ps do
    let cs : List Chunk := ph.filterMap fun i => match i with
      | .w w => some (Chunk.w w)
      | .v => some (Chunk.m g)
      | .m toks => some (Chunk.m toks)
      | .f _ => none
    let sc : Scope := (out.map fun b => (b.name, b.ty)).reverse ++ outer
    out := out ++ [← nounPhrase ([.w w!"@the"] ++ cs ++ [.m p]) sc]
  pure out

def nounBindersImplicitCore (np : List Chunk) (outer : Scope) : M (List BindInfo) := do
  -- `a field $K$ of characteristic $p>0$`: a parameter with its bound, after the noun's
  -- variable: the letter, bound with the bound before the object
  let firstM := np.findIdx? fun c => match c with | .m _ => true | _ => false
  let hit : Option (Nat × Codes × MT) := match firstM with
    | none => none
    | some i0 => (np.zipIdx.filterMap fun (c, i) =>
        if i ≤ i0 then none else
        match c, np[i - 1]? with
        | .m ts, some (.w w) =>
          -- (a condition, `with $n\ge1$`, is not a slot; `with $n\ge3$ vertices` is)
          let slotAfter := match np[i + 1]? with
            | some (.w x) => w == w!"with" && ![w!"and", w!"for", w!"then", w!"where", w!"such", w!"if"].contains x
            | _ => false
          if [w!"with", w!"that", w!"and", w!"where", w!"satisfying"].contains w && !slotAfter then none else
          -- (nor the binder of a condition, `with $f'(x)>0$ for all $x\in I$`)
          if [w!"all", w!"every", w!"each", w!"any"].contains w then none else
          match Math.parseFormula ts with
          | some m@(.chain (.id v) [(_, _)]) =>
            -- (nor a condition on the object's own variable)
            if np.any (fun c => match c with | .m [.id u] => u == v | _ => false) then none else some (i, v, m)
          | _ => none
        | _, _ => none).head?
  match hit with
  | some (i, v, cond) =>
    if (Elab.lookupLocal outer v).isSome || (← Elab.lookupGlob v).isSome then nounBindersImplicitN np 3 outer else
    let (p, pty) ← Elab.term 100000 ((v, .real) :: outer) none cond
    if pty != .prop then fail E.type
    let np' := np.set i (.m [.id v])
    let bs ← nounBindersImplicitN np' 3 ((v, .real) :: outer)
    pure ((⟨v, .real, some (.lam .real .tt (shift 1 0 p))⟩ : BindInfo) :: bs)
  | none => nounBindersImplicitN np 3 outer

/-- `a graph $G$ with vertex set $V$`, `… with vertex set $V$ and edge set $E$`: letters
after the object's own for notions of it. The end of a noun phrase `with NAME $X$ [and NAME
$Y$]`, where the vocabulary has the notions `NAME of $v$` and the letters are new: the
phrase without it, the object's letter, and the names with their letters. -/
def withNotionsSplit (V : Vocab) (np : List Chunk) (outer : Scope) :
    Option (List Chunk × List MTok × List (List Codes × List MTok)) := do
  let isName (ts : List MTok) : Bool := match ts with | [.id _] | [.cmd _] => true | _ => Grammar.subName ts
  let i ← (List.range np.length).reverse.find? fun i => match (np[i]? : Option Chunk) with
    | some (.w w) => w == w!"with"
    | _ => false
  let head := np.take i
  -- (the object's letter: the first formula of the phrase, a name)
  let g ← head.findSome? fun c => match c with | .m ts => some ts | _ => none
  if !isName g then none
  let rec items : Nat → List Chunk → List (List Codes × List MTok) → Option (List (List Codes × List MTok))
    | 0, _, _ => none
    | f + 1, cs, acc =>
      let ws := cs.takeWhile fun (c : Chunk) => match c with | .w w => w != w!"and" | _ => false
      match cs.drop ws.length with
      | .m x :: rest =>
        let name := ws.filterMap fun (c : Chunk) => match c with | .w w => some w | _ => none
        if name.isEmpty || !isName x then none else
        let acc := acc ++ [(name, x)]
        match rest with
        | [] => some acc
        | .w a :: rest' => if a == w!"and" then items f rest' acc else none
        | _ => none
      | _ => none
  let its ← items 4 (np.drop (i + 1)) []
  let key (ts : List MTok) : Option Codes := Math.parseFormula ts >>= Grammar.nameKey
  let gk ← key g
  let ks ← its.mapM fun (_, x) => key x
  if ks.any (fun k => k == gk || (Elab.lookupLocal outer k).isSome) || ks.eraseDups.length != ks.length then none
  -- (each name is a notion of one object: `vertex set of $v$`)
  if !(its.all fun (name, _) => V.notions.any fun n => n.name == name.map PItem.w ++ [.w w!"of", .v]) then none
  some (head, g, its)

/-- The binders of a noun phrase (`nounBindersImplicitCore`); of `@parts $G$ $V$ $E$`, the
parts of `G` (`partsBinders`); and, where the phrase is not read as it stands, of a phrase
that ends with letters for notions of its object (`withNotionsSplit`): the object, then each
letter as `let $V$ be the vertex set of $G$` binds it. -/
def nounBindersImplicit (np : List Chunk) (outer : Scope) : M (List BindInfo) := do
  if let .w pw :: .m g :: ps := np then
    if pw == w!"@parts" then
      return ← partsBinders g (ps.filterMap fun c => match c with | .m ts => some ts | _ => none) outer
  let st0 ← get
  tryCatch (nounBindersImplicitCore np outer) fun e => do
    let some (head, g, its) := withNotionsSplit st0.vocab np outer | throw e
    set st0
    -- (a letter that the article has defined is that object, not a new one)
    for (_, x) in its do
      if let some k := Math.parseFormula x >>= Grammar.nameKey then
        if (← Elab.lookupGlob k).isSome then throw e
    tryCatch (do
        let mut out ← nounBindersImplicitCore head outer
        for (name, x) in its do
          let sc : Scope := (out.map fun b => (b.name, b.ty)).reverse ++ outer
          out := out ++ [← nounPhrase ([.w w!"@the"] ++ name.map Chunk.w ++ [.w w!"of", .m g, .m x]) sc]
        pure out) fun _ => do
      set st0
      throw e

def binderInfosRaw (b : Bind) (before : List BindInfo := []) : M (List BindInfo) :=
  let outer : Scope := (before.map fun b => (b.name, b.ty)).reverse
  match b with
  -- (a multi-index `I\in\mathbb{N}_0^n`: its components `I_1`, …, `I_n`)
  | .every vs d => everyIn outer vs d
  | .noun np => nounBindersImplicit np outer
  | .hyp b => binderInfosRaw b before
  | .on _ => pure []
  | .ifCond φ => do
    -- the free variables of φ range over ℝ; φ is the domain of the last one. The
    -- variables bound before (of the result: `Let $n\ge1$. If $x\in[0,n]$, …`) are not
    -- bound again
    let st ← get
    let free := ((dropBoundIndices st φ (freeIds 64 [] φ)).filter fun n => !(st.globs.zipIdx.any fun (g, i) => g.key == n && !g.family && Elab.visibleIn st i) && !constName n && !st.vocab.symbols.any (·.sym == n) && !st.vocab.methods.any (·.op == .fn n)).eraseDups
    -- (a symbol of an earlier sentence that Leanify did not read is an object of the
    -- article, not a variable: `If $q>2-s$` about the `q` and `s` introduced in words)
    -- (not a variable that the result or the sentence has bound: `Let $T$ be …. If
    -- $K\subseteq\{…T(x)…\}$, …`)
    let unreadHere (n : Codes) : Bool := st.unreadIds.contains n ||
      st.unreadLocal.any fun (e, m) => m == n && (e == st.curEnv || st.curProved == some e)
    if let some v := free.find? (fun n => unreadHere n && !before.any (·.name == n)) then
      fail E.undefined v
    -- (`U_1` of a sequence `U` bound before is its term, not a variable)
    let free := free.filter fun n => (termOfSeq before n).isNone
    let free := (seqFree st [] φ free).filter fun n => !before.any (·.name == n)
    -- (a term `x_1` of a sequence is not a variable of its own)
    if let some x := free.find? fun n => st.seqs.any (·.1 == n) then
      fail E.finding (w!"a condition on the terms of the sequence " ++ x ++ w!" together with new variables: state it where " ++ x ++ w!" is introduced (with $…$)")
    -- (`If $a,b\in R$ and $ab=0$` for a structure `R`: the variables are its elements)
    let rec memsOf : Nat → MT → List (Codes × MT)
      | 0, _ => []
      | f + 1, m => match m with
        | .conj xs => xs.flatMap (memsOf f)
        | .land x y => memsOf f x ++ memsOf f y
        | .chain (.id v) [(.mem, d)] => [(v, d)]
        | .chain (.tuple xs) [(.mem, d)] => xs.filterMap fun x => match x with | .id v => some (v, d) | _ => none
        | _ => []
    let mems := memsOf 8 φ
    -- (`Let $X\sim N(\mu,\sigma^2)$`: `X` is a random variable)
    let rvTy : Option Ty := ((← get).vocab.methods.find? (·.op == .fn w!"@at")).map (·.ty)
    let rec simsOf : Nat → MT → List Codes
      | 0, _ => []
      | f + 1, m => match m with
        | .conj xs => xs.flatMap (simsOf f)
        | .land x y => simsOf f x ++ simsOf f y
        | .chain (.id v) [(.sim, _)] => [v]
        | _ => []
    let sims := simsOf 8 φ
    let tyOf (v : Codes) : M Ty := do
      if sims.contains v then
        if let some t := rvTy then return t
      match mems.find? (·.1 == v) with
      | some (_, d) =>
        let st0 ← get
        let t ← tryCatch (do let (t, _) ← domainOf false d outer; pure t) fun _ => do set st0; pure Ty.real
        pure (if Elab.isBase t then t else .real)
      | none => pure .real
    let tys ← free.mapM tyOf
    match free.reverse with
    | [] => fail E.unsupported
    | last :: _ =>
      let sc : Scope := (free.zip tys).reverse ++ outer
      let (p, pty) ← Elab.term 100000 sc none φ
      if pty != .prop then fail E.type
      let lty := (tys.getLast?).getD .real
      -- the predicate is applied to the last variable where all of them are bound,
      -- so `φ` is shifted past its own (unused) argument
      pure ((free.zip tys).map fun (v, t) => (⟨v, t, if v == last then some (.lam lty .tt (shift 1 0 p)) else none⟩ : BindInfo))
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
        out := out ++ (← nounBindersImplicit np ((before ++ out).map fun b => (b.name, b.ty)).reverse)
      | _ => fail E.unsupported
    pure out
where
  /-- `Let $x\in(0,1]$ and $e\in[0,x]$`: a domain may use the variables bound
  before it; its predicate is applied where they and the variable are bound. -/
  everyAfter (before : List BindInfo) (vs : List Codes) (d : MT) : M (List BindInfo) :=
    everyIn (before.map fun b => (b.name, b.ty)).reverse vs d
  /-- The same, with the domain in the scope `sc` of the binders around it. -/
  everyIn (sc : Scope) (vs : List Codes) (d : MT) : M (List BindInfo) := do
    -- `(x,y)\in K` (`@tuplein K`): the components of a pair in a set of pairs, a set of the
    -- scope or of the article; each has the type of its place, and the last one carries the
    -- condition that the pair is in `K`
    if let .app (.id tup) [d'] := d then
      if tup == w!"@tuplein" then
        let (dt, dty) ← Elab.term 100000 sc none d'
        let n := vs.length
        let (tys, res) := (List.range n).foldl (fun (acc : List Ty × Ty) _ => match acc.2 with
          | .fn a b => (acc.1 ++ [a], b)
          | r => (acc.1, r)) (([] : List Ty), dty)
        if tys.length != n || res != .prop then
          fail E.finding (w!"$(" ++ (vs.intersperse [44]).flatten ++ w!")\\in…$: the set is not a set of such tuples")
        let args := (List.range n).map fun i => if i + 1 == n then Tm.loc 0 else Tm.loc (n - i)
        let p := Tm.lam (tys.getLastD .real) .tt (args.foldl Tm.app (shift (n + 1) 0 dt))
        return (vs.zip tys).zipIdx.map fun ((v, ty), i) => (⟨v, ty, if i + 1 == n then some p else none⟩ : BindInfo)
    -- a multi-index: its components
    let (vs, d) := match vs, multiIndex d with
      | [v], some (base, n) => ((List.range n).map fun k => v ++ [95] ++ (Nat.toDigits 10 (k + 1)).map Char.toNat, base)
      | _, _ => (vs, d)
    -- (`x_1,\ldots,x_n\in\mathbb{R}` with a letter `n` that nothing defines, `Let $a<b$.`
    -- with `b`: a number bound with the variables, before them)
    let st0 ← get
    let (ty, p, pre) ← tryCatch (do let (t, q) ← binderDomain vs d sc; pure (t, q, ([] : List BindInfo))) fun e => do
      -- (also an end of an interval, `Let $a<b$.`: `b` a number bound before `a`)
      let some h := (match d with
          | .app (.id s) [_, .id h, _] => if s == w!"@seq" then some h else none
          -- (`u\in\mathbb{R}^n` with the field `vectors`: the dimension, a number bound before)
          | .sup (.id r) (.id h) => if r == w!"\\mathbb{R}" then some h else none
          | .ival lo hi _ _ => match lo, hi with
            | .id h, _ => if h == e.detail then some h else (match hi with | .id h' => some h' | _ => none)
            | _, .id h => some h
            | _, _ => none
          | _ => none) | throw e
      if !(e.code == E.undefined || e.code == E.free) || e.detail != h || sc.any (·.1 == h) then throw e
      set st0
      let (t, q) ← binderDomain vs d ((h, .real) :: sc)
      pure (t, q, [(⟨h, .real, none⟩ : BindInfo)])
    let (bis, _) := vs.foldl (fun (acc, j) v =>
      (acc ++ [(⟨v, ty, p.map (shift (j + 1) 0)⟩ : BindInfo)], j + 1)) (([] : List BindInfo), 0)
    pure (pre ++ bis)

/-- The binders among `bs` whose variables are `used`, in their order. A used binder
whose domain uses the binders before it (`e\in[0,x]`) keeps them all. -/
def binderInfos (b : Bind) (before : List BindInfo := []) : M (List BindInfo) := do
  declaredInts (← binderInfosRaw b before)

/-- The binders of `env` without those named in `names` (rebound by a new binder) and
without the binders whose domains use one of them (`For every cyclic group $X$ and every
subgroup $Y$ of $X$, …` before `Let $X$ be a group`: `Y` was about the old `X`); the domains
of the others no longer count the removed binders. -/
def dropShadowed (env : List BindInfo) (names : List Codes) : List BindInfo := Id.run do
  let mut removed : List Nat := []
  let mut out : List BindInfo := []
  for (b, j) in env.zipIdx do
    let mentions (i : Nat) : Bool := b.pred.any fun p => Tm.subst (.num 0) (j - i) p != Tm.subst (.num 1) (j - i) p
    if names.contains b.name || removed.any mentions then
      removed := removed ++ [j]
    else
      -- (lower the indices past the removed binders, the farthest first: a nearer one keeps
      -- its index)
      let p := removed.foldl (fun (acc : Option Tm) i => acc.map (Tm.subst (.num 0) (j - i))) b.pred
      out := out ++ [{ b with pred := p }]
  return out

def usedBinders (bs : List BindInfo) (used0 : List Codes) : List BindInfo :=
  -- (a binder whose condition is about a used variable is used too: `Let $K$ be a field
  -- with $\operatorname{char}(K)=p>0$` says what `p` is)
  let mentions (j i : Nat) : Bool := match bs[j]? with
    | some b => b.pred.any fun p => Tm.subst (.num 0) (j - i) p != Tm.subst (.num 1) (j - i) p
    | none => false
  let step (u : List Codes) : List Codes :=
    u ++ ((bs.zipIdx.filter fun (b, j) => !u.contains b.name &&
      (bs.zipIdx.any fun (b', i) => i < j && u.contains b'.name && mentions j i)).map (·.1.name))
  let used := step (step (step used0))
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
      !(st.globs.zipIdx.any fun (g, i) => g.key == n && !g.family && Elab.visibleIn st i) && !constName n && !st.vocab.symbols.any (·.sym == n) && !st.vocab.methods.any (·.op == .fn n)).eraseDups
    -- (it may also use the variables bound before: `Let $c>0$. Let $v$ be a real number
    -- with … and $|v|<c$.`)
    fr.any (fun n => out.any (·.name == n)) && fr.all fun n => out.any (·.name == n) || before.any (·.name == n)
  for b in binds do
    match b with
    | .every vs d =>
      if !vs.isEmpty && vs.all (fun n => out.any (·.name == n)) then
        -- (`(x,y)\in K` of a pair of variables bound before: the pair is in `K`)
        let cs := match d with
          | .app (.id tup) [d'] =>
            if tup == w!"@tuplein" then [MT.chain (.tuple (vs.map MT.id)) [(.mem, d')]] else vs.map fun v => condOfDomain v d
          | _ => vs.map fun v => condOfDomain v d
        out ← attachCond before out (match cs with | [c] => c | _ => .conj cs)
      else out := out ++ (← binderInfosRaw.everyAfter (before ++ out) vs d)
    | .noun np => out := out ++ (← nounBindersImplicit np ((before ++ out).map fun b => (b.name, b.ty)).reverse)
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
  | .everyNP np b _ => b :: (mathsOf np).filterMap Math.parseFormula
  | .everyIs np _ _ => (mathsOf np).filterMap Math.parseFormula
  | .everyMod np md => ((mathsOf np) ++ (mathsOf md)).filterMap Math.parseFormula
  | .exists_ m => [m]
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
  | .solutions _ e _ => [e]
  | .under _ c => clauseMaths c
  | .forEveryNP c np => clauseMaths c ++ (mathsOf np).filterMap Math.parseFormula
  -- (with the sets of a signature, `there is a function $w\colon V\to\mathbb{R}$`: `V` may be
  -- a set that the result binds)
  | .existsNP np _ (some c) => clauseMaths c ++ (mathsOf np).filterMap fun ts => Math.parseFormula ts <|> Math.parseSig ts
  | .existsNP np _ none => (mathsOf np).filterMap fun ts => Math.parseFormula ts <|> Math.parseSig ts
  | .existsNPs nps cs => clauseMathsAll cs ++ (nps.flatMap mathsOf).filterMap fun ts => Math.parseFormula ts <|> Math.parseSig ts
  | .countNP np _ _ (some c) => clauseMaths c ++ (mathsOf np).filterMap Math.parseFormula
  | .countNP np _ _ none => (mathsOf np).filterMap Math.parseFormula
  | .noneExist c => clauseMaths c
  | .firstOf a b => clauseMaths a ++ clauseMaths b
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

mutual
/-- The domains of the binders inside a clause (`there is $x\in U$ such that …`,
`… for every $x\in U$`): a domain may be a set that the result binds. -/
def innerDoms : Clause → List MT
  | .thereIs b c | .under b c =>
    (match b with
      | .every _ d => [d]
      | .many bs => bs.filterMap fun b' => match b' with | .every _ d => some d | _ => none
      | _ => []) ++ innerDoms c
  | .scoped _ _ (some d) _ => [d]
  -- (the clauses about objects that exist: `there is a function $w$ such that … for every
  -- $v\in V$`)
  | .existsNP _ _ (some c) => innerDoms c
  | .existsNPs _ cs => innerDomsAll cs
  | _ => []
def innerDomsAll : List Clause → List MT
  | [] => []
  | c :: cs => innerDoms c ++ innerDomsAll cs
end

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
  -- (a pair: the first variable alone is a random variable of the vocabulary, `randomVar`)
  | some (_, _, some _, df, _, _) =>
    if ms.any (usesRandomPair 64) || (match df with | some d => ids.contains d | none => false)
    then [w!"\\mathbb{P}"] else []
  | _ => []

/-- The free variables of a clause, its trailing definitions and the implicit
parameters of the definitions it uses (for the binders it inherits). -/
def clauseFree (st : St) (bound : List Codes) (cl : CClause) : List Codes :=
  let ms := clauseMaths cl.clause ++ cl.defs ++
    -- (only a letter that is a set bound before: the other domains are as they were)
    (innerDoms cl.clause).filterMap (fun d => match d with
      | .id n => if n.length == 1 then some d else none
      -- (`for every $(x,y)\in K$`: the set of pairs)
      | .app (.id tup) [d'] => if tup == w!"@tuplein" then some d' else none
      | _ => none)
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
  | none =>
    -- `$H$ is a normal subgroup of $G$`: a noun with a complement
    if let .math mt := o then
      let nouns := (← get).vocab.nouns.filter fun n => n.ty == s.2 && !n.onDomain &&
        (n.sing == ws.map PItem.w || n.plural == ws.map PItem.w) &&
        (n.arg.any fun (pw, _, _) => pw.contains w!"of")
      if !nouns.isEmpty then
        let v ← term F sc none mt
        let fits := nouns.filter fun n => n.arg.any fun (_, aty, _) => aty == v.2 || aty == .real
        match fits with
        | [n] =>
          if let some (_, aty, rel) := n.arg then
            let a ← if aty == .real then Elab.asReal v else pure v.1
            return Tm.mkAnd (Notation.betaApply n.pred [s.1]) (Notation.betaApply rel [a, s.1])
        | _ => pure ()
    fail E.noun ((phrase.intersperse [32]).flatten)

def predicate (sc : Scope) (s : Tm × Ty) (phrase : List Codes) (o : Obj) : M Tm := do
  let some i := lookupWords (← get).preds phrase | vocabOf sc s phrase o
  let g := ((← get).globs[i]?).getD default
  match g.ty with
  | .fn _ (.fn b .prop) => do
    let ot ← object sc b o
    let (t, _) ← applyAll (.glob i) g.ty g.doms [s, (ot, b)]
    pure t
  | _ => fail E.type

/-- The subject of a predicate: a formula, or a sequence written by its terms (`$(a_n^2)$
converges to $0$`, `0` at the numbers that are no natural numbers, as the article's
sequences). -/
def subjTerm (sc : Scope) (s : MT) : M (Tm × Ty) := do
  -- (`the function $f(x)=x^2$ is differentiable at $0$`, `the map $x\mapsto|x|$ is even`: the
  -- real function of `x` on the line, its values defined where the claim uses them)
  if let .mapsto (.id v) body := s then
    return ← Elab.lam F sc (.id v) [.real] (some .real) body
  if let some i ← Elab.seqTermVar sc s then
    let b ← Elab.asReal (← term F ((i, .real) :: sc) none s)
    return (.lam .real .tt (.cases (.app (.prim .isNat) (.loc 0)) b (.num 0)), .fn .real .real)
  term F sc none s

def subjectTm (sc : Scope) : Subj → M (Tm × Ty)
  -- (`the function $f(x)=x^2$ is differentiable at $0$`: the real function of `x`, its values
  -- defined where the claim uses them)
  | .math (.mapsto (.id v) body) => Elab.lam F sc (.id v) [.real] (some .real) body
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

/-- Is a function or a family that a sentence of this context defines local to its
environment? One defined inside a result or a proof is; one defined in the running text
or in a definition environment (`\begin{definition}`) is a symbol of the article. -/
def localDef (c : SentCtx) : Bool := match c.ctx.kind with
  | .text => false
  | .result n => n != w!"definition"
  | _ => true

/-- The definition `g` with the arguments `all` and the right-hand side `rhs`, which may
use the symbol that it defines: `a_n\coloneqq 2a_{n-1}+1`. Such a recursive definition
describes its function: the one function `F` with `F(x) = e(F, x)` at every point `x`
of the domain (and, so that there is one, `0` elsewhere, where the symbol is never
read). That exactly one such function exists is the definedness of the definition; its
right-hand side is read as it stands, so `a_{n-1}` asks that `n-1` lies in the domain.

The values that a sequence was given before (`Let $a_0\coloneqq 1$`) belong to it: its
domain is then the stated one together with these indices. -/
def recDef (g : Glob) (all : List BindInfo) (rhs : MT) : M (Nat × Ty) := do
  let sc : Scope := (all.map fun b => (b.name, b.ty)).reverse
  let lams := fun (bs : List BindInfo) (v : Tm) =>
    bs.foldr (fun b t => Tm.lam b.ty (holdsAt b.pred (.loc 0)) t) v
  let st ← get
  match ← tryCatch (Sum.inl <$> term F sc none rhs) (fun e => pure (Sum.inr e)) with
  | .inl (v, vty) =>
    let i ← addGlob { g with ty := all.foldr (fun b t => Ty.fn b.ty t) vty, doms := all.map (·.pred) } (lams all v)
    pure (i, vty)
  | .inr e =>
    let own := e.code == E.undefined && e.detail == g.key && !g.key.isEmpty
    if !own || all.isEmpty then throw e
    if all.any (·.ty != .real) then
      fail E.finding (w!"the definition of " ++ g.key ++ w!" uses " ++ g.key ++ w!" itself: a recursive definition has numbers as its arguments")
    set st
    let n := all.length
    -- the values given before: `a_0`, `a_1`
    let bases : List (Nat × Nat) :=
      if n != 1 || !g.family then [] else
      st.globs.zipIdx.filterMap fun (o, j) =>
        let ds := o.key.drop (g.key.length + 1)
        if visibleIn st j && !o.family && o.ty == .real && (st.implicits.lookup j).isNone &&
            o.key.take (g.key.length + 1) == g.key ++ [95] && !ds.isEmpty && ds.all (fun c => 48 ≤ c && c ≤ 57) then
          some (ds.foldl (fun a c => a * 10 + (c - 48)) 0, j)
        else none
    let all' : List BindInfo := match all, bases with
      | [b], _ :: _ =>
        match b.pred with
        | some p => [{ b with pred := some (.lam .real .tt
            (bases.foldr (fun (k, _) t => Tm.or (.eq (.loc 0) (.num k)) t) (.app (Tm.shift 1 0 p) (.loc 0)))) }]
        | none => all
      | _, _ => all
    let ty := all.foldr (fun b t => Ty.fn b.ty t) Ty.real
    let i ← addGlob { g with ty, doms := all'.map (·.pred) } (lams all' (.undef .real))
    let (v, vty) ← tryCatch (term F sc none rhs) fun e' => do set st; throw e'
    if vty != .real then
      fail E.finding (w!"the definition of " ++ g.key ++ w!" uses " ++ g.key ++ w!" itself: a recursive definition has numbers as its values")
    let fapp := (List.range n).foldl (fun f k => Tm.app f (.loc (n - 1 - k))) (Tm.loc n)
    let dom := fun (bs : List BindInfo) => bs.zipIdx.foldr
      (fun (b, k) t => Tm.mkAnd (Tm.shift (n - 1 - k) 0 (holdsAt b.pred (.loc 0))) t) Tm.tt
    let d := dom all
    let d' := dom all'
    let step := if d == .tt then Tm.eq fapp (Tm.abstractGlob i n v) else Tm.imp d (.eq fapp (Tm.abstractGlob i n v))
    let parts := bases.map (fun (k, j) => Tm.imp (.eq (.loc 0) (.num k)) (.eq fapp (.glob j))) ++ [step] ++
      (if d' == .tt then [] else [Tm.imp (.not d') (.eq fapp (.num 0))])
    let inner := parts.foldr Tm.mkAnd Tm.tt
    let body := all.foldr (fun b t => Tm.all b.ty t) inner
    let value := lams all' ((List.range n).foldl (fun f k => Tm.app f (.loc (n - 1 - k))) (Tm.the ty body))
    modify fun st => { st with values := st.values.set i value }
    pure (i, .real)

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
    let (i, vty) ← recDef ⟨key, .fn b.ty .real, [b.pred], family, 1⟩ [b] rhs
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
    if localDef c then modify fun st => { st with locals := st.locals ++ [(i, c.ctx.env)] }
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
      let (i, _) ← recDef { key := k, ty := .real, doms := [], family := true, indices := names.length } all rhs
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
          let (i, _) ← recDef ⟨k, .real, [], true, 1⟩ all rhs
          if !imp.isEmpty then modify fun st => { st with implicits := st.implicits ++ [(i, imp.map (·.name))] }
          ds := ds ++ [i]
          continue
      let names ← args.mapM fun a => match a with | .id n => pure n | _ => fail E.unsupported
      if names != bs.map (·.name) then fail E.unsupported
      let some key := Elab.symKey h | fail E.unsupported
      let all := imp ++ bs
      let (i, _) ← recDef ⟨key, .real, [], false, 1⟩ all rhs
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
  -- (the object a noun's complement names, `subgroup of $G$`)
  let preps : List Codes := (V.nouns.filterMap fun n => n.arg.map (·.1)).flatten.eraseDups
  let argIdx : List Nat := (List.range np.length).filter fun k => match (np[k]? : Option Chunk), (np[k + 1]? : Option Chunk) with
    | some (Chunk.w p), some (Chunk.m _) => k > 0 && preps.contains (Grammar.lower p)
    | _, _ => false
  if mods.isEmpty && argIdx.isEmpty then return np
  let mut drop : List Nat := argIdx.map (· + 1)
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
  -- (`Suppose that $x_1>0$.` after a sequence `x` of the scope: its term, no new variable)
  | .every vs _ => vs.map fun v =>
    let bs := st.envBinders ++ st.fixed.map (·.2)
    ((bs.find? fun b =>
      (match b.ty with | .fn .real t => t == .real || Elab.isBase t | _ => false) &&
      v.length > b.name.length + 1 && v.take (b.name.length + 1) == b.name ++ [95] &&
      (v.drop (b.name.length + 1)).all fun c => 48 ≤ c && c ≤ 57).map (·.name)).getD v
  | .noun np => (mathsOf (withoutSlotArgs st.vocab np)).flatMap fun ts =>
    match (Grammar.seqBound ts).bind fun (l, _) => Grammar.seqVars l with
    | some (x, _, _, _) => [x]
    | none => npVars [.m ts]
  | .ifCond φ =>
    let free := ((dropBoundIndices st φ (freeIds 64 [] φ)).filter fun n => !(st.globs.zipIdx.any fun (g, i) => g.key == n && !g.family && Elab.visibleIn st i) && !constName n && !st.vocab.symbols.any (·.sym == n) && !st.vocab.methods.any (·.op == .fn n)).eraseDups
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
    -- (a signature, `f\colon A\to B`, whose sets may be variables of the result)
    | none => ((Math.parseFormula ts) <|> (Math.parseSig ts)).toList
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
  -- (the binders' domains may use the subject: `for every $g\in G$`)
  let before : List BindInfo := sc.reverse.map fun (n, t) => ⟨n, t, none⟩
  match cond with
  | .formula f binds =>
    let bs := (← bindersInfos binds before)
    pure (wrap bs (← prop (scopeOf bs ++ sc) none f))
  | .mono binds m mono =>
    let bs := (← bindersInfos binds before)
    pure (wrap bs (← monoTm (scopeOf bs ++ sc) m mono))
  | .clause _ => fail E.unsupported

/-- `We call a copula $C$ NAME (ABBR) if COND.`: the notion `λ C, COND`, named by
`NAME` and `ABBR`. -/
def defNotion (subj : List Chunk) (name abbr : List Codes) (cond : NotionCond)
    (clauseBody : Option (Scope → M Tm) := none) (noun : Bool := false) : M (List Nat × List Nat) := do
  -- (`is called a NAME`: the name of a kind of object, `Let $G$ be a NAME`, `every NAME`)
  let asNoun (i : Nat) : List (List Codes × Nat) :=
    if !noun || name.contains w!"-" then [] else
    [(name, i), (name.dropLast ++ (name.getLast?.map (· ++ [115])).toList, i)]
  let st0 ← get
  -- `Let $G$ be a group. An element $g\in G$ is called NAME if …`: a notion of the objects
  -- of the result's variables (`G`): an object is NAME if it is, for some values of them
  let env := st0.envBinders
  let viaEnv ← match subj with
    | [.m [.id _]] => pure none
    | np =>
      if env.isEmpty then pure none else
      tryCatch (do let _ ← nounPhrase np; set st0; pure none) fun e => do
        set st0
        if e.code != E.undefined && e.code != E.free then throw e
        let outer := scopeOf env
        let s ← nounPhrase np outer
        if s.name.isEmpty then fail E.unsupported
        let sc := (s.name, s.ty) :: outer
        let body ← match cond, clauseBody with
          | .clause _, some cb => cb sc
          | _, _ => notionBody sc cond
        let t := Tm.and (holdsAt s.pred (.loc 0)) body
        -- (the object outermost, the variables inside: `λ g, ∃ G, … ∧ t`)
        let n := env.length
        let t' := Tm.subst (.loc n) 0 t
        let ex := env.foldr (fun b acc => Tm.ex b.ty (match b.pred with
          | some q => .and (.app q (.loc 0)) acc
          | none => acc)) t'
        pure (some (s, ex))
  if let some (s, ex) := viaEnv then
    let i ← addGlob ⟨[], .fn s.ty .prop, [none], false, 1⟩ (.lam s.ty .tt ex)
    let names := [name] ++ (if abbr.isEmpty then [] else [abbr])
    modify fun st => { st with notions := st.notions ++ names.map (·, i), notionSubject := some s }
    return ([i], [])
  -- `Let $G$ be a group. We say that $G$ is NAME if …`: a notion of the objects of that
  -- variable of the result: an object is NAME if it is, for some values of the others
  let envSubj : Option Nat := match subj with
    | [.m [.id v]] => if st0.notionSubject.any (·.name == v) then none else env.findIdx? (·.name == v)
    | _ => none
  if let some k := envSubj then
    let some b := env[k]? | fail E.unsupported
    let body ← match cond, clauseBody with
      | .clause _, some cb => cb (scopeOf env)
      | _, _ => notionBody (scopeOf env) cond
    let chain := ((List.range env.length).zip env).foldr (fun (jb : Nat × BindInfo) acc =>
        let inner := match jb.2.pred with
          | some q => Tm.and (.app q (.loc 0)) acc
          | none => acc
        if jb.1 == k then Tm.app (.lam jb.2.ty .tt inner) (.loc k) else Tm.ex jb.2.ty inner) body
    let i ← addGlob ⟨[], .fn b.ty .prop, [none], false, 1⟩ (.lam b.ty .tt chain)
    let names := [name] ++ (if abbr.isEmpty then [] else [abbr])
    modify fun st => { st with notions := st.notions ++ names.map (·, i) }
    return ([i], [])
  let s ← match subj with
    | [.m [.id v]] => match (← get).notionSubject with
      | some b => if b.name == v then pure b else fail E.free v
      | none => fail E.free v
    | np => nounPhrase np
  if s.name.isEmpty then fail E.unsupported
  let body ← match cond, clauseBody with
    | .clause _, some cb => cb (scopeOf [s])
    | _, _ => notionBody (scopeOf [s]) cond
  let i ← addGlob ⟨[], .fn s.ty .prop, [s.pred], false, 1⟩ (.lam s.ty (holdsAt s.pred (.loc 0)) body)
  let names := [name] ++ (if abbr.isEmpty then [] else [abbr])
  modify fun st => { st with notions := st.notions ++ names.map (·, i), nouns := st.nouns ++ asNoun i, notionSubject := some s }
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
  -- (`of the form $2k+1$`, of numbers)
  if (ofFormOf np).isSome then true else
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

/-- The domain of a map bound by a signature in this result or its proof
(`$\\varphi\\colon G\\to H$`), as a predicate in the scope `sc`. -/
def sigDomain (sc : Scope) (k : Codes) : M (Option Tm) := do
  let st ← get
  if (Elab.lookupLocal sc k).isNone then return none
  -- (an infinite sequence `(a_n)`: its terms are those at the natural numbers)
  if st.infSeqs.any (fun (e, n) => n == k && (e == st.curEnv || st.curProved == some e)) then
    return some (.lam .real .tt (.app (.prim .isNat) (.loc 0)))
  match st.sigDoms.find? fun (e, n, _) => n == k && (e == st.curEnv || st.curProved == some e) with
  | some (_, _, d, _) => tryCatch (do let (_, p) ← domainOf false d sc; pure p) fun _ => pure none
  | none => pure none

/-- The codomain of such a map, likewise. -/
def sigCodomain (sc : Scope) (k : Codes) : M (Option Tm) := do
  let st ← get
  if (Elab.lookupLocal sc k).isNone then return none
  match st.sigDoms.find? fun (e, n, _) => n == k && (e == st.curEnv || st.curProved == some e) with
  | some (_, _, _, c) => tryCatch (do let (_, p) ← domainOf false c sc; pure p) fun _ => pure none
  | none => pure none

/-- Does the complement `ts` elaborate to the type of the slot of `in $v$` of `m`? -/
def complementFits (sc : Scope) (m : Modifier) (ts : List MTok) : M Bool := do
  let some mt := Math.parseFormula ts | return false
  let st0 ← get
  let r ← tryCatch (do let (_, t) ← Elab.term 100000 sc none mt; pure (some t)) fun _ => pure none
  set st0
  -- (the slot of `in $v$`, the last one)
  let k := m.phrase.foldl (fun n i => match i with | .v => n + 1 | _ => n) 0
  match r, (Notation.slotTys k m.pred).getLast? with
  | some t, some want => pure (t == want)
  | _, _ => pure false

/-- The complement of the object `x` (`G` of `Let $H$ be a subgroup of $G$`), where the
vocabulary has the adjective `a` relative to a structure (`normal in $G$`). -/
def relativeAdj (sc : Scope) (x : Tm × Ty) (a : Codes) : M (Option (List MTok)) := do
  let st ← get
  let some k := (match x.1 with | .loc i => (sc[i]?).map (fun (p : Codes × Ty) => p.1) | _ => none) | return none
  let some (_, _, ts) := st.complements.find? (fun ((e, n, _) : Nat × Codes × List MTok) => n == k && (e == st.curEnv || st.curProved == some e))
    | return none
  let some m := st.vocab.mods.find? (fun m => m.ty == x.2 && !m.prenominal && m.phrase == [PItem.w a, PItem.w w!"in", PItem.v])
    | return none
  -- (only of an object of the modifier's kind: `closed in $\tau$` is of a topology, not of
  -- the set `\mathbb{R}` that `compact subset of $\mathbb{R}$` names)
  if !(← complementFits sc m ts) then return none
  return some ts

/-- `$\lambda$ is real`, `… is a real number`, said of a real number: every real number is
one, and the article means a number that need not be real (a complex eigenvalue or root), which
the field does not read. -/
def realOfReal (ty : Ty) (ws : List Codes) : M Unit := do
  if ty == .real && [[w!"real"], [w!"real", w!"number"], [w!"real", w!"numbers"], [w!"reals"]].contains ws then
    fail E.finding (w!"says that a real number is real, which every real number is: the article means a number that " ++
      w!"need not be real (a complex eigenvalue or root), which this field does not read; the field complex reads " ++
      w!"`is real` of a complex number")

/-- `[a|an] NP` or `ADJ[, ADJ] [and ADJ]` about the term `x`: a noun of the vocabulary
(with its modifiers), or prenominal modifiers alone. The type of `x` decides between
modifiers with the same words. -/
def vocabPredicate (sc : Scope) (x : Tm × Ty) (cs : List Chunk) : M Tm := do
  let V := (← get).vocab
  -- (`$n$ is of the form $2k+1$`: the number is a value of the formula)
  if let some (e, []) := ofFormOf cs then
    if x.2 != .real then fail E.type
    let p ← ofFormBody ((w!"@obj", .real) :: sc) w!"@obj" e
    return Notation.betaApply (.lam .real .tt p) [x.1]
  let cs := (kw [w!"a"] cs <|> kw [w!"an"] cs <|> kw [w!"the"] cs).getD cs
  -- (`$\lambda$ is real`, `… is a real number`, of a real number: every real number is one, and
  -- the article means a number that need not be real, a complex eigenvalue or root)
  let ws := cs.filterMap fun c => match c with | .w w => some w | _ => none
  if ws.length == cs.length then realOfReal x.2 ws
  -- (adjectives of an infinite sequence, `$(a_n)$ is increasing and bounded`: properties of
  -- its terms)
  let stS ← get
  let isSeq : Bool := match x with
    | (.loc i, .fn .real .real) => match sc[i]? with
      | some (k, _) => stS.infSeqs.any fun (e, n) => n == k && (e == stS.curEnv || stS.curProved == some e)
      | none => false
    -- (a sequence written by its terms, `$(a_n^2)$`: `subjTerm`)
    | (.lam .real .tt (.cases (.app (.prim .isNat) (.loc 0)) _ (.num 0)), _) => true
    | _ => false
  if isSeq then
    let rec parts : List Chunk → List (List Codes) → List Codes → Option (List (List Codes))
      | [], acc, cur => if cur.isEmpty then none else some (acc ++ [cur])
      | .w w :: r, acc, cur =>
        if w == w!"and" then (if cur.isEmpty then none else parts r (acc ++ [cur]) [])
        else parts r acc (cur ++ [w])
      | .p 44 :: r, acc, cur => if cur.isEmpty then none else parts r (acc ++ [cur]) []
      | .p 45 :: r, acc, cur => parts r acc cur
      | _, _, _ => none
    if let some ps := parts cs [] [] then
      if let some ts := ps.mapM (seqAdjective x.1) then return conjAll ts
  -- (the subject's domain, for a noun of maps meant on one: `$\\varphi$ is a homomorphism`)
  let subjDom : Option Tm ← match x.1 with
    | .loc i => match sc[i]? with
      | some (k, _) => sigDomain sc k
      | none => pure none
    | _ => pure none
  let subjCod : Option Tm ← match x.1 with
    | .loc i => match sc[i]? with
      | some (k, _) => sigCodomain sc k
      | none => pure none
    | _ => pure none
  -- (an adjective of the vocabulary meant on the domain of the subject's signature,
  -- `$f$ is holomorphic` for `f\colon U\to\mathbb{C}`)
  if x.2 != .fn .real .real then
    if let some d := subjDom then
      let ws := cs.filterMap fun c => match c with | .w w => some w | _ => none
      if !ws.isEmpty && cs.all (fun c => match c with | .w _ | .p 45 => true | _ => false) then
        if let some e := V.adjectives.find? (fun e => e.ty == x.2 && e.onDomain && !e.onCodomain &&
            e.words == ws.map Grammar.lower) then
          return Notation.betaApply e.pred [x.1, d]
  -- (of a real function on the domain of its signature, `$f$ is uniformly continuous` for
  -- `f\colon[0,1]\to\mathbb{R}`: the property on that domain)
  if x.2 == .fn .real .real then
    -- (`surjective`, `bijective`: onto the codomain of the signature)
    if let some c := subjCod then
      let ws := cs.filterMap fun c => match c with | .w w => some w | _ => none
      if cs.all (fun c => match c with | .w _ | .p 45 => true | _ => false) then
        if let some body := fnOnto x.1 ws (subjDom.getD (.lam .real .tt .tt)) c then return body
    if let some d := subjDom then
      if d != .lam .real .tt .tt then
        let ws := cs.filterMap fun c => match c with | .w w => some w | _ => none
        if !ws.isEmpty && cs.all (fun c => match c with | .w _ | .p 45 => true | _ => false) then
          if let some body := fnAdjectiveOnNeg x.1 ws d then return body
          -- (an adjective of the vocabulary meant on the domain, `Riemann integrable`)
          if let some e := V.adjectives.find? (fun e => e.ty == x.2 && e.onDomain && !e.onCodomain &&
              e.words == ws.map Grammar.lower) then
            return Notation.betaApply e.pred [x.1, d]
  -- (the noun phrase is read in the scope of the sentence, `$H$ is a subgroup of $G$`; its
  -- predicate is stated where its variable would be bound, one binder further in)
  modify fun st => { st with sigDomPreset := subjDom.map (shift 1 0), sigCodPreset := subjCod.map (shift 1 0) }
  -- (a modifier of the subject's type with exactly these words is meant, not a noun with
  -- modifiers before it: `$h$ is a subadditive sequence`)
  let exactMod := V.mods.any fun m => m.ty == x.2 && !Notation.hasSlots m.phrase &&
    (match matchPhrase m.phrase cs with | some (none, []) => true | _ => false)
  -- (`$I$ is a prime ideal`, of an ideal `I` of `R`: a prime ideal of `R`, the object of the
  -- subject's complement, where the noun says nothing without one)
  let subjComp : Option (List MTok) := match x.1 with
    | .loc i => (sc[i]?).bind fun (p : Codes × Ty) =>
      (stS.complements.find? fun ((e, n, _) : Nat × Codes × List MTok) => n == p.1 && (e == stS.curEnv || stS.curProved == some e)).map
        fun (q : Nat × Codes × List MTok) => q.2.2
    | _ => none
  let withComp (e : Err) : M (Option BindInfo) := do
    let some ts := subjComp | throw e
    if !cs.all (fun c => match c with | .w _ | .p 45 => true | _ => false) then throw e
    let stC ← get
    let rec tryPreps : List Codes → M (Option BindInfo)
      | [] => do set stC; throw e
      | p :: ps => do
        set stC
        tryCatch (some <$> nounPhrase (cs ++ [.w p, .m ts]) sc) fun _ => tryPreps ps
    tryPreps [w!"of", w!"in", w!"over"]
  let np ← if exactMod then pure none else tryCatch (some <$> nounPhrase cs sc) fun e => do
    tryCatch (withComp e) fun e => do
    modify fun st => { st with sigDomPreset := none, sigCodPreset := none }
    if e.code == E.ambiguous then throw e else pure none
  modify fun st => { st with sigDomPreset := none, sigCodPreset := none }
  let np := np.map fun b => if sc.isEmpty then b else { b with pred := b.pred.map (lowerBy 1) }
  -- (a noun of another type: the words may be modifiers of the subject, below)
  let np := np.filter (·.ty == x.2)
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
        -- (`$(x_n)$ is a Cauchy sequence`, of a sequence in a space: after the adjectives, a noun
        -- of the subject's own objects, which says nothing more, `sequence in $X$`)
        if !acc.isEmpty && V.nouns.any (fun n => n.ty == x.2 &&
            ((n.sing.filterMap fun i => match i with | .w w => some w | _ => none).take (wordsOf cs).length == wordsOf cs ||
             (n.plural.filterMap fun i => match i with | .w w => some w | _ => none).take (wordsOf cs).length == wordsOf cs)) &&
            cs.all (fun c => match c with | .w _ => true | _ => false) then pure acc.reverse else
        -- (`$H$ is normal`, of a subgroup `H` of `G`: normal in `G`, where the vocabulary has the
        -- adjective relative to a structure)
        let cs : List Chunk ← match cs with
          | .w a :: rest => do
            let followed := match rest with | .w w :: _ => w == w!"in" | _ => false
            let rel ← if followed then pure none else relativeAdj sc x a
            match rel with
            | some ts => pure ([Chunk.w a, Chunk.w w!"in", Chunk.m ts] ++ rest)
            | none => pure cs
          | _ => pure cs
        -- (`$v$ is of even degree`, of a vertex `v` of `G`: a modifier `of even degree in $v$`
        -- that the words begin, of the object of the subject's complement)
        let cs : List Chunk ← do
          let stR ← get
          let direct := V.mods.any fun m => m.ty == x.2 && (if Notation.hasSlots m.phrase then
              (Notation.matchPrefix m.phrase cs []).isSome else (matchPhrase m.phrase cs).isSome)
          let key : Option Codes := match x.1 with
            | .loc i => (sc[i]?).map fun (p : Codes × Ty) => p.1
            | _ => none
          let comp? : Option (List MTok) := key.bind fun k =>
            (stR.complements.find? fun ((e, n, _) : Nat × Codes × List MTok) => n == k && (e == stR.curEnv || stR.curProved == some e)).map
              fun (q : Nat × Codes × List MTok) => q.2.2
          match comp?, direct with
          | some ts, false =>
            let cands := V.mods.filterMap fun m => if m.ty != x.2 || m.prenominal then none else
              match m.phrase.reverse with
              | .v :: .w i :: front =>
                if i != w!"in" || front.isEmpty then none else
                (Notation.matchPrefix front.reverse cs []).bind fun (_, r) =>
                  let next := match r with | .w w :: _ => w == w!"in" | _ => false
                  if next then none else some (m, cs.take (cs.length - r.length) ++ [Chunk.w w!"in", Chunk.m ts] ++ r)
              | _ => none
            let fitting ← cands.filterM fun (m, _) => complementFits sc m ts
            pure ((fitting.head?.map (·.2)).getD cs)
          | _, _ => pure cs
        -- (a modifier that follows its noun is stated too: `$x$ is orthogonal to $y$`, `$S$ is of measure zero`)
        let cands := V.mods.filterMap fun m => if m.ty == x.2 then
            if Notation.hasSlots m.phrase then (Notation.matchPrefix m.phrase cs []).map fun (_, r) => (m, r) else
            (matchPhrase m.phrase cs).bind fun (v, r) => if v.isNone then some (m, r) else none
          else none
        -- (several fields with the words: those whose variables the formulas fit, `dense in
        -- $[0,1]$` of a set of numbers, `dense in $\tau$` of a topology)
        let fitsSlots (m : Modifier) : M Bool := do
          if !Notation.hasSlots m.phrase then return true
          let some (args, _) := Notation.matchPrefix m.phrase cs [] | return false
          let st ← get
          let ok ← tryCatch (do
              for (a, t) in args.zip (Notation.slotTys args.length m.pred) do
                let some mt := Math.parseFormula a | fail E.unsupported
                let v ← term F sc none mt
                if t == .real then let _ ← Elab.asReal v else if v.2 != t then fail E.type
              pure true) fun _ => pure false
          set st
          pure ok
        let cands ← if (cands.map (·.1.field)).eraseDups.length > 1 then do
            let fit ← cands.filterM fun (m, _) => fitsSlots m
            pure (if fit.isEmpty then cands else fit)
          else pure cands
        match ← theMeaning (fun (m : Modifier) => m.pred) (·.field) cs cands with
        | some (m, r) =>
          -- (`$G$ is $3$-regular`: a modifier with variables, of their values)
          let some (args, _) := (if Notation.hasSlots m.phrase then Notation.matchPrefix m.phrase cs [] else some ([], r))
            | fail E.type
          let ts ← (args.zip (Notation.slotTys args.length m.pred)).mapM fun (a, t) => do
            let some mt := Math.parseFormula a | fail E.unsupported
            let v ← term F sc none mt
            if t == .real then Elab.asReal v else if v.2 == t then pure v.1 else fail E.type
          -- (a modifier of maps meant on the domain, and the codomain, of the subject's signature)
          if m.onDomain then
            let some d := subjDom | fail E.type
            if m.onCodomain then
              let some c := subjCod | fail E.type
              adjs f r (Notation.betaApply m.pred [d, c, x.1] :: acc)
            else adjs f r (Notation.betaApply m.pred [d, x.1] :: acc)
          else
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
    (on : Option MT) (defCod : Option Tm := none) : M Tm := do
  if ty == .real then
    if on.isSome then fail E.unsupported
    if a == [w!"positive"] then pure (.lt (.num 0) t)
    else if a == [w!"negative"] then pure (.lt t (.num 0))
    else if a == [w!"nonnegative"] then pure (.le (.num 0) t)
    else if a == [w!"nonpositive"] then pure (.le t (.num 0))
    -- (`$x$ is zero`, `the Lebesgue measure of $A$ is zero`)
    else if a == [w!"zero"] then pure (.eq t (.num 0))
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
          ([w!"increasing"], .monotone), ([w!"decreasing"], .antitone),
          ([w!"nonnegative"], .nonneg), ([w!"positive"], .pos), ([w!"differentiable"], .differentiable),
          ([w!"continuously", w!"differentiable"], .contDiff), ([w!"injective"], .injective),
          ([w!"lower", w!"semicontinuous"], .lowerSemicont), ([w!"upper", w!"semicontinuous"], .upperSemicont),
          ([w!"lipschitz"], .lipschitz)].lookup a).map Prim.fnProp
    -- (`monotone`: nondecreasing or nonincreasing)
    let p2 : Option (Prim × Prim) := if a == [w!"monotone"] then some (.fnProp .monotone, .fnProp .antitone)
      else if a == [w!"strictly", w!"monotone"] then some (.strictMonoOn, .fnProp .strictAnti) else none
    if let some (p, q) := p2 then
      let own := defDom.getD (.lam .real .tt .tt)
      match on with
      | none => return .or (Tm.app (.app (.prim p) t) own) (Tm.app (.app (.prim q) t) own)
      | some _ => fail E.unsupported
    -- (`surjective` and `bijective` of a function with a signature `f\colon X\to Y`: onto `Y`,
    -- from `X`)
    if on.isNone then
      if let some c := defCod then
        if let some body := fnOnto t a (defDom.getD (.lam .real .tt .tt)) c then return body
    -- (the other standard words, `constant`, `uniformly continuous`, `negative`, …, and the
    -- vocabulary's adjectives meant on a domain, `Riemann integrable`: on the domain)
    if p.isNone then
      let d ← match on with
        | some m => do let (_, d) ← domainOf true m sc; pure (d.getD (.lam .real .tt .tt))
        | none => pure (defDom.getD (.lam .real .tt .tt))
      if let some body := fnAdjectiveOnNeg t a d then return body
      if let some e := (← get).vocab.adjectives.find? (fun e => e.ty == ty && e.onDomain && !e.onCodomain && e.words == a) then
        return Notation.betaApply e.pred [t, d]
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
          if e.onCodomain then
            let some c := defCod | fail E.unsupported
            return Tm.app (.app (.app e.pred t) d) c
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
    (on : Option MT) (defCod : Option Tm := none) : M Tm := do
  let st0 ← get
  tryCatch (adjectiveTmCore sc t ty defDom a on defCod) fun e => do
    if on.isSome then throw e
    -- (relative to the object's structure, `normal` of a subgroup: `vocabPredicate`)
    if let [w] := a then
      if (← relativeAdj sc (t, ty) w).isSome then throw e
    let m? := st0.vocab.mods.find? fun m => m.ty == ty && !Notation.hasSlots m.phrase && !m.onDomain &&
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
  -- (the term is defined: `$\sup A$ exists`)
  | .exists_ m => do
    let (t, _) ← term F sc none m
    pure (Tm.defined t)
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
    let st0 ← get
    tryCatch (predicate sc st ph o) fun e => do
      -- (`$0$ is not a divisor of $n$`: the negation of `is a divisor of $n$`)
      if let w :: rest@(_ :: _) := ph then
        if w == w!"not" then
          set st0
          return .not (← clauseTm c sc onVar lastRhs (.pred s rest o))
      -- (`… is the reciprocal of $x$`, `… is the reciprocal of the determinant of $A$`: the value
      -- of a notion, also of a notion's value)
      let .w t :: _ := ph.map Chunk.w | throw e
      let arg ← match o with
        | .named name (some m) => pure (MT.app (.id w!"@the") (name.map (MT.text ∘ Grammar.lower) ++ [m]))
        | .math m => pure m
        | _ => throw e
      if Grammar.lower t != w!"the" || ph.length < 2 || !(e.code == E.noun || e.code == E.prose || e.code == E.unsupported) then throw e
      set st0
      let outer := MT.app (.id w!"@the") ((ph.drop 1).map (MT.text ∘ Grammar.lower) ++ [.text w!"of", arg])
      let r ← tryCatch (some <$> term F sc none outer) fun _ => pure none
      let some (v, vty) := r | do set st0; throw e
      if vty != st.2 || !(vty == .real || Elab.isBase vty) then do set st0; throw e
      pure (Tm.eq st.1 v)
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
        let b ← nounPhrase np sc
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
    -- `$\sum a_n$ converges`: the series of the terms of an infinite sequence `(a_n)` (from
    -- the index `0`; the start does not matter for convergence)
    let s : MT := match s with
      | .app (.id k) args =>
        if k != w!"@sumall" || !(names.all fun n => n == [w!"convergent"] || n == [w!"divergent"] || n == [w!"absolutely", w!"convergent"]) then s else
        let body := args.headD (.num 0)
        let isSeq (a : Codes) : Bool := (Elab.lookupLocal sc a).isSome &&
          st.infSeqs.any fun (e, n) => n == a && (e == st.curEnv || st.curProved == some e)
        let rec idxs : Nat → MT → List Codes
          | 0, _ => []
          | f + 1, m => match m with
            | .sub (.id a) (.id i) => if isSeq a then [i] else []
            | .add x y | .minus x y | .mul x y | .div x y | .frac x y | .sup x y => idxs f x ++ idxs f y
            | .neg x | .abs x => idxs f x
            | .app _ xs => xs.flatMap (idxs f)
            | _ => []
        let v? : Option Codes := match args with
          | [_, .id v] => some v
          | _ => match (idxs 30 body).eraseDups with
            | [v] => some v
            | _ => none
        match v? with
        | some v =>
          if (Elab.lookupLocal sc v).isSome || (idxs 30 body).isEmpty then s
          else .bigop true v (.num 0) (.id w!"\\infty") body
        | none => s
      | _ => s
    -- `$\sum_{k=0}^\infty a_k$ converges` (`is convergent`), `diverges`: of the series
    if let [[w]] := names then
      if w == w!"convergent" || w == w!"divergent" then
        if let .bigop true _ _ _ _ := s then
          if let (.guard (.and _ conv) _, _) ← subjTerm sc s then
            return (if w == w!"convergent" then conv else .not conv)
    -- (`… converges absolutely`, `is absolutely convergent`: the series of the absolute values)
    if names == [[w!"absolutely", w!"convergent"]] then
      if let .bigop true v lo hi body := s then
        if let (.guard (.and _ conv) _, _) ← subjTerm sc (.bigop true v lo hi (.abs body)) then
          return conv
    unless names.all (fun n => (st.notions.lookup n).isSome || knownStart st (nameChunks n)) do fail E.prose
    let x ← subjTerm sc s
    for n in names do
      if (st.notions.lookup n).isNone then realOfReal x.2 n
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
        -- (`for every $(x,y)\in K$`: the components, the last with its condition)
        let tupleIn := match d with | .app (.id tup) [_] => tup == w!"@tuplein" | _ => false
        if tupleIn then pure ((← binderInfosRaw.everyIn sc vs d).map (·, 0)) else
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
    -- (`$G$ has a Hamiltonian cycle`, without a noun `Hamiltonian cycle of`: the modifier
    -- `with a Hamiltonian cycle` of the subject)
    let st0 ← get
    let asMod : Option (MT × List Chunk) :=
      if unique || cl.isSome then none else
      let head := np.takeWhile fun ch => match ch with | .w w => w != w!"of" | .p 45 => true | _ => false
      match np.drop head.length with
      | .w o :: .m ts :: tail =>
        -- (`$G$ has a cycle of odd length`: the words after the subject go with the noun,
        -- `with a cycle of odd length`; also with formulas, `$p$ has a root in $\mathbb{C}$`)
        if o != w!"of" || head.isEmpty || !(tail.all fun ch => match ch with | .w _ | .m _ | .p 45 => true | _ => false) then none else
        (Math.parseFormula ts).map fun s => (s, head ++ tail)
      | _ => none
    -- (`there is a unique $y\in C$`: the variable with its domain)
    let mathVar : Option (Codes × MT) := match np with
      | [.m ts] => match Grammar.binderMath ts with
        | some ([v], d) => some (v, d)
        | _ => none
      | _ => none
    let b? ← tryCatch (do
        if let some (v, d) := mathVar then
          let before : List BindInfo := sc.reverse.map fun (n, t) => ⟨n, t, none⟩
          match ← binderInfosRaw (.every [v] d) before with
          | [b] => return some b
          | _ => fail E.unsupported
        let b ← match ← pdeNoun np with
          | some [b] => pure b
          | _ => nounPhrase np sc
        pure (some b)) fun e => do
      if !(e.code == E.noun || e.code == E.nounWords || e.code == E.type) || asMod.isNone then throw e
      set st0
      pure none
    match b?, asMod with
    | none, some (s, head) =>
      let first := match head.head? with
        | some (.w w) => (w.head?.map fun ch => [97, 101, 105, 111, 117, 65, 69, 73, 79, 85].contains ch).getD false
        | _ => false
      let art := if first then w!"an" else w!"a"
      let x ← subjTerm sc s
      vocabPredicate sc x ([Chunk.w w!"with", Chunk.w art] ++ head)
    | _, _ =>
    let some b := b? | fail E.unsupported
    -- (`there is a fixed point of $f$`: an object without a name, about which nothing more
    -- is said)
    if b.name.isEmpty && cl.isSome then fail E.unsupported
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
  | .countNP np mode k first => do
    -- (the vocabulary's modifier first, `with at least $2$ leaves`)
    let mut firstErr : Option Err := none
    if let some cl := first then
      let st0 ← get
      match ← tryCatch (Sum.inl <$> clauseTm c sc onVar lastRhs cl) fun e => do
          if e.code == E.prose || e.code == E.noun || e.code == E.unsupported || e.code == E.nounWords then
            set st0; pure (Sum.inr e)
          else throw e with
      | .inl t => return t
      | .inr e => firstErr := some e
    -- the noun phrase of one of the objects, in the singular (`ideals of $K$`: `ideal of $K$`;
    -- `one maximal ideal of $R$` is already)
    let V := (← get).vocab
    let head := np.takeWhile fun ch => match ch with
      | .w w => ![w!"of", w!"with", w!"in", w!"on", w!"at", w!"over", w!"to", w!"from", w!"satisfying"].contains w
      | .p 45 => true
      | _ => false
    -- (a noun with its complement, `ideals of $K$`: its last word in the singular)
    let byRule : Option (List Chunk) := match head.getLast? with
      | some (.w w) => (Grammar.DefForm.singular w).map fun w' => head.dropLast ++ [Chunk.w w'] ++ np.drop head.length
      | _ => none
    let bySet := (setOfElems V ([Chunk.w w!"set", Chunk.w w!"of"] ++ head)).map (· ++ np.drop head.length)
    let cands := if k ≤ 1 then [np] else byRule.toList ++ bySet.toList
    let st0 ← get
    let rec firstNP : List (List Chunk) → M BindInfo
      | [] => fail E.noun
      | [c] => do
        match ← pdeNoun c with
        | some [b] => pure b
        | _ => nounPhrase c sc
      | c :: rest => tryCatch (do
          match ← pdeNoun c with
          | some [b] => pure b
          | _ => nounPhrase c sc) fun _ => do set st0; firstNP rest
    -- (a noun phrase that is not the vocabulary's: the sentence is prose, or what stopped the
    -- modifier's reading)
    let b ← tryCatch (firstNP cands) fun e => do
      if let some e1 := firstErr then throw e1
      if e.code == E.noun || e.code == E.unsupported then fail E.prose else throw e
    -- `P y`, with `y` the innermost local (the predicate is stated under its binder)
    let px := holdsAt b.pred (.loc 0)
    -- (`P` of the `i`-th of `n` objects bound around it, the innermost `0`)
    let pAt (n i : Nat) : Tm := Tm.subst (.loc i) 0 (shift n 1 px)
    let conj (ts : List Tm) : Tm := match ts.reverse with
      | [] => .tt
      | t :: r => r.foldl (fun acc x => Tm.and x acc) t
    let disj (ts : List Tm) : Tm := match ts.reverse with
      | [] => .not .tt
      | t :: r => r.foldl (fun acc x => Tm.or x acc) t
    let pairs (n : Nat) : List (Nat × Nat) :=
      (List.range n).flatMap fun i => ((List.range n).filter (i < ·)).map fun j => (i, j)
    let exs (n : Nat) (body : Tm) : Tm := (List.range n).foldl (fun t _ => Tm.ex b.ty t) body
    let alls (n : Nat) (body : Tm) : Tm := (List.range n).foldl (fun t _ => Tm.all b.ty t) body
    -- at least `k`: `k` distinct objects
    let atLeast (n : Nat) (extra : Tm) : Tm :=
      exs n (conj ((List.range n).map (pAt n) ++ (pairs n).map (fun (i, j) => Tm.not (.eq (.loc i) (.loc j))) ++ [extra]))
    match mode with
    | 1 => pure (atLeast k .tt)
    | 2 =>
      -- (none: `$x$ has no square root`)
      if k == 0 then return .not (exs 1 (pAt 1 0))
      -- at most `k`: among any `k+1` of them, two are the same
      let n := k + 1
      pure (alls n (.imp (conj ((List.range n).map (pAt n))) (disj ((pairs n).map fun (i, j) => Tm.eq (.loc i) (.loc j)))))
    | _ =>
      -- exactly `k`: at least `k`, and every one is one of them
      let every := Tm.all b.ty (.imp (pAt (k + 1) 0) (disj ((List.range k).map fun i => Tm.eq (.loc 0) (.loc (i + 1)))))
      pure (atLeast k every)
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
  | .firstOf a b => do
    -- (the second reading where the first's noun phrase is not the vocabulary's)
    let st0 ← get
    tryCatch (clauseTm c sc onVar lastRhs a) fun e => do
      if !(e.code == E.prose || e.code == E.noun || e.code == E.unsupported || e.code == E.nounWords ||
          e.code == E.type || e.code == E.finding) then throw e
      set st0
      tryCatch (clauseTm c sc onVar lastRhs b) fun e' => do
        if e'.code == E.prose || e'.code == E.noun || e'.code == E.unsupported || e'.code == E.nounWords then throw e
        throw e'
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
  | .solutions kind e np => do
    -- the unknowns: the letters of the equation that nothing binds, in their order, each a
    -- number of the noun phrase (`positive integers`)
    let st ← get
    let unknowns := (freeIds 64 [] e).eraseDups.filter fun n => (Elab.lookupLocal sc n).isNone &&
      !(st.globs.zipIdx.any fun (g, i) => g.key == n && !g.family && Elab.visibleIn st i) && !constName n &&
      !st.vocab.symbols.any (·.sym == n)
    if unknowns.isEmpty then fail E.finding w!"an equation without unknowns: every letter of it is bound"
    -- (`e` and `i` alone are Euler's number and the imaginary unit elsewhere: as unknowns
    -- they would be read otherwise than written)
    if let some v := unknowns.find? (fun n => n == [101] || n == [105]) then
      fail E.finding (w!"the letter " ++ v ++ w!" as an unknown of an equation: name the unknowns (there are no integers $x,y$ with …)")
    let mut bs : List BindInfo := []
    for v in unknowns do
      let b ← nounPhrase (np ++ [.m [.id v]]) (scopeOf bs ++ sc)
      if b.name != v then fail E.unsupported
      bs := bs ++ [b]
    let (p, pty) ← Elab.term 100000 (scopeOf bs ++ sc) none e
    if pty != .prop then fail E.type
    match kind with
    | 2 =>
      -- infinitely many: the set of solutions, of points of `ℝⁿ`, is not finite
      if !(bs.all (·.ty == .real)) then fail E.type
      let k := bs.length
      let conds := bs.zipIdx.map fun (b, j) => shift (k - 1 - j) 0 (holdsAt b.pred (.loc 0))
      let body := conds.foldr (fun q acc => if q == .tt then acc else Tm.and q acc) p
      let set := bs.foldr (fun _ acc => Tm.lam .real .tt acc) body
      if k == 1 then
        pure (.not (.ex .real (.app (.app (.prim .cardIs) (shift 1 0 set)) (.loc 0))))
      else
        pure (.not (.app (.prim (.finiteN k)) set))
    | _ =>
      let ex := bs.foldr (fun b acc => Tm.ex b.ty (match b.pred with
        | some q => .and (.app q (.loc 0)) acc
        | none => acc)) p
      pure (if kind == 0 then .not ex else ex)
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
    -- (`… is zero` of a number: the standard adjective)
    if (match np with | [.w z] => z == w!"zero" | _ => false) then
      let x ← subjTerm sc s
      if x.2 == Ty.real then
        let p ← adjectiveTmCore sc x.1 x.2 none [w!"zero"] none
        return (if neg then .not p else p)
    -- words with which no phrase of the vocabulary starts are prose
    unless knownStart (← get) np do fail E.prose
    let x ← subjTerm sc s
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
    -- (`with exactly $n-1$ edges`: `with $n-1$ edges`; `with more than $k$ edges`: `with at least
    -- $\lfloor k\rfloor+1$ edges`, `fewer than`: `at most $\lceil k\rceil-1$`, of a number of objects)
    let counts : List (List Chunk) := match np with
      | .w w :: .w e :: .m k :: rest =>
        if w == w!"with" && e == w!"exactly" then [[Chunk.w w, .m k] ++ rest] else []
      | .w w :: .w m :: .w t :: .m k :: rest =>
        if w != w!"with" || t != w!"than" then [] else
        if m == w!"more" then [[Chunk.w w, .w w!"at", .w w!"least", .m ([.cmd w!"lfloor"] ++ k ++ [.cmd w!"rfloor", .sym 43, .digit 1])] ++ rest]
        else if m == w!"fewer" || m == w!"less" then [[Chunk.w w, .w w!"at", .w w!"most", .m ([.cmd w!"lceil"] ++ k ++ [.cmd w!"rceil", .sym 45, .digit 1])] ++ rest]
        else []
      | _ => []
    let singulars := singulars ++ counts
    let st0 ← get
    -- words that are not the vocabulary's are prose
    let p ← tryCatch (vocabPredicate sc x np) fun e => do
      let mut res : Option Tm := none
      for np' in singulars do
        if res.isNone then
          set st0
          res ← tryCatch (some <$> vocabPredicate sc x np') fun _ => pure none
      -- (`$A$ has determinant zero`, `with trace $0$`: the value of a notion of the subject,
      -- `the determinant of $A$ is zero`, where no modifier has the words)
      if res.isNone then
        let valueOf : Option (MT × Option MT) := match np with
          | .w w :: rest =>
            if w != w!"with" then none else
            let ws := rest.dropLast
            if ws.isEmpty || ws.length > 3 || !(ws.all fun ch => match ch with | .w _ => true | _ => false) then none else
            let the := MT.app (.id w!"@the") (ws.filterMap (fun ch => match ch with | .w t => some (MT.text t) | _ => none) ++ [.text w!"of", s])
            match rest.getLast? with
            | some (.w z) => if z == w!"zero" then some (the, none) else none
            | some (.m k) => (Math.parseFormula k).map fun v => (the, some v)
            | _ => none
          | _ => none
        if let some (the, v) := valueOf then
          set st0
          res ← tryCatch (some <$> match v with
              | some v => prop sc none (.chain the [(.eq, v)])
              | none => do
                let t ← Elab.term 100000 sc none the
                if t.2 != Ty.real then fail E.type
                adjectiveTmCore sc t.1 t.2 none [w!"zero"] none) fun _ => pure none
      match res with
      | some p => pure p
      | none =>
        if !singulars.isEmpty then set st0
        if e.code == E.noun || e.code == E.unsupported then fail E.prose e.detail else throw e
    pure (if neg then .not p else p)
  | .everyIs np names disj => do
    -- (the noun's complement may be a variable of the scope: `every subgroup of $G$`)
    let b ← nounPhrase np sc
    -- (`every subgroup of $G$`: the object has no name, but the scope needs one)
    let b := if b.name.isEmpty then { b with name := w!"\\everyobj" } else b
    if let some ts := complementOf np then
      modify fun st => { st with complements := (st.curEnv, b.name, ts) :: st.complements.filter (·.2.1 != b.name) }
    let st1 ← get
    for n in names do
      if (st1.notions.lookup n).isNone then realOfReal b.ty n
    -- (notions of the article; or adjectives and nouns of the vocabulary, `Every cyclic group
    -- $G$ is abelian`)
    let ps ← tryCatch (names.mapM (notionApp (.loc 0, b.ty))) fun e => do
      set st1
      tryCatch (names.mapM fun nm => vocabPredicate ((b.name, b.ty) :: sc) (.loc 0, b.ty) (nameChunks nm))
        fun _ => throw e
    pure (wrap [b] (if disj then disjAll ps else conjAll ps))
  | .everyMod np md => do
    let b ← nounPhrase np sc
    let b := if b.name.isEmpty then { b with name := w!"\\everyobj" } else b
    if let some ts := complementOf np then
      modify fun st => { st with complements := (st.curEnv, b.name, ts) :: st.complements.filter (·.2.1 != b.name) }
    let p ← vocabPredicate ((b.name, b.ty) :: sc) (.loc 0, b.ty) md
    pure (wrap [b] p)
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
      -- (without a domain, `the function $x\mapsto e^x$ is strictly increasing`: on the line)
      else if adjs.all (fun (_, on) => on.isNone) then
        let (fn, _) ← Elab.lam F sc (.id v) [.real] (some .real) body
        let ps ← adjs.mapM fun (a, _) => adjectiveTm sc fn (.fn .real .real) (some (.lam .real .tt .tt)) a none
        return conjAll ps
      else pure ()
    | _ => pure ()
    let (t, ty) ← subjTerm sc s
    -- a function's domain is the one its definition states
    -- (a variable of the sentence comes before a definition of the article with its letter)
    let defDom : Option Tm ← match Elab.symKey s with
      | some k => do
        if (Elab.lookupLocal sc k).isSome then sigDomain sc k else
        match ← lookupGlob k with
        | some (_, g) => pure (g.doms.head?).join
        | none => sigDomain sc k
      | none => pure none
    let defCod : Option Tm ← match Elab.symKey s with
      | some k => do
        if (Elab.lookupLocal sc k).isSome then sigCodomain sc k else
        match ← lookupGlob k with
        | some _ => pure none
        | none => sigCodomain sc k
      | none => pure none
    -- (an infinite sequence, `$(a_n)$ is increasing`: a property of its terms)
    let stS ← get
    let seqKey : Option Codes := match s with
      | .id k | .sub (.id k) _ =>
        if stS.infSeqs.any (fun (e, n) => n == k && (e == stS.curEnv || stS.curProved == some e)) &&
          (Elab.lookupLocal sc k).isSome then some k else none
      | _ => none
    let seqKey := match seqKey, t with
      | none, .lam .real .tt (.cases (.app (.prim .isNat) (.loc 0)) _ (.num 0)) => some []
      | k, _ => k
    let ps ← adjs.mapM fun (a, on) =>
      match seqKey, on, (if ty == .fn .real .real then seqAdjective t a else none) with
      | some _, none, some p => pure p
      | _, _, _ =>
      -- the standard adjectives, else the vocabulary's (`even` of an integer)
      tryCatch (adjectiveTm sc t ty defDom a on defCod) fun e =>
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
      -- (a variable bound by the result or the sentence hides a definition of the article
      -- with its name)
      let fr := ((dropBoundIndices st0 φ (freeIds 64 [] φ)).filter fun n => (known.contains n || !(st0.globs.zipIdx.any fun (g, i) => g.key == n && !g.family && Elab.visibleIn st0 i)) && !constName n && !st0.vocab.symbols.any (·.sym == n) && !st0.vocab.methods.any (·.op == .fn n)).eraseDups
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
    -- (`If $p$ is a prime with $p>3$` about a `p` bound before: both)
    | .noun np =>
      let withForm : Option Clause := match np.reverse with
        | .m φ :: .w w :: .m ts :: rest =>
          if w != w!"with" then none else do
          let m ← Math.parseFormula ts
          let v ← Elab.symKey m
          let c ← Math.parseFormula φ
          if known.contains v then some (Clause.both [Clause.isA m rest.reverse false, .fact c]) else none
        | _ => none
      if withForm.isSome then withForm else
      match np.reverse with
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
    | .result _ =>
      -- (in a result, a hypothesis about variables that the claim does not use, nor the
      -- hypotheses about them, is not one of its hypotheses, as the condition of a binder that
      -- the claim does not use: `Let $g$ be continuous on $[c,d]$ and differentiable on $(c,d)$.
      -- … Let $h$ be differentiable at $x_0$. Then $h$ is continuous at $x_0$.`)
      let envNames := st0.envBinders.map (·.name)
      let about (h : Hyp) : List Codes :=
        (((clauseMaths h.clause).flatMap fun m => freeIds 64 [] m ++ subKeys 64 m).filter envNames.contains).eraseDups
      let touches (used : List Codes) (h : Hyp) : Bool :=
        h.heading || h.contra || (about h).isEmpty || (about h).any used.contains
      let rec close : Nat → List Codes → List Codes
        | 0, u => u
        | f + 1, u =>
          let u1 := (usedBinders st0.envBinders u).map (·.name)
          let u2 := (u1 ++ (st0.envHyps.filter (touches u1)).flatMap about).eraseDups
          if u2.length == u.length then u2 else close f u2
      cls.map fun cl =>
        let used := close (st0.envHyps.length + st0.envBinders.length + 1)
          ((clauseFree st0 [] cl).filter envNames.contains).eraseDups
        (st0.envHyps.filter (touches used)).foldr (fun h cl =>
          { cl with clause := Clause.ifClause h.clause cl.clause }) cl
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
  -- (not the object of `every NP`, which only its sentence names: the variable that the grammar
  -- gives it, the last binder)
  let kept := (bs.reverse.dropWhile fun b => b.name == w!"ve" || b.name == w!"\\everyobj").reverse
  if inResult && !kept.isEmpty then
    -- (a binder is in the scope of those before it in the list: new binders that use
    -- variables of the result come after them)
    if domEnv.isEmpty then
      modify fun st => { st with envBinders := kept ++ dropShadowed st.envBinders (kept.map (·.name)) }
    else modify fun st => { st with envBinders := st.envBinders ++ kept }
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
  -- the variables the description uses, apart from its own (not the values of its modifiers,
  -- `$n$` in `primes less than $n$`)
  let own := npVars (withoutSlotArgs st.vocab np)
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
  if localDef c then modify fun st => { st with locals := st.locals ++ [(i, c.ctx.env)] }
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
      modify fun st => { st with envBinders := bs ++ dropShadowed st.envBinders (bs.map (·.name)) }
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
does. In a result, a claim that uses none of the variables of a hypothesis (nor of the
hypotheses that it is made under) is made without it, as without the conditions of the binders
that it does not use. -/
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
  -- (a map bound with its adjectives, then the other hypotheses: `Suppose $f\colon A\to B$ is
  -- differentiable and $f'$ is bounded.`)
  | some (.many [b]) =>
    if contra then fail E.unsupported
    discard <| assumeIn c [b] []
    if hyps.isEmpty then return ([], [])
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
      -- (in a result, a letter that nothing defines in a hypothesis, `Let
      -- $f\colon\mathbb{R}\to\mathbb{R}$ be differentiable at $x_0$.`: a number, a variable of the
      -- result, bound before the hypothesis)
      let isResult := match c.ctx.kind with | .result _ => true | _ => false
      let st1 ← get
      match ← tryCatch (do checkHyp c h; pure none) (fun e => pure (some e)) with
      | none => pure ()
      | some e =>
        let letter (ch : Nat) : Bool := (97 ≤ ch && ch ≤ 122) || (65 ≤ ch && ch ≤ 90)
        let name := (subNameFor (clauseMaths h) e.detail).getD e.detail
        let ok := match name with
          | [ch] => letter ch
          | ch :: 95 :: ds => letter ch && !ds.isEmpty && ds.all fun d => 48 ≤ d && d ≤ 57
          | _ => false
        if !isResult || contra || e.code != E.undefined || !ok then throw e
        set st1
        discard <| assumeIn c [.every [name] (.id w!"\\mathbb{R}")] []
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
      -- constant defined there (`localDef`: not in a definition environment)
      if localDef c then
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
    -- (`Let $X$ be a random variable.`, with a noun `random variable` in the vocabulary: one of
    -- them, until a second makes the two a random pair, `uniformVar`)
    let rv : List PItem := [.w w!"random", .w w!"variable"]
    if !integ && df.isNone && !cont && (← get).vocab.nouns.any (fun n => n.sing == rv && n.arg.isNone) then
      return ← assumeIn c [.noun [.w w!"random", .w w!"variable", .m [.id y]]] []
    pure ([], [])
  | .uniformVar z dom => do
    if c.ctx.kind == .text then fail E.prose
    let st ← get
    let some (e, y, none, df, integ, cont) := st.randomPair | fail E.prose
    if e != st.curEnv then fail E.prose
    -- (the first variable, bound as a random variable of the vocabulary: now of the pair)
    if let some b := st.envBinders.head? then
      if b.name == y && b.ty != .real then
        modify fun st => { st with envBinders := st.envBinders.drop 1 }
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
  | .defNotion subj name abbr cond noun =>
    -- (a clause about the subject: read as the clause of a claim about it)
    let cb : Option (Scope → M Tm) := match cond with
      | .clause cl => some fun sc => clauseTm c sc none none cl
      | _ => none
    defNotion subj name abbr cond cb noun
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
  | .asIn vars label => do
    -- `Let $x$, $y$ and $z$ be as in Theorem~\ref{t}.`: the variables of `t`, all of them, with
    -- its hypotheses, as the first variables of this result or proof
    if c.ctx.kind == .text then fail E.prose
    let st ← get
    let some e := st.resultEnvs.lookup label | fail E.unsupported label
    let bs := (st.resultBinders.lookup e).getD []
    let names := bs.map (·.name)
    if bs.isEmpty || vars.length != bs.length || !names.all vars.contains || !vars.all names.contains then
      fail E.finding (w!"`be as in` the result " ++ label ++ w!" names all of its variables: " ++
        ((names.map fun n => w!"$" ++ n ++ w!"$").intersperse w!", ").flatten)
    if !st.envBinders.isEmpty then fail E.unsupported
    let hyps := ((st.resultHyps.lookup e).getD []).filter fun h => h.item == 0 && !h.contra
    modify fun st => { st with envBinders := bs, envHyps := st.envHyps ++ hyps }
    pure ([], [])
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
    let some repl0 := fs[1]? | fail E.unsupported
    -- (`if $φ$ and $ψ$`: both conditions, `φ\land ψ`)
    let repl : List PTok := (fs.drop 2).foldl (fun acc g =>
      acc ++ [(⟨.cmd w!"land", (g.head?.map (·.pos)).getD 0, true⟩ : PTok)] ++ g) repl0
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
  -- other wordings of the forms that are read, then the words of the article's conventions
  let stdToks := Notation.rewriteWords Notation.standardWords (s.toks.length + 1) none s.toks
  let stdToks := Notation.seqRanges (stdToks.length + 1) stdToks
  let stdToks := Notation.satisfiesForm (stdToks.length + 1) stdToks
  -- (`is called NAME whenever COND`: the condition of a definition, not a range)
  let stdToks :=
    let lw (p : PTok) : Option Codes := if p.math then none else match p.tok with | .word w => some (Grammar.lower w) | _ => none
    if stdToks.any (fun p => [some w!"call", some w!"called", some w!"say", some w!"said"].contains (lw p)) then
      stdToks.map fun p => if lw p == some w!"whenever" then { p with tok := .word w!"if" } else p
    else stdToks
  let s := { s with toks := Notation.standardForms (stdToks.length + 1) false false none stdToks }
  -- (`a (possibly infinite) group`: a group; `a compact, connected metric space`: a compact
  -- connected metric space)
  let s := { s with toks := Notation.dropUnconstraining (s.toks.length + 1) s.toks }
  let s := { s with toks := Notation.dropCounts s.toks }
  let s := { s with toks := Notation.oneToOne (s.toks.length + 1) s.toks }
  -- (`{n\choose k}`, `\stackrel{(a)}{\le}`)
  let s := { s with toks := Notation.annotatedRel (s.toks.length + 1) (Notation.chooseBinom (s.toks.length + 1) s.toks) }
  let s := { s with toks := Notation.unbraceFont (s.toks.length + 1) s.toks }
  let s := { s with toks := Notation.adjectiveCommas st0.vocab (st0.notions.map (·.1)) s.toks }
  let s := if st0.wordAliases.isEmpty then s
    else { s with toks := Notation.rewriteWords st0.wordAliases (s.toks.length + 1) none s.toks }
  -- the symbols this sentence introduces, if it is not read
  let unread : List Codes := introducedSymbols s.toks
  -- (of prose, symbols of the article; of a result or a proof, of that result only)
  let st0u := if s.ctx.kind == .text then { st0 with unreadIds := (st0.unreadIds ++ unread.filter (!st0.unreadIds.contains ·)) }
    else { st0 with unreadLocal := st0.unreadLocal ++ unread.map (s.ctx.env, ·) }
  -- a symbol for a quantity that the article does not define (`Let $\chi(G)$ denote the
  -- chromatic number of a graph $G$.`), if the sentence has no other reading
  -- (the letters in use, which a reading must not bind again)
  let avoidVars : List Codes := st0.envBinders.map (·.name) ++ (st0.fixed.map (·.2.name)) ++
    (st0.globs.zipIdx.filter fun (_, i) => Elab.visibleIn st0 i).map (·.1.key)
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
  -- (in a result, a sentence with nested indefinites, `The continuous image of a compact space
  -- is compact.`, that has no other reading: its reading with more variables, if it compiles)
  let inResult := match s.ctx.kind with | .result _ => true | _ => false
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
  let nestedPre : Unit → List Grammar.Sent := fun _ => if inResult then Grammar.nestedAlts avoidVars s else []
  let parsed := match parsed with
    | some p => some p
    | none => if (flex ()).isEmpty && (nestedPre ()).isEmpty then none else some []
  match parsed with
  | none => { c with st := st0u, idx := c.idx + 1, outcomesRev := .prose :: c.outcomesRev, proofs := incomplete ps }
  | some parts =>
    let sent : Grammar.Sent := match parts with
      | [(_, sn)] => sn
      | _ => .constDefs none [] []
    let sc : SentCtx := ⟨s.ctx, (envs.lookup s.ctx.proves).getD 0, c.idx⟩
    let one (part : Sentence) (sent : Grammar.Sent) (ptoks0 : List PTok) (alts : List Grammar.Sent) :
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
        -- (if no reading of the sentence compiles: its other readings in turn, the quantity it
        -- names, undefined, first)
        let (ds, cs) ← tryCatch primary fun e =>
          match sent with
          | .undefined .. => throw e
          | _ =>
            let rec others : List Grammar.Sent → M (List Nat × List Nat)
              | [] => throw e
              | alt :: rest => do
                set before
                -- (a finding about the quantity says more than the reading that failed)
                tryCatch (Compile.sentence sc alt) fun e' =>
                  if e'.code == E.finding && rest.isEmpty then throw e' else others rest
            others alts
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
        let st1 ← get
        let (d, cl) ← tryCatch (one p sn p.toks []) fun e => do
          set st1
          -- (a part that does not compile may itself be made of sentences: `Assume that
          -- $a>0$ and let $n$ be an integer such that $n>a$.`)
          match (Grammar.partsOfAt 0 p).bind fun qs => qs.mapM fun q => (Grammar.parseSentence q).map (q, ·) with
          | some sub@(_ :: _ :: _) =>
            let mut d' : List Nat := []
            let mut c' : List Nat := []
            for (q, sq) in sub do
              let (a, b) ← one q sq q.toks []
              d' := d' ++ a
              c' := c' ++ b
            pure (d', c')
          | _ => throw e
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
    -- (the readings with nested indefinites of a sentence without a reading of its own, or
    -- whose parts do not compile; then the freer wordings)
    let tryNested (e : Err) : M (List Nat × List Nat) := do
      let st ← get
      match nestedPre () with
      | sn :: rest => tryCatch (one s sn toks0 rest) fun _ => do set st; tryFlex e
      | [] => tryFlex e
    let labelled : M (List Nat × List Nat) :=
      match parts with
      | [] => tryNested ⟨E.prose, []⟩
      | [(_, sn)] => do
        let st ← get
        let alts : List Grammar.Sent := [((undefinedAlt.orElse fun _ => Grammar.thatIsSentence s).orElse
          fun _ => Grammar.defAlt s).orElse fun _ => Grammar.denoteAlt s].filterMap id ++ Grammar.nestedAlts avoidVars s
        tryCatch (one s sn toks0 alts) fun e =>
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
          tryNested e
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

/-! ## The article's own notions

A definition that is not read still says that there is such a notion. `A metric space is
\emph{homogeneous} if its isometry group acts transitively on points.` makes `homogeneous`
an adjective of metric spaces, and `A \emph{Kripke frame} is an ordered pair …` makes
`Kripke frame` a noun, each without a meaning in Lean: what the article states about them
is read, and holds for whatever the definition means (as for the notions that the preamble
declares, `Declared`). -/

namespace DefinedTerms

def lowerC (c : Nat) : Nat := if 65 ≤ c && c ≤ 90 then c + 32 else c
def letterC (c : Nat) : Bool := (97 ≤ c && c ≤ 122) || (65 ≤ c && c ≤ 90)

/-- The words of a text, lower-cased, for the shape of a sentence: a formula `$…$` is the
word `$`, a hyphen between letters the word `-`; commands and other signs are left out. -/
def wordsOfText : Nat → Codes → List Codes → List Codes
  | 0, _, acc => acc.reverse
  | _ + 1, [], acc => acc.reverse
  | f + 1, c :: cs, acc =>
    if c == 36 then
      let r := cs.dropWhile (· != 36)
      wordsOfText f (r.drop 1) ([36] :: acc)
    else if c == 92 then wordsOfText f (cs.dropWhile letterC) acc
    else if letterC c then
      let w := (c :: cs).takeWhile letterC
      wordsOfText f ((c :: cs).drop w.length) (w.map lowerC :: acc)
    else if c == 45 && (acc.head?.any fun w => w != [36] && w != [45]) && (cs.head?.any letterC) then
      wordsOfText f cs ([45] :: acc)
    else wordsOfText f cs acc

/-- The text of a group `{…}` after its opening brace, and what follows it. -/
def group : Nat → Nat → Codes → Codes → Option (Codes × Codes)
  | 0, _, _, _ => none
  | _ + 1, _, [], _ => none
  | f + 1, d, c :: cs, acc =>
    if c == 125 && d == 0 then some (acc.reverse, cs)
    else group f (if c == 123 then d + 1 else if c == 125 then d - 1 else d) cs (c :: acc)

def emphCmds : List Codes := [w!"emph", w!"textit", w!"textbf", w!"term", w!"textsl", w!"defn", w!"textsf", w!"df"]
def emphOld : List Codes := [w!"em", w!"it", w!"bf", w!"sl"]

/-- `\textbf{saturated subalgebra}` as `saturated subalgebra` (emphasis inside emphasis). -/
def unwrap (t : Codes) : Codes :=
  match t.dropWhile (· == 32) with
  | 92 :: cs =>
    let name := cs.takeWhile letterC
    match cs.drop name.length with
    | 123 :: r =>
      if emphCmds.contains name then
        match group (r.length + 1) 0 r [] with
        | some (inner, rest) => if rest.all (· == 32) then inner else t
        | none => t
      else t
    | _ => t
  | _ => t

/-- The emphasized phrases of a text, each with the text before it and the text after it. -/
def emphasized : Nat → Codes → Codes → List (Codes × Codes × Codes) → List (Codes × Codes × Codes)
  | 0, _, _, acc => acc.reverse
  | _ + 1, [], _, acc => acc.reverse
  | f + 1, c :: cs, before, acc =>
    let hit : Option (Codes × Codes) :=
      if c == 92 then
        let name := cs.takeWhile letterC
        match cs.drop name.length with
        | 123 :: r => if emphCmds.contains name then group (r.length + 1) 0 r [] else none
        | _ => none
      else if c == 123 then
        match cs with
        | 92 :: r =>
          let name := r.takeWhile letterC
          if emphOld.contains name then group (r.length + 1) 0 (r.drop name.length) [] else none
        | _ => none
      else none
    match hit with
    | some (inner, rest) =>
      -- (`\emph{\textbf{saturated subalgebra}}`: the inner text)
      let inner := unwrap inner
      emphasized f rest (inner.reverse ++ before) ((inner, before.reverse, rest) :: acc)
    | none => emphasized f cs (c :: before) acc

/-- The text without its `\index[…]{…}` entries. -/
def dropIndex : Nat → Codes → Codes
  | 0, cs => cs
  | _, [] => []
  | f + 1, c :: cs =>
    if c == 92 && cs.take 5 == w!"index" && !((cs.drop 5).head?.any letterC) then
      let r := cs.drop 5
      let r := match r with
        | 91 :: r' => (r'.dropWhile (· != 93)).drop 1
        | _ => r
      match r with
      | 123 :: r' => match group (r'.length + 1) 0 r' [] with
        | some (_, rest) => dropIndex f rest
        | none => c :: dropIndex f cs
      | _ => c :: dropIndex f cs
    else c :: dropIndex f cs

/-- The words of a name: letters, with hyphens between them; at most five words. -/
def nameWords (t : Codes) : Option (List Codes) :=
  if t.any (fun c => !(letterC c || c == 32 || c == 45 || c == 10)) then none else
  let ws := wordsOfText (t.length + 1) t []
  let n := (ws.filter (· != [45])).length
  if n == 0 || n > 5 || ws.head? == some [45] || ws.getLast? == some [45] then none else some ws

/-- The first noun of the vocabulary among the words (the earliest, the longest there), in
the singular or the plural. -/
def firstNoun (V : Vocab) (ws : List Codes) : Option Noun :=
  let nouns := V.nouns.filter fun n => !n.sing.isEmpty && n.sing.all fun i => match i with | .w _ => true | _ => false
  (List.range ws.length).findSome? fun i =>
    let here := nouns.filter fun n =>
      let fits (p : Phrase) : Bool := !p.isEmpty && (ws.drop i).take p.length == p.filterMap fun it => match it with | .w w => some w | _ => none
      fits n.sing || fits n.plural
    here.foldl (fun (best : Option Noun) n => match best with
      | some b => if n.sing.length > b.sing.length then some n else some b
      | none => some n) none

def singWords (n : Noun) : List Codes := n.sing.filterMap fun it => match it with | .w w => some w | _ => none

/-- What an emphasized phrase of a definition declares, by the words around it:
`… NOUN … is [called|said to be] \emph{ADJ}`: an adjective of the noun; `a|an \emph{NAME}`:
a noun, of the objects of the noun that the sentence says it is (`is a|an … NOUN`, or the
noun before `is called a`), or else of objects of its own. -/
def declaredBy (V : Vocab) (before name after : Codes) (sure : Bool := true) : Option Declared := do
  let ws ← nameWords name
  -- (in the running text, without a verb that names: only `… is \emph{NAME} if …` and `A
  -- \emph{NAME} is …`)
  let aw0 := wordsOfText (after.length + 1) after []
  if !sure && !(aw0.head?.any fun w => [w!"if", w!"when", w!"whenever", w!"provided", w!"iff", w!"is", w!"consists"].contains w) then none
  -- (a name, not a phrase that goes on: `bisimulation between`)
  if (ws.getLast?.any fun w => [w!"between", w!"of", w!"in", w!"on", w!"for", w!"to", w!"with", w!"and", w!"or", w!"the", w!"a", w!"an", w!"is", w!"if", w!"arbitrary"].contains w) then none
  let bw := wordsOfText (before.length + 1) before []
  let aw := wordsOfText (after.length + 1) after []
  let ends (xs : List Codes) : Bool := bw.reverse.take xs.length == xs.reverse
  let ph (xs : List Codes) : Phrase := xs.map PItem.w
  if ends [w!"a"] || ends [w!"an"] then
    -- a noun
    if V.nouns.any (fun n => n.sing == ph ws) then none else
    -- (`… is called a NAME`: the objects of the noun before; `A NAME is a|an … NOUN`: after)
    let called := bw.contains w!"called" || bw.contains w!"call"
    let base : Option Noun := if called then firstNoun V bw else
      match aw with
      | i :: a :: rest => if (i == w!"is" || i == w!"consists") && (a == w!"a" || a == w!"an") then firstNoun V (rest.take 6) else none
      | _ => none
    -- (a name that ends with a noun is an adjective of that noun, as a declared one)
    let endsNoun := (List.range ws.length).drop 1 |>.any fun p => V.nouns.any fun n => n.sing == ph (ws.drop p)
    if endsNoun then some { words := ws }
    else match base with
      | some n => some { words := ws, base := singWords n }
      | none =>
        -- (a kind of object of its own: where the sentence names it, `is called a NAME`, or
        -- says what it is, `A NAME is …`)
        let says := match aw with
          | i :: _ => i == w!"is" || i == w!"consists" || i == w!"means"
          | [] => false
        if called || says then some { words := ws } else none
  else if ends [w!"is"] || ends [w!"is", w!"called"] || ends [w!"said", w!"to", w!"be"] || ends [w!"are"] ||
      ends [w!"are", w!"called"] || ends [w!"be"] ||
      -- (`We call a metric space $X$ \emph{homogeneous} if …`)
      (ends [[36]] && (bw.contains w!"call" || bw.contains w!"called")) then
    -- an adjective, of the first noun of the sentence
    let n ← firstNoun V bw
    let words := ws ++ singWords n
    if V.mods.any (fun m => m.phrase == ph ws && m.ty == n.ty) then none else some { words }
  else none

end DefinedTerms

/-- The sentences of an article. -/
def sentencesOf (src : Source) : Option (List Sentence) := do
  let k ← src.findIdx? isBeginDocument
  let ms ← macrosOf (joinLines (src.take k))
  let bs := blocksOf (src.drop (k + 1)) (linesOffset (src.take (k + 1))) none []
  let (ss, _, s) ← lexSeg ms bs [] {}
  some (ss ++ segFinish s)

namespace DefinedTerms

/-- The noun of the vocabulary that the words end with (the longest), or else the first
among them. -/
def headNoun (V : Vocab) (ws : List Codes) : Option Noun :=
  let nouns := V.nouns.filter fun n => !n.sing.isEmpty && n.sing.all fun i => match i with | .w _ => true | _ => false
  let fits (p : Phrase) : Bool :=
    let pw := p.filterMap fun it => match it with | .w w => some w | _ => none
    !pw.isEmpty && pw.length ≤ ws.length && ws.drop (ws.length - pw.length) == pw
  let ending := nouns.filter fun n => fits n.sing || fits n.plural
  match ending.foldl (fun (best : Option Noun) n => match best with
      | some b => if n.sing.length > b.sing.length then some n else some b
      | none => some n) none with
  | some n => some n
  | none => firstNoun V ws

/-- The name of an adjective without the noun it is of, where the sentence repeats it (`are
called left weakly Gorenstein algebras`). -/
def withoutNoun (name noun : List Codes) : List Codes :=
  let k := noun.length
  if k == 0 || name.length ≤ k then name else
  let tail := name.drop (name.length - k)
  let plural := noun.dropLast ++ (noun.getLast?.map (· ++ [115])).toList
  if tail == noun || tail == plural then name.take (name.length - k) else name

/-- The noun of the vocabulary that the words end with (the longest). -/
def headNounEnd (V : Vocab) (ws : List Codes) : Option Noun :=
  let nouns := V.nouns.filter fun n => !n.sing.isEmpty && n.sing.all fun i => match i with | .w _ => true | _ => false
  let fits (p : Phrase) : Bool :=
    let pw := p.filterMap fun it => match it with | .w w => some w | _ => none
    !pw.isEmpty && pw.length ≤ ws.length && ws.drop (ws.length - pw.length) == pw
  (nouns.filter fun n => fits n.sing || fits n.plural).foldl (fun (best : Option Noun) n => match best with
      | some b => if n.sing.length > b.sing.length then some n else some b
      | none => some n) none

/-- What a sentence in one of the forms of a definition declares (`Grammar.DefForm`): an
adjective of the noun of its subject, or a noun, of the objects of that noun or (after a
verb that names) of objects of its own. -/
def declaredByForm (V : Vocab) (named : Bool) (f : Grammar.DefForm) : Option Declared := do
  let (name, _, rest) ← Grammar.nameAbbr f.name
  if !rest.isEmpty then none
  let n := (name.filter (· != w!"-")).length
  if n == 0 || n > 5 || name.head? == some w!"-" || name.getLast? == some w!"-" then none
  if name.any (fun w => w.length < 2 && w != w!"-") then none
  let ph (xs : List Codes) : Phrase := xs.map PItem.w
  let sw := f.subj.filterMap fun c => match c with | Chunk.w w => some w | _ => none
  let genus := headNoun V sw
  if f.noun then
    if V.nouns.any (fun k => k.sing == ph name) then none else
    let endsNoun := (List.range name.length).drop 1 |>.any fun p => V.nouns.any fun k => k.sing == ph (name.drop p)
    if endsNoun then some { words := name }
    else match genus with
      | some g => some { words := name, base := singWords g }
      | none => if named then some { words := name } else none
  else
    let g ← genus
    let name := withoutNoun name (singWords g)
    if name.isEmpty || V.mods.any (fun m => m.phrase == ph name && m.ty == g.ty) then none
    else some { words := name ++ singWords g }

/-- What a sentence that names a notion declares (`Grammar.DefForm.Shape`): the notion, as
an adjective of the noun of its subject or as a noun; and, where the subject introduces an
object of a kind that no field knows (`A geodesic space $X$ is called …`), that kind: its
last word as a noun, the words before it as an adjective of it. -/
def declaredByShape (V : Vocab) (sh : Grammar.DefForm.Shape) : List Declared :=
  let ph (xs : List Codes) : Phrase := xs.map PItem.w
  if sh.name.any (fun w => w.length < 2 && w != w!"-") then [] else
  let genusW := sh.genus.filter (· != w!"-")
  let known : Option Noun := if genusW.isEmpty then none else headNounEnd V genusW
  let isNoun (ws : List Codes) : Bool := V.nouns.any fun k => k.sing == ph ws
  let endsNoun (ws : List Codes) : Bool := (List.range ws.length).drop 1 |>.any fun p => isNoun (ws.drop p)
  match known with
  | some g =>
    if sh.noun then
      if isNoun sh.name then [] else
      if endsNoun sh.name then [{ words := sh.name }] else [{ words := sh.name, base := singWords g }]
    else
      let name := withoutNoun sh.name (singWords g)
      if name.isEmpty || V.mods.any (fun m => m.phrase == ph name && m.ty == g.ty) then []
      else [{ words := name ++ singWords g }]
  | none =>
    -- a kind of object of the article's own: only where the sentence introduces one, in
    -- plain words
    let plain := genusW.all fun w => w.length ≥ 3 && w.all fun c => 97 ≤ c && c ≤ 122
    -- (not a noun of a field that takes a complement, `subset of $A$`)
    let taken := V.nouns.any fun k => k.sing.head? == (genusW.getLast?.map PItem.w) && k.sing.any fun i => match i with | .w _ => false | _ => true
    -- (words for what a sentence speaks of, not for a kind of object)
    let noKind := [w!"theorem", w!"lemma", w!"result", w!"case", w!"condition", w!"property", w!"notion", w!"definition",
      w!"latter", w!"former", w!"above", w!"number", w!"following", w!"object", w!"thing", w!"one", w!"example",
      w!"statement", w!"fact", w!"problem", w!"question", w!"paper", w!"section", w!"proof"].contains (genusW.getLast?.getD [])
    if genusW.isEmpty || !sh.indefinite || !plain || genusW.length > 3 || taken || noKind then
      -- (without a kind: the name of a kind of object of its own)
      if sh.noun && !isNoun sh.name && sh.genus.isEmpty then [{ words := sh.name }] else []
    else
      let head := genusW.getLast?.getD []
      let kind : List Declared := [{ words := [head] }] ++ (if genusW.length > 1 then [{ words := sh.genus }] else [])
      if sh.noun then
        if sh.name.getLast? == some head then kind ++ [{ words := sh.name }]
        else kind ++ [{ words := sh.name, base := [head] }]
      else
        let name := withoutNoun sh.name [head]
        if name.isEmpty then kind else kind ++ [{ words := name ++ [head] }]

end DefinedTerms

/-- The notions that the article defines in sentences that are not read (definitions, and
sentences of the text), with the vocabulary `V`: to be declared (`Vocab.declare`), so that
the article is read with them. A sentence in one of the forms of a definition declares the
notion it names; any other, the phrases it emphasizes. -/
def definedTerms (V : Vocab) (src : Source) : List Declared :=
  match sentencesOf src with
  | none => []
  | some ss =>
    let d := assemble V ss
    let all := joinLines src
    let unread := (ss.zip d.outcomes).filter fun (s, o) =>
      (match o with | .compiled _ _ => false | _ => true) &&
      (match s.ctx.kind with
        | .result e => e.take 3 == w!"def"
        | .text => true
        | .proof => false)
    -- (declared one after another: a later name may end with an earlier noun)
    let add (acc : Vocab × List Declared) (dcl : Declared) : Vocab × List Declared :=
      let W := acc.1.declareOne dcl
      if W == acc.1 then acc else (W, acc.2 ++ [dcl])
    let (_, ds) := unread.foldl (fun (acc : Vocab × List Declared) (s, _) =>
      let inDef := match s.ctx.kind with | .result e => e.take 3 == w!"def" | _ => false
      let forms : List Grammar.DefForm := match Grammar.chunks (s.toks.length + 1) s.toks [] with
        | some cs => Grammar.DefForm.forms inDef cs
        | none => []
      -- (a verb that names: `is called`, `we say`, `we call`, `is said to be`, `we mean`)
      let named : Bool := s.toks.any fun p => !p.math && (match p.tok with
        | .word w => [w!"called", w!"call", w!"say", w!"said", w!"termed", w!"mean", w!"define"].contains (Grammar.lower w)
        | _ => false)
      let acc1 := match forms.findSome? (fun f => DefinedTerms.declaredByForm acc.1 named f) with
        | some dcl => add acc dcl
        | none => acc
      (
        let shapes : List Grammar.DefForm.Shape := match Grammar.chunks (s.toks.length + 1) s.toks [] with
          | some cs => Grammar.DefForm.shapes cs
          | none => []
        let acc' := shapes.foldl (fun (a : Vocab × List Declared) sh => (DefinedTerms.declaredByShape a.1 sh).foldl add a) acc1
        -- (a sentence that names in one of these shapes: its emphasized phrases say no more)
        if acc'.2.length != acc.2.length || shapes.any (!·.genus.isEmpty) then acc' else
          -- (the phrases that it emphasizes)
          let text := (all.drop s.start).take (s.stop + 1 - s.start)
          let text := DefinedTerms.dropIndex (text.length + 1) text
          (DefinedTerms.emphasized (text.length + 1) text [] []).foldl (fun (acc : Vocab × List Declared) (name, before, after) =>
            match DefinedTerms.declaredBy acc.1 before name after (inDef || named) with
            | some dcl => add acc dcl
            | none => acc) acc)) (V, [])
    ds

/-- The vocabulary an article is read with: `V`, the notions of its preamble (`extra`: and
of the command line), the negations it uses, and the notions that it defines in sentences
that are not read. -/
def Vocab.forArticleRead (V : Vocab) (src : Source) (extra : List Declared := []) : Vocab :=
  let V := (V.forArticle src).declare extra
  V.declare (definedTerms V src)

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
