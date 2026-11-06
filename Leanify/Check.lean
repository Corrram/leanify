import Leanify.Render

/-! # Checking an article quickly

`checkArticle` runs the compiler natively on an article file and reports, in the
`file:line:col: severity: message` format of editors, every sentence that did not
compile and (optionally) every sentence of a result or proof that has no
mathematical reading. It is the fast feedback loop while writing: it certifies
nothing. The kernel-checked compilation is `#leanify_article`. -/

namespace Leanify

/-- The file contents as lines of code points (CRLF normalized). -/
def readLines (path : System.FilePath) : IO (List (List Nat)) := do
  let s ← IO.FS.readFile path
  let s := s.replace "\r\n" "\n"
  let lines := s.splitOn "\n"
  let lines := if lines.getLast? == some "" then lines.dropLast else lines
  pure (lines.map fun l => l.toList.map Char.toNat)


def errMessage (e : Err) : String :=
  let d := Codes.toString e.detail
  let what := if e.code == E.undefined then "undefined symbol"
    else if e.code == E.type then "type mismatch"
    else if e.code == E.unsupported then "unsupported construction"
    else if e.code == E.noun then "unknown noun"
    else if e.code == E.label then "unknown label"
    else if e.code == E.free then "unbound variable"
    else if e.code == E.redefined then "symbol defined twice"
    else if e.code == E.referent then "no referent"
    else if e.code == E.shadow then "variable shadows a definition"
    else s!"error {e.code}"
  if d.isEmpty then what else s!"{what}: {d}"

/-- Greek letters: names of variables, not notation. -/
def greekNames : List String :=
  ["alpha", "beta", "gamma", "delta", "epsilon", "varepsilon", "zeta", "eta", "theta", "vartheta",
   "iota", "kappa", "lambda", "mu", "nu", "xi", "pi", "varpi", "rho", "varrho", "sigma", "varsigma",
   "tau", "upsilon", "phi", "varphi", "chi", "psi", "omega", "Gamma", "Delta", "Theta", "Lambda",
   "Xi", "Pi", "Sigma", "Upsilon", "Phi", "Psi", "Omega", "ell"]

/-- Commands of formulas that the grammar reads itself (relations, operations,
fonts, accents, spacing). Any other command is a symbol: defined in the article
or by its vocabulary, or else unknown. -/
def structuralCmds : List String :=
  ["le", "leq", "ge", "geq", "in", "coloneqq", "neq", "ne", "frac", "tfrac", "dfrac", "sqrt",
   "min", "max", "int", "hat", "widehat", "cdot", "to", "mapsto", "longmapsto", "times", "top",
   "perp", "cup", "cap", "approx", "ldots", "quad", "qquad", "pm", "mp", "infty",
   "text", "mathcal", "mathbb", "mathbf", "mathrm", "operatorname", "mathit", "overline", "bar",
   "tilde", "underline", "check", "sup", "inf", "sum", "prod", "circ", "subseteq", "subseteqq", "supseteq", "supseteqq"]

/-- A symbol written as a command that is not a variable name (a Greek letter):
notation the article or its vocabulary must define. -/
def isNotation (d : String) : Bool :=
  match d.toList with
  | '\\' :: r => !greekNames.contains (String.ofList (r.takeWhile Char.isAlpha))
  | _ => false

/-- What stopped a sentence, in a few words. -/
def failedMessage (e : Err) : String :=
  let d := Codes.toString e.detail
  if e.code == E.undefined && !d.isEmpty then
    if isNotation d then s!"unknown notation {d}" else s!"{d} is not defined"
  else errMessage e

/-- Line and column (both from 1) of a code point offset. -/
def lineCol (lines : List (List Nat)) (off : Nat) : Nat × Nat := Id.run do
  let mut o := off
  let mut ln := 1
  for l in lines do
    if o ≤ l.length then return (ln, o + 1)
    o := o - (l.length + 1)
    ln := ln + 1
  return (ln, 1)

def kindString : EnvKind → String
  | .text => "text"
  | .result n => Codes.toString n
  | .proof => "proof"

/-- Coverage of an article: per environment kind, the number of compiled,
failed and prose sentences. -/
structure Coverage where
  rows : List (String × Nat × Nat × Nat) := []

def Coverage.add (c : Coverage) (kind : String) (outcome : Outcome) : Coverage :=
  let (a, b, p) := match outcome with
    | .compiled _ _ => (1, 0, 0) | .failed _ => (0, 1, 0) | .prose => (0, 0, 1)
  match c.rows.find? (·.1 == kind) with
  | some _ => ⟨c.rows.map fun (k, x, y, z) => if k == kind then (k, x + a, y + b, z + p) else (k, x, y, z)⟩
  | none => ⟨c.rows ++ [(kind, a, b, p)]⟩

def Coverage.render (c : Coverage) : String :=
  let line (k : String) (a b p : Nat) := s!"  {k}: {a} compiled, {b} failed, {p} prose (of {a + b + p})"
  let total := c.rows.foldl (fun (x, y, z) (_, a, b, p) => (x + a, y + b, z + p)) (0, 0, 0)
  String.intercalate "\n" (c.rows.map (fun (k, a, b, p) => line k a b p) ++
    [line "all" total.1 total.2.1 total.2.2])

def resultKind : EnvKind → String
  | .result _ => "results"
  | .proof => "proofs"
  | .text => "text"

/-- Environments that discuss rather than state: a sentence of a remark, an example
or a conjecture without a reading is not a gap in a statement. -/
def wDiscussion : List Codes := [w!"remark", w!"example", w!"conjecture"]

/-! ### Where an undefined symbol comes from

A symbol is often undefined because the sentence that defines it was not read:
`\beta` in `It holds that …`, when the sentence `… are $\beta(C)\coloneqq…$,
$\xi(C)\coloneqq…$` failed on `\xi`. The check then reports the defining sentence,
with the later sentences that fail for the symbol, instead of each of them. The
defining sentence is found in the source: the symbol, its subscripts and its
arguments, then `\coloneqq`. In a proof, a symbol of the statement it proves is
defined by the statement. -/

def skipGroup (op cl : Char) : Nat → Nat → List Char → Option (List Char)
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | f + 1, d, c :: cs =>
    if c == cl then (if d == 0 then some cs else skipGroup op cl f (d - 1) cs)
    else if c == op then skipGroup op cl f (d + 1) cs
    else skipGroup op cl f d cs

/-- Skip what may follow a defined symbol before `\coloneqq`: spaces, sub- and
superscripts, sizing commands and an argument list. -/
def afterHead : Nat → List Char → List Char
  | 0, cs => cs
  | f + 1, cs =>
    match cs with
    | ' ' :: r | '\n' :: r => afterHead f r
    | '_' :: '{' :: r | '^' :: '{' :: r =>
      match skipGroup '{' '}' 10000 0 r with | some r' => afterHead f r' | none => cs
    | '_' :: '\\' :: r | '^' :: '\\' :: r => afterHead f (r.dropWhile Char.isAlpha)
    | '_' :: _ :: r | '^' :: _ :: r => afterHead f r
    | '(' :: r => match skipGroup '(' ')' 10000 0 r with | some r' => afterHead f r' | none => cs
    | '\\' :: r =>
      let n := String.ofList (r.takeWhile Char.isAlpha)
      if ["bigl", "Bigl", "left", "bigr", "Bigr", "right"].contains n then
        afterHead f (r.dropWhile Char.isAlpha) else cs
    | _ => cs

/-- The positions in `t` where the symbol `m` occurs as a whole symbol. -/
def occurrences (t m : List Char) : List (List Char) := Id.run do
  let mut out := []
  let mut prev : Option Char := none
  let mut r := t
  for _ in [0:t.length] do
    match r with
    | [] => break
    | c :: rest =>
      if r.take m.length == m then
        let after := r.drop m.length
        let okBefore := match m.head?, prev with
          | some h, some p => h == '\\' || !(p.isAlpha || p == '\\')
          | _, _ => true
        let okAfter := match m.getLast?, after.head? with
          | some l, some a => !(l.isAlpha && a.isAlpha)
          | _, _ => true
        if okBefore && okAfter then out := out ++ [after]
      prev := some c
      r := rest
  return out

/-- The spellings of a symbol in the source: `\bar{a}` is also written `\bar a`. -/
def spellings (m : String) : List (List Char) :=
  let cs := m.toList
  match cs with
  | '\\' :: r =>
    let n := r.takeWhile Char.isAlpha
    match r.dropWhile Char.isAlpha with
    | '{' :: x => if x.getLast? == some '}' then [cs, '\\' :: n ++ ' ' :: x.dropLast] else [cs]
    | _ => [cs]
  | _ => [cs]

/-- The text `t` defines the symbol `m` with `\coloneqq`. -/
def definesSym (t : List Char) (m : String) : Bool :=
  (spellings m).any fun sp => (occurrences t sp).any fun after =>
    (afterHead 32 after).take 9 == "\\coloneqq".toList

/-- The text `t` binds the symbol `m`: `$m\in A$`, `$m>0$`, `$m,y\in A$`, `$m$ be …`. -/
def bindsSym (t : List Char) (m : String) : Bool :=
  (spellings m).any fun sp => (occurrences t sp).any fun after =>
    let r := afterHead 32 after
    ["\\in", "\\ge", "\\le", ">", "<", ",", "$ be ", "$ denote"].any fun p => r.take p.length == p.toList

/-- The text `t` mentions the symbol `m`. -/
def mentions (t : List Char) (m : String) : Bool :=
  (spellings m).any fun sp => !(occurrences t sp).isEmpty

/-- For every sentence that fails on an undefined symbol defined by an earlier
sentence that was not read: that sentence. -/
def rootsOf (d : Doc) (texts : Array (List Char)) : List (Nat × Nat) := Id.run do
  let mut acc : List (Nat × Nat) := []
  for s in [0:d.sentences.length] do
    if let some (.failed e) := d.outcomes[s]? then
      if e.code == E.undefined then
        let m := Codes.toString e.detail
        let (ctx, _, _) := d.sentences[s]!
        let unread (r : Nat) : Bool := match d.outcomes[r]? with
          | some (.compiled _ _) => false | _ => true
        -- `Let $e\in[\eta_-(x),1]$.` binds `e` for the sentences after it
        let binding (t : List Char) : Bool :=
          let t := t.dropWhile Char.isWhitespace
          (t.take 4 == "Let ".toList || t.take 4 == "Fix ".toList ||
            (String.ofList t).contains "let $") && bindsSym t m
        let defining := (List.range s).filter fun r => unread r && (definesSym texts[r]! m || binding texts[r]!)
        let statement := if ctx.kind == .proof && !ctx.proves.isEmpty then
            (List.range s).filter fun r =>
              let (rc, _, _) := d.sentences[r]!
              (match rc.kind with | .result _ => true | _ => false) && rc.label == ctx.proves &&
                unread r && mentions texts[r]! m
          else []
        -- the latest definition, or the first sentence of the statement that names it
        match defining.max?, statement.min? with
        | some r, _ | none, some r => acc := acc ++ [(s, r)]
        | none, none => pure ()
  return acc

/-- For every undefined symbol, the sentences (in order) that fail because of it,
other than those traced to the sentence that defines it. -/
def undefinedUses (d : Doc) (rooted : List Nat) : List (String × List Nat) := Id.run do
  let mut acc : List (String × List Nat) := []
  for s in [0:d.sentences.length] do
    if let some (.failed e) := d.outcomes[s]? then
      if e.code == E.undefined && !rooted.contains s then
        let m := errMessage e
        acc := if acc.any (·.1 == m) then acc.map (fun (k, ss) => if k == m then (k, ss ++ [s]) else (k, ss))
          else acc ++ [(m, [s])]
  return acc

def andList : List String → String
  | [] => ""
  | [a] => a
  | [a, b] => s!"{a} and {b}"
  | a :: rest => s!"{a}, {andList rest}"

/-- The tokens of the sentences of an article, as the compiler segments them. -/
def sentenceToks (src : Source) : Array (List PTok) := Id.run do
  let some k := src.findIdx? isBeginDocument | return #[]
  let some ms := macrosOf (joinLines (src.take k)) | return #[]
  let bs := blocksOf (src.drop (k + 1)) (linesOffset (src.take (k + 1))) none []
  match lexSeg ms bs [] {} with
  | some (ss, _, st) => return ((ss ++ segFinish st).map (·.toks)).toArray
  | none => return #[]

/-- The notation of a sentence that neither the grammar nor the article defines:
commands of its formulas other than Greek letters, the commands the grammar reads,
and the symbols the article defines. -/
def unknownNotation (d : Doc) (toks : List PTok) : List String :=
  let keys := d.globs.map fun g => Codes.toString g.key
  let known (n : String) : Bool :=
    greekNames.contains n || structuralCmds.contains n || keys.any fun k =>
      let c := "\\" ++ n
      k == c || (k.startsWith c && !((k.toList.drop c.length).head?.any Char.isAlpha))
  (toks.filterMap fun p => match p.tok with
    | .cmd n => if p.math && !known (Codes.toString n) then some ("\\" ++ Codes.toString n) else none
    | _ => none).eraseDups

/-- The noun phrase after `be a`/`is an` in a sentence (`Let $X$ be a Markov jump
process with …` gives `Markov jump process`): the likely reason a sentence that
introduces an object has no reading, when the phrase is not a notion of the
article or its vocabulary. -/
def nounPhrase (t : List Char) : Option String := Id.run do
  let s := String.ofList t
  for pre in [" be a ", " be an ", " is a ", " is an "] do
    match s.splitOn pre with
    | _ :: after :: _ =>
      let ws := (after.toList.takeWhile fun c => c.isAlpha || c == ' ' || c == '-')
      let words := (String.ofList ws).splitOn " " |>.filter (· != "")
      let stop := ["with", "and", "such", "that", "on", "of", "in", "for", "which", "where", "if"]
      let words := (words.takeWhile fun w => !stop.contains w).take 5
      if !words.isEmpty then return some (String.intercalate " " words)
    | _ => pure ()
  return none

/-- `a, b and c`, with at most `k` items and `…` for the rest. -/
def fewOf (k : Nat) (xs : List String) : String :=
  let shown := xs.take k
  let s := String.intercalate ", " shown
  if xs.length > k then s ++ ", …" else s

/-- `line 3` or `lines 3, 7`. -/
def linesText (ls : List Nat) : String :=
  let ls := ls.eraseDups
  s!"line{if ls.length == 1 then "" else "s"} {String.intercalate ", " (ls.map toString)}"

def capitalize (s : String) : String :=
  match s.toList with
  | c :: r => String.ofList (c.toUpper :: r)
  | [] => s

/-- Diagnostics for a compiled document. A result (theorem, lemma, …) whose
sentences have no reading is reported once, at its first such sentence, with the
notation in them that nothing defines. A sentence that failed is reported with
what stopped it. An undefined symbol is reported once: at the sentence that
defines it if that sentence was not read, otherwise at its first use, with the
later sentences that fail for the same symbol (they follow from the first). A
sentence with `\coloneqq` that has no reading is reported wherever it is.
Sentences of remarks, examples and conjectures without a reading are not
reported. `prose` also lists the sentences of proofs (and of remarks) without a
reading, and the proof sentences whose construction is not supported; `claims`
prints the reading of every claim. -/
def diagnostics (V : Vocab) (rel : String) (lines : List (List Nat)) (d : Doc)
    (prose claims : Bool) : List String × Coverage := Id.run do
  let mut out : List String := []
  let mut cov : Coverage := {}
  let cs := V.constNames.map Codes.toString
  let gs := d.globNames
  let all := joinLines lines
  let texts : Array (List Char) := (d.sentences.map fun (_, a, b) =>
    (Codes.toString ((all.drop a).take (b - a))).toList).toArray
  let toks := sentenceToks lines
  let roots := rootsOf d texts
  let undef := undefinedUses d (roots.map (·.1))
  let lineOf (s : Nat) : Nat := (lineCol lines (d.sentences[s]!).2.1).1
  let excerpt (s : Nat) : String :=
    let (_, a, b) := d.sentences[s]!
    let text := Codes.toString (all.drop a |>.take (min 90 (b - a)))
    let text := text.replace "\n" " "
    if b - a > 90 then text ++ "…" else text
  let unknownIn (ss : List Nat) : String :=
    match (ss.flatMap fun s => unknownNotation d (toks[s]?.getD [])).eraseDups with
    | [] => ""
    | ns => s!"; unknown notation {fewOf 4 ns}"
  -- the symbols a sentence that was not read leaves undefined, and where
  let consequences (s : Nat) : String :=
    let deps := (roots.filter (·.2 == s)).map (·.1)
    if deps.isEmpty then "" else
      let syms := (deps.filterMap fun t => match (d.outcomes[t]? : Option Outcome) with
        | some (Outcome.failed e) => some (Codes.toString e.detail) | _ => none).eraseDups
      s!"; {andList syms} {if syms.length == 1 then "is" else "are"} then undefined at {linesText (deps.map lineOf)}"
  -- a sentence of a statement without a reading leaves the statement partly
  -- unchecked: always reported, once per statement
  let stated (ctx : Context) : Bool := match ctx.kind with
    | .result n => !wDiscussion.contains n | _ => false
  let isProse (s : Nat) : Bool := d.outcomes[s]?.getD .prose == .prose
  for s in [0:d.sentences.length] do
    let (ctx, a, _) := d.sentences[s]!
    let (l, c) := lineCol lines a
    let o := d.outcomes[s]?.getD .prose
    cov := cov.add (resultKind ctx.kind) o
    match o with
    | .failed e =>
      if roots.any (·.1 == s) then pure () else
      let m := failedMessage e
      let more := consequences s
      -- in a proof, a construction the grammar does not support is like prose
      if ctx.kind == .proof && e.code == E.unsupported && more.isEmpty then
        if prose then
          out := out ++ [s!"{rel}:{l}:{c}: info: proof sentence not read ({m}): {excerpt s}"]
      else
      let uses := if e.code == E.undefined then ((undef.find? (·.1 == errMessage e)).map (·.2)).getD [] else []
      match uses with
      | first :: later =>
        if first == s then
          let same := if later.isEmpty then "" else s!"; the same at {linesText (later.map lineOf)}"
          out := out ++ [s!"{rel}:{l}:{c}: warning: {m}: sentence not checked{same}{more}"]
      | [] => out := out ++ [s!"{rel}:{l}:{c}: warning: {m}: sentence not checked{more}"]
    | .prose =>
      -- a definition of the running text defines symbols of the article
      let defining := ctx.kind == .text && (String.ofList texts[s]!).contains "\\coloneqq"
      let more := consequences s
      if stated ctx then
        let env := (List.range d.sentences.length).filter fun t => (d.sentences[t]!).1.env == ctx.env
        let unread := env.filter isProse
        if unread.head? == some s then
          let first := env.headD s
          -- a result without a label is named by the beginning of its statement
          let name := capitalize (kindString ctx.kind) ++
            (if !ctx.label.isEmpty then s!" {Codes.toString ctx.label}" else
              let (_, a0, b0) := d.sentences[first]!
              let t := (Codes.toString ((all.drop a0).take (min 32 (b0 - a0)))).replace "\n" " "
              s!" \"{t}{if b0 - a0 > 32 then "…" else ""}\"")
          let read := env.filter fun t => match d.outcomes[t]? with
            | some (.compiled _ _) => true | _ => false
          let what := if !read.isEmpty then
              s!"is only partly checked: Leanify cannot read {unread.length} of its {env.length} sentences ({linesText (unread.map lineOf)})"
            else if env.length == 1 then "is not checked: Leanify cannot read its statement"
            else s!"is not checked: Leanify cannot read any of its {env.length} sentences"
          let phrases := (unread.filterMap fun t => nounPhrase texts[t]!).eraseDups
          let phraseHint := match phrases with
            | [] => ""
            | ps => s!"; unknown noun {fewOf 2 (ps.map fun p => s!"\"{p}\"")}"
          let hint := unknownIn unread ++ phraseHint
          let hint := if hint.isEmpty then
              "; docs/writing.md lists the forms it reads" else hint
          let mores := String.join (unread.map consequences)
          out := out ++ [s!"{rel}:{l}:{c}: warning: {name} {what}{hint}{mores}"]
      else if !more.isEmpty then
        out := out ++ [s!"{rel}:{l}:{c}: warning: definition not read{unknownIn [s]}{more}"]
      else if prose && defining then
        out := out ++ [s!"{rel}:{l}:{c}: info: definition not read{unknownIn [s]}: {excerpt s}"]
      else if prose && ctx.kind != .text then
        out := out ++ [s!"{rel}:{l}:{c}: info: {kindString ctx.kind} sentence not read: {excerpt s}"]
    | .compiled ds ks =>
      if claims then
        for i in ds do
          out := out ++ [s!"{rel}:{l}:{c}: info: defines {gs.getD i s!"g{i}"} ({defName d i})"]
        for k in ks do
          match d.claims[k]? with
          | some cl => out := out ++ [s!"{rel}:{l}:{c}: info: claim {k}: {cl.body.tex cs gs []}"]
          | none => pure ()
  return (out, cov)

/-- Compile the article at `path` natively and print its diagnostics. Returns
the number of sentences that failed to compile. -/
def checkArticle (V : Vocab) (path : System.FilePath) (prose claims : Bool := false) : IO Nat := do
  let lines ← readLines path
  match compileArticle V lines with
  | none =>
    IO.eprintln s!"{path}: error: the article could not be read (no \\begin\{document}, or unbalanced math)"
    pure 1
  | some d =>
    let (out, cov) := diagnostics V path.toString lines d prose claims
    for l in out do IO.println l
    IO.println s!"{path}: {d.globs.length} definitions, {d.claims.length} claims\n{cov.render}"
    pure (d.outcomes.filter (fun o => match o with | .failed _ => true | _ => false)).length

end Leanify
