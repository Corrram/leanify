import Leanify.Render

/-! # Checking an article quickly

`checkArticle` runs the compiler natively on an article file and reports, in the
`file:line:col: severity: message` format of editors, every sentence that did not
compile and (optionally) every sentence of a result or proof that has no
mathematical reading. It is the fast feedback loop while writing: it certifies
nothing. The kernel-checked compilation is `#leanify_article`. -/

namespace Leanify

/-- The version of Leanify (of the Lean package and of `leanify.sty`). A reading is
the reading of a version: reports and the PDF name it. -/
def version : String := "0.5.0"

/-- The file contents as lines of code points (CRLF normalized). -/
def readLines (path : System.FilePath) : IO (List (List Nat)) := do
  let s ← IO.FS.readFile path
  let s := s.replace "\r\n" "\n"
  let lines := s.splitOn "\n"
  let lines := if lines.getLast? == some "" then lines.dropLast else lines
  pure (lines.map fun l => l.toList.map Char.toNat)


/-! ### The files an article inputs

An article is often several files: `\input{sections/intro}`, `\include{proofs}`,
`\subfile{appendix}`, and macros in a local package. The quick check reads them
where they are input, as TeX does, and reports every finding at its own file and
line. Only `.tex` files and the article's own `.sty` files are read: a drawing or a
table that is input is layout. -/

/-- The first `\input{f}`, `\include{f}` or `\subfile{f}` of a line, outside a comment:
the text before it, the file name and the text after it. -/
def inputUse (l : List Char) : Option (List Char × String × List Char) :=
  let rec go : Nat → List Char → List Char → Option (List Char × String × List Char)
    | 0, _, _ => none
    | _ + 1, _, [] => none
    | f + 1, before, c :: cs =>
      if c == '%' then none
      else if c == '\\' then
        let name := cs.takeWhile Char.isAlpha
        let rest := cs.dropWhile Char.isAlpha
        if name.isEmpty then go f ((cs.take 1).reverse ++ c :: before) (cs.drop 1)
        else if ["input", "include", "subfile"].contains (String.ofList name) then
          match rest.dropWhile (· == ' ') with
          | '{' :: r =>
            match r.dropWhile (· != '}') with
            | '}' :: after =>
              some (before.reverse, String.ofList ((r.takeWhile (· != '}')).filter (· != ' ')), after)
            | _ => none
          | _ => go f (name.reverse ++ c :: before) rest
        else go f (name.reverse ++ c :: before) rest
      else go f (c :: before) cs
  go (l.length + 1) [] l

/-- The packages a line loads with `\usepackage` (outside a comment). -/
def packagesOf (l : List Char) : List String :=
  let l := l.dropWhile (· == ' ')
  if l.take 11 != "\\usepackage".toList then [] else
  let r := l.drop 11
  let r := match r with
    | '[' :: r' => (r'.dropWhile (· != ']')).drop 1
    | _ => r
  match r with
  | '{' :: r' =>
    ((String.ofList (r'.takeWhile (· != '}'))).splitOn ",").map fun n =>
      String.ofList (n.toList.filter (· != ' '))
  | _ => []

/-- An article as the compiler reads it: its lines with the files it inputs in
their places, and where each line comes from. -/
structure SourceFiles where
  lines : Array (List Nat) := #[]
  /-- The file and the line in it of each line. -/
  origin : Array (String × Nat) := #[]
  /-- The files read besides the article. -/
  inputs : Array String := #[]
  /-- Files that are input and were not read (not found, or not a `.tex` file). -/
  skipped : Array String := #[]

def SourceFiles.push (s : SourceFiles) (l : List Char) (file : String) (n : Nat) : SourceFiles :=
  { s with lines := s.lines.push (l.map Char.toNat), origin := s.origin.push (file, n) }

/-- The lines of a file, numbered from 1 (CRLF normalized); of a file that is a
document of its own, the lines of its body. -/
def numberedLines (path : System.FilePath) (body : Bool) : IO (List (List Char × Nat)) := do
  let s ← IO.FS.readFile path
  let lines := (s.replace "\r\n" "\n").splitOn "\n"
  let lines := if lines.getLast? == some "" then lines.dropLast else lines
  let ls := (lines.map String.toList).zipIdx.map fun (l, i) => (l, i + 1)
  let isBegin (l : List Char) := l.take 16 == "\\begin{document}".toList
  let isEnd (l : List Char) := l.take 14 == "\\end{document}".toList
  if body && ls.any (isBegin ·.1) then
    pure (((ls.dropWhile (!isBegin ·.1)).drop 1).takeWhile (!isEnd ·.1))
  else pure ls

/-- Read a file into the source, following what it inputs (`shown` is the file's
path as findings print it). -/
partial def readInto (dir : Option System.FilePath) (path : System.FilePath) (shown : String) (body : Bool)
    (depth : Nat) (acc : SourceFiles) : IO SourceFiles := do
  let mut acc := acc
  -- a file of the article's folder, and its path as findings print it (with `/` on
  -- every system, so that the output of the check does not depend on the system)
  let inDir (f : System.FilePath) : System.FilePath := match dir with
    | some d => d / f
    | none => f
  let shownIn (f : String) : String := match dir with
    | some d => s!"{d}/{f}"
    | none => f
  for (l, n) in ← numberedLines path body do
    -- the rest of the line, after an input in it
    let mut rest := l
    let mut whole := true
    let mut fuel := 8
    while fuel > 0 do
      fuel := fuel - 1
      match (if depth < 8 then inputUse rest else none) with
      | some (before, name, after) =>
        let file : System.FilePath := if (System.FilePath.mk name).extension.isNone then name ++ ".tex" else name
        if file.extension == some "tex" && (← (inDir file).pathExists) then
          unless before.all Char.isWhitespace do acc := acc.push before shown n
          let inner := shownIn file.toString
          acc := { acc with inputs := if acc.inputs.contains inner then acc.inputs else acc.inputs.push inner }
          acc ← readInto dir (inDir file) inner true (depth + 1) acc
          rest := after
          whole := false
        else
          -- (`\input{sections/#1}` in a macro of the preamble names no file)
          unless name.contains '#' do
            acc := { acc with skipped := if acc.skipped.contains name then acc.skipped else acc.skipped.push name }
          fuel := 0
      | none => fuel := 0
    if whole || !(rest.all Char.isWhitespace) then acc := acc.push rest shown n
    -- the article's own packages: their macros are the article's
    if !body && depth < 8 then
      for pkg in packagesOf l do
        let file := inDir (pkg ++ ".sty")
        if pkg != "leanify" && (← file.pathExists) then
          let inner := shownIn (pkg ++ ".sty")
          acc := { acc with inputs := if acc.inputs.contains inner then acc.inputs else acc.inputs.push inner }
          acc ← readInto dir file inner false (depth + 1) acc
  pure acc

/-- The article at `path` with the files it inputs. -/
def readSource (path : System.FilePath) : IO SourceFiles :=
  let dir := path.parent.filter fun p => !p.toString.isEmpty
  readInto dir path path.toString false 0 {}

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
    else if e.code == E.ambiguous then "ambiguous phrase"
    else if e.code == E.dependence then "unknown dependence"
    else if e.code == E.finding then "not read"
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
   "tilde", "underline", "check", "sup", "inf", "sum", "prod", "circ", "exp", "log", "ln", "sin", "cos", "tan", "pi",
   "emptyset", "varnothing", "setminus", "notin", "forall", "exists", "neg", "lnot", "land", "lor",
   "wedge", "vee", "lfloor", "rfloor", "lceil", "rceil", "lim", "binom", "tbinom", "dbinom", "Rightarrow", "implies", "Longrightarrow", "iff", "Leftrightarrow", "Longleftrightarrow", "subseteq", "subseteqq", "supseteq", "supseteqq",
   "mid", "nmid", "divides", "equiv", "pmod", "bmod", "mod", "gcd", "dot", "ddot", "breve", "acute",
   "grave", "vec", "mathring", "widetilde", "widecheck", "overrightarrow", "substack", "#", "ll", "gg", "asymp",
   "limsup", "liminf", "cdots", "dots"]

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
    if d == "\\subset" || d == "\\supset" then
      s!"{d} is ambiguous (inclusion or strict inclusion): write \\subseteq or \\subsetneq, or state the convention (We write $A\\subset B$ if $A\\subseteq B$.)"
    else if isNotation d then s!"unknown notation {d}" else s!"{d} is not defined"
  else if e.code == E.ambiguous then
    s!"{d}; say which is meant in the text (By a … we mean …)"
  else if e.code == E.finding then d
  else if e.code == E.dependence then
    s!"the dependence of a constant is stated by variables ($k$, $I$) or the fixed data, not by \"{d}\"; name the variables it stands for"
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
  /-- The proofs, and those of them that are read completely. -/
  proofs : Nat := 0
  complete : Nat := 0

def Coverage.add (c : Coverage) (kind : String) (outcome : Outcome) : Coverage :=
  let (a, b, p) := match outcome with
    | .compiled _ _ => (1, 0, 0) | .failed _ => (0, 1, 0) | .prose => (0, 0, 1)
  match c.rows.find? (·.1 == kind) with
  | some _ => { c with rows := c.rows.map fun (k, x, y, z) => if k == kind then (k, x + a, y + b, z + p) else (k, x, y, z) }
  | none => { c with rows := c.rows ++ [(kind, a, b, p)] }

def Coverage.render (c : Coverage) : String :=
  let line (k : String) (a b p : Nat) := s!"  {k}: {a} compiled, {b} failed, {p} prose (of {a + b + p})"
  let total := c.rows.foldl (fun (x, y, z) (_, a, b, p) => (x + a, y + b, z + p)) (0, 0, 0)
  String.intercalate "\n" (c.rows.map (fun (k, a, b, p) => line k a b p) ++
    [line "all" total.1 total.2.1 total.2.2] ++
    (if c.proofs == 0 then [] else
      [s!"  complete proofs: {c.complete} of {c.proofs} (a result is derived from a proof that is read completely)"]))

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

/-- The spellings of the defining sign that the lexer reads. -/
def defSigns : List String := ["\\coloneqq", ":=", "\\vcentcolon=", "\\colonequals", "\\triangleq", "\\mathrel{:=}"]

/-- The text `t` defines the symbol `m` with `\coloneqq` (or `:=`). -/
def definesSym (t : List Char) (m : String) : Bool :=
  (spellings m).any fun sp => (occurrences t sp).any fun after =>
    let r := afterHead 32 after
    defSigns.any fun d => r.take d.length == d.toList

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

/-- `line 3` or `lines 3, 7` (a line of another file with its file: `sec/a.tex:3`). -/
def linesText (ls : List String) : String :=
  let ls := ls.eraseDups
  s!"line{if ls.length == 1 then "" else "s"} {String.intercalate ", " ls}"

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
    (prose claims : Bool) (origin : Nat → String × Nat := fun l => (rel, l)) :
    List String × Coverage := Id.run do
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
  -- the line of a sentence, as a finding names it (with its file, in an input file)
  let lineOf (s : Nat) : String :=
    let (file, l) := origin (lineCol lines (d.sentences[s]!).2.1).1
    if file == rel then toString l else s!"{file}:{l}"
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
  -- a proof with sentences that are not read, and not reported either (prose, or a
  -- construction of proofs the grammar does not have): its result can be checked, but
  -- it is not derived from the printed proof
  let quiet (t : Nat) : Bool := match d.outcomes[t]? with
    | some (.compiled _ _) => false
    | some (.failed e) => e.code == E.unsupported
    | _ => true
  let derived (p : ProofInfo) : Bool := p.complete && !p.steps.isEmpty
  cov := { cov with proofs := d.proofs.length, complete := (d.proofs.filter derived).length }
  for s in [0:d.sentences.length] do
    let (pctx, pa, _) := d.sentences[s]!
    if pctx.kind == .proof && (List.range s).all (fun t => (d.sentences[t]!).1.env != pctx.env) then
      if let some p := d.proofs.find? (·.env == pctx.env) then
        let sents := (List.range d.sentences.length).filter fun t => (d.sentences[t]!).1.env == p.env
        let unread := sents.filter quiet
        -- (only for a result whose statement is read: the others are reported themselves)
        let stated := !p.proves.isEmpty && (List.range d.sentences.length).any fun t =>
          let (rc, _, _) := d.sentences[t]!
          (match rc.kind with | .result _ => true | _ => false) && rc.label == p.proves &&
            (match d.outcomes[t]? with | some (.compiled _ _) => true | _ => false)
        if !derived p && !unread.isEmpty && stated then
          let (pl, pc) := lineCol lines pa
          let (pfile, pl) := origin pl
          let name := Codes.toString p.proves
          out := out ++ [s!"{pfile}:{pl}:{pc}: info: the proof of {name} is not read completely \
            (Leanify cannot read {unread.length} of its {sents.length} sentences): {name} can be checked, \
            but it is not derived from this proof"]
    let (ctx, a, _) := d.sentences[s]!
    let (l, c) := lineCol lines a
    let (rel, l) := origin l
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
      let defining := ctx.kind == .text && defSigns.any fun d => (String.ofList texts[s]!).contains d
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
          | some cl => out := out ++ [s!"{rel}:{l}:{c}: info: claim {k}: {V.texTypes (cl.body.tex cs gs [])}"]
          | none => pure ()
  return (out, cov)

/-- The end of a sentence in the text: its span ends one code point into its last
token, which may be the closing of a display (`\end{equation}`, `\]`, `$$`). -/
def sentenceEnd (all : List Nat) (stop : Nat) : Nat :=
  if stop == 0 then 0 else
  match all.drop (stop - 1) with
  | 92 :: r =>
    let name := r.takeWhile Lex.isLetter
    if name.isEmpty then stop + 1
    else match r.drop name.length with
      | 123 :: r' => stop + name.length + 1 + (r'.takeWhile (· != 125)).length + 1
      | _ => stop + name.length
  | 36 :: 36 :: _ => stop + 1
  | _ => stop

open Lean (Json toJson) in
/-- A finding `file:line:column: severity: message`, in its parts. -/
def findingJson (f : String) : Json :=
  let sevs := ["warning", "info", "error"]
  let cut := sevs.findSome? fun sev =>
    match f.splitOn s!": {sev}: " with
    | pre :: m :: more => some (pre, sev, String.intercalate s!": {sev}: " (m :: more))
    | _ => none
  match cut with
  | some (pre, sev, msg) =>
    let parts := pre.splitOn ":"
    let n := parts.length
    let file := String.intercalate ":" (parts.take (n - 2))
    Json.mkObj [("file", toJson file), ("line", toJson ((parts.getD (n - 2) "").toNat?.getD 0)),
      ("column", toJson ((parts.getD (n - 1) "").toNat?.getD 0)), ("severity", toJson sev),
      ("message", toJson msg)]
  | none => Json.mkObj [("message", toJson f)]

open Lean (Json toJson) in
/-- The check as JSON, for tools: the findings, every sentence with its place, its
text and its outcome, the definitions, the claims with their readings, and the proofs. -/
def checkJson (V : Vocab) (path : String) (src : SourceFiles) (d : Doc) (out : List String)
    (cov : Coverage) : Json := Id.run do
  let lines := src.lines.toList
  let all := joinLines lines
  let origin (l : Nat) : String × Nat := src.origin[l - 1]?.getD (path, l)
  let cs := V.constNames.map Codes.toString
  let gs := d.globNames
  let mut sents : Array Json := #[]
  for s in [0:d.sentences.length] do
    let (ctx, a, b) := d.sentences[s]!
    let b := sentenceEnd all b
    let (l1, c1) := lineCol lines a
    let (l2, c2) := lineCol lines b
    let (f1, l1) := origin l1
    let (f2, l2) := origin l2
    let o : List (String × Json) := match d.outcomes[s]? with
      | some (.failed e) => [("outcome", toJson "failed"), ("message", toJson (failedMessage e))]
      | some (.compiled ds ks) =>
        [("outcome", toJson "compiled"), ("definitions", toJson ds), ("claims", toJson ks)]
      | _ => [("outcome", toJson "prose")]
    let base : List (String × Json) := [
      ("index", toJson s), ("file", toJson f1), ("line", toJson l1), ("column", toJson c1),
      ("endFile", toJson f2), ("endLine", toJson l2), ("endColumn", toJson c2),
      ("environment", toJson (kindString ctx.kind)), ("env", toJson ctx.env),
      ("label", toJson (Codes.toString ctx.label)), ("proves", toJson (Codes.toString ctx.proves)),
      ("text", toJson (Codes.toString ((all.drop a).take (b - a))))]
    sents := sents.push (Json.mkObj (base ++ o))
  let roleOf (r : Role) : String := match r with
    | .definition => "definition" | .statement _ => "statement" | .step _ => "proof step" | .text => "text"
  let claims : List Json := (List.range d.claims.length).map fun k =>
    let c := d.claims[k]!
    Json.mkObj [("index", toJson k), ("sentence", toJson c.sent), ("role", toJson (roleOf c.role)),
      ("reading", toJson (V.texTypes (c.body.tex cs gs []))), ("premises", toJson c.premises),
      ("cites", toJson (c.cites.map Codes.toString))]
  let defs : List Json := (List.range d.values.length).map fun i =>
    Json.mkObj [("index", toJson i), ("name", toJson (defName d i)), ("symbol", toJson (gs.getD i ""))]
  let proofs : List Json := d.proofs.map fun p =>
    Json.mkObj [("env", toJson p.env), ("proves", toJson (Codes.toString p.proves)),
      ("complete", toJson (p.complete && !p.steps.isEmpty)), ("steps", toJson p.steps)]
  let rows : List (String × Json) := cov.rows.map fun (k, a, b, p) =>
    (k, Json.mkObj [("compiled", toJson a), ("failed", toJson b), ("prose", toJson p)])
  return Json.mkObj [
    ("article", toJson path), ("leanify", toJson version), ("inputs", toJson src.inputs),
    ("skipped", toJson src.skipped), ("findings", Json.arr (out.map findingJson).toArray),
    ("sentences", Json.arr sents), ("definitions", Json.arr defs.toArray),
    ("claims", Json.arr claims.toArray), ("proofs", Json.arr proofs.toArray),
    ("coverage", Json.mkObj (rows ++ [("proofsTotal", toJson cov.proofs), ("proofsComplete", toJson cov.complete)]))]

/-- Compile the article at `path` natively, with the files it inputs, and print its
diagnostics (as JSON with `json`). Returns the number of sentences that failed to
compile. -/
def checkArticle (V : Vocab) (path : System.FilePath) (prose claims : Bool := false)
    (json : Bool := false) : IO Nat := do
  let src ← readSource path
  let lines := src.lines.toList
  match compileArticle V lines with
  | none =>
    IO.eprintln s!"{path}: error: the article could not be read (no \\begin\{document}, or unbalanced math)"
    pure 1
  | some d =>
    let origin (l : Nat) : String × Nat := src.origin[l - 1]?.getD (path.toString, l)
    let (out, cov) := diagnostics V path.toString lines d prose claims origin
    if json then IO.println (checkJson V path.toString src d out cov).compress
    else
      for l in out do IO.println l
      IO.println s!"{path}: {d.globs.length} definitions, {d.claims.length} claims\n{cov.render}"
      -- the files read with the article (`leanify.sty` checks them for changes)
      unless src.inputs.isEmpty do
        IO.println s!"{path}: inputs: {String.intercalate ", " src.inputs.toList}"
      unless src.skipped.isEmpty do
        IO.println s!"{path}: not read: {String.intercalate ", " src.skipped.toList} (input, but not a .tex file of the article)"
    pure (d.outcomes.filter (fun o => match o with | .failed _ => true | _ => false)).length

end Leanify
