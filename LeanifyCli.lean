import Leanify.Check
import Leanify.Meta
import Leanify.Report
import Leanify.Library.Fields

/-! The `leanify` command line.

* `leanify check ARTICLE.tex [--vocab FIELDS] [--prose] [--claims] [--json]`
  compiles the article natively, with the files it inputs, and prints its
  diagnostics (fast; certifies nothing); `--json` prints them for tools, with every
  sentence, its place and its text. Projects with their own vocabulary define a
  three-line executable calling `Leanify.checkArticle`.
* `leanify certify ARTICLE.tex [--vocab FIELDS] [--name NAME]` goes from the article to
  its certificate: it writes the Lean files and makes the project if there are none,
  fetches the packages if they are missing, updates the pin and runs `lake build`.
* `leanify tex ARTICLE.tex [--vocab FIELDS] [--certify]` is what `leanify.sty` runs on a
  compile: the quick check and, with `--certify`, the certificate, written to
  `ARTICLE.leanify.out` as records that TeX reads.
* `leanify flatten ARTICLE.tex [OUT.tex]` writes the article with the files it
  inputs in their places, as one file (the certificate pins one file).
* `leanify --version` prints the version.
* `leanify init ARTICLE.tex [--name NAME] [--vocab FIELDS]` writes the
  four Lean files of an article next to it (`Compiled`, `Article`, `Proofs`,
  `Certified`, in namespace `NAME`, by default the article's folder name), with a
  stub proof of every claim, and prints the `lean_lib` entry for `lakefile.toml`.
  It never overwrites an existing file.
* `leanify prepare ARTICLE.tex --lean COMPILED.lean [--cache DIR --module PREFIX]`
  updates the article's pin in `COMPILED.lean` and writes the lexing cache: one
  module per section, named after its content, with the certificates of its
  blocks, and the index module `DIR.lean`. Run it before `lake build`.

`FIELDS` are the fields of the vocabulary the article uses, separated by commas
(`numbers,analysis`; `docs/vocabulary.md` lists them); the core vocabulary is
always there. -/

open Leanify

def usage : String :=
  "usage: leanify check ARTICLE.tex [--vocab FIELD,FIELD,…] [--prose] [--claims] [--json]\n" ++
  "       leanify certify ARTICLE.tex [--vocab FIELD,FIELD,…] [--name NAME]\n" ++
  "       leanify tex ARTICLE.tex [--vocab FIELD,FIELD,…] [--certify] [--status] (for leanify.sty)\n" ++
  "       leanify flatten ARTICLE.tex [OUT.tex]\n" ++
  "       leanify --version\n" ++
  "       leanify init ARTICLE.tex [--name NAME] [--vocab FIELD,FIELD,…]\n" ++
  "       leanify prepare ARTICLE.tex --lean COMPILED.lean [--cache DIR --module PREFIX]"

def optArg (opts : List String) (flag : String) : Option String :=
  match opts.dropWhile (· != flag) with
  | _ :: v :: _ => some v
  | _ => none

/-- The fields named by `--vocab` (none: the core vocabulary alone). -/
def fieldsOf (opts : List String) : List String :=
  (((optArg opts "--vocab").getD "").splitOn ",").map (fun n => String.ofList (n.toList.filter (· != ' ')))
    |>.filter fun n => n != "" && n != "core"

/-- The vocabulary of the named fields, or the names that are not fields. -/
def vocabOf (fs : List String) : Except String Vocab :=
  match Fields.unknown fs with
  | [] => .ok (if fs == ["unitsquare"] then UnitSquare.withCore
      else if fs.isEmpty then Vocab.core else Fields.select fs)
  | bad => .error s!"unknown vocabulary field {String.intercalate ", " bad}; the fields are \
      {String.intercalate ", " Fields.names}"

def fnvHex (s : String) : String :=
  let h := s.toUTF8.foldl (fun (h : UInt64) b => (h ^^^ b.toUInt64) * 0x100000001b3) 0xcbf29ce484222325
  let hex := String.ofList (Nat.toDigits 16 h.toNat)
  String.ofList (List.replicate (16 - hex.length) '0') ++ hex

/-- Replace the pin of the `#leanify_article` command in a Lean file. -/
def updatePin (file : System.FilePath) (pin : String) : IO Bool := do
  let s ← IO.FS.readFile file
  let parts := s.splitOn "\"fnv1a64:"
  match parts with
  | [pre, post] =>
    let rest := post.dropWhile (· != '"')
    let s' := pre ++ "\"" ++ pin ++ rest
    if s' != s then IO.FS.writeFile file s'
    pure (s' != s)
  | _ => throw (IO.userError s!"{file}: expected exactly one pin \"fnv1a64:…\"")

/-- A certificate pins one file: say so for an article that inputs others. -/
def noteInputs (path : System.FilePath) : IO Unit := do
  let src ← readSource path
  unless src.inputs.isEmpty do
    IO.eprintln s!"{path}: note: the article inputs {String.intercalate ", " src.inputs.toList}. \
      The certificate covers {path} alone; `leanify flatten {path} OUT.tex` writes one file with all of them."

/-- `leanify flatten`: the article and the files it inputs, as one file. -/
def flatten (path : System.FilePath) (out : Option String) : IO UInt32 := do
  let src ← readSource path
  let text := String.join (src.lines.toList.map fun l => Codes.toString l ++ "\n")
  match out with
  | some o =>
    if (System.FilePath.mk o).normalize == path.normalize then
      IO.eprintln "leanify flatten: the output is the article itself"
      return 2
    IO.FS.writeFile o text
    IO.println s!"wrote {o} ({src.lines.size} lines, from {src.inputs.size + 1} files)"
  | none => IO.print text
  pure 0

def startsSection (lines : List Codes) : Bool :=
  lines.any fun l => ((Codes.toString l).trimAsciiStart.toString).startsWith "\\section"

def prepare (path : System.FilePath) (opts : List String) : IO UInt32 := do
  noteInputs path
  let contents ← IO.FS.readFile path
  let pin := sourcePin contents
  if let some lean := optArg opts "--lean" then
    if ← updatePin lean pin then IO.println s!"{lean}: pin updated to {pin}"
  match optArg opts "--cache", optArg opts "--module" with
  | some dir, some pre =>
    let src ← readLines path
    let some k := src.findIdx? isBeginDocument | throw (IO.userError "no \\begin{document}")
    let some ms := macrosOf (joinLines (src.take k)) | throw (IO.userError "the preamble macros could not be read")
    let bs := blocksOf (src.drop (k + 1)) (linesOffset (src.take (k + 1))) none []
    -- blocks, with their modes, grouped by section
    let mut groups : Array (Array (String × String)) := #[#[]]
    let mut mode : List Bool := []
    for (_, ls) in bs do
      let text := joinLines ls
      let some (_, m') := lexBlock ms text mode | throw (IO.userError "a block could not be lexed")
      if startsSection ls && !groups.back!.isEmpty then groups := groups.push #[]
      let modeS := String.ofList (mode.map fun b => if b then '1' else '0')
      groups := groups.modify (groups.size - 1) (·.push (modeS, Codes.toString text))
      mode := m'
    let dirP : System.FilePath := dir
    IO.FS.createDirAll dirP
    let msS := encodeMacros ms
    let mut names : Array String := #[]
    for g in groups do
      if g.isEmpty then continue
      let body := String.join (g.toList.map fun (m, t) =>
        s!"#leanify_lex_cache {msS.quote} {m.quote} {t.quote}\n")
      let name := "S" ++ (fnvHex body).take 12
      names := names.push name
      let file := dirP / (name ++ ".lean")
      unless ← file.pathExists do
        IO.FS.writeFile file (s!"import Leanify.Meta\n\n/-! Lexing certificates of {path.fileName.getD ""}, " ++
          "generated by `leanify prepare`; do not edit. -/\n\n" ++ body)
        IO.println s!"wrote {file}"
    -- remove modules of earlier versions
    for e in ← dirP.readDir do
      if e.fileName.endsWith ".lean" && !names.contains ((e.fileName.dropEnd 5).toString) then
        IO.FS.removeFile e.path
        IO.println s!"removed {e.path}"
    let index := String.join (names.toList.map fun n => s!"import {pre}.{n}\n")
    let indexFile := dirP.withExtension "lean"
    let old ← if ← indexFile.pathExists then IO.FS.readFile indexFile else pure ""
    if old != index then IO.FS.writeFile indexFile index
    -- the compiled file imports the cache
    if let some lean := optArg opts "--lean" then
      let text ← IO.FS.readFile lean
      let imp := s!"import {pre}"
      unless (text.splitOn "\n").any (fun l => l.replace "\r" "" == imp) do
        IO.FS.writeFile lean (imp ++ "\n" ++ text)
        IO.println s!"{lean}: imports {pre}"
    IO.println s!"{names.size} cache modules for {bs.length} blocks"
    pure 0
  | _, _ => pure 0

/-- A dotted Lean module name. -/
def validModule (n : String) : Bool :=
  !n.isEmpty && (n.splitOn ".").all fun c =>
    match c.toList with
    | h :: t => (h.isAlpha || h == '_') && t.all (fun x => x.isAlphanum || x == '_')
    | [] => false

/-- Text for a Lean comment (no comment delimiters inside). -/
def commentSafe (s : String) : String := (s.replace "-/" "- /").replace "/-" "/ -"

/-- Write a file unless it exists. -/
def writeNew (file : System.FilePath) (contents : String) : IO Unit := do
  if ← file.pathExists then IO.println s!"kept {file} (it exists)"
  else
    IO.FS.writeFile file contents
    IO.println s!"wrote {file}"

/-! ### The Lean project of an article -/

/-- The Lean project a folder lies in: the folder or one of the three above it with a
lakefile (as `leanify.sty` looks for it). -/
def findRoot (dir : System.FilePath) : IO (Option System.FilePath) := do
  let abs ← IO.FS.realPath (if dir.toString.isEmpty then "." else dir)
  let mut d := abs
  for _ in [0:4] do
    if (← (d / "lakefile.toml").pathExists) || (← (d / "lakefile.lean").pathExists) then return some d
    match d.parent with
    | some p => d := p
    | none => return none
  return none

/-- A Lean module name made from a file or folder name (`my-paper` gives `MyPaper`). -/
def moduleNameOf (s : String) : String :=
  let parts := (s.splitOn "-").flatMap (·.splitOn "_") |>.flatMap (·.splitOn " ") |>.flatMap (·.splitOn ".")
  let cap (w : String) : String := match (w.toList.filter Char.isAlphanum) with
    | c :: r => String.ofList (c.toUpper :: r)
    | [] => ""
  let n := String.join (parts.map cap)
  match n.toList with
  | [] => "Article"
  | c :: _ => if c.isAlpha then n else "A" ++ n

/-- The compiled Lean file of an article: the one given, `Compiled.lean` next to the
article, or `NS/Compiled.lean` in a folder next to it that compiles `../ARTICLE`. -/
def findCompiled (path : System.FilePath) (given : Option String) : IO (Option System.FilePath) := do
  if let some g := given then return some g
  let dir : System.FilePath := (path.parent.filter fun p => !p.toString.isEmpty).getD "."
  let file := path.fileName.getD ""
  let names (f : System.FilePath) (ref : String) : IO Bool := do
    if !(← f.pathExists) then return false
    return ((← IO.FS.readFile f).splitOn "#leanify_article ").any fun part => (part.splitOn s!"\"{ref}\"").length > 1
  if ← names (dir / "Compiled.lean") file then return some (dir / "Compiled.lean")
  for e in ← dir.readDir do
    if ← e.path.isDir then
      if ← names (e.path / "Compiled.lean") ("../" ++ file) then return some (e.path / "Compiled.lean")
  return none

/-- The namespace a compiled Lean file compiles its article into. -/
def namespaceOf (compiled : System.FilePath) : IO (Option String) := do
  for l in (← IO.FS.readFile compiled).splitOn "\n" do
    let l := l.trimAsciiStart.toString
    if l.startsWith "#leanify_article " then
      return ((l.drop 17).toString.splitOn " ").head?
  return none

def initArticle (path : System.FilePath) (opts : List String) : IO UInt32 := do
  let fs := fieldsOf opts
  if let .error e := vocabOf fs then
    IO.eprintln s!"leanify init: {e}"
    return 2
  let V := (vocabOf fs).toOption.getD Vocab.core
  let unitSquare := fs.contains "unitsquare"
  let selected := !fs.isEmpty && fs != ["unitsquare"]
  -- the Lean meanings of the constants of a field (at most one field has constants)
  let models : List (String × String × String) := [
    ("unitsquare", "Leanify.Library.UnitSquareModel", "Leanify.UnitSquare.model"),
    ("torus", "Leanify.Library.TorusModel", "Leanify.Torus.model"),
    ("complex", "Leanify.Library.ComplexModel", "Leanify.Complex.model")]
  let withModel := models.filter fun (f, _) => fs.contains f
  let model : Option (String × String) := withModel.head?.map fun (_, m, n) => (m, n)
  if withModel.length > 1 then
    IO.eprintln s!"leanify init: the fields {" and ".intercalate (withModel.map (·.1))} all have constants; use one of them"
    return 2
  let dir : System.FilePath := (path.parent.filter fun p => !p.toString.isEmpty).getD "."
  let file := (path.fileName.getD "article.tex")
  -- the Lean project of the article. Without one, a project is made in the article's
  -- folder, with the Lean files in a folder of their own, named after the article's
  let root? ← findRoot dir
  let fresh := root?.isNone
  let absDir ← IO.FS.realPath dir
  -- (an article in the folder of the project itself: its Lean files are in a folder of
  -- their own as well, as a library needs)
  let sub := fresh || root?.map (·.toString) == some absDir.toString
  -- the namespace: the one given, the one of the Lean files the article has, or the
  -- name of its folder
  let existing ← match ← findCompiled path none with
    | some c => namespaceOf c
    | none => pure none
  let some ns := ((optArg opts "--name").orElse fun _ => existing).orElse (fun _ =>
      if sub then some (moduleNameOf (absDir.fileName.getD ((System.FilePath.mk file).fileStem.getD "")))
      else dir.normalize.fileName <|> absDir.fileName)
    | IO.eprintln "leanify init: give the namespace with --name NAME"; pure 2
  unless validModule ns do
    IO.eprintln s!"leanify init: {ns} is not a Lean module name; give one with --name NAME"
    return 2
  if sub && (ns.splitOn ".").length > 1 then
    IO.eprintln s!"leanify init: the Lean files go into a folder named after the namespace; give a name without dots (--name NAME)"
    return 2
  -- where the Lean files go, and the article as they name it
  let leanDir := if sub then dir / ns else dir
  let relArticle := if sub then "../" ++ file else file
  noteInputs path
  let contents ← IO.FS.readFile path
  let lines ← readLines path
  let some d := compileArticle V lines
    | IO.eprintln s!"{path}: error: the article could not be read (no \\begin\{document}, or unbalanced math)"; pure 1
  let pin := sourcePin contents
  let cs := V.constNames.map Codes.toString
  let gs := d.globNames
  let nsParts := ns.splitOn "."
  let fieldList := String.intercalate ", " (fs.map fun f => s!"\"{f}\"")
  let vocabImport := if selected then "import Leanify.Library.Fields\n"
    else if unitSquare then "import Leanify.Library.UnitSquare\n" else ""
  let vocabDef := if selected then
      s!"\n/-- The vocabulary of the article: the core and the fields {String.intercalate ", " fs}. -/\n" ++
      s!"def {ns}.vocabulary : Leanify.Vocab := Leanify.Fields.select [{fieldList}]\n"
    else ""
  let vocabWith := if selected then s!" with {ns}.vocabulary"
    else if unitSquare then " with Leanify.UnitSquare.withCore" else ""
  let modelImport := match model with | some (m, _) => s!"import {m}\n" | none => ""
  let modelWith := match model with | some (_, v) => s!" with {v}" | none => ""
  let compiled := s!"import Leanify.Meta\n{vocabImport}
/-! # `{file}`, compiled by the kernel

`{ns}.compiled : compileArticle {ns}.vocab {ns}.source = some {ns}.doc` is checked
by the kernel from the contents of `{file}`. The last string pins those contents:
after editing the article, run

    lake exe leanify prepare {path} --lean {leanDir / "Compiled.lean"}

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
{vocabDef}
#leanify_article {ns} \"{relArticle}\" \"{pin}\"{vocabWith}
"
  let article := s!"import {ns}.Compiled
import Leanify.Readable
{modelImport}
/-! # The definitions and claims of `{file}` as Lean

For every definition, a Lean definition with the symbol's name, and for every
claim `K`: `claimK` (what the sentence says), `meaningfulK` (every term in it is
defined) and `obligationK` (its premises imply both). Each is tied to the
compiled document by a kernel-checked `rfl` theorem. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#leanify_semantics {ns} \"{relArticle}\"{modelWith}
"
  let defStubs := (List.range d.values.length).map fun i =>
    let sym := gs.getD i ""
    let what := if sym == defName d i || sym.isEmpty then s!"`{defName d i}`" else s!"`{defName d i}` (`{sym}`)"
    s!"/-- Definition {i}: {what} is well defined. -/
theorem defined{i} : wellDefined{i} := by
  unfold wellDefined{i}
  definedness []
"
  let claimStubs := (List.range d.claims.length).map fun k =>
    let c := d.claims[k]!
    let (ctx, a, _) := (d.sentences[c.sent]?).getD default
    let (l, _) := lineCol lines a
    let place := match ctx.kind with
      | .result n => s!"{Codes.toString n} at line {l}"
      | .proof => s!"proof at line {l}"
      | .text => s!"line {l}"
    let ps := if c.premises.isEmpty then "no premises"
      else "premises: " ++ String.intercalate ", " (c.premises.map fun j => s!"claim {j}")
    s!"/-- Claim {k}, {roleString c.role} ({place}; {ps}):
`{commentSafe (c.body.tex cs gs [])}` -/
theorem proof{k} : obligation{k} := by
  intro_premises
  refine ⟨by unfold meaningful{k}; definedness [], ?_⟩
  sorry
" ++ (
    -- a statement with hypotheses: that they can hold together
    let stated : Bool := match c.role with
      | .statement _ | .text => true
      | _ => false
    if stated && c.body.hasHyps then s!"
/-- The hypotheses of claim {k} can hold together:
`{commentSafe (c.body.hyps.tex cs gs [])}` -/
theorem satisfied{k} : satisfiable{k} := by
  unfold satisfiable{k}
  sorry
" else "")
  let stubs := String.intercalate "\n" (defStubs ++ claimStubs)
  let proofs := s!"import {ns}.Article

/-! # Proofs of the definitions and claims of `{file}`

* `definedI : wellDefinedI`: definition `I` makes sense (no division by zero, every
  argument in its domain). `definedness [h₁, …]` proves most of these; give it the
  facts it cannot find.
* `proofK : obligationK`: claim `K` holds. `intro_premises` introduces
  `cJ : claimJ` for each premise `J` (in a proof, the earlier steps and the cited
  results). A claim the text derives (a proof step, or a result with a compiled
  proof) may use only its premises, Mathlib and the article: `#leanify_certify`
  audits this.
* `refuteK : meaningfulK ∧ ¬ claimK` instead records that claim `K` is false as
  stated; readers and the PDF margin then mark it.
* `satisfiedK : satisfiableK`: the hypotheses of statement `K` can hold together (give
  values for its variables). A statement whose hypotheses cannot all hold is true for
  an empty reason; the report says for which statements this is shown.

`leanify_step` is the standard tactic for a whole obligation. The certificate reports
which claims that the text derives it closes.

A proof that still uses `sorry` leaves its claim unverified, and `lake build`
certifies the others. -/

namespace {ns}.Proofs
open {ns}

{stubs}
end {ns}.Proofs
"
  let reportJson := (System.FilePath.mk file).withExtension "leanify.json"
  let reportTex := (System.FilePath.mk file).withExtension "leanify.tex"
  let certified := s!"import {ns}.Proofs
import Leanify.Certify

/-! # The certified article

The kernel checks `{ns}.certificate`: every verified claim of `{file}` holds and
every definition is well defined. `{ns}.verifiedK : meaningfulK ∧ claimK` is then
claim `K`, as stated in the text. The command also writes
`{reportJson}` (for the reader and the diagnostics) and `{reportTex}` (for the
margin marks of `leanify.sty`). -/

#leanify_certify {ns} \"{relArticle}\" using {ns}.Proofs
"
  IO.FS.createDirAll leanDir
  writeNew (leanDir / "Compiled.lean") compiled
  writeNew (leanDir / "Article.lean") article
  writeNew (leanDir / "Proofs.lean") proofs
  writeNew (leanDir / "Certified.lean") certified
  let lib := nsParts.headD ns
  IO.println s!"\n{d.values.length} definitions and {d.claims.length} claims."
  let entry (src : String) : String :=
    s!"[[lean_lib]]\nname = \"{lib}\"\nsrcDir = \"{src}\"\nglobs = [\"{lib}.+\"]\n"
  if fresh then
    -- a project of its own, in the article's folder
    let toolchain := s!"leanprover/lean4:v{Lean.versionString}\n"
    writeNew (dir / "lean-toolchain") toolchain
    writeNew (dir / "lakefile.toml") (s!"name = \"{ns.toLower}\"\n\n" ++
      "[[require]]\nname = \"leanify\"\ngit = \"https://github.com/Corrram/leanify.git\"\nrev = \"main\"\n\n" ++ entry ".")
    IO.println s!"Made a Lean project in {absDir}. `leanify certify {path}` fetches Leanify and mathlib \
      (once) and builds the certificate; or run `lake update` and `lake build {ns}.Certified` there."
    return 0
  -- the library's source directory: the folders between the project and the namespace's own
  let some root := root? | return 0
  let rel := absDir.components.drop root.components.length
  let srcDir : Option String :=
    if sub then some "."
    else if rel.length ≥ nsParts.length && rel.drop (rel.length - nsParts.length) == nsParts then
      let pre := rel.take (rel.length - nsParts.length)
      some (if pre.isEmpty then "." else String.intercalate "/" pre)
    else none
  match srcDir with
  | some src =>
    let lakefile := root / "lakefile.toml"
    if ← lakefile.pathExists then
      let text ← IO.FS.readFile lakefile
      if (text.splitOn s!"name = \"{lib}\"").length > 1 then
        IO.println s!"The library {lib} is in lakefile.toml. Build the certificate with `lake build {ns}.Certified`."
      else
        IO.FS.writeFile lakefile (text ++ (if text.endsWith "\n" then "" else "\n") ++ "\n" ++ entry src)
        IO.println s!"Added the library {lib} to {lakefile}. Build the certificate with `lake build {ns}.Certified`."
    else
      IO.println s!"Add the library to the lakefile (once):\n\n{entry src}\nthen build the certificate with `lake build {ns}.Certified`."
  | none =>
    let want := String.intercalate "/" nsParts
    IO.println s!"The files of namespace {ns} must lie in a folder path that ends in {want}: move them, or choose --name to match {dir}."
  pure 0

/-! ### Checking and certifying an article for `leanify.sty`

`leanify tex ARTICLE.tex` does what the package needs on a compile and writes the
result as `ARTICLE.leanify.out`, a list of records that TeX reads line by line: the
kind of a record on one line, then each of its fields on a line of its own.

    W  LINE, MESSAGE          a finding at a line of the article
    F  FILE, LINE, MESSAGE    a finding in a file the article inputs
    M  MESSAGE                a warning without a line
    S  TEXT                   a line of the summary, for the terminal

The file is the same for the same article and proofs, so that `latexmk` sees no
change between its passes. -/

/-- A record of `ARTICLE.leanify.out`. -/
inductive Rec where
  | at (line : Nat) (msg : String)
  | inFile (file : String) (line : Nat) (msg : String)
  | warn (msg : String)
  | say (text : String)

def Rec.lines : Rec → List String
  | .at l m => ["W", toString l, m]
  | .inFile f l m => ["F", f, toString l, m]
  | .warn m => ["M", m]
  | .say t => ["S", t]

/-- A finding `file:line:column: severity: message`, in its parts. -/
def splitFinding (f : String) : Option (String × Nat × String × String) :=
  ["warning", "info", "error"].findSome? fun sev =>
    match f.splitOn s!": {sev}: " with
    | pre :: m :: more =>
      let parts := pre.splitOn ":"
      let n := parts.length
      some (String.intercalate ":" (parts.take (n - 2)), (parts.getD (n - 2) "").toNat?.getD 0, sev,
        String.intercalate s!": {sev}: " (m :: more))
    | _ => none

/-- The quick check of an article, as records. -/
def checkRecs (V : Vocab) (path : System.FilePath) : IO (Array Rec) := do
  let src ← readSource path
  let lines := src.lines.toList
  match compileArticle V lines with
  | none => pure #[.warn "Leanify could not read the article (no \\begin{document}, or unbalanced math)"]
  | some d =>
    let origin (l : Nat) : String × Nat := src.origin[l - 1]?.getD (path.toString, l)
    let (out, cov) := diagnostics V path.toString lines d false false origin
    let mut recs : Array Rec := #[]
    for f in out do
      match splitFinding f with
      | some (file, line, sev, msg) =>
        if sev != "info" then
          recs := recs.push (if file == path.toString then .at line msg else .inFile file line msg)
      | none => pure ()
    recs := recs.push (.say s!"{d.globs.length} definitions, {d.claims.length} claims")
    let total := cov.rows.foldl (fun (x, y, z) (_, a, b, p) => (x + a, y + b, z + p)) (0, 0, 0)
    recs := recs.push (.say s!"sentences: {total.1} compiled, {total.2.1} failed, {total.2.2} prose (of {total.1 + total.2.1 + total.2.2})")
    if cov.proofs > 0 then
      recs := recs.push (.say s!"complete proofs: {cov.complete} of {cov.proofs}")
      if cov.complete < cov.proofs then
        recs := recs.push (.warn s!"Complete proofs: {cov.complete} of {cov.proofs}. A result whose proof has \
          sentences that Leanify does not read can be checked, but it is not derived from its printed proof \
          (leanify check --prose lists the sentences)")
    pure recs

/-- The errors of the output of `lake build` of a certificate, as records, and whether
it was built. -/
def buildRecs (output : String) : Array Rec × Bool := Id.run do
  let mut recs : Array Rec := #[]
  let mut built := false
  for l in output.splitOn "\n" do
    let l := (l.replace "\r" "").trimAscii.toString
    if l.startsWith "Build completed successfully" then built := true
    else if l.startsWith "error: " && (l.splitOn ".lean:").length > 1 then
      recs := recs.push (.warn (l.drop 7).toString)
  return (recs, built)

/-- What the certificate of an article says, from its report `ARTICLE.leanify.json`: the
claims that are false as stated, at their lines, and the summary. The records are those
of the report, whether it was just built or not, so they are the same on every compile.
A report of another state of the article gives none. -/
def reportRecs (path : System.FilePath) : IO (Array Rec) := do
  let file := path.withExtension "leanify.json"
  unless ← file.pathExists do return #[]
  let .ok j := Lean.Json.parse (← IO.FS.readFile file) | return #[]
  if (j.getObjValAs? String "sourceHash").toOption != some (sourcePin (← IO.FS.readFile path)) then return #[]
  let arr (k : String) : Array Lean.Json := ((j.getObjVal? k).toOption.bind (·.getArr?.toOption)).getD #[]
  let str (o : Lean.Json) (k : String) : String := (o.getObjValAs? String k).toOption.getD ""
  let claims := arr "claims"
  let sentences := arr "sentences"
  let mut recs : Array Rec := #[]
  for c in claims do
    if str c "status" == "refuted" then
      let line := ((c.getObjValAs? Nat "sentence").toOption.bind fun i =>
        sentences[i]?.bind fun s => (s.getObjValAs? Nat "line").toOption).getD 0
      recs := recs.push (.at line s!"this {str c "role"} is false as stated: refuted in Lean by {str c "justification"}")
  let count (k v : String) : Nat := (claims.filter fun c => str c k == v).size
  let derived := count "status" "text"
  let steps := if count "step" "standard" + count "step" "argument" == 0 then ""
    else s!" ({count "step" "standard"} by the standard tactic)"
  recs := recs.push (.say s!"certificate: {claims.size} claims: {derived} derived in the text from their citations{steps}, \
    {count "status" "companion"} justified by companion proofs, {count "status" "refuted"} refuted, \
    {count "status" "unverified"} unverified; {(arr "definitions").size} definitions well defined")
  let withHyps := count "hypotheses" "shown" + count "hypotheses" "open"
  if count "hypotheses" "open" > 0 then
    recs := recs.push (.say s!"hypotheses shown to hold together: {count "hypotheses" "shown"} of {withHyps} statements")
  pure recs

/-- Run a command in a folder; its output (both streams) and whether it succeeded. -/
def run (cmd : String) (args : Array String) (cwd : System.FilePath) : IO (String × Bool) := do
  try
    let out ← IO.Process.output { cmd, args, cwd := some cwd }
    pure (out.stdout ++ out.stderr, out.exitCode == 0)
  catch e => pure (s!"{cmd} could not be run: {e}", false)

/-- The time a file was last changed (none: no such file). -/
def modified (f : System.FilePath) : IO (Option IO.FS.SystemTime) := do
  if ← f.pathExists then pure (some (← f.metadata).modified) else pure none

/-- Update the pin and build the certificate of an article whose Lean files exist;
the output of `lake` goes to `log`. -/
def buildCertificate (path : System.FilePath) (opts : List String) (log : String → IO Unit) :
    IO (Array Rec) := do
  let dir : System.FilePath := (path.parent.filter fun p => !p.toString.isEmpty).getD "."
  let some root ← findRoot dir
    | return #[.warn "The certificate needs a Lean project (a lakefile in the article's folder or up to \
        three folders above): it was not built. `leanify certify ARTICLE.tex` makes one"]
  -- the Lean files; the first time, they are written
  let mut made := false
  if (← findCompiled path (optArg opts "--lean")).isNone then
    let code ← initArticle path opts
    if code != 0 then return #[.warn "Leanify could not write the Lean files of the article (see the log)"]
    made := true
  let some compiled ← findCompiled path (optArg opts "--lean")
    | return #[.warn s!"The Lean files of {path} were not found: name its compiled file with the option lean"]
  let some ns ← namespaceOf compiled
    | return #[.warn s!"{compiled} has no #leanify_article command"]
  let module := (optArg opts "--module").getD (ns ++ ".Certified")
  if !(← (root / ".lake" / "packages").pathExists) && (← (root / "lakefile.toml").pathExists) &&
      ((← IO.FS.readFile (root / "lakefile.toml")).splitOn "[[require]]").length > 1 then
    return #[.warn s!"Leanify and mathlib are not fetched yet: run `lake update` in {root} once (or `leanify \
      certify {path}` in a terminal), then compile again"]
  -- the pin, with the lexing cache of the article when the module is its own `NS.Certified`
  let leanDir := (compiled.parent.filter fun p => !p.toString.isEmpty).getD "."
  let cache := if module == ns ++ ".Certified"
    then ["--cache", (leanDir / "LexCache").toString, "--module", ns ++ ".LexCache"] else []
  discard <| prepare path (["--lean", compiled.toString] ++ cache)
  -- nothing changed since the last build: the status file is newer than the article and
  -- the Lean files
  let status := path.withExtension "leanify.tex"
  let mut newest ← modified path
  for e in ← leanDir.readDir do
    if e.fileName.endsWith ".lean" then
      let t ← modified e.path
      if newest.isNone || (t.isSome && newest.get! < t.get!) then newest := t
  let statusTime ← modified status
  if !made && statusTime.isSome && newest.isSome && newest.get! ≤ statusTime.get! then
    log s!"the certificate is up to date ({module})\n"
    return ← reportRecs path
  log s!"lake build {module} (in {root})\n"
  let (output, _) ← run "lake" #["build", module] root
  log output
  let (recs, built) := buildRecs output
  if built then pure (recs ++ (← reportRecs path))
  else pure (recs.push (.warn s!"The certificate did not build (see {path.withExtension "leanify.log"})"))

/-- `leanify tex ARTICLE.tex [--vocab FIELDS] [--certify] [--no-check] [--lean FILE]
[--module MODULE]`: the quick check, and with `--certify` the certificate, written as
records for `leanify.sty`. -/
def texCommand (path : System.FilePath) (opts : List String) : IO UInt32 := do
  -- (what is printed goes to `ARTICLE.leanify.log`, where the package sends it)
  IO.println s!"leanify {Leanify.version}: {path}"
  let log (t : String) : IO Unit := IO.print t
  let mut recs : Array Rec := #[]
  match vocabOf (fieldsOf opts) with
  | .error e => recs := recs.push (.warn e)
  | .ok V =>
    unless opts.contains "--no-check" do recs := recs ++ (← checkRecs V path)
    if opts.contains "--certify" then recs := recs ++ (← buildCertificate path opts log)
  -- the marks of a status file older than the article may be out of date
  if !opts.contains "--certify" && opts.contains "--status" then
    let status := path.withExtension "leanify.tex"
    match ← modified status, ← modified path with
    | some t, some a =>
      if t < a then recs := recs.push (.warn s!"{path} changed after its certificate was built: the margin \
        marks may be out of date. Rebuild, or load the package with certify")
    | _, _ => pure ()
  let text := String.join ((recs.toList.flatMap Rec.lines).map (· ++ "\n"))
  IO.FS.writeFile (path.withExtension "leanify.out") (s!"leanify {Leanify.version}\n" ++ text)
  log text
  pure 0

/-- `leanify certify ARTICLE.tex [--vocab FIELDS] [--name NS]`: everything from the
article to its certificate, in a terminal: the Lean files and the project if there are
none, the packages if they are not fetched, the pin, and the build. -/
def certifyCommand (path : System.FilePath) (opts : List String) : IO UInt32 := do
  let dir : System.FilePath := (path.parent.filter fun p => !p.toString.isEmpty).getD "."
  if (← findCompiled path (optArg opts "--lean")).isNone then
    let code ← initArticle path opts
    if code != 0 then return code
  let some root ← findRoot dir
    | IO.eprintln "leanify certify: no Lean project (run `leanify init` first)"; return 1
  let some compiled ← findCompiled path (optArg opts "--lean")
    | IO.eprintln s!"leanify certify: the Lean files of {path} were not found (--lean FILE names its compiled file)"; return 1
  let some ns ← namespaceOf compiled
    | IO.eprintln s!"leanify certify: {compiled} has no #leanify_article command"; return 1
  let inTerminal (cmd : String) (args : Array String) : IO UInt32 := do
    IO.println s!"$ {cmd} {" ".intercalate args.toList}   (in {root})"
    try
      let child ← IO.Process.spawn { cmd, args, cwd := some root }
      child.wait
    catch e => IO.eprintln s!"{cmd} could not be run: {e}. Install Lean (https://lean-lang.org/install)."; pure 1
  unless ← (root / ".lake" / "packages").pathExists do
    let code ← inTerminal "lake" #["update"]
    if code != 0 then return code
  discard <| prepare path ["--lean", compiled.toString]
  let module := (optArg opts "--module").getD (ns ++ ".Certified")
  inTerminal "lake" #["build", module]

def main (args : List String) : IO UInt32 := do
  match args with
  | "check" :: path :: opts =>
    if let .error e := vocabOf (fieldsOf opts) then
      IO.eprintln s!"leanify check: {e}"
      return 2
    let vocab := (vocabOf (fieldsOf opts)).toOption.getD Vocab.core
    let failed ← checkArticle vocab path (opts.contains "--prose") (opts.contains "--claims")
      (opts.contains "--json")
    pure (if failed == 0 then 0 else 1)
  | "tex" :: path :: opts => texCommand path opts
  | "certify" :: path :: opts => certifyCommand path opts
  | ["flatten", path] => flatten path none
  | ["flatten", path, out] => flatten path (some out)
  | ["--version"] => IO.println s!"leanify {Leanify.version}"; pure 0
  | "prepare" :: path :: opts => prepare path opts
  | "init" :: path :: opts => initArticle path opts
  | _ => IO.eprintln usage; pure 2
