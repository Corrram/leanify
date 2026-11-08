import Leanify.Check
import Leanify.Meta
import Leanify.Report
import Leanify.Library.Fields

/-! The `leanify` command line.

* `leanify check ARTICLE.tex [--vocab FIELDS] [--prose] [--claims]`
  compiles the article natively and prints its diagnostics (fast; certifies
  nothing). Projects with their own vocabulary define a three-line executable
  calling `Leanify.checkArticle`.
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
  "usage: leanify check ARTICLE.tex [--vocab FIELD,FIELD,…] [--prose] [--claims]\n" ++
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

def startsSection (lines : List Codes) : Bool :=
  lines.any fun l => ((Codes.toString l).trimAsciiStart.toString).startsWith "\\section"

def prepare (path : System.FilePath) (opts : List String) : IO UInt32 := do
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
  let dir := path.parent.getD "."
  let file := (path.fileName.getD "article.tex")
  let some ns := (optArg opts "--name").orElse (fun _ => dir.normalize.fileName)
    | IO.eprintln "leanify init: give the namespace with --name NAME"; pure 2
  unless validModule ns do
    IO.eprintln s!"leanify init: {ns} is not a Lean module name; give one with --name NAME"
    return 2
  let contents ← IO.FS.readFile path
  let lines ← readLines path
  let some d := compileArticle V lines
    | IO.eprintln s!"{path}: error: the article could not be read (no \\begin\{document}, or unbalanced math)"; pure 1
  let pin := sourcePin contents
  let cs := V.constNames.map Codes.toString
  let gs := d.globNames
  -- where the library's source directory is: the folders above the namespace's own
  let dirParts := (dir.normalize.components.filter (· != "."))
  let nsParts := ns.splitOn "."
  let srcDir : Option String :=
    if dirParts.length ≥ nsParts.length && dirParts.drop (dirParts.length - nsParts.length) == nsParts then
      let pre := dirParts.take (dirParts.length - nsParts.length)
      some (if pre.isEmpty then "." else String.intercalate "/" pre)
    else none
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

    lake exe leanify prepare {path} --lean {dir / "Compiled.lean"}

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
{vocabDef}
#leanify_article {ns} \"{file}\" \"{pin}\"{vocabWith}
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

#leanify_semantics {ns} \"{file}\"{modelWith}
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
"
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

#leanify_certify {ns} \"{file}\" using {ns}.Proofs
"
  writeNew (dir / "Compiled.lean") compiled
  writeNew (dir / "Article.lean") article
  writeNew (dir / "Proofs.lean") proofs
  writeNew (dir / "Certified.lean") certified
  let root := nsParts.headD ns
  IO.println s!"\n{d.values.length} definitions and {d.claims.length} claims."
  match srcDir with
  | some src =>
    IO.println s!"Add the library to lakefile.toml (once):

[[lean_lib]]
name = \"{root}\"
srcDir = \"{src}\"
globs = [\"{root}.+\"]

then build the certificate with `lake build {ns}.Certified`."
  | none =>
    let want := String.intercalate "/" nsParts
    IO.println s!"The files of namespace {ns} must lie in a folder path that ends in {want}: move them, or choose --name to match {dir}."
  pure 0

def main (args : List String) : IO UInt32 := do
  match args with
  | "check" :: path :: opts =>
    if let .error e := vocabOf (fieldsOf opts) then
      IO.eprintln s!"leanify check: {e}"
      return 2
    let vocab := (vocabOf (fieldsOf opts)).toOption.getD Vocab.core
    let failed ← checkArticle vocab path (opts.contains "--prose") (opts.contains "--claims")
    pure (if failed == 0 then 0 else 1)
  | "prepare" :: path :: opts => prepare path opts
  | "init" :: path :: opts => initArticle path opts
  | _ => IO.eprintln usage; pure 2
