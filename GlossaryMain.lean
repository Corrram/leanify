import Leanify.Library.Fields

/-! `lake exe glossary > docs/glossary.md` writes the glossary of the vocabulary:
every phrase of every field, with its type and meaning. -/

open Leanify

def mtokText : MTok → String
  | .id n => Codes.toString n
  | .digit d => toString d
  | .sym c => String.singleton (Char.ofNat c)
  | .cmd n => "\\" ++ Codes.toString n ++ " "
  | .lb => "{" | .rb => "}"
  | .setl => "\\{" | .setr => "\\}"
  | .row => "\\\\" | .diff => "d"
  | .text w => "\\text{" ++ Codes.toString w ++ "}"
  | .begin e => "\\begin{" ++ Codes.toString e ++ "}"
  | .finish e => "\\end{" ++ Codes.toString e ++ "}"

def toksText (ts : List MTok) : String := (String.join (ts.map mtokText)).trimAsciiEnd.toString

/-- A phrase as written (`$x$` for the variable, `$a$`, `$b$`, … for arguments). -/
def phraseText (p : Phrase) (start : Nat := 0) : String := Id.run do
  let names := ["x", "a", "b", "c", "d", "e"]
  let mut k := start
  let mut out : List String := []
  for it in p do
    match it with
    | .w w => out := out ++ [Codes.toString w]
    | .m ts => out := out ++ ["$" ++ toksText ts ++ "$"]
    | .v => out := out ++ ["$" ++ names.getD k "y" ++ "$"]; k := k + 1
    | .f segs =>
      let mut s := ""
      let mut first := true
      for seg in segs do
        if !first then s := s ++ names.getD k "y"; k := k + 1
        s := s ++ toksText seg
        first := false
      out := out ++ ["$" ++ s ++ "$"]
  return (" ".intercalate out).replace " - " "-" |>.replace " , " ", " |>.replace " / " "/"

/-- A type, with the names of the field's own types (`B0` without one). -/
def tyText (ts : List Codes) : Ty → String
  | .real => "ℝ" | .prop => "Prop"
  | .base k => match ts[k]? with
    | some n => "$" ++ Codes.toString n ++ "$"
    | none => s!"B{k}"
  | .fn a b => (match a with | .fn .. => "(" ++ tyText ts a ++ ")" | _ => tyText ts a) ++ " → " ++ tyText ts b

/-- A piece of notation on a type (`$+$`). -/
def opText : OpKey → String
  | .ofReal => "a real number" | .add => "$+$" | .sub => "$-$" | .mul => "$\\cdot$" | .div => "$/$"
  | .neg => "$-$ (sign)" | .pow => "$x^n$" | .abs => "$\\lvert x\\rvert$" | .sum => "$\\sum_{k=a}^{b}$"
  | .prod => "$\\prod_{k=a}^{b}$" | .le => "$\\le$" | .lt => "$<$"
  | .fn n => (if n.head? == some 92 then "$" ++ Codes.toString n ++ "$" else "$\\operatorname{" ++ Codes.toString n ++ "}$")
  | .decor n => if n.head? == some 94 then "$x" ++ Codes.toString n ++ "$" else "$" ++ Codes.toString n ++ "{x}$"
  | .call => "$x(t)$"
  | .eq => "$=$" | .ofRealIn => "a number in a set" | .inv => "$x^{-1}$" | .sig => "$f\\colon A\\to B$"

def cell (s : String) : String := s.replace "|" "\\|"

def fieldSection (name : String) (V : Vocab) : List String :=
  [s!"## `{name}`", ""] ++
  (if V.nouns.isEmpty then [] else
    ["| Noun | Of | Meaning |", "| --- | --- | --- |"] ++
    V.nouns.map (fun n => s!"| {cell (phraseText n.sing)} | {tyText V.types n.ty} | {cell n.doc} |") ++ [""]) ++
  (if V.mods.isEmpty then [] else
    ["| Adjective or phrase | Of | Meaning |", "| --- | --- | --- |"] ++
    V.mods.map (fun m => s!"| {cell (phraseText m.phrase)} | {tyText V.types m.ty} | {cell m.doc} |") ++ [""]) ++
  (if V.adjectives.isEmpty then [] else
    ["| Adjective | Of | Meaning |", "| --- | --- | --- |"] ++
    V.adjectives.map (fun a =>
      let words := " ".intercalate (a.words.map Codes.toString) ++ (if a.onDomain then " [on $A$]" else "")
      s!"| {cell words} | {tyText V.types a.ty} | {cell a.doc} |") ++ [""]) ++
  (if V.notions.isEmpty then [] else
    ["| Notion | Type | Meaning |", "| --- | --- | --- |"] ++
    V.notions.map (fun n => s!"| {cell (phraseText n.name 1)} | {tyText V.types n.ty} | {cell n.doc} |") ++ [""]) ++
  (if V.symbols.isEmpty then [] else
    ["| Symbol | Type | Meaning |", "| --- | --- | --- |"] ++
    V.symbols.map (fun s => s!"| ${cell (Codes.toString s.sym)}$ | {tyText V.types s.ty} | {cell s.doc} |") ++ [""]) ++
  (if V.methods.isEmpty then [] else
    ["| Notation | On | Meaning |", "| --- | --- | --- |"] ++
    V.methods.map (fun m => s!"| {cell (opText m.op)} | {tyText V.types m.ty} | {cell m.doc} |") ++ [""])

/-- The tree of the bundles, from `math` down, as nested list items. -/
partial def bundleTree (b : String) (depth : Nat) : List String :=
  let pad := String.ofList (List.replicate (2 * depth) ' ')
  match Fields.bundles.lookup b with
  | some ms => s!"{pad}* `{b}`" :: ms.flatMap fun m => bundleTree m (depth + 1)
  | none => [s!"{pad}* `{b}`"]

/-- The bundles: the tree, and each with its fields. -/
def bundleSection : List String :=
  ["## Bundles", "",
   "A bundle is a name for several fields: `\\usepackage[vocab=analysis]{leanify}` reads an",
   "article with all of them, and `vocab=math` with every field. The realms are the bundles",
   "that `math` is made of. No two fields of a bundle give a phrase different meanings,",
   "except a notion whose meanings take arguments of different types, which the types decide",
   "(`lake exe glossary --bundles` checks this).", ""] ++
  bundleTree "math" 0 ++ [""] ++
  ["| Bundle | Made of | Its fields |", "| --- | --- | --- |"] ++
  Fields.bundles.map (fun (b, ms) =>
    s!"| `{b}` | {", ".intercalate (ms.map fun m => s!"`{m}`")} | {", ".intercalate ((Fields.expand [b]).map fun f => s!"`{f}`")} |") ++ [""]

/-- `glossary --bundles`: the phrases that two fields of a bundle read differently (none,
or the exit status is 1), and the notions that the types of their arguments tell apart. -/
def checkBundles : IO UInt32 := do
  let mut bad := 0
  for (b, _) in Fields.bundles do
    let unknown := Fields.unknown [b]
    unless unknown.isEmpty do
      IO.println s!"{b}: unknown field {", ".intercalate unknown}"
      bad := bad + 1
    if Fields.names.contains b then
      IO.println s!"{b}: a bundle and a field have this name"
      bad := bad + 1
    for (p, fs) in Fields.bundleCollisions b do
      IO.println s!"{b}: \"{phraseText p}\" has several meanings (in {", ".intercalate (fs.map Codes.toString)})"
      bad := bad + 1
  -- every field is in `math`
  let inMath := Fields.expand ["math"]
  let covered (f : String) : Bool :=
    inMath.contains f || inMath.any fun g => ((Fields.includes.lookup g).getD []).contains f
  for f in Fields.names do
    unless covered f do
      IO.println s!"math: the field {f} is in no realm"
      bad := bad + 1
  for (p, fs) in Fields.bundleOverloads "math" do
    IO.println s!"math: \"{phraseText p}\" has a meaning for each type of its arguments (in {", ".intercalate (fs.map Codes.toString)})"
  if bad == 0 then IO.println s!"{Fields.bundles.length} bundles: no phrase with several meanings"
  pure (if bad == 0 then 0 else 1)

/-- A type of the core language as Lean, with the Lean types that the vocabulary names for
its base types. -/
def leanTy (V : Vocab) : Ty → String
  | .real => "ℝ"
  | .prop => "Prop"
  | .fn a b => s!"({leanTy V a} → {leanTy V b})"
  | .base k => s!"({Codes.toString (V.typeLean.getD k ([], [])).1})"

/-- `glossary --models`: a Lean file that states, for every field, that each Lean
declaration the vocabulary names has the type the vocabulary gives its constant, and that
each type has the element named for it. Building it checks the Mathlib side of the
vocabulary without an article (`tests/ModelsCheck/Check.lean`). -/
def modelsFile : List String :=
  let fields := ("core", Vocab.core) :: Fields.all
  let modules := (fields.flatMap fun (_, V) => V.modules.map Codes.toString).eraseDups
  let checks := fields.foldl (fun (acc : List String × List String) (n, V) =>
    let named (c : Codes) : Bool := !c.isEmpty && !Vocab.isDeclaredName c
    let tys := V.typeLean.filterMap fun (t, d) =>
      if named t && named d then some s!"example : {Codes.toString t} := {Codes.toString d}" else none
    let cs := (List.range V.consts.length).filterMap fun i =>
      let l := V.constLean.getD i []
      -- (a constant whose type names a base type without a Lean type is not checked)
      let rec ok : Ty → Bool
        | .base k => named (V.typeLean.getD k ([], [])).1
        | .fn a b => ok a && ok b
        | _ => true
      if named l && ok V.consts[i]! then some s!"example : {leanTy V V.consts[i]!} := {Codes.toString l}" else none
    -- (a field that comes with another states the other's constants again: once is enough)
    let fresh := (tys ++ cs).filter fun l => !acc.2.contains l
    if fresh.isEmpty then acc else (acc.1 ++ ["", s!"/-! ## `{n}` -/", ""] ++ fresh, acc.2 ++ fresh)) ([], [])
  modules.map (s!"import {·}") ++
  ["", "/-! # The Lean meanings of the vocabulary have the types the vocabulary gives them",
   "", "Generated by `lake exe glossary --models`; do not edit by hand. For every field: each type",
   "of the vocabulary with the element named for it, and each constant with its type. -/"] ++
  checks.1

def main (args : List String) : IO UInt32 := do
  if args == ["--bundles"] then return ← checkBundles
  if args == ["--models"] then
    IO.println ("\n".intercalate modelsFile)
    return 0
  let lines := ["# Glossary of the vocabulary", "",
    "Generated by `lake exe glossary` from `Leanify.Fields.all`; do not edit by hand.",
    "An article chooses its fields with `\\usepackage[vocab={…}]{leanify}`",
    "(`docs/vocabulary.md`). `$x$` is the object a noun or adjective is about;",
    "`$a$`, `$b$`, … are the arguments of a notion.", ""] ++
    bundleSection ++
    fieldSection "core" Vocab.core ++ Fields.all.flatMap (fun (n, V) => fieldSection n V)
  IO.println ("\n".intercalate lines)
  pure 0
