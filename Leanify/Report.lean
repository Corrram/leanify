import Leanify.Meta
import Lean.Data.Json

/-! # The per-sentence report of a compiled article

`<article>.leanify.json` records, for every sentence of the article, whether it
compiled, the claims and definitions it produced, their readings and Lean
statements, and (after `#leanify_certify`) how each claim is verified. Readers,
editors and CI read this file; it is never an input to a certificate.

`sourceHash` pins the article text. Lake does not track files read during
elaboration, so `#leanify_article` takes the hash of `article.tex` as an
argument: editing the article changes the hash, the pin must be updated, and
the changed Lean file makes Lake recompile and recertify. -/
namespace Leanify
open Lean Elab Command Meta

/-- The current pin of the article file. -/
def readPin (rel : String) : CommandElabM String := do
  let path ← liftCoreM (resolvePath rel)
  pure (sourcePin (← IO.FS.readFile path))

/-- The pin recorded by `#leanify_article` (the literal `Foo.sourceHash`). -/
def recordedPin (ns : Name) : CommandElabM String := do
  match (← getEnv).find? (ns ++ `sourceHash) with
  | some (.defnInfo v) =>
    match v.value with
    | .lit (.strVal s) => pure s
    | _ => throwError "{ns ++ `sourceHash} is not a string literal"
  | _ => throwError "{ns} has no compiled article (run #leanify_article first)"

/-- Stop if the article changed after it was compiled. -/
def checkFresh (ns : Name) (rel : String) : CommandElabM Unit := do
  let now ← readPin rel
  let was ← recordedPin ns
  unless now == was do
    throwError "{rel} changed after it was compiled ({was}, now {now}): update the pin in \
      #leanify_article to \"{now}\" so that the article is recompiled"

def moduleOf (env : Environment) (c : Name) : Option Name :=
  (env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!

def roleString : Role → String
  | .definition => "definition"
  | .statement _ => "statement"
  | .step _ => "proof step"
  | .text => "text"

/-- The statements that the article quotes from the literature and does not prove: the
claims of a result whose heading cites its source, when no proof of the article is a
proof of that result. They are the assumptions of the article: `#leanify_semantics`
declares each as an axiom `Foo.Quoted.claimK`, and the certificate names them. -/
def Doc.quotedClaims (d : Doc) : List Nat :=
  (List.range d.claims.length).filter fun k =>
    match d.claims[k]? with
    | some c =>
      match c.role, d.sentences[c.sent]? with
      | .statement _, some (ctx, _, _) =>
        ctx.quoted && c.premises.isEmpty && !(d.proofs.any fun p => p.proves == ctx.label)
      | _, _ => false
    | none => false

/-- How a claim is verified, for the report. -/
structure ClaimInfo where
  /-- `text`, `companion`, `quoted` (a statement quoted from the literature, assumed),
  `refuted` or `unverified`. -/
  status : String := "unverified"
  /-- The quoted statements that the verification of the claim rests on. -/
  rests : List Nat := []
  rank : Nat := 0
  justification : String := ""
  module : String := ""
  /-- Why a claim is not verified (a proof with `sorry`, an unverified citation). -/
  note : String := ""
  /-- For a claim the text derives: `standard` if the standard tactic (`leanify_step`)
  proves its obligation, `argument` if its proof needs a Lean argument beyond it, and
  empty if that was not tried. -/
  step : String := ""
  /-- For a claim with hypotheses: `shown` if they are proved to hold together
  (`J.satisfiedK`, for the first claim `K` with these hypotheses), `open` if not; empty
  for a claim without hypotheses and for one made under a hypothesis that the proof
  refutes. -/
  hypotheses : String := ""

/-- The claim that stands for the hypotheses of claim `k`: the first claim with the same
hypotheses. None: the claim has no hypotheses, or the proof refutes them (a proof by
contradiction), so that they are not meant to hold together. That the hypotheses of a
claim can hold together is asked once, of this claim (`satisfiableK`). -/
def Doc.hypsOf (d : Doc) (k : Nat) : Option Nat :=
  match d.claims[k]? with
  | some c =>
    if c.refuted || !c.body.hasHyps then none else
    (List.range (k + 1)).find? fun j => match d.claims[j]? with
      | some c' => !c'.refuted && c'.body.hasHyps && c'.body.hyps == c.body.hyps
      | none => false
  | none => none

/-- The status of each labelled result, for the margin marks of `leanify.sty`:
`text` (every sentence of the statement compiled and every claim derived in the
text from its citations, each step closed by the standard tactic, or not tried, and
under hypotheses that are shown to hold together),
`argued` (derived in the text, with a reservation: a step whose proof needs a Lean
argument beyond the standard tactic, or a claim whose hypotheses are not shown to hold
together, so that it may be true for an empty reason), `verified` (every sentence compiled, every claim
verified), `refuted` (a claim of the result is false), `partial` (some sentences
compiled and verified), `quoted` (a result quoted from the literature, which the article
assumes), `compiled` (compiled claims not yet verified) or `none`.
The steps of a result are its own claims and their premises in its proof. -/
def resultStatus (d : Doc) (claims : Array ClaimInfo) (env : Nat) : String := Id.run do
  let sents := (List.range d.sentences.length).filter fun s => (d.sentences[s]!).1.env == env
  let outs := sents.map fun s => d.outcomes[s]?.getD .prose
  let ks := outs.flatMap fun o => match o with | .compiled _ cs => cs | _ => []
  let allCompiled := !outs.isEmpty && outs.all fun o => match o with | .compiled _ _ => true | _ => false
  let st (k : Nat) := (claims.getD k {}).status
  if ks.isEmpty then return "none"
  if ks.any (st · == "refuted") then return "refuted"
  -- (a result quoted from the literature: assumed, not verified)
  if allCompiled && ks.all (st · == "quoted") then return "quoted"
  let ok (k : Nat) : Bool := st k == "text" || st k == "companion"
  let allVerified := ks.all ok
  let someVerified := ks.any ok
  if allCompiled && allVerified then
    if !ks.all (fun k => st k == "text") then return "verified"
    -- the result's own claims and the steps of its proof
    let steps := (ks ++ ks.flatMap fun k => (d.claims[k]?.map (·.premises)).getD []).eraseDups
    let isStep (k : Nat) : Bool := match (d.claims[k]? : Option Claim) with
      | some ⟨_, _, Role.step _, _, _, _⟩ => true
      | _ => ks.contains k
    return (if steps.any (fun k => isStep k &&
        ((claims.getD k {}).step == "argument" || (claims.getD k {}).hypotheses == "open")) then "argued" else "text")
  if someVerified then return "partial"
  return "compiled"

/-- `<article>.leanify.tex`: the status of every labelled result, a summary, and the
formal reading of every definition and of every statement, read by `leanify.sty`
(`status` marks the results in the margin, `\leanifyreadings` prints the readings).
The entries a version of the package does not know are declared first, so that an
older `leanify.sty` reads the file as well. -/
def statusTex (V : Vocab) (rel : String) (lines : List (List Nat)) (d : Doc) (claims : Array ClaimInfo)
    (verified : List Nat) : String := Id.run do
  let mut out := s!"% Generated by Leanify from {rel}; do not edit.\n"
  out := out ++ "\\providecommand\\leanifyversion[1]{}\\providecommand\\leanifydefinition[3]{}" ++
    "\\providecommand\\leanifyreading[4]{}\\providecommand\\leanifysteps[2]{}" ++
    "\\providecommand\\leanifyhypotheses[2]{}\\providecommand\\leanifyquoted[2]{}" ++
    "\\providecommand\\leanifynotdefined[1]{}\\providecommand\\leanifycontext[1]{}\n"
  out := out ++ s!"\\leanifyversion\{{version}}\n"
  let mut seen : List Nat := []
  for s in [0:d.sentences.length] do
    let (ctx, _, _) := d.sentences[s]!
    match ctx.kind with
    | .result _ =>
      if !ctx.label.isEmpty && !seen.contains ctx.env then
        seen := ctx.env :: seen
        out := out ++ s!"\\leanifystatus\{{Codes.toString ctx.label}}\{{resultStatus d claims ctx.env}}\n"
    | _ => pure ()
  -- the readings: what Lean is asked to prove, for a reader of the PDF to compare
  let cs := V.constNames.map Codes.toString
  let gs := d.globNames
  let lineOf (s : Nat) : Nat := (lineCol lines ((d.sentences[s]?.map (·.2.1)).getD 0)).1
  for i in [0:d.values.length] do
    -- (a quantity that the article does not define has no reading: it is listed below)
    if (undefinedDefs V d).contains i then continue
    let sent := (List.range d.outcomes.length).find? fun s =>
      match d.outcomes[s]! with
      | .compiled ds _ => ds.contains i
      | _ => false
    let line := (sent.map lineOf).getD 0
    out := out ++ s!"\\leanifydefinition\{{line}}\{{gs.getD i ""}}\{{V.texTypes ((d.values[i]!).tex cs gs [])}}\n"
  for k in [0:d.claims.length] do
    let c := d.claims[k]!
    let (ctx, _, _) := d.sentences[c.sent]?.getD default
    let stated : Bool := match c.role with
      | .statement _ | .text => true
      | _ => false
    if stated then
      -- (a claim of the running text is printed as a sentence)
      let kind := if ctx.kind == .text then "sentence" else kindString ctx.kind
      out := out ++ s!"\\leanifyreading\{{Codes.toString ctx.label}}\{{kind}}\{{lineOf c.sent}}\{{V.texTypes (c.body.tex cs gs [])}}\n"
  let count (st : String) := ((List.range d.claims.length).filter fun k => (claims.getD k {}).status == st).length
  let compiled := (d.outcomes.filter fun o => match o with | .compiled _ _ => true | _ => false).length
  -- of the claims derived in the text, those the standard tactic closes; of the
  -- different hypotheses under which claims are made, those shown to hold together
  let countBy (f : ClaimInfo → Bool) := ((List.range d.claims.length).filter fun k => f (claims.getD k {})).length
  -- (the claims that follow a sentence which is not read are counted apart, below)
  let open_ := d.openContext.map (·.1)
  let countAt (f : ClaimInfo → Bool) :=
    ((List.range d.claims.length).filter fun k => !open_.contains k && f (claims.getD k {})).length
  let tried := countAt fun i => i.step != ""
  if tried > 0 then
    out := out ++ s!"\\leanifysteps\{{countAt fun i => i.step == "standard"}}\{{tried}}\n"
  let reps := (List.range d.claims.length).filter fun k => d.hypsOf k == some k
  if !reps.isEmpty then
    out := out ++ s!"\\leanifyhypotheses\{{(reps.filter fun k => (claims.getD k {}).hypotheses == "shown").length}}\{{reps.length}}\n"
  -- the statements quoted from the literature, and the verified claims that rest on them
  let quoted := count "quoted"
  if quoted > 0 then
    out := out ++ s!"\\leanifyquoted\{{quoted}}\{{countBy fun i => i.status != "quoted" && !i.rests.isEmpty}}\n"
  -- what the article uses without defining it
  match notDefinedHere V d true with
  | [] => pure ()
  | ns => out := out ++ s!"\\leanifynotdefined\{{String.intercalate ", " ns}}\n"
  -- the verified claims that follow a sentence of their result or proof that is not read:
  -- they are verified as read, and the summary counts them apart
  let after := (verified.filter open_.contains).length
  if after > 0 then
    out := out ++ s!"\\leanifycontext\{{after}}\n"
  let derived := countAt fun i => i.status == "text"
  out := out ++ s!"\\leanifysummary\{{d.claims.length}}\{{verified.length - after}}\{{derived}}\{{d.values.length}}\{{compiled}}\{{d.sentences.length}}\n"
  return out

/-- Write `<article>.leanify.json`. Claims without information are unverified. -/
def writeReport (ns jn : Name) (rel : String) (d : Doc) (claims : Array ClaimInfo)
    (defs : Array (String × String)) (verified : List Nat) (axioms : List Name) : CommandElabM Unit := do
  let path ← liftCoreM (resolvePath rel)
  let lines ← readLines path
  let nm (s : String) : Name := Name.mkSimple s
  let names := (List.range d.values.length).map (defName d)
  let gTex := d.globNames
  let V ← liftCoreM <| articleVocab ns
  let cTex := V.constNames.map Codes.toString
  let short (str : String) : String :=
    ((str.replace (toString ns ++ ".") "").replace "Leanify.Prelude." "").replace "↑unitInterval" "I"
  let ppConst (n : Name) : CommandElabM String := liftTermElabM do
    match (← getEnv).find? n with
    | some (.defnInfo v) => pure (short (toString (← ppExpr v.value)))
    | _ => pure ""
  let mut claimsJ : Array Json := #[]
  for k in [0:d.claims.length] do
    let c := d.claims[k]!
    let info := claims.getD k {}
    claimsJ := claimsJ.push <| Json.mkObj [
      ("index", toJson k), ("sentence", toJson c.sent), ("role", toJson (roleString c.role)),
      ("cites", toJson (c.cites.map Codes.toString)), ("premises", toJson c.premises),
      ("status", toJson info.status), ("rank", toJson info.rank), ("rests", toJson info.rests),
      -- (the sentences of its result or proof before it that are not read: its reading
      -- may lack a hypothesis of one of them, or keep one that it ends)
      ("after", toJson (d.unreadBefore c.sent)),
      ("reading", toJson (V.texTypes (c.body.tex cTex gTex []))),
      ("lean", toJson (← ppConst (ns ++ nm s!"claim{k}"))),
      ("meaningful", toJson (← ppConst (ns ++ nm s!"meaningful{k}"))),
      ("justification", toJson info.justification), ("module", toJson info.module),
      ("note", toJson info.note), ("step", toJson info.step), ("hypotheses", toJson info.hypotheses),
      -- (the claim that stands for these hypotheses, and for that claim the Lean statement
      -- that they can hold together; `refuted`: the proof refutes them)
      ("hypothesesOf", ((d.hypsOf k).map toJson).getD Json.null), ("refuted", toJson c.refuted),
      ("satisfiable", toJson (← ppConst (ns ++ nm s!"satisfiable{k}")))]
  let mut defsJ : Array Json := #[]
  for i in [0:d.values.length] do
    let g := d.globs[i]!
    let sent := (List.range d.outcomes.length).find? fun s =>
      match d.outcomes[s]! with
      | .compiled ds _ => ds.contains i
      | _ => false
    let (just, mod) := defs.getD i ("", "")
    defsJ := defsJ.push <| Json.mkObj [
      ("index", toJson i), ("name", toJson names[i]!), ("symbol", toJson gTex[i]!),
      ("key", toJson (Codes.toString g.key)), ("sentence", (sent.map toJson).getD Json.null),
      ("lean", toJson (← ppConst (ns ++ nm names[i]!))),
      ("wellDefined", toJson (← ppConst (ns ++ nm s!"wellDefined{i}"))),
      ("justification", toJson just), ("module", toJson mod),
      -- (a quantity that the article introduces and does not define)
      ("undefined", toJson ((undefinedDefs V d).contains i))]
  let mut sentsJ : Array Json := #[]
  for s in [0:d.sentences.length] do
    let (ctx, a, b) := d.sentences[s]!
    let (l1, c1) := lineCol lines a
    let (l2, c2) := lineCol lines b
    let out : List (String × Json) := match d.outcomes[s]? with
      | some (.failed e) => [("outcome", toJson "failed"), ("code", toJson e.code), ("message", toJson (errMessage e))]
      | some (.compiled ds cs) => [("outcome", toJson "compiled"), ("definitions", toJson ds), ("claims", toJson cs)]
      | _ => [("outcome", toJson "prose")]
    let base : List (String × Json) := [
      ("index", toJson s), ("start", toJson a), ("stop", toJson b), ("line", toJson l1),
      ("column", toJson c1), ("endLine", toJson l2), ("endColumn", toJson c2),
      ("environment", toJson (kindString ctx.kind)), ("env", toJson ctx.env),
      ("label", toJson (Codes.toString ctx.label))]
    sentsJ := sentsJ.push <| Json.mkObj (base ++ out)
  let report := Json.mkObj [
    ("article", toJson rel), ("leanify", toJson version), ("sourceHash", toJson (← recordedPin ns)),
    ("namespace", toJson (toString ns)), ("justifications", toJson (toString jn)),
    ("verified", toJson verified), ("axioms", toJson (axioms.map toString)),
    ("notDefined", toJson (notDefinedHere V d)),
    ("definitions", Json.arr defsJ), ("claims", Json.arr claimsJ), ("sentences", Json.arr sentsJ)]
  IO.FS.writeFile (path.withExtension "leanify.json") (report.pretty 100 ++ "\n")
  IO.FS.writeFile (path.withExtension "leanify.tex") (statusTex V rel lines d claims verified)

/-- Report sentences that did not compile (as information: they assert nothing). -/
def logUncompiled (rel : String) (d : Doc) : CommandElabM Unit := do
  let lines ← readLines (← liftCoreM (resolvePath rel))
  for s in [0:d.sentences.length] do
    if let some (.failed e) := d.outcomes[s]? then
      let (_, a, _) := d.sentences[s]!
      let (l, c) := lineCol lines a
      logInfo m!"{rel}:{l}:{c}: {failedMessage e}: sentence not checked"

end Leanify
