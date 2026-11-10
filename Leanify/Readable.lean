import Leanify.Semantics
import Leanify.Report
import Leanify.Tactic

/-! # Readable Lean statements for compiled definitions and claims

`#leanify_semantics Foo "article.tex"` names every article definition as
a Lean constant whose value is its denotation written as ordinary Lean, and
states every claim as a proposition `Foo.claimK`. The model of the vocabulary the
article was compiled with is built from the names of the Lean meanings of its constants
(`Vocab.constLean`); `with M` gives a model written by hand instead.
Each is tied to the compiled document by a theorem proved with `Eq.refl`, so the
kernel checks that the readable form *is* the semantics of the article's text:
`Foo.env` (the definitions), `Foo.holdsK` (claim `K` holds iff `Foo.claimK`),
`Foo.welldefI` (definition `I` is well defined iff `Foo.wellDefinedI`). The
translator is untrusted. -/
namespace Leanify
open Lean Elab Term Meta Command

/-- The Lean type of a term type: `ℝ`, `Prop`, function types, and the base types of the
model `M`, as the model names them (the type of the points of a set, `↥unitInterval`,
stays that type: it is not unfolded into a subtype). -/
partial def tyExpr (M : Expr) : Ty → MetaM Expr
  | .real => pure (Lean.mkConst ``Real)
  | .prop => pure (mkSort Level.zero)
  | .fn a b => do mkArrow (← tyExpr M a) (← tyExpr M b)
  | .base k => withCanUnfoldPred (fun _ ci => pure (ci.name != ``Set.Elem)) do
      let e ← whnf (mkApp (mkApp (Lean.mkConst ``Model.base) M) (mkNatLit k))
      -- (the type of a notion that the article does not define: `Foo.Notion.Graph.1`)
      match e with
      | .proj n i s => pure (.proj n i (← whnf s))
      | _ =>
        if e.isAppOfArity ``Sigma.fst 3 then pure (mkAppN e.getAppFn (e.getAppArgs.set! 2 (← whnf e.getAppArgs[2]!)))
        else pure e

/-- The Lean values of the model's constants, read from its definition. -/
partial def modelConsts (M : Expr) : MetaM (Array Expr) := do
  let rec go (e : Expr) (acc : Array Expr) (fuel : Nat) : MetaM (Array Expr) := do
    if fuel == 0 then return acc
    let e ← whnf e
    if e.isAppOfArity ``List.cons 3 then
      let hd ← whnf (e.getArg! 1)
      let v := if hd.isAppOfArity ``Sigma.mk 4 then hd.getArg! 3 else mkProj ``Sigma 1 hd
      -- (a meaning that is an abbreviation, `abbrev add (z w : ℂ) := z + w`, is written
      -- out: the readable statement then says `z + w`)
      let v ← match v.headBeta with
        | .const n ls =>
          if ← isReducible n then
            match (← getEnv).find? n with
            | some (.defnInfo d) => pure (d.value.instantiateLevelParams d.levelParams ls)
            | _ => pure v
          else pure v
        | _ => pure v
      -- (a proof that Lean moved out of such a meaning, `…._proof_1`, is written back:
      -- `Set.projIcc 0 1 zero_le_one`)
      let env ← getEnv
      let v := v.replace fun e => match e with
        | .const n ls => match n with
          | .str _ last =>
            if last.startsWith "_proof_" then
              match env.find? n with
              | some (.thmInfo d) => some (d.value.instantiateLevelParams d.levelParams ls)
              | _ => none
            else none
          | _ => none
        | _ => none
      go (e.getArg! 2) (acc.push v.headBeta) (fuel - 1)
    else return acc
  go (mkApp (Lean.mkConst ``Model.consts) M) #[] 100000

def primConst : Prim → Option Name
  | .hasDerivWithin => some ``Prelude.hasDerivWithin
  | .intervalIntegral => some ``Prelude.intervalIntegral
  | .intervalIntegrable => some ``Prelude.intervalIntegrable
  | .compact2 => some ``Prelude.compact2
  | .convex2 => some ``Prelude.convex2
  | .symm2 => some ``Prelude.symm2
  | .continuousOn => some ``Prelude.continuousOn
  | .concaveOn => some ``Prelude.concaveOn
  | .strictMonoOn => some ``Prelude.strictMonoOn
  | .fnProp k => some <| match k with
    | .convex => ``Prelude.convexOn | .strictConvex => ``Prelude.strictConvexOn
    | .strictConcave => ``Prelude.strictConcaveOn | .strictAnti => ``Prelude.strictAntiOn
    | .monotone => ``Prelude.monotoneOn | .antitone => ``Prelude.antitoneOn
    | .bounded => ``Prelude.boundedOn | .nonneg => ``Prelude.nonnegOn | .pos => ``Prelude.posOn
    | .differentiable => ``Prelude.differentiableOn | .contDiff => ``Prelude.contDiffOn
    | .injective => ``Prelude.injOn | .lowerSemicont => ``Prelude.lowerSemicontinuousOn
    | .upperSemicont => ``Prelude.upperSemicontinuousOn | .lipschitz => ``Prelude.lipschitzOn
  | .setProp k => some <| match k with
    | .closed => ``Prelude.closed2 | .isOpen => ``Prelude.open2
    | .bounded => ``Prelude.bounded2 | .connected => ``Prelude.connected2
  | .realFn k => some <| match k with
    | .exp => ``Real.exp | .log => ``Real.log | .sin => ``Real.sin | .cos => ``Real.cos
    | .tan => ``Real.tan
  | .pi => some ``Real.pi
  | .isInt => some ``Prelude.isInt
  | .isNat => some ``Prelude.isNat
  | .floor => some ``Prelude.floor
  | .ceil => some ``Prelude.ceil
  | .finSum => some ``Prelude.finSum
  | .finProd => some ``Prelude.finProd
  | .series => some ``Prelude.series
  | .seriesConv => some ``Prelude.seriesConv
  | .limAt => some ``Prelude.limAt
  | .limAtConv => some ``Prelude.limAtConv
  | .limTop => some ``Prelude.limTop
  | .limTopConv => some ``Prelude.limTopConv
  | .factorial => some ``Prelude.factorial
  | .binom => some ``Prelude.binom
  | .zpow => some ``Prelude.zpow
  | .cardIs => some ``Prelude.cardIs
  | _ => none

def realLit (n : Nat) : TermElabM Expr := do
  let e ← Term.elabTerm (← `(($(Syntax.mkNumLit (toString n)) : ℝ))) none
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- The translation context: the model, its constants, and the article's definitions. -/
structure RCtx where
  model : Expr
  consts : Array Expr
  globs : Array Expr

/-- Translate a core term to a readable Lean expression (verified afterwards by `rfl`). -/
partial def readable (R : RCtx) (ls : List Expr) : Tm → TermElabM Expr
  | .glob i => pure (R.globs.getD i (Lean.mkConst `sorryAx))
  | .loc i => pure (ls.getD i (Lean.mkConst `sorryAx))
  | .const i => pure (R.consts.getD i (Lean.mkConst `sorryAx))
  | .prim p => do
    match primConst p with
    | some n => pure (Lean.mkConst n)
    | none =>
      let e := mkApp2 (Lean.mkConst ``Prim.denote) (mkApp (Lean.mkConst ``Model.base) R.model) (toExpr p)
      Meta.reduce e (explicitOnly := false)
  | .app (.app (.prim .rpow) x) y => do mkAppM ``HPow.hPow #[← readable R ls x, ← readable R ls y]
  | .app (.app (.prim .min) x) y => do mkAppM ``Min.min #[← readable R ls x, ← readable R ls y]
  | .app (.app (.prim .max) x) y => do mkAppM ``Max.max #[← readable R ls x, ← readable R ls y]
  | .app (.prim p) x => do
    match primConst p with
    | some n => pure (mkApp (Lean.mkConst n) (← readable R ls x))
    | none => pure (mkApp (← readable R ls (.prim p)) (← readable R ls x))
  | .app f x => do
    let f' ← readable R ls f
    let x' ← readable R ls x
    pure (mkApp f' x').headBeta
  | .lam t _ b => do
    withLocalDeclD `x (← tyExpr R.model t) fun v => do
      mkLambdaFVars #[v] (← readable R (v :: ls) b)
  | .num n => realLit n
  | .add x y => do mkAppM ``HAdd.hAdd #[← readable R ls x, ← readable R ls y]
  | .sub x y => do mkAppM ``HSub.hSub #[← readable R ls x, ← readable R ls y]
  | .mul x y => do mkAppM ``HMul.hMul #[← readable R ls x, ← readable R ls y]
  | .div x y => do mkAppM ``HDiv.hDiv #[← readable R ls x, ← readable R ls y]
  | .neg x => do mkAppM ``Neg.neg #[← readable R ls x]
  | .abs x => do mkAppM ``abs #[← readable R ls x]
  | .powNat x n => do mkAppM ``HPow.hPow #[← readable R ls x, mkNatLit n]
  | .cases c v r => do
    let c' ← readable R ls c
    let v' ← readable R ls v
    let r' ← readable R ls r
    let ty ← inferType v'
    pure (mkApp5 (Lean.mkConst ``ite [Level.succ Level.zero]) ty c'
      (mkApp (Lean.mkConst ``Classical.propDecidable) c') v' r')
  | .undef .real => realLit 0
  | .undef .prop => pure (Lean.mkConst ``False)
  | .undef (.fn a b) => do
    withLocalDeclD `x (← tyExpr R.model a) fun v => do
      mkLambdaFVars #[v] (← readable R (v :: ls) (.undef b))
  | .undef t => do
    let e := mkApp3 (Lean.mkConst ``Ty.default) (mkApp (Lean.mkConst ``Model.base) R.model)
      (mkApp (Lean.mkConst ``Model.default) R.model) (toExpr t)
    Meta.reduce e (explicitOnly := false)
  | .eq x y => do mkEq (← readable R ls x) (← readable R ls y)
  | .lt x y => do mkAppM ``LT.lt #[← readable R ls x, ← readable R ls y]
  | .le x y => do mkAppM ``LE.le #[← readable R ls x, ← readable R ls y]
  | .tt => pure (Lean.mkConst ``True)
  | .not p => do pure (mkNot (← readable R ls p))
  | .and p q => do pure (mkAnd (← readable R ls p) (← readable R ls q))
  | .or p q => do pure (mkOr (← readable R ls p) (← readable R ls q))
  | .iff p q => do pure (mkIff (← readable R ls p) (← readable R ls q))
  | .imp p q => do mkArrow (← readable R ls p) (← readable R ls q)
  | .all t b => do
    withLocalDeclD `x (← tyExpr R.model t) fun v => do
      mkForallFVars #[v] (← readable R (v :: ls) b)
  | .ex t b => do
    withLocalDeclD `x (← tyExpr R.model t) fun v => do
      let body ← mkLambdaFVars #[v] (← readable R (v :: ls) b)
      mkAppM ``Exists #[body]
  | .guard _ e => readable R ls e
  | .the t b => do
    let T ← tyExpr R.model t
    let dflt := mkApp3 (Lean.mkConst ``Ty.default) (mkApp (Lean.mkConst ``Model.base) R.model)
      (mkApp (Lean.mkConst ``Model.default) R.model) (toExpr t)
    let inst := mkApp2 (Lean.mkConst ``Nonempty.intro [Level.succ Level.zero]) T dflt
    withLocalDeclD `x T fun v => do
      let p ← mkLambdaFVars #[v] (← readable R (v :: ls) b)
      pure (mkApp3 (Lean.mkConst ``Classical.epsilon [Level.succ Level.zero]) T inst p)

/-- Recompile natively (the literal `Foo.doc` is certified by `Foo.compiled`). -/
def nativeDoc (ns : Name) (rel : String) : CommandElabM Doc := do
  let path ← liftCoreM (resolvePath rel)
  let lines ← readLines path
  let V ← liftCoreM <| articleVocab ns
  match compileArticle V lines with
  | some d => pure d
  | none => throwError "the article could not be compiled"

/-- A Lean name from its text (`Leanify.Torus.smoothT2`). -/
def nameOfCodes (c : Codes) : Name :=
  ((Codes.toString c).splitOn ".").foldl (fun n s => Name.mkStr n s) Name.anonymous

/-- The model of a vocabulary, from the names of the Lean meanings of its base types and
constants (`Vocab.typeLean`, `Vocab.constLean`): the declarations it names must be
there (the article's Lean file imports `Vocab.modules`), and each constant must have the
type the vocabulary gives it, which the kernel checks when the model is added. -/
def modelOfVocab (ns : Name) (V : Vocab) (d : Doc) : CommandElabM Expr := do
  let env ← getEnv
  let lean (what : String) (c : Codes) : CommandElabM Expr := do
    if c.isEmpty then
      throwError "the vocabulary of {ns} does not name the Lean meaning of {what}: give its model (#leanify_semantics … with M)"
    let n := nameOfCodes c
    unless env.contains n do
      throwError "the Lean meaning {n} of {what} is not there: import the module that defines it \
        ({", ".intercalate (V.modules.map Codes.toString)})"
    pure (Lean.mkConst n)
  -- a notion that the article does not define: an opaque constant `ns.Notion.Name`, of
  -- which Lean knows the type and nothing else
  let notion (name : String) (ty val : Expr) : CommandElabM Expr := do
    let n := ns ++ `Notion ++ Name.mkSimple name
    if (← getEnv).contains n then throwError "the notions of {ns} have two with the Lean name {n}"
    liftCoreM <| addDecl <| Declaration.opaqueDecl
      { name := n, levelParams := [], type := ty, value := val, isUnsafe := false, all := [n] }
    pure (Lean.mkConst n)
  let clean (c : Codes) : String := String.ofList ((Codes.toString c).toList.filter Char.isAlphanum)
  -- the base types, each with an element
  let typeTy := mkSort (Level.succ Level.zero)
  let sigTy := mkApp2 (Lean.mkConst ``Sigma [Level.succ Level.zero, Level.zero]) typeTy
    (.lam `T typeTy (.bvar 0) .default)
  let mut ts : Array Expr := #[]
  for k in [0:V.types.length] do
    let (t, dflt) := V.typeLean.getD k ([], [])
    let what := s!"its type {Codes.toString (V.types.getD k [])}"
    if Vocab.isDeclaredName t then
      -- (a type with an element: the types of the core language are not empty)
      ts := ts.push (← notion (clean t) sigTy
        (mkApp4 (Lean.mkConst ``Sigma.mk [Level.succ Level.zero, Level.zero]) typeTy
          (.lam `T typeTy (.bvar 0) .default) (Lean.mkConst ``Unit) (Lean.mkConst ``Unit.unit)))
    else
      ts := ts.push (mkApp4 (Lean.mkConst ``Sigma.mk [Level.succ Level.zero, Level.zero]) typeTy
        (.lam `T typeTy (.bvar 0) .default) (← lean what t) (← lean (what ++ " (an element of it)") dflt))
  -- (a list of types with an element each: in the universe above them)
  let u1 := Level.succ Level.zero
  let tsE := ts.toList.foldr (fun x acc => mkApp3 (Lean.mkConst ``List.cons [u1]) sigTy x acc)
    (mkApp (Lean.mkConst ``List.nil [u1]) sigTy)
  let baseE := mkApp (Lean.mkConst ``Model.baseOf) tsE
  let defaultE := mkApp (Lean.mkConst ``Model.defaultOf) tsE
  let valTy := mkApp (Lean.mkConst ``Val) baseE
  -- a constant without a meaning: of its type, with the value that every type has
  let opaqueConst (name : String) (ty : Ty) : CommandElabM Expr :=
    notion name (mkApp2 (Lean.mkConst ``Ty.denote) baseE (toExpr ty))
      (mkApp3 (Lean.mkConst ``Ty.default) baseE defaultE (toExpr ty))
  let mut cs : Array Expr := #[]
  for i in [0:V.consts.length] do
    let l := V.constLean.getD i []
    let c ← if Vocab.isDeclaredName l then opaqueConst (clean l) V.consts[i]!
      else lean s!"its constant {i} ({Codes.toString (V.constNames.getD i [])})" l
    cs := cs.push (mkApp4 (Lean.mkConst ``Sigma.mk [Level.zero, Level.zero]) (Lean.mkConst ``Ty)
      (mkApp (Lean.mkConst ``Ty.denote) baseE) (toExpr (V.consts[i]!)) c)
  -- the quantities that the article introduces without defining them (`Let $\chi(G)$
  -- denote the chromatic number of a graph $G$.`): the constants after the vocabulary's
  for i in undefinedDefs V d do
    let g := d.globs[i]!
    unless d.values[i]? == some (.const cs.size) do
      throwError "the undefined quantities of {ns} are not numbered in their order"
    let c ← opaqueConst (defName d i) g.ty
    cs := cs.push (mkApp4 (Lean.mkConst ``Sigma.mk [Level.zero, Level.zero]) (Lean.mkConst ``Ty)
      (mkApp (Lean.mkConst ``Ty.denote) baseE) (toExpr g.ty) c)
  pure (mkApp3 (Lean.mkConst ``Model.mk) baseE defaultE (listExpr valTy cs.toList))

syntax (name := leanifySemantics) "#leanify_semantics " ident str (" with " ident)? : command

@[command_elab leanifySemantics] def elabLeanifySemantics : CommandElab := fun stx => do
  let ns := stx[1].getId
  let some rel := stx[2].isStrLit? | throwUnsupportedSyntax
  checkFresh ns rel
  let d ← nativeDoc ns rel
  -- the model of the vocabulary: the one given, or the one its constants name
  let modelE ← match withClause stx[3] with
    | some v => do pure (Lean.mkConst (← liftCoreM <| realizeGlobalConstNoOverloadWithInfo v))
    | none => do
      let V ← liftCoreM <| articleVocab ns
      if V.consts.isEmpty && V.types.isEmpty && (undefinedDefs V d).isEmpty then pure (Lean.mkConst ``Model.empty)
      else modelOfVocab ns V d
  try
    liftCoreM <| addDecl <| Declaration.defnDecl
      { name := ns ++ `model, levelParams := [], type := Lean.mkConst ``Model, value := modelE,
        hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe }
  catch e =>
    throwError "the model of the vocabulary of {ns} is not well typed: a constant's Lean meaning does not \
      have the type the vocabulary gives it.\n{e.toMessageData}"
  let M := Lean.mkConst (ns ++ `model)
  let consts ← liftTermElabM <| modelConsts M
  -- definitions as readable constants
  let mut R : RCtx := ⟨M, consts, #[]⟩
  let mut vals : Array Expr := #[]
  let baseE := mkApp (Lean.mkConst ``Model.base) M
  for i in [0:d.values.length] do
    let v := d.values[i]!
    let g := d.globs[i]!
    let name := ns ++ Name.mkSimple (defName d i)
    let (ty, val) ← liftTermElabM do
      let ty ← tyExpr M g.ty
      let val ← readable R [] v
      pure (ty, val)
    liftCoreM <| addDecl <| Declaration.defnDecl
      { name, levelParams := [], type := ty, value := val,
        hints := ReducibilityHints.regular 0, safety := DefinitionSafety.safe }
    R := { R with globs := R.globs.push (Lean.mkConst name) }
    vals := vals.push (mkApp4 (Lean.mkConst ``Sigma.mk [Level.zero, Level.zero]) (Lean.mkConst ``Ty)
      (mkApp (Lean.mkConst ``Ty.denote) baseE) (toExpr g.ty) (Lean.mkConst name))
  -- the environment of definition values
  let valTy := mkApp (Lean.mkConst ``Val) baseE
  let gList := listExpr valTy vals.toList
  liftCoreM <| addDecl <| Declaration.defnDecl
    { name := ns ++ `G, levelParams := [], type := mkApp (Lean.mkConst ``List [Level.zero]) valTy,
      value := gList, hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe }
  let docE := Lean.mkConst (ns ++ `doc)
  let gE := Lean.mkConst (ns ++ `G)
  let envLhs := mkApp2 (Lean.mkConst ``Doc.env) M docE
  let envRhs := mkApp2 (Lean.mkConst ``Option.some [Level.zero])
    (mkApp (Lean.mkConst ``List [Level.zero]) valTy) gE
  let envTy := mkApp (Lean.mkConst ``Option [Level.zero]) (mkApp (Lean.mkConst ``List [Level.zero]) valTy)
  kernelRefl (ns ++ `env) envTy envLhs envRhs
  -- well-definedness of each definition
  for i in [0:d.values.length] do
    let v := d.values[i]!
    let p ← liftTermElabM do readable R [] v.defined
    let pn := ns ++ Name.mkSimple s!"wellDefined{i}"
    liftCoreM <| addDecl <| Declaration.defnDecl
      { name := pn, levelParams := [], type := mkSort Level.zero, value := p,
        hints := ReducibilityHints.regular 0, safety := DefinitionSafety.safe }
    let lhs := mkApp4 (Lean.mkConst ``Doc.welldef) M docE gE (mkNatLit i)
    kernelRefl (ns ++ Name.mkSimple s!"welldef{i}") (mkSort Level.zero) lhs (Lean.mkConst pn)
  -- claims
  for k in [0:d.claims.length] do
    let c := d.claims[k]!
    let (pd, pc) ← liftTermElabM do
      pure (← readable R [] c.body.defined, ← readable R [] c.body)
    let dn := ns ++ Name.mkSimple s!"meaningful{k}"
    let cn := ns ++ Name.mkSimple s!"claim{k}"
    liftCoreM <| addDecl <| Declaration.defnDecl
      { name := dn, levelParams := [], type := mkSort Level.zero, value := pd,
        hints := ReducibilityHints.regular 0, safety := DefinitionSafety.safe }
    liftCoreM <| addDecl <| Declaration.defnDecl
      { name := cn, levelParams := [], type := mkSort Level.zero, value := pc,
        hints := ReducibilityHints.regular 0, safety := DefinitionSafety.safe }
    let lhs := mkApp4 (Lean.mkConst ``Doc.holds) M docE gE (mkNatLit k)
    kernelRefl (ns ++ Name.mkSimple s!"holds{k}") (mkSort Level.zero) lhs
      (mkAnd (Lean.mkConst dn) (Lean.mkConst cn))
  -- that the hypotheses of a claim can hold together (`satisfiableK`): a claim with
  -- hypotheses that cannot all hold is true for an empty reason. Asked once for each set
  -- of hypotheses, of the first claim made under it, and not of a claim under a
  -- hypothesis that the proof refutes
  for k in [0:d.claims.length] do
    if d.hypsOf k == some k then
      let p ← liftTermElabM do readable R [] (d.claims[k]!).body.hyps
      liftCoreM <| addDecl <| Declaration.defnDecl
        { name := ns ++ Name.mkSimple s!"satisfiable{k}", levelParams := [], type := mkSort Level.zero, value := p,
          hints := ReducibilityHints.regular 0, safety := DefinitionSafety.safe }
  -- sizes, premises and proof obligations
  let natE := Lean.mkConst ``Nat
  let lenTy := natE
  kernelRefl (ns ++ `definitionCount) lenTy
    (← liftTermElabM do mkAppM ``List.length #[← mkAppM ``Doc.values #[docE]]) (mkNatLit d.values.length)
  kernelRefl (ns ++ `claimCount) lenTy
    (← liftTermElabM do mkAppM ``List.length #[← mkAppM ``Doc.claims #[docE]]) (mkNatLit d.claims.length)
  let holdsProp (j : Nat) : Expr :=
    mkAnd (Lean.mkConst (ns ++ Name.mkSimple s!"meaningful{j}")) (Lean.mkConst (ns ++ Name.mkSimple s!"claim{j}"))
  for k in [0:d.claims.length] do
    let ps := d.claims[k]!.premises
    let pn := ns ++ Name.mkSimple s!"premises{k}"
    kernelRefl pn (mkApp (Lean.mkConst ``List [Level.zero]) natE)
      (mkApp2 (Lean.mkConst ``Doc.premisesOf) docE (mkNatLit k))
      (listExpr natE (ps.map mkNatLit))
    -- `obligationK`: the cited premises imply the claim (curried, in reading order)
    let ob := ps.foldr (fun j acc => Expr.forallE `h (holdsProp j) acc .default) (holdsProp k)
    let on := ns ++ Name.mkSimple s!"obligation{k}"
    liftCoreM <| addDecl <| Declaration.defnDecl
      { name := on, levelParams := [], type := mkSort Level.zero, value := ob,
        hints := ReducibilityHints.regular 0, safety := DefinitionSafety.safe }
    let id (n : String) : Ident := mkIdent (ns ++ Name.mkSimple n)
    let args : Array Term ← ps.toArray.mapM fun j => do
      `((Eq.mp $(id s!"holds{j}") (hp $(Syntax.mkNumLit (toString j)) (by simp))))
    let thm ← `(command| theorem $(id s!"obligation{k}_sound") :
        $(id s!"obligation{k}") →
          (∀ j ∈ Doc.premisesOf $(mkIdent (ns ++ `doc)) $(Syntax.mkNumLit (toString k)),
            Doc.holds $(mkIdent (ns ++ `model)) $(mkIdent (ns ++ `doc)) $(mkIdent (ns ++ `G)) j) →
          Doc.holds $(mkIdent (ns ++ `model)) $(mkIdent (ns ++ `doc)) $(mkIdent (ns ++ `G))
            $(Syntax.mkNumLit (toString k)) := by
        intro h hp
        rw [$(id s!"premises{k}"):ident] at hp
        rw [$(id s!"holds{k}"):ident]
        exact h $args*)
    elabCommand thm
  -- the statements that the article quotes from the literature and does not prove:
  -- its assumptions, each an axiom that the certificate names
  for k in d.quotedClaims do
    liftCoreM <| addDecl <| Declaration.axiomDecl
      { name := ns ++ `Quoted ++ Name.mkSimple s!"claim{k}", levelParams := [],
        type := Lean.mkConst (ns ++ Name.mkSimple s!"obligation{k}"), isUnsafe := false }
  -- the report before verification, and the sentences that did not compile
  writeReport ns .anonymous rel d #[] #[] [] []
  logUncompiled rel d

end Leanify
