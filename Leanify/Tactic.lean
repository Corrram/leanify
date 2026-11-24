import Lean
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.CasesM
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Leanify.Integers

/-! # Tactics for writing justifications of compiled claims -/
namespace Leanify
open Lean Elab Tactic Meta

/-- The number `K` in a generated name `claimK`. -/
def claimIndex? (n : Name) : Option Nat :=
  match n with
  | .str _ s => if s.startsWith "claim" then (String.ofList (s.toList.drop 5)).toNat? else none
  | _ => none

/-- `intro_premises` unfolds a goal `obligationK` and introduces its premises:
the premise `meaningfulJ ∧ claimJ` becomes `mJ : meaningfulJ` and `cJ : claimJ`. -/
elab "intro_premises" : tactic => do
  let ty ← instantiateMVars (← (← getMainGoal).getType)
  if let .const n _ := ty then
    evalTactic (← `(tactic| unfold $(mkIdent n):ident))
  let rec loop : Nat → TacticM Unit
    | 0 => pure ()
    | fuel + 1 => do
      let ty ← instantiateMVars (← (← getMainGoal).getType)
      match ty with
      | .forallE _ (.app (.app (.const ``And _) (.const _ _)) (.const c _)) _ _ =>
        match claimIndex? c with
        | some k =>
          let mI := mkIdent (Name.mkSimple s!"m{k}")
          let cI := mkIdent (Name.mkSimple s!"c{k}")
          evalTactic (← `(tactic| rintro ⟨$mI:ident, $cI:ident⟩))
          loop fuel
        | none => pure ()
      | _ => pure ()
  loop 1000

/-- The parts of a proof `e` of a proposition: `e`, and for a conjunction (once the
definitions are unfolded) the parts of its two sides, with their propositions. -/
partial def partsOf (fuel : Nat) (e : Expr) : MetaM (List (Expr × Expr)) := do
  let ty ← instantiateMVars (← inferType e)
  if fuel == 0 then return [(e, ty)]
  let t ← whnf ty
  match t.and? with
  | some (a, b) =>
    let l ← partsOf (fuel - 1) (mkApp3 (Lean.mkConst ``And.left) a b e)
    let r ← partsOf (fuel - 1) (mkApp3 (Lean.mkConst ``And.right) a b e)
    return (e, ty) :: l ++ r
  | none => return [(e, ty)]

/-- `leanify_part` closes a goal that is a part of a hypothesis: a side of a conjunction
that the hypothesis is once its definitions are unfolded (that a function is a
distribution function, from the hypothesis that it is a copula of the article). -/
elab "leanify_part" : tactic => withMainContext do
  let g ← getMainGoal
  let target ← instantiateMVars (← g.getType)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    unless ← isProp d.type do continue
    for (p, ty) in ← partsOf 3 d.toExpr do
      if ← withReducible (isDefEq ty target) then
        g.assign p
        replaceMainGoal []
        return
  throwError "leanify_part: the goal is not a part of a hypothesis"

/-- `leanify_points` closes an inequality with what the points of an interval in the
context are: a variable `x` of a subtype whose condition is a conjunction (`0 ≤ x ∧ x ≤ 1`
for a point of `[0,1]`) gives its two sides, and `linarith` concludes. -/
elab "leanify_points" : tactic => do
  let g ← getMainGoal
  let g' ← g.withContext do
    let mut g := g
    let mut n := 0
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← whnfR (← instantiateMVars d.type)
      unless ty.isAppOf ``Subtype do continue
      let pf ← mkAppM ``Subtype.property #[d.toExpr]
      let p ← whnf (← inferType pf)
      match p.and? with
      | some (a, b) =>
        let (_, g1) ← (← g.assert `hp a (mkApp3 (Lean.mkConst ``And.left) a b pf)).intro1P
        let (_, g2) ← (← g1.assert `hp b (mkApp3 (Lean.mkConst ``And.right) a b pf)).intro1P
        g := g2
        n := n + 1
      | none => pure ()
    if n == 0 then throwError "leanify_points: no point of an interval in the context"
    pure g
  replaceMainGoal [g']
  evalTactic (← `(tactic| linarith))

/-- `leanify_pinch` uses two hypotheses `a ≤ b` and `b ≤ a` (the conditions of two cases
that meet in a point): `a = b`, which is substituted, and `norm_num` concludes. -/
elab "leanify_pinch" : tactic => do
  let g ← getMainGoal
  let r ← g.withContext do
    let hyps := (← getLCtx).foldl (init := #[]) fun acc d =>
      if d.isImplementationDetail then acc else acc.push d
    let mut found : Option MVarId := none
    for d1 in hyps do
      if found.isSome then break
      let t1 ← instantiateMVars d1.type
      unless t1.isAppOfArity ``LE.le 4 do continue
      for d2 in hyps do
        let t2 ← instantiateMVars d2.type
        unless t2.isAppOfArity ``LE.le 4 do continue
        if d1.fvarId == d2.fvarId then continue
        if (← withReducible (isDefEq (t1.getArg! 2) (t2.getArg! 3))) &&
            (← withReducible (isDefEq (t1.getArg! 3) (t2.getArg! 2))) then
          let pf ← mkAppM ``le_antisymm #[d1.toExpr, d2.toExpr]
          let (_, g1) ← (← g.assert `hpinch (← inferType pf) pf).intro1P
          found := some g1
          break
    pure found
  match r with
  | none => throwError "leanify_pinch: no two cases that meet in a point"
  | some g1 =>
    replaceMainGoal [g1]
    let hp := mkIdent `hpinch
    evalTactic (← `(tactic| ((try subst_vars); (first | (norm_num; done) | (simp only [$hp:ident]; norm_num; done) | (simp_all; done)))))

/-- `leanify_neq` closes a goal whose hypotheses contain `a ≠ b` for two terms that
`linarith` proves equal: a case and its endpoint, when the endpoint is excluded and the
bounds leave nothing else. -/
elab "leanify_neq" : tactic => do
  let g ← getMainGoal
  let hyps ← g.withContext do
    let mut out : Array Expr := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      if t.isAppOfArity ``Ne 3 || (t.isAppOfArity ``Not 1 && (t.getArg! 0).isAppOfArity ``Eq 3) then
        out := out.push d.toExpr
    pure out
  for h in hyps do
    let s ← saveState
    try
      let hs ← (← getMainGoal).withContext (Term.exprToSyntax h)
      evalTactic (← `(tactic| (exfalso; apply $hs; linarith)))
      if (← getUnsolvedGoals).isEmpty then return
      s.restore
    catch _ => s.restore
  throwError "leanify_neq: no excluded point that the bounds force"

/-- `leanify_unfold` unfolds the definitions of the article (the constants of a namespace
that holds the compiled statements of an article) in the goal and in the hypotheses, one
level: a leaf about `\kappa_w` becomes a leaf about `\frac{3-2w}{2w}`. It fails when there
is none. -/
elab "leanify_unfold" : tactic => do
  let g ← getMainGoal
  let env ← getEnv
  let names ← g.withContext do
    let mut cs : Array Name := (← instantiateMVars (← g.getType)).getUsedConstants
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      cs := cs ++ (← instantiateMVars d.type).getUsedConstants
    let article (n : Name) : Bool :=
      match n with
      | .str p s =>
        !p.isAnonymous && (env.contains (p ++ `obligation0) || env.contains (p ++ `wellDefined0)) &&
          !(s.startsWith "wellDefined" || s.startsWith "meaningful" || s.startsWith "claim" ||
            s.startsWith "obligation" || s.startsWith "satisfiable")
      | _ => false
    pure ((cs.filter fun n => article n && (match env.find? n with | some (.defnInfo _) => true | _ => false)).toList.eraseDups)
  if names.isEmpty then throwError "leanify_unfold: no definition of the article"
  for n in names do
    evalTactic (← `(tactic| try unfold $(mkIdent n):ident at *))

/-- `leanify_denoms` adds, for each denominator in the goal and in the hypotheses, that it
is positive, when `positivity` or `linarith` proves it. -/
elab "leanify_denoms" : tactic => do
  let g ← getMainGoal
  let dens ← g.withContext do
    let mut es : Array Expr := #[← instantiateMVars (← g.getType)]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      es := es.push (← instantiateMVars d.type)
    let mut out : Array Expr := #[]
    for e in es do
      let subs : Array Expr := Id.run do
        let mut acc : Array Expr := #[]
        let mut todo : List Expr := [e]
        let mut fuel := 4000
        while fuel > 0 do
          fuel := fuel - 1
          match todo with
          | [] => break
          | t :: rest =>
            todo := rest
            if t.isAppOfArity ``HDiv.hDiv 6 then
              let c := t.getArg! 5
              if !c.hasLooseBVars then acc := acc.push c
            match t with
            | .app f x => todo := f :: x :: todo
            | .lam _ d b _ | .forallE _ d b _ => todo := d :: b :: todo
            | .mdata _ b => todo := b :: todo
            | _ => pure ()
        pure acc
      for c in subs do
        unless out.contains c do out := out.push c
    pure out
  for c in dens do
    (← getMainGoal).withContext do
      let cs ← Term.exprToSyntax c
      evalTactic (← `(tactic| try (have : 0 < $cs := by first | positivity | linarith)))

/-- `leanify_arith` closes a leaf of arithmetic: by `linarith` or `positivity`, as a quotient
or product of positive terms, from case conditions that contradict each other, or, with the
quotients in the hypotheses cleared, by `nlinarith`. -/
macro "leanify_arith" : tactic => `(tactic|
  first
    | (linarith; done)
    | (positivity; done)
    | ((first | apply div_pos | apply div_nonneg | apply mul_pos | apply mul_nonneg) <;> linarith)
    | (exfalso; (try simp only [not_and_or, not_le, not_lt] at *); (try casesm* _ ∨ _) <;> linarith)
    | (exfalso;
        leanify_denoms;
        (try simp (disch := assumption) only [le_div_iff₀, div_le_iff₀, lt_div_iff₀, div_lt_iff₀] at *);
        nlinarith))

/-- `leanify_facts` closes a leaf of a definedness condition with the facts of the model of
a vocabulary: a library gives its rules with `macro_rules` (the unit square: an integral
against a distribution function of a bounded expression). Without a rule that applies,
it fails. -/
syntax "leanify_facts" : tactic

macro_rules
  | `(tactic| leanify_facts) => `(tactic| fail "leanify_facts: no fact of a model applies")

/-- `definedness [t₁, …]` proves a definedness condition (`meaningfulK`, `wellDefinedI`):
a tree of `∧`, `→` and `∀` whose leaves are hypotheses, numeric side conditions,
signs that `positivity` proves, bounds of points of an interval, products and powers that
are not zero, or the given facts, and whose impossible branches (contradictory case
conditions) are closed by `linarith` or `tauto`. Two cases that meet in a point agree there
(`leanify_pinch`). A condition on almost every point of an
interval (that an integrand is defined there) is proved for every point. A hypothesis `∃ z, φ` (what a hypothesis
about another variable says about the variables of a definition) is opened, and a leaf
that follows from the hypotheses by rewriting is closed by `simp_all`. A leaf that is a
side of a hypothesis (`leanify_part`) or a fact of the model of the vocabulary
(`leanify_facts`) is closed by it. -/
elab "definedness" " [" ts:term,* "]" : tactic => do
  let leaf ← ts.getElems.foldlM (fun acc t => do
    let accS ← `(Lean.Parser.Tactic.tacticSeq| $acc:tactic)
    `(tactic| first | $accS | exact $t)) (← `(tactic| assumption))
  let aeOfForall := mkIdent `Leanify.Prelude.ae_of_forall
  let step ← `(tactic| first
    | $leaf:tactic
    -- a side of a hypothesis that is a conjunction once its definitions are unfolded
    | leanify_part
    | (norm_num; done)
    -- what holds at every point holds at almost every point
    | refine $aeOfForall:ident ?_
    | (intro _; try casesm* _ ∧ _, ∃ _, _)
    -- a fact of the model of the vocabulary
    | (leanify_facts; done)
    -- a witness that a hypothesis gives
    | (apply Exists.intro; assumption; done)
    | refine And.intro ?_ ?_
    | (linarith; done)
    | (positivity; done)
    -- a bound of a point of an interval
    | (leanify_points; done)
    -- a product or a power that is not zero
    | (exfalso; simp only [mul_eq_zero, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        false_or, or_false, sub_eq_zero] at *; (try casesm* _ ∨ _) <;> linarith)
    -- two cases that meet in a point agree there
    | (leanify_pinch; done)
    -- a leaf about a definition of the article: about its value, in each of its cases
    | (leanify_unfold; (try split_ifs) <;> (try leanify_unfold) <;> leanify_arith)
    -- one of the cases of a definition applies: otherwise their negations contradict the domain
    | (apply Classical.byContradiction; intro _;
        (try simp only [not_or, not_and_or, not_le, not_lt] at *);
        (try casesm* _ ∧ _); (try casesm* _ ∨ _) <;>
          first | (linarith; done) | (leanify_points; done) | (leanify_neq; done))
    -- a branch whose case conditions contradict each other
    | (exfalso; tauto; done)
    -- uncovered cases: the negated case conditions contradict the domain
    | (exfalso; (try simp only [not_and_or, not_le, not_lt, ← ne_eq, ne_iff_lt_or_gt] at *);
        (casesm* _ ∨ _) <;> linarith)
    -- a hypothesis about another variable (`∃ z, x z ≠ 0` for `x ≠ 0`)
    | (simp_all; done))
  let stepS ← `(Lean.Parser.Tactic.tacticSeq| $step:tactic)
  evalTactic (← `(tactic| repeat' $stepS))

/-! ## The standard step

`leanify_step` proves an obligation with a fixed list of steps and nothing else: it
introduces the premises, proves that the claim is meaningful, takes each premise at
the variables and hypotheses of the claim, and closes the claim with one of a few
decision procedures. A claim the text derives is *closed by the standard tactic* when
`leanify_step` proves its obligation: the step of the text is then no larger than
what these procedures find. `#leanify_certify` tries it on every such claim and
reports the result, whatever proof the claim has. -/

/-- The namespace and the number `K` of a generated name `NS.obligationK`. -/
def obligationIndex? (n : Name) : Option (Name × Nat) :=
  match n with
  | .str ns s =>
    if s.startsWith "obligation" then (String.ofList (s.toList.drop 10)).toNat?.map (ns, ·) else none
  | _ => none

/-- The definitions of the article compiled into the namespace `ns` (the constants of
its environment `ns.G`). -/
def articleDefs (ns : Name) : MetaM (Array Name) := do
  match (← getEnv).find? (ns ++ `G) with
  | some ci => pure (((ci.value?.map (·.getUsedConstants)).getD #[]).filter fun c =>
      ns.isPrefixOf c && c != ns ++ `model)
  | none => pure #[]

/-- Run a tactic that should close every goal, with a budget of its own (in thousands of
heartbeats) and without a trace when it fails: the goals and the messages are as before. -/
def closes (budget : Nat) (tac : TSyntax `tactic) : TacticM Bool := do
  let s ← saveState
  let log ← Core.getMessageLog
  -- (a closer that runs out of its budget fails like any other: the exception of the
  -- limit is caught too)
  let ok ← tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxHeartbeats := budget * 1000 * 1000 }) <|
      withCurrHeartbeats do
        evalTactic tac
        pure ((← getUnsolvedGoals).isEmpty && !(← Core.getMessageLog).hasErrors))
    (fun _ => pure false)
  unless ok do
    s.restore
    Core.setMessageLog log
  pure ok

/-- A proof of the proposition by the tactic, with a budget of its own; none if the tactic
does not prove it. -/
def proveBy (budget : Nat) (prop : Expr) (tac : TSyntax `tactic) : TacticM (Option Expr) := do
  let s ← saveState
  let log ← Core.getMessageLog
  let m ← Meta.mkFreshExprMVar prop
  let ok ← tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxHeartbeats := budget * 1000 * 1000 }) <|
      withCurrHeartbeats do
        let rest ← Tactic.run m.mvarId! (evalTactic tac)
        pure (rest.isEmpty && !(← Core.getMessageLog).hasErrors))
    (fun _ => pure false)
  if ok then pure (some (← instantiateMVars m))
  else
    s.restore
    Core.setMessageLog log
    pure none

/-- What a reader uses without saying so, added to the hypotheses: between two integers
there is a gap of one (`a < b` gives `a + 1 ≤ b`), and a hypothesis `A → B` whose `A`
follows at once gives `B` (the hypothesis of an induction about `n - 1`, whose `n - 1`
is a positive integer). -/
def saturate : TacticM Unit := do
  let add (name : Name) (e : Expr) : TacticM Unit := do
    let t ← withMainContext (do instantiateMVars (← Meta.inferType e))
    let g ← (← getMainGoal).assert name t e
    let (_, g) ← g.intro1P
    replaceMainGoal [g]
  let side ← `(tactic| first
    | assumption | leanify_int | (linarith; done)
    | (constructor <;> first | assumption | leanify_int | (linarith; done)))
  let isIntOf (x : Expr) : Expr := mkApp (Lean.mkConst ``Leanify.Prelude.isInt) x
  -- the gap between integers
  let lctx ← withMainContext getLCtx
  for d in lctx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    match t.getAppFn, t.getAppArgs with
    | .const ``LT.lt _, #[ty, _, a, b] =>
      if ty.isConstOf ``Real then
        let some ha ← withMainContext (proveBy 10 (isIntOf a) (← `(tactic| leanify_int))) | continue
        let some hb ← withMainContext (proveBy 10 (isIntOf b) (← `(tactic| leanify_int))) | continue
        add `gap (mkApp5 (Lean.mkConst ``Leanify.Prelude.isInt.add_one_le_of_lt) a b ha hb d.toExpr)
    | _, _ => pure ()
  -- hypotheses whose own hypothesis holds
  let lctx ← withMainContext getLCtx
  for d in lctx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if t.isArrow then
      let a := t.bindingDomain!
      if ← withMainContext (Meta.isProp a) then
        let some ha ← withMainContext (proveBy 20 a side) | continue
        add (d.userName.appendAfter "'") (mkApp d.toExpr ha)

/-- The lists of `n` different terms among the given ones. -/
def tuples (xs : Array Expr) : Nat → List (Array Expr)
  | 0 => [#[]]
  | n + 1 => (tuples xs n).flatMap fun t => (xs.toList.filter (!t.contains ·)).map t.push

/-- The steps of `leanify_step`. -/
def stepCore : TacticM Unit := do
  let ty ← instantiateMVars (← (← getMainGoal).getType)
  let some (ns, k) := (match ty with | .const n _ => obligationIndex? n | _ => none)
    | throwError "leanify_step proves an obligation of a compiled article (obligationK)"
  let meaningful := mkIdent (ns ++ Name.mkSimple s!"meaningful{k}")
  let claim := mkIdent (ns ++ Name.mkSimple s!"claim{k}")
  let defs ← liftM (m := MetaM) (articleDefs ns)
  let lems : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ← defs.mapM fun d =>
    `(Lean.Parser.Tactic.simpLemma| $(mkIdent d):ident)
  evalTactic (← `(tactic| intro_premises))
  -- the claim is meaningful: as it stands, or with the article's definitions unfolded
  -- (a division by a mean of positive numbers)
  evalTactic (← `(tactic| refine ⟨?_, ?_⟩))
  evalTactic (← `(tactic| focus (first
    | (unfold $meaningful:ident; definedness []; done)
    | (unfold $meaningful:ident; simp only [$lems,*]; definedness []; done))))
  evalTactic (← `(tactic| unfold $claim:ident))
  -- the variables and hypotheses of the claim
  let before ← withMainContext do pure (← getLCtx).getFVarIds
  evalTactic (← `(tactic| intros))
  -- each premise `cJ` at the variables and hypotheses of the claim: every way of
  -- giving it as many of them as it takes (a lemma about every positive `x` is used at
  -- `x` and at `y`), or else at the first of them
  withMainContext do
    let lctx ← getLCtx
    let vars := (lctx.getFVarIds.filter fun f => !before.contains f).map mkFVar
    let add (name : Name) (e : Expr) : TacticM Unit := do
      let t ← withMainContext (do instantiateMVars (← Meta.inferType e))
      let g ← (← getMainGoal).assert name t e
      let (_, g) ← g.intro1P
      replaceMainGoal [g]
    for d in lctx do
      let isPremise := match d.userName with
        | .str .anonymous s => s.startsWith "c" && (String.ofList (s.toList.drop 1)).toNat?.isSome
        | _ => false
      if isPremise && !d.isImplementationDetail then
        let arity ← Meta.forallTelescopeReducing d.type fun xs _ => pure xs.size
        let mut n := min arity vars.size
        let mut found := false
        while n > 0 && !found do
          if vars.size ^ n ≤ 256 then
            for tuple in tuples vars n do
              let e := mkAppN d.toExpr tuple
              if ← withMainContext (Meta.isTypeCorrect e) then
                add (d.userName.appendAfter "'") e
                found := true
          n := n - 1
        -- (too many to try: the first variables, as many as fit)
        n := if found then 0 else vars.size
        while n > 0 do
          let e := mkAppN d.toExpr (vars.extract 0 n)
          if ← withMainContext (Meta.isTypeCorrect e) then
            add (d.userName.appendAfter "'") e
            n := 0
          else n := n - 1
  evalTactic (← `(tactic| try casesm* _ ∧ _))
  saturate
  evalTactic (← `(tactic| try casesm* _ ∧ _))
  saturate
  evalTactic (← `(tactic| try casesm* _ ∧ _))
  -- (every alternative closes its goal or fails: `ring1`, not `ring`, which rewrites a
  -- goal it cannot close)
  let each ← `(tactic| first
    | assumption | linarith | positivity | ring1 | leanify_int | (field_simp; ring1) | (norm_num [$lems,*]; done)
    | (simp only [$lems,*]; ring1) | (simp only [$lems,*]; field_simp; ring1)
    | (simp only [$lems,*] at *; linarith) | (simp only [$lems,*]; positivity))
  -- the closers, each with a budget of its own (in thousands of heartbeats): what the
  -- tactic proves does not depend on the limits of the file it is used in
  let closers : List (Nat × TSyntax `tactic) := [
    (20, ← `(tactic| assumption)),
    (30, ← `(tactic| linarith)),
    (30, ← `(tactic| positivity)),
    (30, ← `(tactic| ring1)),
    (20, ← `(tactic| leanify_int)),
    (30, ← `(tactic| (field_simp; ring1))),
    (30, ← `(tactic| norm_num [$lems,*])),
    (50, ← `(tactic| (repeat' constructor) <;> ($each:tactic))),
    (30, ← `(tactic| (simp only [$lems,*] at *; field_simp; ring1))),
    (30, ← `(tactic| (simp only [$lems,*] at *; linarith))),
    (30, ← `(tactic| (simp only [$lems,*]; positivity))),
    -- an equivalence: each direction from the other side
    (50, ← `(tactic| constructor <;> intro _ <;> first | (linarith; done) | (nlinarith; done) | (simp_all; done))),
    (50, ← `(tactic| simp_all [$lems,*])),
    (50, ← `(tactic| nlinarith)),
    (50, ← `(tactic| (simp only [$lems,*] at *; nlinarith))),
    (60, ← `(tactic| grind)),
    (60, ← `(tactic| aesop)),
    (30, ← `(tactic| tauto))]
  for (budget, tac) in closers do
    if ← closes budget tac then return
  throwError "leanify_step: the claim does not follow from its premises by the standard steps"

/-- `leanify_step` proves `obligationK` by the standard steps (see above), or fails. -/
elab "leanify_step" : tactic => do
  -- (the tactic has budgets of its own: its cost does not count against the limit of the
  -- declaration it is used in)
  let h0 ← IO.getNumHeartbeats
  try stepCore finally IO.setNumHeartbeats h0

/-! ## Values for the hypotheses of a statement

`satisfiableK` says that the hypotheses of statement `K` can hold together: `∃ x, P x
∧ ∃ y, Q x y`. `leanify_values 1 2` proves it with these values for its variables, in
the order of the text (the last value is used for every further variable), if the
conditions on them then follow by computation. -/

/-- The goal with the given values for its variables, in order; the conditions go to
`leaf`. -/
partial def valuesLoop (leaf : TSyntax `tactic) (vals : IO.Ref (List Term)) : TacticM Unit := do
  let goals ← getGoals
  match goals with
  | [] => pure ()
  | g :: rest =>
    setGoals [g]
    let ty ← g.withContext do Meta.whnfR (← instantiateMVars (← g.getType))
    if ty.isAppOf ``Exists then
      let v ← match ← vals.get with
        | [v] => pure v
        | v :: more => vals.set more; pure v
        | [] => throwError "leanify_values: no value"
      evalTactic (← `(tactic| refine ⟨$v, ?_⟩))
      valuesLoop leaf vals
    else if ty.isAppOf ``And then
      evalTactic (← `(tactic| constructor))
      match ← getGoals with
      | [a, b] =>
        setGoals [a]; valuesLoop leaf vals
        let left ← getGoals
        setGoals [b]; valuesLoop leaf vals
        setGoals (left ++ (← getGoals))
      | _ => throwError "leanify_values: unexpected goals"
    else evalTactic leaf
    setGoals ((← getGoals) ++ rest)

syntax "leanify_values" (ppSpace colGt term:max)+ : tactic

elab_rules : tactic
  | `(tactic| leanify_values $vs*) => do
    let ty ← instantiateMVars (← (← getMainGoal).getType)
    let mut lems : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
    if let .const n _ := ty then
      evalTactic (← `(tactic| unfold $(mkIdent n):ident))
      if let .str ns _ := n then
        lems ← (← liftM (m := MetaM) (articleDefs ns)).mapM fun d =>
          `(Lean.Parser.Tactic.simpLemma| $(mkIdent d):ident)
    -- a condition: by computation; an integer, by naming it
    let leaf ← `(tactic| first
      | exact trivial | (norm_num [$lems,*]; done) | (positivity; done) | (linarith; done)
      | (refine ⟨(0 : ℤ), ?_⟩; norm_num; done) | (refine ⟨(1 : ℤ), ?_⟩; norm_num; done)
      | (refine ⟨(2 : ℤ), ?_⟩; norm_num; done) | (refine ⟨(3 : ℤ), ?_⟩; norm_num; done)
      | (refine ⟨(4 : ℤ), ?_⟩; norm_num; done) | (refine ⟨(-1 : ℤ), ?_⟩; norm_num; done))
    let vals ← IO.mkRef (vs.toList.map fun v => (⟨v.raw⟩ : Term))
    valuesLoop leaf vals
    unless (← getGoals).isEmpty do throwError "leanify_values: the conditions do not follow for these values"

end Leanify
