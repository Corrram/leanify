import Lean
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.CasesM
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

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

/-- `definedness [t₁, …]` proves a definedness condition (`meaningfulK`, `wellDefinedI`):
a tree of `∧`, `→` and `∀` whose leaves are hypotheses, numeric side conditions,
signs that `positivity` proves, or the given facts, and whose impossible branches (contradictory case
conditions) are closed by `linarith` or `tauto`. -/
elab "definedness" " [" ts:term,* "]" : tactic => do
  let leaf ← ts.getElems.foldlM (fun acc t => do
    let accS ← `(Lean.Parser.Tactic.tacticSeq| $acc:tactic)
    `(tactic| first | $accS | exact $t)) (← `(tactic| assumption))
  let step ← `(tactic| first
    | $leaf:tactic
    | (norm_num; done)
    | (intro _; try casesm* _ ∧ _)
    | refine ⟨?_, ?_⟩
    | (linarith; done)
    | (positivity; done)
    -- a branch whose case conditions contradict each other
    | (exfalso; tauto; done)
    -- uncovered cases: the negated case conditions contradict the domain
    | (exfalso; (try simp only [not_and_or, not_le, not_lt, ← ne_eq, ne_iff_lt_or_gt] at *);
        (casesm* _ ∨ _) <;> linarith))
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

/-- The lists of `n` different terms among the given ones. -/
def tuples (xs : Array Expr) : Nat → List (Array Expr)
  | 0 => [#[]]
  | n + 1 => (tuples xs n).flatMap fun t => (xs.toList.filter (!t.contains ·)).map t.push

/-- `leanify_step` proves `obligationK` by the standard steps (see above), or fails. -/
elab "leanify_step" : tactic => do
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
  -- (every alternative closes its goal or fails: `ring1`, not `ring`, which rewrites a
  -- goal it cannot close)
  let each ← `(tactic| first
    | assumption | linarith | positivity | ring1 | (field_simp; ring1) | (norm_num [$lems,*]; done)
    | (simp only [$lems,*]; ring1) | (simp only [$lems,*]; field_simp; ring1)
    | (simp only [$lems,*] at *; linarith) | (simp only [$lems,*]; positivity))
  evalTactic (← `(tactic| first
    | (assumption; done)
    | (linarith; done)
    | (positivity; done)
    | (ring1; done)
    | (field_simp; ring1; done)
    | (norm_num [$lems,*]; done)
    | ((repeat' constructor) <;> ($each:tactic); done)
    | (simp only [$lems,*] at *; field_simp; ring1; done)
    | (simp only [$lems,*] at *; linarith; done)
    | (simp only [$lems,*]; positivity; done)
    -- an equivalence: each direction from the other side
    | (constructor <;> intro _ <;> first | (linarith; done) | (nlinarith; done) | (simp_all; done))
    | (simp_all [$lems,*]; done)
    | (nlinarith; done)
    | (simp only [$lems,*] at *; nlinarith; done)
    | (grind; done)
    | (aesop; done)
    | (tauto; done)))

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
