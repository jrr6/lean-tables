import Table.API
import Lean

section
open Lean Lean.Elab Lean.Elab.Term Lean.Elab.Command Lean.Meta
syntax (name := headerTacTerm) "byHeader" : term

elab_rules : term
| `(headerTacTerm| byHeader) => do
  Lean.Elab.Term.elabByTactic (← `(tactic| header)) none

-- # Table Notation
declare_syntax_cat cell
syntax (name := emptyCell) "EMP" : cell
syntax (name := valueCell) term : cell

elab_rules : term
| `(emptyCell| EMP) => do Lean.Elab.Term.elabTerm (← `(Cell.emp)) none
| `(valueCell| $x) => do Lean.Elab.Term.elabTerm (← `(Cell.val $x)) none

syntax (name := rowLiteralParser) "/[" cell,* "]" : term

macro_rules
  | `(/[ $elems,* ]) => do
    let rec expandRowLit (i : Nat) (skip : Bool) (result : Lean.TSyntax `term)
        : Lean.MacroM Lean.Syntax := do
      match i, skip, result with
      | 0,   _,     _     => pure result
      | i+1, true,  _  => expandRowLit i false result
      | i+1, false, _ =>
        expandRowLit i true
          (← ``(Row.cons $(⟨elems.elemsAndSeps.get! i⟩) $result))
    expandRowLit elems.elemsAndSeps.size false (← ``(Row.nil))

#check Lean.TSyntax.getNat

syntax (name := namedRowLiteralParser) "/[" (term " := " cell),* "]" : term
macro_rules
  | `(/[ $[$nms:term := $vals:cell],* ]) => do
    let accCell : (Lean.TSyntax `term × Lean.TSyntax `cell) → Lean.TSyntax `term
                    → Lean.MacroM (Lean.TSyntax `term)
    | (nm, val), acc => do
        let cell ← `(($(⟨val.raw⟩) : Cell $nm _))
        `(Row.cons $cell $acc)
      let nil ← `(Row.nil)
      let ts_res ← Array.foldrM accCell nil (Array.zip nms vals)
      return ts_res

-- # ActionList Notation
syntax (name := autocomp_actionlist) "A[" term,* "]" : term

open Lean Elab Tactic in

-- Tactic to autogenerate ActionList proofs (we may need to cycle the goals
-- so that our Schema proof can figure out what type we need to find an instance
-- for, etc.)
open Lean Elab Tactic in
elab "cycle_goals" : tactic => do
  let goals ← getGoals
  match goals with
    | [] => throwError "No goals to cycle"
    | [_] => throwError "Only one goal; can't cycle"
    | g :: gs => setGoals (gs ++ [g])
-- We can't just throw `cycle_goals` into the list of repeatable tactics and
-- call it a day b/c if there are multiple unsolvable goals, `cycle_goals` loops
macro "action_list_tactic_no_cycle" : tactic =>
`(tactic|
  repeat (first | apply Sigma.mk
                | apply Prod.mk
                | apply Schema.HasCol.hd
                | apply Schema.HasCol.tl
                | apply Schema.HasName.hd
                | apply Schema.HasName.tl
                | exact inferInstance
                | decide  -- for `Fin`s
  )
)

open Lean Elab Tactic in
/-
TODO: better termination checking
* We can't detect cycling through goals by observing whether we've reached the
  first goal again b/c we may have been able to discharge that. We'd need
  something like a set of previously seen goals.
* We can't check that the number of goals is decreasing after every cycle b/c
  `Prod.mk`
-/
elab "action_list_tactic" : tactic => do
  let maxIters := 100
  let mut numIters := 0
  -- We shouldn't need to make more than 2 passes through the goals; if we do,
  -- then the goal is probably unsolvable
  let mut curGoals ← getGoals
  -- TODO: detect failure intelligently rather than spinning
  while curGoals.length > 0 && numIters < maxIters do
    evalTactic (← `(tactic| action_list_tactic_no_cycle))
    evalTactic (← `(tactic| rotate_left))
    numIters := numIters + 1
    curGoals ← getGoals

-- Detects whether an argument type for an (Action)List requires tuple insertion
-- Note: this can also be done using `isDefEq`, though that breaks if `e`
-- contains bound arguments
def isProdArgTp (e : Expr) : MetaM Bool := do
  -- `whnfD` approach
  let e ← whnfD e
  pure $
  -- "Vanilla" product cases
  e.isAppOf `Prod ||
  -- Nested product cases
  (e.isAppOf `Sigma && (← whnfD e.getAppArgs[0]!).isAppOf `Prod)

elab_rules : term <= expType
  | `(A[ $elems,* ]) => do
    -- Detect (a) if we need an ActionList or List and (b) whether we need
    -- tuples with holes
    let listTpMVar ← mkFreshTypeMVar
    let isList ← isDefEq expType
                  (.app (.const ``List [(← mkFreshLevelMVar)]) listTpMVar)
    let paramTp ←
      if isList
      then instantiateMVars listTpMVar
      else do
        -- TODO: find a way to avoid having to hardcode the position of the
        -- relevant arg to the `ActionList` constructor?
        -- Note: this section can also be done using `isDefEq`
        let actionListFnMVar ← mkFreshExprMVar none
        let defeqOK ← isDefEq expType
          (mkAppN (.const ``ActionList
            [←mkFreshLevelMVar, ←mkFreshLevelMVar, ←mkFreshLevelMVar])
            #[←mkFreshTypeMVar, ←mkFreshExprMVar none, ←mkFreshExprMVar none,
              actionListFnMVar, ←mkFreshExprMVar none])
        if ! defeqOK then
          throwError "Invalid expected type found during ActionList unification"

        let actionListFn ← instantiateMVars actionListFnMVar
        let actionListFnType ← inferType actionListFn

        -- Type of the "action function" for this action list
        -- let actionListFnType ← inferType expType.getAppArgs[3]!.getAppFn
        -- Type of the "action item" argument to the action function (i.e., the
        -- argument that goes in the action list)
        let actionListParam := actionListFnType.getForallBodyMaxDepth 1
        (match ← whnfD actionListParam with
          | .forallE _ tp _ _ => pure tp
          | _ => throwError "Invalid expected type for A[]")
    let needTuple ← isProdArgTp paramTp
    let rec expandListLit (i : Nat) (skip : Bool)
        (result : Lean.TSyntax `term) : TermElabM Lean.Syntax := do
      match i, skip with
      | 0,   _     => pure result
      | i+1, true  => expandListLit i false result
      -- In addition to unfolding to cons/nil applications, we also insert any
      -- necessary proof terms in subsequent tuple elements
      | i+1, false =>
        let ctor : TSyntax `term ←
          if isList then ``(List.cons) else ``(ActionList.cons)
        let elemRaw : TSyntax `term := ⟨elems.elemsAndSeps.get! i⟩
        let elemRawTp ← inferType (← elabTerm elemRaw none)
        let elemRawIsTuple := (← whnfD elemRawTp).isAppOf ``Prod  -- or use paramTp
        let item : TSyntax `term :=
          if needTuple && !elemRawIsTuple
          then (← `(($elemRaw, _)))
          else elemRaw
        expandListLit i true (←``($ctor ⟨$item, by action_list_tactic⟩ $result))

    let nil ← if isList then ``(List.nil) else ``(ActionList.nil)
    elabTerm (← expandListLit elems.elemsAndSeps.size false nil) expType

-- # Table `toString`
-- TODO: make this prettier
instance : ToString (@Row η dec_η []) where
  toString := λ_ => ""

instance {η nm τ} {xs : @Schema η}
         [ToString τ] [DecidableEq η] [ToString (Row xs)]
    : ToString (Row ((nm, τ) :: xs)) where
  toString := λ(Row.cons cell d) =>
                let s := match cell.toOption with
                         | some v => toString v
                         | none   => "{empty}";
                let s_d := toString d;
                s ++ (if s_d = "" then "" else "\t|\t" ++ s_d)

instance {η} {schema : @Schema η}
         [ToString η] [DecidableEq η] [inst : ToString (Row schema)]
    : ToString (Table schema) where
  toString := λ t =>
    List.foldr (λ (nm, _) acc =>
      ToString.toString nm ++
      (if acc = "" then "" else "\t|\t") ++
      acc) "" schema
    ++ "\n"
    ++ List.foldr (λ r acc => inst.toString r ++ "\n" ++ acc) "" t.rows
