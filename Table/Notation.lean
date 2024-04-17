import Table.API
import Lean

section
open Lean Lean.Elab Lean.Elab.Term Lean.Elab.Command Lean.Meta
syntax (name := headerTacTerm) "byHeader" : term

elab_rules : term
| `(headerTacTerm| byHeader) => do
  Lean.Elab.Term.elabByTactic (← `(tactic| header)) none

-- #reduce (byHeader : Schema.HasCol ("hi", Nat) [("hi", Nat)])

-- private def mkInfoTree (elaborator : Name) (stx : Syntax) (trees : Std.PersistentArray InfoTree) : CommandElabM InfoTree := do
--   let ctx ← read
--   let s ← get
--   let scope := s.scopes.head!
--   let tree := InfoTree.node (Info.ofCommandInfo { elaborator, stx }) trees
--   return InfoTree.context {
--     env := s.env, fileMap := ctx.fileMap, mctx := {}, currNamespace := scope.currNamespace,
--     openDecls := scope.openDecls, options := scope.opts, ngen := s.ngen
--   } tree
-- elab_rules : term
-- | `(byHeader) => do
--   let (deLean.Elab.liftMacroM <| Lean.Elab.expandMacroImpl? (←Lean.getEnv) (← `(tactic| header))
--   withInfoTreeContext (mkInfoTree := mkInfoTree decl stx) do
--             let stxNew ← liftMacroM <| liftExcept stxNew?
--             withMacroExpansion stx stxNew do
--               elabCommand stxNew
-- -- Lean.Elab.expandMacroImpl? (← `(tactic| header)) none --do Lean.Elab.Term.elabLeadingParserMacro (← `(tactic| header)) none
-- #check Lean.Elab.Command.elabCommand
-- #reduce (byHeader : Nat)
-- end

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
  -- let maxPasses := 10
  -- let mut numCycles := 0
  let maxIters := 100
  let mut numIters := 0
  -- We shouldn't need to make more than 2 passes through the goals; if we do,
  -- then the goal is probably unsolvable
  let mut curGoals ← getGoals
  -- let firstGoal := curGoals[0]!
  -- while curGoals.length > 0 && numCycles < maxPasses do
  -- TODO: detect failure intelligently rather than spinning
  while curGoals.length > 0 && numIters < maxIters do
    -- let mut failure := false
    -- -- Work on this goal as much as we can
    -- while ! failure do
    --   try
    --     evalTactic (← `(tactic| action_list_tactic_one_goal))
    --   catch _ =>
    --     failure := true
    -- curGoals ← getGoals
    -- if curGoals.length > 0 && curGoals[0]! == firstGoal then
      -- numCycles := numCycles + 1
    evalTactic (← `(tactic| action_list_tactic_no_cycle))
    evalTactic (← `(tactic| rotate_left))
    numIters := numIters + 1
    curGoals ← getGoals
  -- if curGoals.length > 0 && numCycles == maxPasses then
  --   throwError "Unable to generate required (Action)List proof"

-- Detects whether an argument type for an (Action)List requires tuple insertion
-- TODO: decide which approach to use
-- Previously, defeq approach would break because `e` contained bound arguments
def isProdArgTp (e : Expr) : MetaM Bool := do
  -- `whnfD` approach
  let e ← whnfD e
  pure $
  -- "Vanilla" product cases
  e.isAppOf `Prod ||
  -- Nested product cases
  (e.isAppOf `Sigma && (← whnfD e.getAppArgs[0]!).isAppOf `Prod)

  -- `isDefEq` approach
  -- let prodUnifTgt := mkAppN (Expr.const ``Prod
  --                             [(← mkFreshLevelMVar), (← mkFreshLevelMVar)])
  --                           #[(← mkFreshTypeMVar), (← mkFreshTypeMVar)]
  -- let sigmaUnifTgt :=
  --   mkAppN (.const ``Sigma [(← mkFreshLevelMVar), (← mkFreshLevelMVar)])
  --         #[prodUnifTgt, (← mkFreshExprMVar none)]
  -- return (← isDefEq e prodUnifTgt) || (← isDefEq e sigmaUnifTgt)

elab_rules : term <= expType
-- @[term_elab autocomp_actionlist] def elabAutocompActionList : TermElab
  | `(A[ $elems,* ]) => do
    -- Detect (a) if we need an ActionList or List and (b) whether we need
    -- tuples with holes
    -- let isList := expType.isAppOf `List
    let listTpMVar ← mkFreshTypeMVar
    let isList ← isDefEq expType
                  (.app (.const ``List [(← mkFreshLevelMVar)]) listTpMVar)
    let paramTp ←
      if isList
      then instantiateMVars listTpMVar
      else do
        -- TODO: find a way to avoid having to hardcode the position of the
        -- relevant arg to the `ActionList` constructor?

        -- let actionListFnType ← mkFreshTypeMVar
        -- TODO: issue is that we're extracting *under* a binder; of course there
        -- are bound variables!
        -- let c ← isDefEq expType (.forallE `x (← mkFreshTypeMVar) (← mkFreshExprMVar none) _)
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
        -- let paramArg ← mkFreshExprMVar none
        -- let predType : Expr :=
        --   .forallE .anonymous (← mkFreshTypeMVar)
        --     (.forallE .anonymous paramArg (←mkFreshTypeMVar) .default) .default
        -- let defeqOK ← isDefEq actionListFnType predType
        -- if ! defeqOK then
        --   throwError "Found invalid ActionList function type"
        -- let paramArg ← instantiateMVars paramArg
        -- dbg_trace s!"the param arg is {paramArg}"
        -- let oldActionListFnType ← inferType expType.getAppArgs[3]!.getAppFn
        -- dbg_trace s!"Old type: {oldActionListFnType}"
        -- dbg_trace ("there for type " ++ toString expType.getAppArgs[3]! ++ ":")
        -- dbg_trace (← inferType actionListFnName)


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
        -- let unifTgt := mkAppN (Expr.const ``Prod
        --                         [(← mkFreshLevelMVar), (← mkFreshLevelMVar)])
        --                       #[(← mkFreshTypeMVar), (← mkFreshTypeMVar)]
        -- let elemRawIsTuple ← isDefEq elemRawTp unifTgt
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

-- def students : Table [("name", String), ("age", Nat), ("favorite color", String)] :=
-- Table.mk [
--   /["Bob"  , 12, "blue" ],
--   /["Alice", 17, "green"],
--   /["Eve"  , 13, "red"  ]
-- ]

-- #eval renameColumns students A[("favorite color", "preferred color"),
--                          ("name", "first name")]

-- def abstractAgeUpdate := λ (r : Row $ schema students) =>
--   match getValue r "age" (by header) with
--   | some age =>
--     match (age ≤ 12 : Bool), (age ≤ 19 : Bool) with
--     | true, _ => /["age" := "kid"]
--     | _, true => /["age" := "teenager"]
--     | _, _ => /["age" := "adult"]
--   | _ => /["age" := EMP]

-- #reduce RetypedSubschema (schema students)
-- TODO: why aren't any of the `RetypedSubschema` metavars being synthesized
-- prior to elaborating the `A[]` syntax?
-- #eval update A["age"] students abstractAgeUpdate
-- #eval (A[1,2,3] : List (Fin 4))

-- This is an example that *won't* work with our syntax, since we expect that
-- any non-dependent tuples have inferrable second arguments
-- #reduce (A["name", "hello"] : List (String × (Schema.HasName "hi" [("hi", Nat)])))

-- #reduce (A["hi"] : List ((s : String) × Schema.HasName s [("hi", Nat)]))

-- #eval pivotLonger students A["age"] "attribute" "value"

-- #eval leftJoin students students A["name", "age"]
-- #eval dropColumns students A["age", "name"]
-- #eval selectColumns3 students A["favorite color", "age"]
-- def oAverage (xs : List $ Option Nat) : Option Nat := some $
--   List.foldl (λ acc => λ | none => acc | some x => x + acc) 0 xs / xs.length

-- #eval
-- pivotTable students A["favorite color"] [⟨("age-average", _), ⟨("age", _), by header⟩, oAverage⟩]
-- #reduce (A["a1", "a"] : ActionList (Schema.removeOtherDecCH [("a", Nat), ("a1", Nat)]) [("a", Nat), ("a1", Nat), ("b", Nat)])
