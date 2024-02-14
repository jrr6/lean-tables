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

-- TODO: avoid use of `!`? (figure out what the new convention/standard is)
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
        -- TODO: This is madness! Figure out how to actually get from
        -- `TSyntax cell` to `TSyntax term` without invoking arrays...
        let arr : Lean.Syntax.TSepArray `cell "," :=
          Lean.Syntax.TSepArray.mk (Array.mk [val])
        let cell ← `(($(⟨arr.elemsAndSeps.get! 0⟩) : Cell $nm _))
        `(Row.cons $cell $acc)
      let nil ← `(Row.nil)
      let ts_res ← Array.foldrM accCell nil (Array.zip nms vals)
      return ts_res

-- # ActionList Notation
syntax (name := autocomp_actionlist) "A[" term,* "]" : term

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
macro "action_list_tactic" : tactic =>
`(tactic|
  repeat (first | apply Sigma.mk
                | apply Prod.mk
                | apply Schema.HasCol.hd
                | apply Schema.HasCol.tl
                | apply Schema.HasName.hd
                | apply Schema.HasName.tl
                | exact inferInstance
                | decide  -- for `Fin`s
                | cycle_goals)
)

-- Detects whether an argument type for an (Action)List requires tuple insertion
def isProdArgTp (e : Expr) : Bool :=
  -- "Vanilla" product cases
  e.isAppOf `Header || e.isAppOf `Prod ||
  -- Nested product cases
  e.isAppOf `CertifiedHeader ||
  (e.isAppOf `Sigma &&
    (e.getAppArgs[0]!.isAppOf `Header || e.getAppArgs[0]!.isAppOf `Prod))

elab_rules : term <= expType
-- @[term_elab autocomp_actionlist] def elabAutocompActionList : TermElab
  | `(A[ $elems,* ]) => do
    -- Detect (a) if we need an ActionList or List and (b) whether we need
    -- tuples with holes
    let isList := expType.isAppOf `List
    let needTuple ←
      if let .app (.const `List _) rest := expType
      then pure (isProdArgTp rest)
      else do
        -- TODO: find a way to avoid having to hardcode the position of the
        -- relevant arg to the `ActionList` constructor?

        -- Type of the "action function" for this action list
        let actionListFnType ← inferType expType.getAppArgs[3]!.getAppFn
        -- Type of the "action item" argument to the action function (i.e., the
        -- argument that goes in the action list)
        let actionListParam := actionListFnType.getForallBodyMaxDepth 3
        -- TODO: I don't think this "sees through" `Certified_`
        (match actionListParam with
          | .forallE _ tp _ _ => pure (isProdArgTp tp)
          | _ => pure false)
    dbg_trace needTuple
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
        let item : TSyntax `term :=
          if needTuple
          then (← `(($(⟨elems.elemsAndSeps.get! i⟩), _)))
          else ⟨elems.elemsAndSeps.get! i⟩
        expandListLit i true (←``($ctor ⟨$item, by action_list_tactic⟩ $result))

    let nil ← if isList then ``(List.nil) else ``(ActionList.nil)
    elabTerm (← expandListLit elems.elemsAndSeps.size false nil) expType
-- #reduce (A["a1", "a"] : ActionList (Schema.removeOtherDecCH [("a", Nat), ("a1", Nat)]) [("a", Nat), ("a1", Nat), ("b", Nat)])


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
