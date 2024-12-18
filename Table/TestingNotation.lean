import Lean
import Table.API

section

open Lean Lean.Elab Lean.Elab.Command Lean.Meta

/-
This file contains a modified version of `#eval` (pulled from
`Lean.Elab.BuiltinCommand`) to facilitate our `#test` command.
-/

-- Modified version of `elabEvalUnsafe` (src/lean/lean/elab/builtincommand.lean)
syntax (name := test) "#test" term : command
@[command_elab test]
unsafe def elabTest : Lean.Elab.Command.CommandElab
| `(#test%$tk $term) => do
    let n := `_evalTest
    let addAndCompile (value : Lean.Expr) : Lean.Elab.TermElabM Unit := do
      -- the type really should be `Bool` at this point (b/c of `mkDecide`)
      -- (but could enforcing that explicitly lead to less-graceful failures?)
      let value ← Lean.Elab.Term.levelMVarToParam (← Lean.instantiateMVars value)
      let type ← Lean.Meta.inferType value
      let us := Lean.collectLevelParams {} value |>.params
      -- let value ← Lean.Meta.instantiateMVars value
      let decl := Lean.Declaration.defnDecl {
        name        := n
        levelParams := us.toList
        type        := type
        value       := value
        hints       := Lean.ReducibilityHints.opaque
        safety      := Lean.DefinitionSafety.unsafe
      }
      Lean.Elab.Term.ensureNoUnassignedMVars decl
      Lean.addAndCompile decl
    let elabEvalTerm : Lean.Elab.TermElabM Lean.Expr := do
      let ebool ← Lean.Elab.Term.elabTerm (← `(Bool)) none
      let e ← Lean.Elab.Term.elabTerm term none
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing

      -- Note for debugging:
      -- When we give a type hint, `Lean.Meta.getMVars e` is empty;
      -- when we don't, there's a single mvar in the array

      if (← Lean.Elab.Term.logUnassignedUsingErrorInfos
            (← Lean.Meta.getMVars e)) then
        Lean.Elab.throwAbortTerm

      -- Need to do this here so we can ensure the type is correct and return
      -- a meaningful error message otherwise
      let e ← Lean.Elab.Term.levelMVarToParam (← Lean.instantiateMVars e)
      let e_type ← Lean.Meta.inferType e
      if (← Lean.Meta.isProp e) then
        Lean.Meta.mkDecide e
      else if (← Lean.Meta.isDefEq e_type ebool) then
        return e
      else
        throwError m!"Tests must be of type Bool or Prop, but got '{e_type}'"
    let elabEval : Lean.Elab.Command.CommandElabM Unit :=
    Lean.Elab.Command.runTermElabM (λ _ => Lean.Elab.Term.withDeclName n do
      let e ← elabEvalTerm
      let env ← Lean.getEnv
      let res ← try addAndCompile e; Lean.evalConst Bool n
                finally Lean.setEnv env
      if res
      then Lean.logInfoAt tk "Test passed"
      else Lean.logErrorAt tk "Test failed")
    elabEval
| _ => Lean.Elab.throwUnsupportedSyntax

end

-- Ways of making type class inference work where Lean struggles
def instHint (α : Type _) (inst : DecidableEq α) (x : α) (y : α) :=
  decide (x = y)

macro "inst" : tactic =>
  `(tactic| repeat (first
    | apply instDecidableEqTable (inst := _)
    | apply instDecidableEqRowCons (it := _) (ic := _) (ir := _)
    | apply instDecidableEqRowNil
    | apply instDecidableEqCell (inst := _)
    | infer_instance))

notation lhs "=(" tp ")" rhs => instHint tp inferInstance lhs rhs

notation lhs "=[" inst "]" rhs => instHint _ inst lhs rhs

notation lhs "=(" tp ")[" inst "]" rhs => instHint tp inst lhs rhs
