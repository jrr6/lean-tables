import Lean
import Table.API

section

open Lean Lean.Elab Lean.Elab.Command Lean.Meta

/-
This file contains a modified version of `#eval` (pulled from
`Lean.Elab.BuiltinCommand`) to facilitate our `#test` command.
-/

private def mkEvalInstCore (evalClassName : Name) (e : Expr) : MetaM Expr := do
  let α    ← inferType e
  let u    ← getDecLevel α
  let inst := mkApp (Lean.mkConst evalClassName [u]) α
  try
    synthInstance inst
  catch _ =>
    -- Put `α` in WHNF and try again
    try
      let α ← whnf α
      synthInstance (mkApp (Lean.mkConst evalClassName [u]) α)
    catch _ =>
      -- Fully reduce `α` and try again
      try
        let α ← reduce (skipTypes := false) α
        synthInstance (mkApp (Lean.mkConst evalClassName [u]) α)
      catch _ =>
        throwError "expression{indentExpr e}\nhas type{indentExpr α}\nbut instance{indentExpr inst}\nfailed to be synthesized, this instance instructs Lean on how to display the resulting value, recall that any type implementing the `Repr` class also implements the `{evalClassName}` class"

private def mkRunMetaEval (e : Expr) : Lean.MetaM Expr :=
  Lean.Meta.withLocalDeclD `env (mkConst ``Lean.Environment) fun env =>
  Lean.Meta.withLocalDeclD `opts (mkConst ``Lean.Options) fun opts => do
    let α ← Lean.Meta.inferType e
    let u ← Lean.Meta.getDecLevel α
    let instVal ← mkEvalInstCore ``Lean.MetaEval e
    let e := mkAppN (mkConst ``Lean.runMetaEval [u]) #[α, instVal, env, opts, e]
    instantiateMVars (← mkLambdaFVars #[env, opts] e)

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
    let elabMetaEval : Lean.Elab.Command.CommandElabM Unit := do
      -- act? is `some act` if elaborated `term` has type `CommandElabM α`
      let act? ← Lean.Elab.Command.runTermElabM fun _ => Lean.Elab.Term.withDeclName n do
        let e ← elabEvalTerm
        let eType ← Lean.instantiateMVars (← Lean.Meta.inferType e)
        if eType.isAppOfArity ``Lean.Elab.Command.CommandElabM 1 then
          let mut stx ← Lean.Elab.Term.exprToSyntax e
          unless (← Lean.Meta.isDefEq eType.appArg! (Lean.mkConst ``Unit)) do
            stx ← `($stx >>= fun v => IO.println (repr v))
          let act ← Lean.Elab.Term.evalTerm (Lean.Elab.Command.CommandElabM Unit) (Lean.mkApp (mkConst ``CommandElabM) (mkConst ``Unit)) stx
          pure <| some act
        else
          let e ← mkRunMetaEval e
          let env ← getEnv
          let opts ← getOptions
          let act ← try addAndCompile e; evalConst (Environment → Options → IO (String × Except IO.Error Environment)) n finally setEnv env
          let (out, res) ← act env opts -- we execute `act` using the environment
          logInfoAt tk out
          match res with
          | Except.error e => throwError e.toString
          | Except.ok env  => do setEnv env; pure none
      let some act := act? | return ()
      act
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
    | apply instDecidableEqRowConsHeaderMkType (it := _) (ic := _) (ir := _)
    | apply instDecidableEqRowNilHeader
    | apply instDecidableEqCell (inst := _)
    | infer_instance))

notation lhs "=(" tp ")" rhs => instHint tp inferInstance lhs rhs

notation lhs "=[" inst "]" rhs => instHint _ inst lhs rhs

notation lhs "=(" tp ")[" inst "]" rhs => instHint tp inst lhs rhs
