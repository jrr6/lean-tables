import Lean
import Table.API
import Table.Notation
import Table.TestingNotation

open Lean Widget

class ToHTML (α : Type u) where toHTML : α → String

instance (α : Type u) [ToString α] : ToHTML α := ⟨ToString.toString⟩

instance : ToHTML (@Row η dec_η []) where
  toHTML := λ_ => "<tr></tr>"

instance {η nm τ} {xs : @Schema η}
         [τInst : ToHTML τ] [DecidableEq η] [rowInst : ToHTML (Row xs)]
    : ToHTML (Row ((nm, τ) :: xs)) where
  toHTML := λ (Row.cons cell d) =>
                let s := match cell.toOption with
                         | some v => "<td style=\"border:1px solid gray\">" ++ ToHTML.toHTML v ++ "</td>"
                         | none   => "<td style=\"border:1px solid gray\"></td>";
                let s_d := ToHTML.toHTML d
                            |> String.drop (n := 4)
                            |> String.dropRight (n := 5);
                "<tr>" ++ s ++ s_d ++ "</tr>"

instance {η} {schema : @Schema η}
         [ToHTML η] [DecidableEq η] [rowInst : ToHTML (Row schema)]
    : ToHTML (Table schema) where
  toHTML := λ t =>
    "<table cellpadding=\"5\" style=\"border:1px solid gray; border-collapse: collapse\"><thead><tr>" ++
    List.foldl (λ acc (nm, _) =>
      acc ++ "<th style=\"border:1px solid gray\">" ++ ToHTML.toHTML nm ++ "</th>") "" schema
    ++ "</tr></thead><tbody>"
    ++ List.foldr (λ r acc => rowInst.toHTML r ++ acc) "" t.rows
    ++ "</tbody></table>"

def mkTableWidget {η} [DecidableEq η] {schema : @Schema η} (t : Table schema) [htmlInst : ToHTML (Table schema)] :
    UserWidgetDefinition where
  name :=  "Display Table"
  javascript :=  "
    import * as React from 'react';
    export default function(props) {
      return React.createElement('div', {dangerouslySetInnerHTML: {__html: '" ++ ToHTML.toHTML t ++ "'}})
    }"

-- TODO: in an ideal world, this wouldn't be necessary, but we keep this around
-- to deal with reducibility issues
macro "html_inst" : tactic =>
-- The order matters because we don't want to use a row/table's ToString impl
  `(tactic| repeat (first
    | apply instToHTMLTable (rowInst := _)
    | apply instToHTMLRowConsHeaderMkType (τInst := _) (rowInst := _)
    | apply instToHTMLRowNilHeader
    | apply instToHTML
    | infer_instance))

syntax (name := tableWidgetCommand) "#table" term : command
-- TODO: this uses deprecated APIs that are broken in the latest Lean version
@[command_elab tableWidgetCommand] private unsafe def elabTableWidget : Lean.Elab.Command.CommandElab :=
  open Lean Lean.Elab Command Term in λ
  | stx@`(#table $table:term) => do
    let ns ← getCurrNamespace
    let ident ← mkFreshIdent stx
    let nm := ident.getId
    let decl := Name.append ns nm

    elabDeclaration (←
      `(@[widget] def $ident := mkTableWidget ($table) (htmlInst := by html_inst))
    )
    let null_stx ← `(Json.null)
    let props : Json ← runTermElabM fun _ =>
      Term.evalTerm Json (mkConst ``Json) null_stx
    saveWidgetInfo decl props stx
  | _ => throwUnsupportedSyntax
