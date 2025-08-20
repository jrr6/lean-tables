import Lean
import Table.API
import Table.Notation

open Lean Widget

class ToHTML (α : Type u) where toHTML : α → String

instance instToHTMLOfToString (α : Type u) [ToString α] : ToHTML α := ⟨ToString.toString⟩

instance instToHTMLRowNil : ToHTML (@Row η dec_η []) where
  toHTML := λ_ => "<tr></tr>"

instance instToHTMLRowCons {η nm τ} {xs : @Schema η}
         [τInst : ToHTML τ] [DecidableEq η] [rowInst : ToHTML (Row xs)]
    : ToHTML (Row ((nm, τ) :: xs)) where
  toHTML := λ (Row.cons cell d) =>
    let curCell :=
      match cell.toOption with
      | some v => s!"<td style=\"border:1px solid gray\">{ToHTML.toHTML v}</td>"
      | none   => "<td style=\"border:1px solid gray\"></td>";
    let restOfRow :=
      ToHTML.toHTML d |> String.drop (n := 4) |> String.dropRight (n := 5)
    "<tr>" ++ curCell ++ restOfRow ++ "</tr>"

instance instToHTMLTable {η} {schema : @Schema η}
         [ToHTML η] [DecidableEq η] [rowInst : ToHTML (Row schema)]
    : ToHTML (Table schema) where
  toHTML := λ t =>
    "<table cellpadding=\"5\" style=\"border:1px solid gray; border-collapse: collapse\"><thead><tr>" ++
    List.foldl (λ acc (nm, _) =>
      acc ++ "<th style=\"border:1px solid gray\">" ++ ToHTML.toHTML nm ++ "</th>") "" schema
    ++ "</tr></thead><tbody>"
    ++ List.foldr (λ r acc => rowInst.toHTML r ++ acc) "" t.rows
    ++ "</tbody></table>"

structure HTMLRendererWidgetProps where
  html? : Option String
  deriving Server.RpcEncodable

@[widget_module] def htmlRendererWidget : Widget.Module where
  javascript := "
  import * as React from 'react';
  export default function(props) {
    return React.createElement('div', {dangerouslySetInnerHTML: {__html: props.html}})
  }"

-- TODO: in an ideal world, this wouldn't be necessary, but we keep this around
-- to deal with reducibility issues
macro "html_inst" : tactic =>
-- The order matters because we don't want to use a row/table's ToString impl
  `(tactic| repeat (first
    | apply instToHTMLTable (rowInst := _)
    | apply instToHTMLRowCons (τInst := _) (rowInst := _)
    | apply instToHTMLRowNil
    | apply instToHTMLOfToString
    | infer_instance))

syntax (name := tableWidgetCommand) "#table" term : command

@[command_elab tableWidgetCommand]
private unsafe def elabTableWidget : Lean.Elab.Command.CommandElab :=
  open Lean Lean.Elab Command Term in λ
  | stx@`(#table $table:term) => do
    let tableHTMLStx ← `(ToHTML.toHTML $table (self := by html_inst))
    let tableHTML ← runTermElabM fun _ =>
      evalTerm String (mkConst ``String) tableHTMLStx
    let props : HTMLRendererWidgetProps := { html? := tableHTML }
    let encodedProps := Server.RpcEncodable.rpcEncode props
    Elab.Command.liftCoreM <|
      savePanelWidgetInfo htmlRendererWidget.javascriptHash encodedProps stx
  | _ => throwUnsupportedSyntax
