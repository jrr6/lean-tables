import Lean
import Table.API
import Table.Notation

macro "inst" : tactic =>
  `(repeat (first
    | apply instDecidableEqTable (inst := _)
    | apply instDecidableEqRowConsHeaderMkType (it := _) (ic := _) (ir := _)
    | apply instDecidableEqRowNilHeader
    | apply instDecidableEqCell (inst := _)
    | infer_instance))

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

-- def t1 : Table [("name", String), ("age", Nat), ("favorite color", String)] :=
-- Table.mk [
--   /["Bob"  , 12, "blue" ],
--   /["Alice", 17, "green"],
--   /["Eve"  , 13, "red"  ],
--   /["Colton", 19, "blue"]
-- ]

def mkTableWidget {η} [DecidableEq η] {schema : @Schema η} (t : Table schema) [htmlInst : ToHTML (Table schema)] :
    UserWidgetDefinition where
  name :=  "Display Table"
  javascript :=  "
    import * as React from 'react';
    export default function(props) {
      return React.createElement('div', {dangerouslySetInnerHTML: {__html: '" ++ ToHTML.toHTML t ++ "'}})
    }"

def null := Lean.Json.null

-- @[widget] def table1Widget :=
--   mkTableWidget t1 --(Table.mk (hs := [("name", String), ("age", Nat)]) [/["hi", 3]])

-- #widget table1Widget Json.null

-- def gradebookTable : Table [("name", ULift String),
--                             ("age", ULift Nat),
--                             ("quizzes", Table [("quiz#", Nat), ("grade", Nat)]),
--                             ("midterm", ULift Nat),
--                             ("final", ULift Nat)] :=
-- Table.mk [
--   /[ULift.up "Bob"  , ULift.up 12, Table.mk [/[1, 8],
--                                              /[2, 9],
--                                              /[3, 7],
--                                              /[4, 9]], ULift.up 77, ULift.up 87],
--   /[ULift.up "Alice", ULift.up 12, Table.mk [/[1, 6],
--                                              /[2, 8],
--                                              /[3, 8],
--                                              /[4, 7]], ULift.up 88, ULift.up 85],
--   /[ULift.up "Eve"  , ULift.up 13, Table.mk [/[1, 7],
--                                              /[2, 9],
--                                              /[3, 8],
--                                              /[4, 8]], ULift.up 84, ULift.up 77]
-- ]

-- @[widget] def gbTableWidget := mkTableWidget gradebookTable

-- #widget gbTableWidget Json.null

macro "html_inst" : tactic =>
-- The order matters because we don't want to use a row/table's ToString impl
  `(repeat (first
    | apply instToHTMLTable (rowInst := _)
    | apply instToHTMLRowConsHeaderMkType (τInst := _) (rowInst := _)
    | apply instToHTMLRowNilHeader
    | apply instToHTML
    | infer_instance))

syntax (name := tableWidgetCommand) "#table" term : command

@[commandElab tableWidgetCommand] private unsafe def elabTableWidget : Lean.Elab.Command.CommandElab := 
  open Lean Lean.Elab Command Term in λ
  | stx@`(#table $table:term) => do
    let ident ← mkFreshIdent stx
    let decl := Lean.Syntax.getId ident
    -- TODO: better way to get from `Syntax` to `TSyntax _`?
    let ident := mkIdent decl
    elabDeclaration (←
      `(@[widget] def $ident := mkTableWidget ($table) (htmlInst := by html_inst))
    )
    let null_stx ← `(Json.null)
    let props : Json ← runTermElabM fun _ =>
      Term.evalTerm Json (mkConst ``Json) null_stx
    saveWidgetInfo decl props stx
  | _ => throwUnsupportedSyntax
