import Table.API
import Lean

-- # Header/Name Tactics
macro "header" : tactic => `(repeat (first | apply Schema.HasCol.hd | apply Schema.HasCol.tl))
macro "name" : tactic => `(repeat (first | apply Schema.HasName.hd | apply Schema.HasName.tl))

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
    let rec expandRowLit (i : Nat) (skip : Bool) (result : Lean.Syntax) : Lean.MacroM Lean.Syntax := do
      match i, skip, result with
      | 0,   _,     _     => pure result
      | i+1, true,  _  => expandRowLit i false result
      | i+1, false, _ =>
        let elem := elems.elemsAndSeps[i]
        expandRowLit i true (← ``(Row.cons $elem $result))
    expandRowLit elems.elemsAndSeps.size false (← ``(Row.nil))

syntax (name := namedRowLiteralParser) "/[" (term " := " cell),* "]" : term
macro_rules
  | `(/[ $[$nms:term := $vals:cell],* ]) => do
    let accCell : (Lean.Syntax × Lean.Syntax) → Lean.Syntax
                    → Lean.MacroM Lean.Syntax
    | (nm, val), acc => do
      let cell ← `(($val : Cell $nm _))
      `(Row.cons $cell $acc)
    let nil ← ``(Row.nil)
    Array.foldrM accCell nil (Array.zip nms vals)

-- # ActionList Notation
syntax "A[" term,* "]" : term
macro_rules
  | `(A[ $elems,* ]) => do
    let rec expandListLit (i : Nat) (skip : Bool) (result : Lean.Syntax) : Lean.MacroM Lean.Syntax := do
      match i, skip with
      | 0,   _     => pure result
      | i+1, true  => expandListLit i false result
      | i+1, false => expandListLit i true  (← ``(ActionList.cons $(elems.elemsAndSeps[i]) $result))
    expandListLit elems.elemsAndSeps.size false (← ``(ActionList.nil))

-- # Table `toString`
-- TODO: make this prettier
instance : ToString (@Row η dec_η []) where
  toString := λ_ => ""

instance {η nm τ} {xs : @Schema η} [ToString τ] [DecidableEq η] [ToString (Row xs)] : ToString (Row ((nm, τ) :: xs)) where
  toString := λ(Row.cons cell d) =>
                let s := match cell.toOption with
                         | some v => toString v
                         | none   => "[empty]";
                let s_d := toString d; 
                s ++ (if s_d = "" then "" else "\t|\t" ++ s_d)

instance {η} {schema : @Schema η} [ToString η] [DecidableEq η] [inst : ToString (Row schema)] : ToString (Table schema) where
  toString := λ t =>
  List.foldr (λ (nm, _) acc => ToString.toString nm ++ (if acc = "" then "" else "\t|\t") ++ acc) "" schema
    ++ "\n"
    ++ List.foldr (λ r acc => inst.toString r ++ "\n" ++ acc) "" t.rows
