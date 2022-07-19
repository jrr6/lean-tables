import Table.CellRowTable
import Lean

-- # Header/Name Tactics
macro "header" : tactic => `(repeat (first | apply Schema.HasCol.hd | apply Schema.HasCol.tl))
macro "name" : tactic => `(repeat (first | apply Schema.HasName.hd | apply Schema.HasName.tl))

-- # Table Notation
syntax (name := rowLiteralParser) "/[" term,* "]" : term

-- TODO: there's got to be a better way to handle empty cells -- ideally, there
-- should be some empty-cell syntax that's only valid within a `/[]` term
-- TODO: explore using a new syntax category for empty cells! Literals then take
-- *either* a term or an empty-cell cat. This seems like the real answer here.
notation "EMP" => termEMP  -- previously `()` -- actual value doesn't matter
macro_rules
  | `(/[ $elems,* ]) => do
    let rec expandRowLit (i : Nat) (skip : Bool) (result : Lean.Syntax) : Lean.MacroM Lean.Syntax := do
      match i, skip, result with
      | 0,   _,     _     => pure result
      | i+1, true,  _  => expandRowLit i false result
      | i+1, false, _ =>
        let elem := elems.elemsAndSeps[i]
        if elem.getKind == `termEMP
        then expandRowLit i true (← ``(Row.cons (Cell.emp) $result))
        else expandRowLit i true (← ``(Row.cons (Cell.val $(elems.elemsAndSeps[i])) $result))
    expandRowLit elems.elemsAndSeps.size false (← ``(Row.nil))

syntax (name := namedRowLiteralParser) "/[" (term " := " term),* "]" : term
macro_rules
  | `(/[ $[$nms:term := $vals:term],* ]) => do
    let mkCell (nm val : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
      if val.getKind == `termEMP
      then `(@Cell.emp _ _ $nm _)
      else `(@Cell.val _ _ $nm _ $val)
    let accCell : (Lean.Syntax × Lean.Syntax) → Lean.Syntax
                    → Lean.MacroM Lean.Syntax
    | (nm, val), acc => do
      let cell ← mkCell nm val
      `(Row.cons $cell $acc)
    let nil ← ``(Row.nil)
    Array.foldrM accCell nil (Array.zip nms vals)

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
