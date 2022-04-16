import Table.CellRowTable

universe u_η
universe u
variable {η : Type u_η} [dec_η : DecidableEq η] {schema : @Schema η}

#check Cell "hi" Nat

def x : Cell "hi" Nat := Cell.val 42

-- Implementation of a table string-representation function (provided all τs in
-- the schema have ToString instances):
instance : ToString (@Row η dec_η []) where
  toString := λ_ => ""

instance {η nm τ} {xs : @Schema η} [ToString τ] [DecidableEq η] [ToString (Row xs)] : ToString (Row ((nm, τ) :: xs)) where
  toString := λ(Row.cons cell d) =>
                let s := match cell.toOption with
                         | some v => toString v
                         | none   => "[empty]";
                let s_d := toString d; 
                s ++ (if s_d = "" then "" else "\t|\t" ++ s_d)

def Row.repr [ToString (Row schema)] (r : Row schema) := toString r

instance {η} {schema : @Schema η} [ToString η] [DecidableEq η] [inst : ToString (Row schema)] : ToString (Table schema) where
  toString := λ t =>
  List.foldr (λ (nm, _) acc => ToString.toString nm ++ (if acc = "" then "" else "\t|\t") ++ acc) "" schema
    ++ "\n"
    ++ List.foldr (λ r acc => inst.toString r ++ "\n" ++ acc) "" t.rows

def Table.repr [ToString (Table schema)] (t : Table schema) := toString t

#eval Row.repr (Row.cons x (Row.cons x Row.nil))

-- This could probably use some syntactic sugar...
def t1 : Table [("prof", String), ("course", Nat), ("taught", Bool)] :=
  -- Can simplify this by just using Table.mk
  addRows
    (emptyTable |> (λ t => addColumn t "prof" [])
                |> (λ t => addColumn t "course" [])
                |> (λ t => addColumn t "taught" []))
    [Row.cons (Cell.val "Kaynar") (Row.cons (Cell.val 15122) (Row.cons (Cell.val true) Row.nil)),
      Row.cons (Cell.val "Crary") (Row.cons (Cell.val 15150) (Row.cons (Cell.val true) Row.nil)),
      Row.cons (Cell.val "Erdmann") (Row.cons (Cell.val 15150) (Row.cons (Cell.val false) Row.nil)),
      Row.cons (Cell.val "Cervesato") (Row.cons (Cell.val 15122) (Row.cons (Cell.val false) Row.nil))]

#eval Table.repr t1
#reduce t1

infixr:50 "|" => Row.cons
notation "**|" => Row.nil
notation "/[" elem "]/" => Cell.val elem
notation "/[_]/" => Cell.emp

def t2 : Table [("prof", String), ("course", Nat), ("taught", Bool)] :=
  Table.mk
    [
      /[ "Lewis" ]/         | /[_]/      | /[ true ]/  | **|,
      /[ "Krishnamurthi" ]/ | /[ 1730 ]/ | /[ false ]/ | **|
      ]

def joined := vcat t1 t2
#eval Table.repr joined
#reduce joined

-- FIXME: what happened here? I swear this was working.
#reduce selectColumnsH t2 [⟨"prof", (by name)⟩, ⟨"course", (by name)⟩]
#reduce @selectColumnsH String
                        inferInstance
                        [("prof", String), ("course", Nat), ("taught", Bool)] t2 [⟨"prof", Schema.HasName.hd⟩]
                        inferInstance
#reduce Row.pick (Row.append
        (@Row.singleCell String _ "pi" (List Nat) [3,1,4,1,5])
        (@Row.singleCell String _ "age" Nat 20)) [⟨"pi", by name⟩]

def schoolIded := addColumn joined "school" ["CMU", "CMU", "CMU", "CMU", "Brown", "Brown"]
#check schoolIded

#reduce getValue (List.head schoolIded.rows _) "course" (by header)

#reduce selectRowsIndices schoolIded [⟨3, _⟩, ⟨4, _⟩]
#reduce schoolIded |> (λ t => selectRowsIndices t [⟨1, _⟩, ⟨4, _⟩])
                   |> (λ t => selectColumns t [true, false, false, true])

-- Testing, etc.
#reduce addRows (addColumn emptyTable "name" []) [Row.singleCell "hello"]
-- FIXME: the Lean m4 update broke this (used to be no need for explicit args)
-- More generally, type-class resolution seems to be kind of broken right now.
#reduce getValue (Row.append
        (@Row.singleCell String _ "pi" (List Nat) [3,1,4,1,5])
        (@Row.singleCell String _ "age" Nat 20))
        "age" (by header)

def departments : Table [("Department ID", Nat),
                         ("Department Name", String)] :=
Table.mk [
  /[31]/ | /["Sales"]/       | **|,
  /[33]/ | /["Engineering"]/ | **|,
  /[34]/ | /["Clerical"]/    | **|,
  /[35]/ | /["Marketing"]/   | **|
]

def gradebookTable : Table [("name", ULift String),
                            ("age", ULift Nat),
                            ("quizzes", Table [("quiz#", {n : Nat // 1 ≤ n ∧ n ≤ 4}),
                                               ("grade", Nat)]),
                            ("midterm", ULift Nat),
                            ("final", ULift Nat)] :=
Table.mk [
  /[ULift.up "Bob"]/ |
  /[ULift.up 12]/ |
  /[Table.mk [/[⟨1, by simp⟩]/ | /[8]/ | **|,
              /[⟨2, by simp⟩]/ | /[9]/ | **|,
              /[⟨3, by simp⟩]/ | /[7]/ | **|,
              /[⟨4, by simp⟩]/ | /[9]/ | **|]]/ |
  /[ULift.up 77]/ |
  /[ULift.up 87]/ | **|,

  /[ULift.up "Alice"]/ |
  /[ULift.up 17]/ |
  /[Table.mk [/[⟨1, by simp⟩]/ | /[6]/ | **|,
              /[⟨2, by simp⟩]/ | /[8]/ | **|,
              /[⟨3, by simp⟩]/ | /[8]/ | **|,
              /[⟨4, by simp⟩]/ | /[7]/ | **|]]/ |
  /[ULift.up 88]/ |
  /[ULift.up 85]/ | **|,

  /[ULift.up "Eve"]/ |
  /[ULift.up 13]/ |
  /[Table.mk [/[⟨1, by simp⟩]/ | /[7]/ | **|,
              /[⟨2, by simp⟩]/ | /[9]/ | **|,
              /[⟨3, by simp⟩]/ | /[8]/ | **|,
              /[⟨4, by simp⟩]/ | /[8]/ | **|]]/ |
  /[ULift.up 84]/ |
  /[ULift.up 77]/ | **|
  
]

#eval Table.repr gradebookTable
