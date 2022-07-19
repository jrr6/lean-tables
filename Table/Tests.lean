import Table.CellRowTable

macro "header" : tactic => `(repeat ((try apply Schema.HasCol.hd) <;> (apply Schema.HasCol.tl)))
macro "name" : tactic => `(repeat ((try apply Schema.HasName.hd) <;> (apply Schema.HasName.tl)))

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

infixr:50 "||" => Row.cons
notation "**|" => Row.nil
notation "/[" elem "]/" => Cell.val elem
notation "/[_]/" => Cell.emp

def t2 : Table [("prof", String), ("course", Nat), ("taught", Bool)] :=
  Table.mk
    [
      /[ "Lewis" ]/         || /[_]/      || /[ true ]/  || **|,
      /[ "Krishnamurthi" ]/ || /[ 1730 ]/ || /[ false ]/ || **|
      ]

def row1 := getRow t2 1 (by simp)

def joined := vcat t1 t2
#eval joined
#reduce joined

#reduce selectColumns3 t2 [⟨"prof", (by name)⟩, ⟨"course", (by name)⟩]
#reduce @selectColumns3 String
                        inferInstance
                        [("prof", String), ("course", Nat), ("taught", Bool)] t2 [⟨"prof", Schema.HasName.hd⟩]
#reduce Row.pick (Row.append
        (@Row.singleCell String _ "pi" (List Nat) [3,1,4,1,5])
        (@Row.singleCell String _ "age" Nat 20)) [⟨"pi", by name⟩]

def schoolIded := addColumn joined "school" ["CMU", "CMU", "CMU", "CMU", "Brown", "Brown"]
#check schoolIded

#reduce getValue (List.head schoolIded.rows _) "course" (by header)

#reduce selectRows1 schoolIded [⟨3, _⟩, ⟨4, _⟩]
#reduce schoolIded |> (λ t => selectRows1 t [⟨1, _⟩, ⟨4, _⟩])
                   |> (λ t => selectColumns1 t [true, false, false, true])

-- Testing, etc.
#reduce addRows (addColumn emptyTable "name" []) [Row.singleCell "hello"]
-- FIX?ME: the Lean m4 update broke this (used to be no need for explicit args)
-- More generally, type-class resolution seems to be kind of broken right now.
-- (Haven't checked this since moving away from type classes)
#reduce getValue (Row.append
        (@Row.singleCell String _ "pi" (List Nat) [3,1,4,1,5])
        (@Row.singleCell String _ "age" Nat 20))
        "age" (by header)

#eval @update _ _ _ [⟨("prof", String), by header⟩] t2 (λ r => @Row.singleCell _ _ "prof" String "Rob")
-- #eval update _ t2 (λ r => @Row.singleCell _ _ "prof" String "Rob")

#eval fillna joined ⟨"course", (by header)⟩ 1951

def departments : Table [("Department ID", Nat),
                         ("Department Name", String)] :=
Table.mk [
  /[31]/ || /["Sales"]/       || **|,
  /[33]/ || /["Engineering"]/ || **|,
  /[34]/ || /["Clerical"]/    || **|,
  /[35]/ || /["Marketing"]/   || **|
]

def dupDepts := addRows departments [/[31]/ || /["Information"]/ || **|,
                                     /[33]/ || /["Security"]/ || **|,
                                     /[34]/ || /["Parallelism"]/ || **|,
                                     /[35]/ || /["Functionalism"]/ || **|]
def dupDepts' := addColumn dupDepts "Number" [89, 7, 25, 27, 4, 3, 24, 1]

#eval head departments ⟨-2, sorry⟩
#reduce dropColumn joined ⟨"taught", by name⟩
#eval tsort dupDepts' ⟨"Number", by header⟩ true
#eval sortByColumns dupDepts' [⟨("Department ID", _), by header, by infer_instance⟩,
                               ⟨("Number", _), by header, by infer_instance⟩]


#reduce (count joined ⟨"course", by header⟩)
def merge : Option Nat → List (Option Nat) → Row [("Parity", Bool), ("Length", Nat)]
| (some n), xs =>
  let xs_sum := xs.foldl (λ | acc, none => acc
                            | acc, (some n) => acc + n) 0
  Row.cons (Cell.val (n = 1)) (Row.cons (Cell.val xs_sum) Row.nil)
| none, _ => Row.cons Cell.emp (Row.cons Cell.emp Row.nil)

-- FIXME: allowing different η' broke something
#reduce @groupBy _ _ _ String _ _ _ _ _ departments (λ r => (getValue r "Department ID" (by header)).map (λ (x : Nat) => Nat.mod x 2))
                            (λ r => (getValue r "Department Name" (by header)).map (λ (x : String) => x.length))
  (λ | (some n), xs =>
        let xs_sum := xs.foldl (λ | acc, none => acc
                                  | acc, (some n) => acc + n) 0
        Row.cons (Cell.val (decide (n = 1))) (Row.cons (Cell.val xs_sum) Row.nil)
     | none, _ => Row.cons Cell.emp (Row.cons Cell.emp Row.nil))

def listTable : Table [("Number", String), ("Digits", List Nat)] :=
Table.mk [
  /["pi"]/ || /[[3,1,4,1,5]]/ || **|,
  /["e"]/  || /[[2,7,1,8,2]]/ || **|
]

#reduce flattenOne listTable ⟨"Digits", by header⟩

#eval bin departments ⟨"Department ID", by header⟩ 2

def gradebookTable : Table [("name", ULift String),
                            ("age", ULift Nat),
                            ("quizzes", Table [("quiz#", {n : Nat // 1 ≤ n ∧ n ≤ 4}),
                                               ("grade", Nat)]),
                            ("midterm", ULift Nat),
                            ("final", ULift Nat)] :=
Table.mk [
  /[ULift.up "Bob"]/ ||
  /[ULift.up 12]/ ||
  /[Table.mk [/[⟨1, by simp⟩]/ || /[8]/ || **|,
              /[⟨2, by simp⟩]/ || /[9]/ || **|,
              /[⟨3, by simp⟩]/ || /[7]/ || **|,
              /[⟨4, by simp⟩]/ || /[9]/ || **|]]/ ||
  /[ULift.up 77]/ ||
  /[ULift.up 87]/ || **|,

  /[ULift.up "Alice"]/ ||
  /[ULift.up 17]/ ||
  /[Table.mk [/[⟨1, by simp⟩]/ || /[6]/ || **|,
              /[⟨2, by simp⟩]/ || /[8]/ || **|,
              /[⟨3, by simp⟩]/ || /[8]/ || **|,
              /[⟨4, by simp⟩]/ || /[7]/ || **|]]/ ||
  /[ULift.up 88]/ ||
  /[ULift.up 85]/ || **|,

  /[ULift.up "Eve"]/ ||
  /[ULift.up 13]/ ||
  /[Table.mk [/[⟨1, by simp⟩]/ || /[7]/ || **|,
              /[⟨2, by simp⟩]/ || /[9]/ || **|,
              /[⟨3, by simp⟩]/ || /[8]/ || **|,
              /[⟨4, by simp⟩]/ || /[8]/ || **|]]/ ||
  /[ULift.up 84]/ ||
  /[ULift.up 77]/ || **|
  
]

#eval Table.repr gradebookTable
