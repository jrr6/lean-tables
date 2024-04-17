import Table.API
import Table.Widgets
import Table.Proofs

/-! # Verified Tables in Lean 4

The goal: implement the **Brown Benchmark for Table Types (B2T2)** (Lu et al.,
2022) in Lean 4 (including specifications!).

Why do this?
- Develop a Lean 4 library for working with tabular data
- See what B2T2 looks like in a different (strong, dependent) type system
- See how precisely/usably Lean can realize B2T2
- Have fun with dependent types
- Take advantage of some neat Lean 4 features

What is a table?
                                     -
     (String)    (String)  (Nat)      |  <-- Schema
|    "City"    | "State" | "ZIP" |    |
----------------------------------   -
| "Providence" | "RI"    | 2912  |    |
| "Pawtucket"  | "RI"    | 2860  |    |  <-- Table = collection of rows
| "Boston"     | "MA"    | 2110  |    |        (Row = collection of cells)
| "Washington" |         | 20001 |    |
----------------------------------   -

The main types in the table encoding:

- *Header*: a (name, type) pair that specifies a column
  Ex: `("Name", String)`
- *Schema*: a list of headers describing the columns in a table
  Ex: `[("Name", String), ("Value", Nat)]`
- *Table* (indexed by a schema): a list of rows
  Ex: `[/["Name 1", 1], /["Name 2", 2]]`
- *Row* (indexed by a schema `s`): Empty, or a `hd s`-cell cons-ed onto a
  `tl s`-row (≈ `HList`)
  Ex: `/[]`, `/["Name 1", 1] = Row.cons (Cell.val "Name 1") ...`
- *Cell* (indexed by a header): is either empty or contains a value of the
  type specified by the header (≈ `option`)
  Ex: `Cell.emp`, `Cell.val 1`

Basically, we're just adding names and empty cells to our HW 4 setup.
-/

#reduce @Header
#print Schema
#check Table
#check Row
#check Cell

/-
| Number |       Content       |
--------------------------------
| 9      | Rationals and reals |
| 10     | Metaprogramming     |
-/

def myTable : Table [("Number", Nat), ("Content", String)] :=
Table.mk [
  Row.cons (Cell.val 9) $
    Row.cons (Cell.val "Rationals and reals") Row.nil,
  /[10, "Metaprogramming"]
]

-- List (CertifiedName (schema myTable))
def myTableDropped := dropColumns myTable A[⟨"Number", by name⟩]

#table myTableDropped

#check ActionList

-- /- Demo! -/

inductive GradeMode
| ABC | SNC
deriving DecidableEq
instance : ToString GradeMode := ⟨λ | .ABC => "ABC" | .SNC => "SNC"⟩

inductive LetterGrade
| A | B | C | S | NC
deriving DecidableEq
instance : ToString LetterGrade :=
  ⟨λ | .A => "A" | .B => "B" | .C => "C" | .S => "S" | .NC => "NC"⟩

def roster :
  Table [("Name", String), ("Banner ID", String), ("Grade Mode", GradeMode)] :=
Table.mk [
  /[ "Alice", "B00000001", GradeMode.ABC ],
  /[ "Bob"  , "B00000002", GradeMode.ABC ],
  /[ "Carol", "B00000003", GradeMode.SNC ],
  /[ "Dave" , "B00000004", GradeMode.ABC ],
  /[ "Eve"  , "B00000005", GradeMode.SNC ],
  /[ "Frank", "B00000006", GradeMode.ABC ],
  /[ "Grace", "B00000007", GradeMode.SNC ]
]

#table roster

def disambiguationTable : Table [("Name", String), ("Anonymous ID", Nat)] :=
Table.mk [
  /[ "Grace", 18637600 ],
  /[ "Carol", 19511951 ],
  /[ "Bob"  , 27182818 ],
  /[ "Eve"  , 29109101 ],
  /[ "Alice", 31415926 ],
  /[ "Dave" , 32033030 ],
  /[ "Frank", 40186310 ]
]

#table disambiguationTable

def grades :
  Table [("Anonymous ID", Nat),
         ("hw1", Nat),
         ("hw2", Nat),
         ("midterm", Nat),
         ("hw3", Nat),
         ("final", Nat),
         ("project", LetterGrade)] :=
Table.mk [
  /[ 31415926, 95 , EMP, 82, 91 , 88, LetterGrade.A ],
  /[ 32033030, 92 , 98 , 90, 90 , 91, LetterGrade.A ],
  /[ 27182818, 75 , EMP, 78, 88 , 83, LetterGrade.B ],
  /[ 29109101, 97 , 92 , 91, EMP, 90, LetterGrade.B ],
  /[ 19511951, EMP, 83 , 70, 84 , 74, LetterGrade.C ],
  /[ 18637600, 92 , 96 , 89, 97 , 91, LetterGrade.A ],
  /[ 40186310, 86 , 91 , 77, 85 , 81, LetterGrade.C ]
]

#table grades

-- Match up the roster with anonymous IDs

def studentsWithIDs :=
  leftJoin roster disambiguationTable A["Name"]

#table studentsWithIDs

-- Join the IDed roster with grade data; in the end, we only need Banner IDs

def studentsWithIdsAndGrades :=
  leftJoin studentsWithIDs
           grades
           A["Anonymous ID"]

#table studentsWithIdsAndGrades

-- Compute final grades

def computeGrade (r : Row (schema studentsWithIdsAndGrades))
                 (_ : Fin (nrows studentsWithIdsAndGrades)) :=
  let hw1 := (getValue r "hw1").getD 0
  let hw2 := (getValue r "hw2").getD 0
  let hw3 := (getValue r "hw3").getD 0
  let midterm := (getValue r "midterm").getD 0
  let final := (getValue r "final").getD 0
  let project :=
    match getValue r "project" with
    | some LetterGrade.A => 95
    | some LetterGrade.B => 85
    | some LetterGrade.C => 75
    | _ => 0
  let gradeMode := getValue r "Grade Mode"
  let numericGrade :=
    ((hw1 + hw2 + hw3) + 2 * midterm + 2 * final + 3 * project) / 10
  let finalGrade :=
    match gradeMode with
    | some GradeMode.ABC =>
      if numericGrade ≥ 90
      then LetterGrade.A
      else if numericGrade ≥ 80
      then LetterGrade.B
      else if numericGrade ≥ 70
      then LetterGrade.C
      else LetterGrade.NC
    | _ => if numericGrade ≥ 70 then LetterGrade.S else LetterGrade.NC
  match getValue (τ := String) r "Banner ID" with
  | some bid => /["Banner ID" := bid, "Grade" := finalGrade]
  | _        => /["Banner ID" := EMP, "Grade" := finalGrade]

def finalGrades := select studentsWithIdsAndGrades computeGrade

#table finalGrades

-- Group student grades by project grades:

def groupedByProject := groupBySubtractive grades "project"

#table groupedByProject

-- The result of doing this kind of "grouping" should only ever reduce the
-- number of rows in the resulting (outer) table:

#check groupBySubtractive_spec7
#check getColumn2_spec2
#check List.length_unique_le

theorem nrows_groupBySubtractive {η τ} [DecidableEq η] [DecidableEq τ]
  {schema : @Schema η} (t : Table schema) (c : η) (hc : schema.HasCol (c, τ)) :
    nrows (groupBySubtractive t c hc) ≤ nrows t := by
  have h_gbs := groupBySubtractive_spec7 t c hc
  rw [h_gbs]
  rw [←getColumn2_spec2 t c hc]
  apply List.length_unique_le
