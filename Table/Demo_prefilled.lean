import Table.Widgets
import Table.Proofs

#print Header
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

def myTable :
  Table [("Number", Nat), ("Content", String)] :=
Table.mk [
  (Row.cons (Cell.val 9)
    (Row.cons (Cell.val "Rationals and Reals")
      Row.nil))
]
-- Table.mk
--       [ /[9             ,  "Rationals and Reals" ],
--         /[10            ,  "Metaprogramming"]
--       ]

def myTableDropped := dropColumns myTable A[⟨"Number", by name⟩]

#table myTable

#check ActionList

/- Demo! -/

inductive GradeMode
| ABC
| SNC
deriving DecidableEq
instance : ToString GradeMode := ⟨λ | .ABC => "ABC" | .SNC => "SNC"⟩

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

inductive LetterGrade
| A | B | C | S | NC
deriving DecidableEq
instance : ToString LetterGrade :=
  ⟨λ | .A => "A" | .B => "B" | .C => "C" | .S => "S" | .NC => "NC"⟩

def grades :
  Table [("Anonymous ID", Nat),
         ("hw1", Nat),
         ("hw2", Nat),
         ("midterm", Nat),
         ("hw3", Nat),
         ("final", Nat),
         ("project", LetterGrade)] :=
Table.mk [
  /[ 31415926, 95 , 83, 85, 91 , 88, LetterGrade.A ],
  /[ 32033030, 92 , 98 , 90, 90 , 91, LetterGrade.A ],
  /[ 27182818, 75 , EMP, 78, 88 , 83, LetterGrade.B ],
  /[ 29109101, 97 , 92 , 91, EMP, 90, LetterGrade.B ],
  /[ 19511951, EMP, 83 , 70, 84 , 74, LetterGrade.C ],
  /[ 18637600, 92 , 96 , 89, 97 , 91, LetterGrade.A ],
  /[ 40186310, 86 , 91 , 77, 85 , 81, LetterGrade.C ]
]

#table grades

-- Find the average prior performance of students by project grade:

def oAverage (xs : List $ Option Nat) : Option Nat := some $
  List.foldl (λ acc => λ | none => acc | some x => x + acc) 0 xs / xs.length

def projectExamGrades :
  Table [("project", LetterGrade), ("mt_avg", Nat), ("final_avg", Nat)] :=
  pivotTable
        grades
        [⟨("project", _), by header⟩]
        (by inst)
        [⟨("mt_avg", _), ⟨("midterm", _), by header⟩, oAverage⟩,
         ⟨("final_avg", _), ⟨("final", _), by header⟩, oAverage⟩]

#table projectExamGrades
    
-- Try to match up the roster with anonymous IDs

def studentsWithIdsBasic := hcat roster disambiguationTable

#table disambiguationTable
#table studentsWithIdsBasic

def studentsWithIds :=
  leftJoin roster
           disambiguationTable
           A[⟨("Name", _), inferInstance, by header, by header⟩]

#table studentsWithIds

-- Join the IDed roster with grade data; in the end, we only need Banner IDs

def studentsWithIdsAndGrades :=
  leftJoin studentsWithIds
           grades
           A[⟨("Anonymous ID", _), inferInstance, by header, by header⟩]

#table studentsWithIdsAndGrades

def gradesByBannerID :=
  dropColumns studentsWithIdsAndGrades
    A[⟨"Anonymous ID", by name⟩, ⟨"Name", by name⟩]

#table gradesByBannerID

-- Fill in 0s for missing grades

def gradesFilledIn :=
  List.foldl (λ acc x =>
    fillna acc x 0
  ) gradesByBannerID
  [⟨"hw1", by header⟩, ⟨"hw2", by header⟩, ⟨"hw3", by header⟩,
   ⟨"midterm", by header⟩, ⟨"final", by header⟩]

#table gradesFilledIn

-- Compute final grades

/- USE THIS IF NOT DOING FILLNA:
def computeGrade (r : Row (schema studentsWithIdsAndGrades))
                 (_ : Fin (nrows studentsWithIdsAndGrades)) :=
  let hw1 := (getValue r "hw1" (by header)).getD 0
  let hw2 := (getValue r "hw2" (by header)).getD 0
  let hw3 := (getValue r "hw3" (by header)).getD 0
  let midterm := (getValue r "midterm" (by header)).getD 0
  let final := (getValue r "final" (by header)).getD 0
  let project :=
    match getValue r "project" (by header) with
    | some LetterGrade.A => 95
    | some LetterGrade.B => 85
    | some LetterGrade.C => 75
    | _ => 0
  let gradeMode := getValue r "Grade Mode" (by header)
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
  match getValue (τ := String) r "Banner ID" (by header) with
  | some bid => /["Banner ID" := bid, "Grade" := finalGrade]
  | _        => /["Banner ID" := EMP, "Grade" := finalGrade]
-/

def computeGrade (r : Row (schema gradesFilledIn))
                 (_ : Fin (nrows gradesFilledIn)) :=
  let hw1 := (getValue r "hw1" (by header)).getD 0
  let hw2 := (getValue r "hw2" (by header)).getD 0
  let hw3 := (getValue r "hw3" (by header)).getD 0
  let midterm := (getValue r "midterm" (by header)).getD 0
  let final := (getValue r "final" (by header)).getD 0
  let project :=
    match getValue r "project" (by header) with
    | some LetterGrade.A => 95
    | some LetterGrade.B => 85
    | some LetterGrade.C => 75
    | _ => 0
  let gradeMode := getValue r "Grade Mode" (by header)
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
  match getValue (τ := String) r "Banner ID" (by header) with
  | some bid => /["Banner ID" := bid, "Grade" := finalGrade]
  | _        => /["Banner ID" := EMP, "Grade" := finalGrade]

def finalGrades := select gradesFilledIn computeGrade

#table gradesFilledIn

#table finalGrades

-- Group student grades by project grades:

def groupedByProject := groupBySubtractive grades ⟨"project", by header⟩

#table groupedByProject

#check groupBySubtractive_spec7
#check getColumn2_spec2

-- The result of doing this kind of "grouping" should only ever reduce the
-- number of rows in the resulting (outer) table:

theorem nrows_groupBySubtractive {η τ} [DecidableEq η] [DecidableEq τ]
  {schema : @Schema η} (t : Table schema) (c : (c : η) × schema.HasCol (c, τ)) :
  nrows (groupBySubtractive t c) ≤ nrows t :=
  by
    have h_spec := groupBySubtractive_spec7 t c
    rw [h_spec]
    have h := getColumn2_spec2 t c.fst c.snd
    rw [←h]
    apply List.length_unique_le
