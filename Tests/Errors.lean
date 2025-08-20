import Table.API
import Table.Notation
import Tests.ExampleTables

namespace Table.Examples.Errors
open Tables

set_option pp.mvars false

-- # Malformed Tables

-- ## missingSchema
-- Error is suboptimal: the first thing to fail is resolving `[DecidableEq η]`,
-- hence the relatively unreadable message

/--
error: typeclass instance problem is stuck, it is often due to metavariables
  DecidableEq ?_
-/
#guard_msgs in
def missingSchema :=
Table.mk [
  /[ "Bob"   , 12 , "blue"  ],
  /[ "Alice" , 17 , "green" ],
  /[ "Eve"   , 13 , "red"   ]
]

-- ## missingRow

/--
error: application type mismatch
  List.cons Row.nil
argument
  Row.nil
has type
  Row [] : Type 1
but is expected to have type
  Row [("name", String), ("age", Nat), ("favorite color", String)] : Type 1
-/
#guard_msgs in
def missingRow :
  Table [("name", String), ("age", Nat), ("favorite color", String)] :=
Table.mk [
  /[ "Bob"   , 12     , "blue"         ],
  /[ "Alice" , 17     , "green"        ],
  /[                                   ]
]

-- ## missingCell

/--
error: application type mismatch
  Row.cons (Cell.val "blue")
argument
  Cell.val "blue"
has type
  Cell "age" String : Type
but is expected to have type
  Cell "age" Nat : Type
-/
#guard_msgs in
def missingCell :
  Table [("name", String), ("age", Nat), ("favorite color", String)] :=
Table.mk [
  /[ "Bob"   , "blue" ],
  /[ "Alice" , 17     , "green"        ],
  /[ "Eve"   , 13     , "red"          ]
]

-- ## swappedColumns
/--
error: application type mismatch
  Row.cons (Cell.val "Bob")
argument
  Cell.val "Bob"
has type
  Cell "age" String : Type
but is expected to have type
  Cell "age" Nat : Type
---
error: application type mismatch
  Row.cons (Cell.val "Alice")
argument
  Cell.val "Alice"
has type
  Cell "age" String : Type
but is expected to have type
  Cell "age" Nat : Type
---
error: application type mismatch
  Row.cons (Cell.val "Eve")
argument
  Cell.val "Eve"
has type
  Cell "age" String : Type
but is expected to have type
  Cell "age" Nat : Type
---
error: failed to synthesize
  OfNat String 12
numerals are polymorphic in Lean, but the numeral `12` cannot be used in a context where the expected type is
  String
due to the absence of the instance above
Additional diagnostic information may be available using the `set_option diagnostics true` command.
---
error: failed to synthesize
  OfNat String 17
numerals are polymorphic in Lean, but the numeral `17` cannot be used in a context where the expected type is
  String
due to the absence of the instance above
Additional diagnostic information may be available using the `set_option diagnostics true` command.
---
error: failed to synthesize
  OfNat String 13
numerals are polymorphic in Lean, but the numeral `13` cannot be used in a context where the expected type is
  String
due to the absence of the instance above
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
def swappedColumns :
  Table [("name", String), ("age", Nat), ("favorite color", String)] :=
Table.mk [
  /[ 12     , "Bob"   , "blue"         ],
  /[ 17     , "Alice" , "green"        ],
  /[ 13     , "Eve"   , "red"          ]
]

-- ## schemaTooShort
-- Error is somewhat unreadable, but at least conveys a general sense of "there
-- are data present where an absence of data was expected"

/--
error: application type mismatch
  Row.cons (Cell.val 12) (Row.cons (Cell.val "blue") Row.nil)
argument
  Row.cons (Cell.val "blue") Row.nil
has type
  Row [(?_, String)] : Type 1
but is expected to have type
  Row [] : Type 1
---
error: application type mismatch
  Row.cons (Cell.val 17) (Row.cons (Cell.val "green") Row.nil)
argument
  Row.cons (Cell.val "green") Row.nil
has type
  Row [(?_, String)] : Type 1
but is expected to have type
  Row [] : Type 1
---
error: application type mismatch
  Row.cons (Cell.val 13) (Row.cons (Cell.val "red") Row.nil)
argument
  Row.cons (Cell.val "red") Row.nil
has type
  Row [(?_, String)] : Type 1
but is expected to have type
  Row [] : Type 1
-/
#guard_msgs in
def schemaTooShort : Table [("name", String), ("age", Nat)] :=
Table.mk [
  /[ "Bob"   , 12     , "blue"         ],
  /[ "Alice" , 17     , "green"        ],
  /[ "Eve"   , 13     , "red"          ]
]

-- ## schemaTooLong
-- This is arguably an unilluminating way of framing this example because of the
-- type mismatch. Changing the type of the "favorite number" column to `String`
-- reveals a reasonably informative error message regarding the absence of a
-- fourth column.

/--
error: application type mismatch
  Row.cons (Cell.val "blue")
argument
  Cell.val "blue"
has type
  Cell "favorite number" String : Type
but is expected to have type
  Cell "favorite number" Nat : Type
---
error: application type mismatch
  Row.cons (Cell.val "green")
argument
  Cell.val "green"
has type
  Cell "favorite number" String : Type
but is expected to have type
  Cell "favorite number" Nat : Type
---
error: application type mismatch
  Row.cons (Cell.val "red")
argument
  Cell.val "red"
has type
  Cell "favorite number" String : Type
but is expected to have type
  Cell "favorite number" Nat : Type
-/
#guard_msgs in
def schemaTooLong :
  Table [("name", String), ("age", Nat),
         ("favorite number", Nat), ("favorite color", String)] :=
Table.mk [
  /[ "Bob"   , 12     , "blue"          ],
  /[ "Alice" , 17     , "green"         ],
  /[ "Eve"   , 13     , "red"           ]
]

-- # Using Tables

universe u_η
variable {η : Type u_η} [DecidableEq η] {sch : @Schema η}

-- Since we don't have an actual image type, we fake it:
abbrev Image : Type := Nat  -- Any inhabited type will do
opaque scatterPlot (t : Table sch)
                   (c1 : η)
                   (c2 : η)
                   (hc1 : sch.HasCol (c1, Nat) := by header)
                   (hc2 : sch.HasCol (c2, Nat) := by header) : Image
-- What's a "categorical value?" For our purposes, let's make it a boolean.
opaque pieChart (t : Table sch)
                (c1 : η)
                (c2 : η)
                (hc1 : sch.HasCol (c1, Bool) := by header)
                (hc2 : sch.HasCol (c2, Nat) := by header) : Image


-- ## midFinal
-- We generate this error message, so it's fairly helpful by design. Recent
-- Lean updates have inserted the unavoidable "could not synthesize using
-- tactics" error message, which may create some confusion.

/--
error: could not synthesize default value for parameter 'hc1' using tactics
---
error: Could not prove that header ("mid",
  Nat) is in schema [("name", String), ("age", Nat), ("quiz1", Nat), ("quiz2", Nat), ("midterm", Nat), ("quiz3", Nat),
  ("quiz4", Nat), ("final", Nat)]
-/
#guard_msgs in
def midFinal :=
  scatterPlot gradebook "mid" "final"

def midFinalCorrected :=
  scatterPlot gradebook "midterm" "final"

-- ## blackAndWhite

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Could not prove that header ("black and white", Bool) is in schema jellyAnon.schema
-/
#guard_msgs in
def eatBlackAndWhite (r : Row (schema jellyAnon)) : Option Bool :=
  getValue r "black and white" == some true
def blackAndWhite :=
  buildColumn jellyAnon "eat black and white" eatBlackAndWhite

def eatBlackAndWhiteCorrected (r : Row (schema jellyAnon)) : Option Bool :=
  match getValue r "black", getValue r "white" with
    | .some true, .some true => true
    | _, _                   => false
def blackAndWhiteCorrected :=
  buildColumn jellyAnon "eat black and white" eatBlackAndWhite

-- ## pieCount
-- This is a hard case to mimic with our setup because it's unlikely one would
-- jump through so many hoops to contrive this particular circumstance.

/--
error: could not synthesize default value for parameter 'hc1' using tactics
---
error: Could not prove that header ("true", Bool) is in schema [("value", Bool), ("count", Nat)]
---
error: could not synthesize default value for parameter 'hc2' using tactics
---
error: Could not prove that header ("get acne", Nat) is in schema [("value", Bool), ("count", Nat)]
-/
#guard_msgs in
def showAcneProportions {sch : @Schema String}
  (t : Table sch)
  (hacne : sch.HasCol ("get acne", Bool)) :=
  pieChart (count t "get acne") "true" "get acne"
def pieCount := showAcneProportions jellyAnon

def showAcneProportionsCorrected {sch : @Schema String}
  (t : Table sch)
  (hacne : sch.HasCol ("get acne", Bool)) :=
  pieChart (count t "get acne" hacne) "value" "count"
def pieCountCorrected := showAcneProportionsCorrected jellyAnon

-- ## brownGetAcne
def brownAndGetAcne {sch: @Schema String}
  (r : Row sch)
  (hacne : sch.HasCol ("get acne", Bool) := by header)
  (hbrown : sch.HasCol ("brown", Bool) := by header) :=
  match getValue r "brown", getValue r "get acne" with
  | .some true, .some true => some true
  | _         , _          => some false
def brownAndGetAcneTable :=
  buildColumn jellyNamed "part2" brownAndGetAcne
/--
error: could not synthesize default value for parameter 'hc' using tactics
---
error: Could not prove that header ("brown and get acne",
  ?_) is in schema Schema.append
  [("name", String), ("get acne", Bool), ("red", Bool), ("black", Bool), ("white", Bool), ("green", Bool),
    ("yellow", Bool), ("brown", Bool), ("orange", Bool), ("pink", Bool), ("purple", Bool)]
  [("part2", Bool)]
-/
#guard_msgs in
def brownGetAcne :=
  count brownAndGetAcneTable "brown and get acne"

def brownAndGetAcneTableCorrected :=
  buildColumn jellyNamed "brown and get acne" brownAndGetAcne
def brownGetAcneCorrected :=
  count brownAndGetAcneTableCorrected "brown and get acne"

-- ## getOnlyRow
-- In recent versions of Lean, `decide` gives better error messages, making this
-- more readable

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: tactic 'decide' proved that the proposition
  1 < (students.tfilter fun r => decide (getValue r "name" Schema.HasCol.hd = some "Alice")).nrows
is false
-/
#guard_msgs in
def getOnlyRow :=
  getValue (
    getRow
      (tfilter students (λ r => getValue r "name" = "Alice"))
      1
  )
  "favorite color"

def getOnlyRowCorrected :=
  getValue (
    getRow
      (tfilter students (λ r => getValue r "name" = "Alice"))
      0
  )
  "favorite color"

-- ## favoriteColor

/--
error: type mismatch
  getValue r "favorite color" ?_
has type
  Option ?_ : Type
but is expected to have type
  Bool : Type
-/
#guard_msgs in
def participantsLikeGreen {sch : @Schema String} (t : Table sch)
  (hcolor: sch.HasCol ("favorite color", String) := by header) :=
      tfilter t (λ r => getValue r "favorite color")

def participantsLikeGreenCorrected {sch : @Schema String} (t : Table sch)
  (hcolor: sch.HasCol ("favorite color", String) := by header) :=
      tfilter t (λ r => getValue r "favorite color" = "green")

-- ## brownJellybeans
def keep {sch : Schema}
         (hcolor : sch.HasCol ("color", Bool) := by header)
         (r : Row sch) :=
  match getValue r "color" hcolor with
  | none => false
  | some b => b
def countParticipants {sch : @Schema String}
  (t : Table sch) (color : String)
  (hcolor : sch.HasCol ("color", Bool) := by header) :=
  nrows (tfilter t keep)
/--
error: could not synthesize default value for parameter 'hcolor' using tactics
---
error: Could not prove that header ("color",
  Bool) is in schema [("get acne", Bool), ("red", Bool), ("black", Bool), ("white", Bool), ("green", Bool),
  ("yellow", Bool), ("brown", Bool), ("orange", Bool), ("pink", Bool), ("purple", Bool)]
-/
#guard_msgs in
def brownJellyBeans := countParticipants jellyAnon "brown"

def keepCorrected1 {sch : Schema}
  (color: String) (hcolor : sch.HasCol (color, Bool) := by header)
  (r : Row sch) :=
  match getValue r color hcolor with
  | none => false
  | some b => b
def countParticipantsCorrected1 {sch : @Schema String}
  (color : String) (t : Table sch)
  (hcolor : sch.HasCol (color, Bool) := by header) :=
  nrows (tfilter t (keepCorrected1 color))
def brownJellyBeansCorrected1 :=
  countParticipantsCorrected1 "brown" jellyAnon

def countParticipantsCorrected2 {sch : @Schema String}
  (color : String) (t : Table sch)
  (hcolor : sch.HasCol (color, Bool) := by header) :=
  let keep (r : Row sch) :=
    match getValue r color with
    | none => false
    | some b => b
  nrows (tfilter t keep)
def brownJellyBeansCorrected2 :=
  countParticipantsCorrected2 "brown" jellyAnon

-- ## employeeToDepartment
def lastNameToDeptId {sch : Schema}
  (deptTab : Table sch) (name : Option String)
  (hln : sch.HasCol ("Last Name", String) := by header)
  (hid : sch.HasCol ("Department ID", Nat) := by header) :=
  let matchName (r : Row sch) : Bool :=
    getValue r "Last Name" = name
  let matchedTab := tfilter deptTab matchName
  match hnrows : nrows matchedTab with
  | 0 => none
  | .succ n =>
    let matchedRow := getRow matchedTab 0 (hnrows ▸ Nat.zero_lt_succ _)
    getValue matchedRow "Department ID"
def employeeToDept {emplSch deptSch : @Schema String}
  (name : String)
  (emplTab : Table emplSch)
  (deptTab : Table deptSch)
  (heln : emplSch.HasCol ("Last Name", String) := by header)
  (hdln : deptSch.HasCol ("Last Name", String) := by header)
  (hid : deptSch.HasCol ("Department ID", Nat) := by header) :=
  buildColumn emplTab "Department Name" (λ r =>
    lastNameToDeptId deptTab (getValue r "Last Name"))
/--
error: could not synthesize default value for parameter 'hdln' using tactics
---
error: Could not prove that header ("Last Name", String) is in schema [("Department ID", Nat), ("Department Name", String)]
-/
#guard_msgs in
def employeeToDepartment :=
  employeeToDept "Rafferty" employees departments

def deptIdToDeptNameCorrected {sch : Schema}
  (deptTab : Table sch) (deptId : Option Nat)
  (hnm : sch.HasCol ("Department Name", String) := by header)
  (hid : sch.HasCol ("Department ID", Nat) := by header) :=
  let matchName (r : Row sch) : Bool :=
    getValue r "Department ID" hid = deptId
  let matchedTab := tfilter deptTab matchName
  match hnrows : nrows matchedTab with
  | 0 => none
  | .succ n =>
    let matchedRow := getRow matchedTab 0 (hnrows ▸ Nat.zero_lt_succ _)
    getValue matchedRow "Department Name"
def employeeToDeptCorrected {emplSch deptSch : @Schema String}
  (name : String)
  (emplTab : Table emplSch)
  (deptTab : Table deptSch)
  (heln : emplSch.HasCol ("Last Name", String) := by header)
  (hdnm : deptSch.HasCol ("Department Name", String) := by header)
  (heid : emplSch.HasCol ("Department ID", Nat) := by header)
  (hdid : deptSch.HasCol ("Department ID", Nat) := by header) :=
  let matchName (r : Row emplSch) : Bool :=
    getValue r "Last Name" = some name
  let matchedTab := tfilter emplTab matchName
  match hnrows : nrows matchedTab with
  | 0 => none
  | .succ n =>
    let matchedRow := getRow matchedTab 0 (hnrows ▸ Nat.zero_lt_succ _)
    let deptId := getValue matchedRow "Department ID"
    deptIdToDeptNameCorrected deptTab deptId
def employeeToDepartmentCorrected :=
  employeeToDeptCorrected "Rafferty" employees departments
