import Table.API
import Table.Notation
import Table.ExampleTables

namespace Table.Examples.Errors
open Tables

-- # Malformed Tables

-- ## missingSchema
-- Error is suboptimal: the first thing to fail is resolving `[DecidableEq η]`,
-- hence the relatively unreadable message
def missingSchema :=
Table.mk [
  /[ "Bob"   , 12 , "blue"  ],
  /[ "Alice" , 17 , "green" ],
  /[ "Eve"   , 13 , "red"   ]
]

-- ## missingRow
def missingRow :
  Table [("name", String), ("age", Nat), ("favorite color", String)] :=
Table.mk [
  /[ "Bob"   , 12     , "blue"         ],
  /[ "Alice" , 17     , "green"        ],
  /[                                   ]
]

-- ## missingCell
def missingCell :
  Table [("name", String), ("age", Nat), ("favorite color", String)] :=
Table.mk [
  /[ "Bob"   , "blue" ],
  /[ "Alice" , 17     , "green"        ],
  /[ "Eve"   , 13     , "red"          ]
]

-- ## swappedColumns
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
-- We generate this error message, so it's fairly helpful by design
def midFinal :=
  scatterPlot gradebook "mid" "final"

def midFinalCorrected :=
  scatterPlot gradebook "midterm" "final"

-- ## blackAndWhite
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
def brownGetAcne :=
  count brownAndGetAcneTable "brown and get acne"

def brownAndGetAcneTableCorrected :=
  buildColumn jellyNamed "brown and get acne" brownAndGetAcne
def brownGetAcneCorrected :=
  count brownAndGetAcneTableCorrected "brown and get acne"

-- ## getOnlyRow
-- Proof error is not at all enlightening, but locality should at least make it
-- somewhat evident where things are going wrong.
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
