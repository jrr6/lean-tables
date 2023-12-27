import Table.API
import Table.Notation
import Table.ExampleTables

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

abbrev Image : Type := Nat  -- Any inhabited type will do
opaque scatterPlot (t : Table sch)
                   (c1 : ((nm : η) × sch.HasCol (nm, Nat)))
                   (c2 : ((nm : η) × sch.HasCol (nm, Nat))) : Image
-- What's a "categorical value?" For our purposes, let's make it a boolean.
opaque pieChart (t : Table sch)
                (c1 : ((nm : η) × sch.HasCol (nm, Bool)))
                (c2 : ((nm : η) × sch.HasCol (nm, Nat))) : Image


-- ## midFinal
-- Error message is somewhat unreadable but is localized.
def midFinal :=
  scatterPlot gradebook ⟨"mid", by header⟩ ⟨"final", by header⟩

def midFinalCorrected :=
  scatterPlot gradebook ⟨"midterm", by header⟩ ⟨"final", by header⟩

-- ## blackAndWhite
def eatBlackAndWhite (r : Row (schema jellyAnon)) : Option Bool :=
  some $ getValue r "black and white" (by header) == true
def blackAndWhite :=
  buildColumn jellyAnon "eat black and white" eatBlackAndWhite

def eatBlackAndWhiteCorrected (r : Row (schema jellyAnon)) : Option Bool :=
  match getValue r "black" (by header), getValue r "white" (by header) with
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
  pieChart (count t ⟨"get acne", hacne⟩) ⟨"true", by header⟩ ⟨"get acne", hacne⟩
def pieCount := showAcneProportions jellyAnon (by header)

def showAcneProportionsCorrected {sch : @Schema String}
  (t : Table sch)
  (hacne : sch.HasCol ("get acne", Bool)) :=
  pieChart (count t ⟨"get acne", hacne⟩)
           ⟨"value", by header⟩ ⟨"count", by header⟩
def pieCountCorrected := showAcneProportionsCorrected jellyAnon (by header)

-- ## brownGetAcne
def brownAndGetAcne {sch: @Schema String}
  (hacne : sch.HasCol ("get acne", Bool))
  (hbrown : sch.HasCol ("brown", Bool))
  (r : Row sch) :=
  match getValue r "brown" hbrown, getValue r "get acne" hacne with
  | .some true, .some true => some true
  | _         , _          => some false
def brownAndGetAcneTable :=
  buildColumn jellyNamed "part2" (brownAndGetAcne (by header) (by header))
def brownGetAcne :=
  count brownAndGetAcneTable ⟨"brown and get acne", by header⟩

def brownAndGetAcneTableCorrected :=
  buildColumn jellyNamed "brown and get acne"
    (brownAndGetAcne (by header) (by header))
def brownGetAcneCorrected :=
  count brownAndGetAcneTableCorrected ⟨"brown and get acne", by header⟩

-- ## getOnlyRow
-- Proof error is again not entirely enlightening, but locality should make it
-- clear where things are going wrong.
def getOnlyRow :=
  getValue (
    getRow
      (tfilter students (λ r => getValue r "name" (by header) = "Alice"))
      1
      (by decide)
  )
  "favorite color"
  (by header)

def getOnlyRowCorrected :=
  getValue (
    getRow
      (tfilter students (λ r => getValue r "name" (by header) = "Alice"))
      0
      (by decide)
  )
  "favorite color"
  (by header)

-- ## favoriteColor
def participantsLikeGreen {sch : @Schema String} (t : Table sch)
  (hcolor: sch.HasCol ("favorite color", String)) :=
      tfilter t (λ r => getValue r "favorite color" hcolor)

def participantsLikeGreenCorrected {sch : @Schema String} (t : Table sch)
  (hcolor: sch.HasCol ("favorite color", String)) :=
      tfilter t (λ r => getValue r "favorite color" hcolor = "green")

-- ## brownJellybeans
def keep {sch : Schema} (hcolor : sch.HasCol ("color", Bool)) (r : Row sch) :=
  match getValue r "color" hcolor with
  | none => false
  | some b => b
def countParticipants {sch : @Schema String}
  (hcolor : sch.HasCol ("color", Bool)) (t : Table sch) (color : String) :=
  nrows (tfilter t (keep hcolor))
def brownJellyBeans := countParticipants (by header) jellyAnon "brown"

def keepCorrected1 {sch : Schema}
  (color: String) (hcolor : sch.HasCol (color, Bool))
  (r : Row sch) :=
  match getValue r color hcolor with
  | none => false
  | some b => b
def countParticipantsCorrected1 {sch : @Schema String}
  (color : String) (hcolor : sch.HasCol (color, Bool)) (t : Table sch) :=
  nrows (tfilter t (keepCorrected1 color hcolor))
def brownJellyBeansCorrected1 :=
  countParticipantsCorrected1 "brown" (by header) jellyAnon

def countParticipantsCorrected2 {sch : @Schema String}
  (color : String) (hcolor : sch.HasCol (color, Bool)) (t : Table sch) :=
  let keep (r : Row sch) :=
    match getValue r color hcolor with
    | none => false
    | some b => b
  nrows (tfilter t keep)
def brownJellyBeansCorrected2 :=
  countParticipantsCorrected2 "brown" (by header) jellyAnon

-- ## employeeToDepartment
def lastNameToDeptId {sch : Schema}
  (deptTab : Table sch) (name : Option String)
  (hln : sch.HasCol ("Last Name", String))
  (hid : sch.HasCol ("Department ID", Nat)) :=
  let matchName (r : Row sch) : Bool :=
    getValue r "Last Name" hln = name
  let matchedTab := tfilter deptTab matchName
  match hnrows : nrows matchedTab with
  | 0 => none
  | .succ n =>
    let matchedRow := getRow matchedTab 0 (hnrows ▸ Nat.zero_lt_succ _)
    getValue matchedRow "Department ID" hid
def employeeToDept {emplSch deptSch : @Schema String}
  (name : String)
  (emplTab : Table emplSch)
  (deptTab : Table deptSch)
  (heln : emplSch.HasCol ("Last Name", String))
  (hdln : deptSch.HasCol ("Last Name", String))
  (hid : deptSch.HasCol ("Department ID", Nat)) :=
  buildColumn emplTab "Department Name" (λ r =>
    lastNameToDeptId deptTab (getValue r "Last Name" heln) hdln hid)
def employeeToDepartment :=
  employeeToDept "Rafferty" employees departments
    (by header) (by header) (by header)

def deptIdToDeptNameCorrected {sch : Schema}
  (deptTab : Table sch) (deptId : Option Nat)
  (hnm : sch.HasCol ("Department Name", String))
  (hid : sch.HasCol ("Department ID", Nat)) :=
  let matchName (r : Row sch) : Bool :=
    getValue r "Department ID" hid = deptId
  let matchedTab := tfilter deptTab matchName
  match hnrows : nrows matchedTab with
  | 0 => none
  | .succ n =>
    let matchedRow := getRow matchedTab 0 (hnrows ▸ Nat.zero_lt_succ _)
    getValue matchedRow "Department Name" hnm
def employeeToDeptCorrected {emplSch deptSch : @Schema String}
  (name : String)
  (emplTab : Table emplSch)
  (deptTab : Table deptSch)
  (heln : emplSch.HasCol ("Last Name", String))
  (hdnm : deptSch.HasCol ("Department Name", String))
  (heid : emplSch.HasCol ("Department ID", Nat))
  (hdid : deptSch.HasCol ("Department ID", Nat)) :=
  let matchName (r : Row emplSch) : Bool :=
    getValue r "Last Name" heln = some name
  let matchedTab := tfilter emplTab matchName
  match hnrows : nrows matchedTab with
  | 0 => none
  | .succ n =>
    let matchedRow := getRow matchedTab 0 (hnrows ▸ Nat.zero_lt_succ _)
    let deptId := getValue matchedRow "Department ID" heid
    deptIdToDeptNameCorrected deptTab deptId hdnm hdid
def employeeToDepartmentCorrected :=
  employeeToDeptCorrected "Rafferty" employees departments
    (by header) (by header) (by header)
