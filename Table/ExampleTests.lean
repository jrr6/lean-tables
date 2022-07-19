import Table.CellRowTable
import Table.ExampleTables
import Table.Notation

-- Table equality typeclass resolution requires a lot of instances
set_option synthInstance.maxSize 12000
set_option synthInstance.maxHeartbeats 0

-- TODO: come up with a better testing system
-- Modified version of `elabEvalUnsafe` (src/lean/lean/elab/builtincommand.lean)
syntax (name := test) "#test" term : command
@[commandElab test]
unsafe def elabTest : Lean.Elab.Command.CommandElab
| `(#test%$tk $term) => do
    let n := `_eval
    let ctx ← read
    let addAndCompile (value : Lean.Expr) : Lean.Elab.TermElabM Unit := do
      -- the type really should be `Bool` at this point (b/c of `mkDecide`)
      -- (but could enforcing that explicitly lead to less-graceful failures?)
      let type ← Lean.Meta.inferType value
      let us := Lean.collectLevelParams {} value |>.params
      -- let value ← Lean.Meta.instantiateMVars value
      let decl := Lean.Declaration.defnDecl {
        name        := n
        levelParams := us.toList
        type        := type
        value       := value
        hints       := Lean.ReducibilityHints.opaque
        safety      := Lean.DefinitionSafety.unsafe
      }
      Lean.Elab.Term.ensureNoUnassignedMVars decl
      Lean.addAndCompile decl
    let elabEvalTerm : Lean.Elab.TermElabM Lean.Expr := do
      let ebool ← Lean.Elab.Term.elabTerm (← `(Bool)) none
      let e ← Lean.Elab.Term.elabTerm term none
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing

      -- Need to do this here so we can ensure the type is correct and return
      -- a meaningful error message otherwise
      let (e, _) ← Lean.Elab.Term.levelMVarToParam
                    (← Lean.Meta.instantiateMVars e)
      let e_type ← Lean.Meta.inferType e
      if (← Lean.Meta.isProp e) then
        Lean.Meta.mkDecide e
      else if (← Lean.Meta.isDefEq e_type ebool) then
        return e
      else
        throwError m!"Tests must be of type Bool or Prop, but got '{e_type}'"
    let elabEval : Lean.Elab.Command.CommandElabM Unit :=
    Lean.Elab.Command.runTermElabM (some n) (λ _ => do
      let e ← elabEvalTerm
      let env ← Lean.getEnv
      let res ← try addAndCompile e; Lean.evalConst Bool n
                finally Lean.setEnv env
      if res
      then Lean.Elab.logInfoAt tk "Test passed"
      else Lean.Elab.logErrorAt tk "Test failed")
    elabEval
| _ => Lean.Elab.throwUnsupportedSyntax

-- `addRows`
#test
addRows students [/["Colton", 19, "blue"]]
=
Table.mk [
  /["Bob"  , 12, "blue" ],
  /["Alice", 17, "green"],
  /["Eve"  , 13, "red"  ],
  /["Colton", 19, "blue"]
]

#test
addRows gradebook []
=
Table.mk [
  /["Bob"  , 12, 8, 9, 77, 7, 9, 87],
  /["Alice", 17, 6, 8, 88, 8, 7, 85],
  /["Eve"  , 13, 7, 9, 84, 8, 8, 77]
]

-- `addColumn`
def hairColor := ["brown", "red", "blonde"]
#check addColumn students "hair-color" hairColor
#check (instDecidableEqRowConsHeaderMkType : DecidableEq $ Row (List.append [("name", String), ("age", Nat), ("favorite color", String)] [("hair-color", String)]))

#test
addColumn students "hair-color" hairColor
=
Table.mk [
  /[ "Bob"   , 12  , "blue"         , "brown"    ],
  /[ "Alice" , 17  , "green"        , "red"      ],
  /[ "Eve"   , 13  , "red"          , "blonde"   ]
]

def presentation := [9, 9, 6]
#test
addColumn gradebook "presentation" presentation
=
Table.mk [
  /[ "Bob"  , 12, 8, 9, 77, 7, 9, 87, 9],
  /[ "Alice", 17, 6, 8, 88, 8, 7, 85, 9],
  /[ "Eve"  , 13, 7, 9, 84, 8, 8, 77, 6]
]

-- `buildColumn`
def isTeenagerBuilder := λ (r : Row $ schema students) =>
  match getValue r "age" (by header) with
  | some age => 12 < age && age < 20
  | _ => false
#test
buildColumn students "is-teenager" isTeenagerBuilder
=
Table.mk [
  /[ "Bob"   , 12  , "blue"         , false       ],
  /[ "Alice" , 17  , "green"        , true        ],
  /[ "Eve"   , 13  , "red"          , true        ]
]

def didWellOnFinal := λ (r : Row $ schema gradebook) =>
  match getValue r "final" (by header) with
  | some score => decide $ 85 <= score
  | _ => false
#test
buildColumn gradebook "did-well-on-final" didWellOnFinal
=
Table.mk [
  /[ "Bob"  , 12, 8, 9, 77, 7, 9, 87, true ],
  /[ "Alice", 17, 6, 8, 88, 8, 7, 85, true ],
  /[ "Eve"  , 13, 7, 9, 84, 8, 8, 77, false]
]

-- `vcat`
def increaseAge := λ (r : Row $ schema students) =>
  ((
    Row.cons
      (Cell.fromOption $ (getValue r "age" (by header)).map (λ x => x + 1))
      Row.nil
  )
  : Row [("age", Nat)])

#test
vcat students (update [⟨("age", Nat), by header⟩] students increaseAge)
=
Table.mk [
  /[ "Bob"   , 12  , "blue"         ],
  /[ "Alice" , 17  , "green"        ],
  /[ "Eve"   , 13  , "red"          ],
  /[ "Bob"   , 13  , "blue"         ],
  /[ "Alice" , 18  , "green"        ],
  /[ "Eve"   , 14  , "red"          ]
]

def curveMidtermAndFinal := λ (r : Row $ schema gradebook) =>
  let curve := λ | some n => some (n + 5)
                 | _ => none
  let midterm := getValue r "midterm" (by header)
  let final := getValue r "final" (by header)
  (Row.cons (Cell.fromOption $ curve midterm) $
     Row.cons (Cell.fromOption $ curve final) Row.nil
   : Row [("midterm", Nat), ("final", Nat)])

#test
vcat gradebook (update [⟨("midterm", Nat), by header⟩,  
                        ⟨("final", Nat), by header⟩] gradebook
                                                     curveMidtermAndFinal)
=
Table.mk [
  /[ "Bob"   , 12  , 8     , 9     , 77      , 7     , 9     , 87    ],
  /[ "Alice" , 17  , 6     , 8     , 88      , 8     , 7     , 85    ],
  /[ "Eve"   , 13  , 7     , 9     , 84      , 8     , 8     , 77    ],
  /[ "Bob"   , 12  , 8     , 9     , 82      , 7     , 9     , 92    ],
  /[ "Alice" , 17  , 6     , 8     , 93      , 8     , 7     , 90    ],
  /[ "Eve"   , 13  , 7     , 9     , 89      , 8     , 8     , 82    ]
]

-- `hcat`
-- TODO: don't have `dropColumns` yet

-- `values`
#test
values [/["Alice"], /["Bob"]]
=
(Table.mk [
  /["Alice"],
  /["Bob"]
] : Table [("name", String)])

#test
values [/["Alice", 12], /["Bob", 13]]
=
(Table.mk [
  /["Alice", 12],
  /["Bob", 13]
] : Table [("name", String), ("age", Nat)])

-- `crossJoin`
def petiteJelly :=
selectRows1 (selectColumns2 jellyAnon [⟨0, by simp⟩, ⟨1, by simp⟩, ⟨2, by simp⟩])
            [⟨0, by simp⟩, ⟨1, by simp⟩]
#test
crossJoin students petiteJelly
=
Table.mk [
  /[ "Bob"   , 12  , "blue"         , true     , false , false ],
  /[ "Bob"   , 12  , "blue"         , true     , false , true  ],
  /[ "Alice" , 17  , "green"        , true     , false , false ],
  /[ "Alice" , 17  , "green"        , true     , false , true  ],
  /[ "Eve"   , 13  , "red"          , true     , false , false ],
  /[ "Eve"   , 13  , "red"          , true     , false , true  ]
]

#test
crossJoin emptyTable petiteJelly
=
Table.mk []

-- TODO: `leftJoin`

-- `nrows`
#test nrows (@emptyTable String _) = 0

#test nrows studentsMissing = 3

-- `ncols`
#test ncols students = 3

#test ncols studentsMissing = 3

-- `header`
#test header students = ["name", "age", "favorite color"]

#test
header gradebook
=
["name", "age", "quiz1", "quiz2", "midterm", "quiz3", "quiz4", "final"]

-- `getRow`
#test
getRow students 0 (by simp)
=
/["Bob", 12, "blue"]

#test
getRow gradebook 1 (by simp)
=
/["Alice", 17, 6, 8, 88, 8, 7, 85]

-- `getValue`
#test
getValue /["name" := "Bob", "age" := 12] "name" (by header)
=
some "Bob"

#test
getValue /["name" := "Bob", "age" := 12] "age" (by header)
=
some 12

-- `getColumn1`
#test
getColumn1 students 1 (by simp)
=
[some 12, some 17, some 13]

#test
getColumn1 gradebook 0 (by simp)
=
[some "Bob", some "Alice", some "Eve"]

-- `getColumn2`
#test
getColumn2 students "age" (by header)
=
[some 12, some 17, some 13]

#test
getColumn2 gradebook "name" (by header)
=
[some "Bob", some "Alice", some "Eve"]

-- `selectRows1`
#test
selectRows1 students [⟨2, by simp⟩, ⟨0, by simp⟩, ⟨2, by simp⟩, ⟨1, by simp⟩]
=
Table.mk [
  /[ "Eve"   , 13  , "red"          ],
  /[ "Bob"   , 12  , "blue"         ],
  /[ "Eve"   , 13  , "red"          ],
  /[ "Alice" , 17  , "green"        ]
]

#test
selectRows1 gradebook [⟨2, by simp⟩, ⟨1, by simp⟩]
=
Table.mk [
  /[ "Eve"   , 13  , 7     , 9     , 84      , 8     , 8     , 77    ],
  /[ "Alice" , 17  , 6     , 8     , 88      , 8     , 7     , 85    ]
]

-- `selectRows2`
#test
selectRows2 students [true, false, true] (by simp)
=
Table.mk [
  /[ "Bob" , 12  , "blue"         ],
  /[ "Eve" , 13  , "red"          ]
]

#test
selectRows2 gradebook [false, false, true] (by simp)
=
Table.mk [/["Eve", 13, 7, 9, 84, 8, 8, 77]]

-- `selectColumns1`
#test
selectColumns1 students [true, true, false] (by simp)
=
Table.mk [
  /[ "Bob"   , 12  ],
  /[ "Alice" , 17  ],
  /[ "Eve"   , 13  ]
]

#test
selectColumns1 gradebook [true, false, false, false, true, false, false, true] (by simp)
=
Table.mk [
  /[ "Bob"   , 77      , 87    ],
  /[ "Alice" , 88      , 85    ],
  /[ "Eve"   , 84      , 77    ]
]

-- `selectColumns2`
#test
selectColumns2 students [⟨2, by simp⟩, ⟨1, by simp⟩]
=
Table.mk [
  /[ "blue"         , 12  ],
  /[ "green"        , 17  ],
  /[ "red"          , 13  ]
]

#test
selectColumns2 gradebook [⟨7, by simp⟩, ⟨0, by simp⟩, ⟨4, by simp⟩]
=
Table.mk [
  /[ 87    , "Bob"   , 77      ],
  /[ 85    , "Alice" , 88      ],
  /[ 77    , "Eve"   , 84      ]
]

-- `selectColumns3`
#test
selectColumns3 students [⟨"favorite color", by name⟩, ⟨"age", by name⟩]
=
Table.mk [
  /[ "blue"         , 12  ],
  /[ "green"        , 17  ],
  /[ "red"          , 13  ]
]

#test
selectColumns3 gradebook [⟨"final", by name⟩, ⟨"name", by name⟩, ⟨"midterm", by name⟩]
=
Table.mk [
  /[ 87    , "Bob"   , 77      ],
  /[ 85    , "Alice" , 88      ],
  /[ 77    , "Eve"   , 84      ]
]

-- `head`
#test
head students ⟨1, by simp⟩
=
Table.mk [ /["Bob", 12, "blue"]]

#test
head students ⟨-2, by simp⟩
=
Table.mk [ /["Bob", 12, "blue"]]

-- `distinct`
#test
distinct students
=
Table.mk [
  /[ "Bob"   , 12  , "blue"         ],
  /[ "Alice" , 17  , "green"        ],
  /[ "Eve"   , 13  , "red"          ]
]

#test
distinct (selectColumns3 gradebook [⟨"quiz3", by name⟩])
=
Table.mk [ /[7, 8] ]

-- `dropColumn`
#test
dropColumn students ⟨"age", by name⟩
=
Table.mk [
  /[ "Bob"   , "blue"         ],
  /[ "Alice" , "green"        ],
  /[ "Eve"   , "red"          ]
]

#test
dropColumn gradebook ⟨"final", by name⟩
=
Table.mk [
  /[ "Bob"   , 12  , 8     , 9     , 77      , 7     , 9     ],
  /[ "Alice" , 17  , 6     , 8     , 88      , 8     , 7     ],
  /[ "Eve"   , 13  , 7     , 9     , 84      , 8     , 8     ]
]

-- TODO: `dropColumns`

-- `tfilter`
def ageUnderFifteen : (Row $ schema students) → Bool := λ r =>
  match getValue r "age" (by header) with
  | some a => a < 15
  | _ => false

#test
tfilter students ageUnderFifteen
=
Table.mk [
  /[ "Bob" , 12  , "blue"         ],
  /[ "Eve" , 13  , "red"          ]
]

def nameLongerThan3Letters : (Row $ schema gradebook) → Bool := λ r =>
  match getValue r "name" (by header) with
  | some name => String.length name > 3
  | _ => false

#test
tfilter gradebook nameLongerThan3Letters
=
Table.mk [/["Alice", 17, 6, 8, 88, 8, 7, 85]]

-- `tsort`
#test
tsort students ⟨"age", by header⟩ true
=
Table.mk [
  /[ "Bob"   , 12  , "blue"         ],
  /[ "Eve"   , 13  , "red"          ],
  /[ "Alice" , 17  , "green"        ]
]

#test
tsort gradebook ⟨"final", by header⟩ false
=
Table.mk [
  /[ "Bob"   , 12  , 8     , 9     , 77      , 7     , 9     , 87    ],
  /[ "Alice" , 17  , 6     , 8     , 88      , 8     , 7     , 85    ],
  /[ "Eve"   , 13  , 7     , 9     , 84      , 8     , 8     , 77    ]
]

-- `sortByColumns`
#test
sortByColumns students [⟨("age", Nat), by header, inferInstance⟩]
=
Table.mk [
  /[ "Bob"   , 12  , "blue"         ],
  /[ "Eve"   , 13  , "red"          ],
  /[ "Alice" , 17  , "green"        ]
]

-- FIXME: merge sort isn't stable
#test
sortByColumns gradebook [⟨("quiz2", Nat), by header, inferInstance⟩,
                         ⟨("quiz1", Nat), by header, inferInstance⟩]
=
Table.mk [
  /[ "Alice" , 17  , 6     , 8     , 88      , 8     , 7     , 85    ],
  /[ "Eve"   , 13  , 7     , 9     , 84      , 8     , 8     , 77    ],
  /[ "Bob"   , 12  , 8     , 9     , 77      , 7     , 9     , 87    ]
]

-- TODO: `orderBy`

-- `count`
#test
count students ⟨"favorite color", by header⟩
=
Table.mk [
  /[ "blue"  , 1     ],
  /[ "green" , 1     ],
  /[ "red"   , 1     ]
]

#test
count gradebook ⟨"age", by header⟩
=
Table.mk [
  /[ 12    , 1     ],
  /[ 17    , 1     ],
  /[ 13    , 1     ]
]

-- `bin`
#test
bin students ⟨"age", by header⟩ 5
=
Table.mk [
  /[ "10 <= age < 15" , 2     ],
  /[ "15 <= age < 20" , 1     ]
]

#test
bin gradebook ⟨"final", by header⟩ 5
=
Table.mk [
  /[ "75 <= age < 80" , 1     ],
  /[ "80 <= age < 85" , 0     ],
  /[ "85 <= age < 90" , 2     ]
]

-- TODO: `pivotTable`

-- `groupBy`
-- TODO: handle `none` case?
def colorTemp : (Row $ schema students) → String := λ r =>
  match getValue r "favorite color" (by header) with
  | some "red" => "warm"
  | _ => "cool"

def nameLength : (Row $ schema students) → Nat := λ r =>
  match getValue r "name" (by header) with
  | some s => String.length s
  | _ => 0

def average (xs : List Nat) := List.foldl (·+·) 0 xs / xs.length

def aggregate := λ (k : String) vs =>
/["key" := k, "average" := average vs]

#test
groupBy students colorTemp nameLength aggregate
=
Table.mk [
  /[ "warm" , 3       ],
  /[ "cool" , 4       ]
]

def abstractAge := λ (r : Row $ schema gradebook) =>
  match getValue r "age" (by header) with
  | some age =>
    match (age ≤ 12 : Bool), (age ≤ 19 : Bool) with
    | true, _ => "kid"
    | _, true => "teenager"
    | _, _ => "adult"
  | _ => ""

def finalGrade := λ (r : Row $ schema gradebook) =>
  match getValue r "final" (by header) with
  | some grade => grade
  | _ => 0

#test
groupBy gradebook abstractAge finalGrade aggregate
=
Table.mk [
  /[ "kid"      , 87      ],
  /[ "teenager" , 81      ]
]

-- `completeCases`
#test
completeCases students ⟨"age", by header⟩
=
[true, true, true]

#test
completeCases studentsMissing ⟨"age", by header⟩
=
[false, true, true]

-- `dropna`
#test
dropna studentsMissing
=
Table.mk [/["Alice", 17, "green"]]

#test
dropna gradebookMissing
=
Table.mk [/["Bob", 12, 8, 9, 77, 7, 9, 87]]

-- `fillna`
#test
fillna studentsMissing ⟨"favorite color", by header⟩ "white"
=
Table.mk [
  /[ "Bob"   , EMP, "blue"],
  /[ "Alice" , 17 , "green"],
  /[ "Eve"   , 13 , "white"]
]

#test
fillna gradebookMissing ⟨"quiz1", by header⟩ 0
=
Table.mk [
  /[ "Bob"   , 12  , 8     , 9     , 77      , 7     , 9     , 87    ],
  /[ "Alice" , 17  , 6     , 8     , 88      , EMP   , 7     , 85    ],
  /[ "Eve"   , 13  , 0     , 9     , 84      , 8     , 8     , 77    ]
]

-- TODO: `pivotLonger`

-- TODO: `pivotWider`

-- TODO: `flatten`

-- FIXME: more typeclass issues
-- `transformColumn`
def addLastName := Option.map (· ++ " Smith")

#test
transformColumn students ⟨"name", by header⟩ addLastName
=
Table.mk [
  /[ "Bob Smith"   , 12  , "blue"         ],
  /[ "Alice Smith" , 17  , "green"        ],
  /[ "Eve Smith"   , 13  , "red"          ]
]

def quizScoreToPassFail := Option.map (λ n =>
  if n <= 6
  then "fail"
  else "pass")

#test
transformColumn gradebook ⟨"quiz1", by header⟩ quizScoreToPassFail
=
Table.mk [
  /[ "Bob"   , 12  , "pass" , 9     , 77      , 7     , 9     , 87    ],
  /[ "Alice" , 17  , "fail" , 8     , 88      , 8     , 7     , 85    ],
  /[ "Eve"   , 13  , "pass" , 9     , 84      , 8     , 8     , 77    ]
]

-- TODO: `renameColumns`

-- `find`
#test
find students /["age" := 13]
=
some 2

#test
find students /["age" := 14]
=
none

-- `groupByRetentive`
#test
groupByRetentive students ⟨"favorite color", by header⟩
=
Table.mk [
  /[ULift.up "blue" , Table.mk [
                        /["Bob"  , 12, "blue" ]]],
  /[ULift.up "green", Table.mk [
                        /["Alice", 17, "green"]]],
  /[ULift.up "red"  , Table.mk [
                        /["Eve"  , 13, "red"  ]]]
]

#test
groupByRetentive jellyAnon ⟨"brown", by header⟩
=
Table.mk [
  /[ULift.up false, Table.mk [
    /[ true     , false , false , false , true  , false  , false , true   , false , false  ],
    /[ true     , false , true  , false , true  , true   , false , false  , false , false  ],
    /[ false    , false , false , false , true  , false  , false , false  , true  , false  ],
    /[ false    , false , false , false , false , true   , false , false  , false , false  ],
    /[ false    , false , false , false , false , true   , false , false  , true  , false  ],
    /[ true     , false , true  , false , false , false  , false , true   , true  , false  ],
    /[ false    , false , true  , false , false , false  , false , false  , true  , false  ],
    /[ true     , false , false , false , false , false  , false , true   , false , false  ]
  ]],
  /[ULift.up true, Table.mk [
    /[ true     , false , false , false , false , false  , true  , true   , false , false  ],
    /[ false    , true  , false , false , false , true   , true  , false  , true  , false  ]
  ]]
]

-- `groupBySubtractive`
-- FIXME: why does the `header` tactic fail here?
-- Interestingly, only fails when we have the equality test -- evaluating
-- `groupBySubtractive` alone works just fine
#test
groupBySubtractive students ⟨"favorite color", Schema.HasCol.tl (Schema.HasCol.tl (Schema.HasCol.hd))⟩
=
Table.mk [
  /[ULift.up "blue" , Table.mk [/["Bob"  , 12]]],
  /[ULift.up "green", Table.mk [/["Alice", 17]]],
  /[ULift.up "green", Table.mk [/["Eve"  , 13]]]
]

#test
groupBySubtractive jellyAnon ⟨"brown",
  Schema.HasCol.tl $ Schema.HasCol.tl $ Schema.HasCol.tl $ Schema.HasCol.tl $
    Schema.HasCol.tl $ Schema.HasCol.tl $ Schema.HasCol.hd⟩
=
Table.mk [
  /[ULift.up false, Table.mk [
    /[ true     , false , false , false , true  , false  , true   , false , false  ],
    /[ true     , false , true  , false , true  , true   , false  , false , false  ],
    /[ false    , false , false , false , true  , false  , false  , true  , false  ],
    /[ false    , false , false , false , false , true   , false  , false , false  ],
    /[ false    , false , false , false , false , true   , false  , true  , false  ],
    /[ true     , false , true  , false , false , false  , true   , true  , false  ],
    /[ false    , false , true  , false , false , false  , false  , true  , false  ],
    /[ true     , false , false , false , false , false  , true   , false , false  ]
  ]],
  /[ULift.up true, Table.mk [
    /[ true     , false , false , false , false , false  , true   , false , false  ],
    /[ false    , true  , false , false , false , true   , false  , true  , false  ]
  ]]
]

-- `update`
def abstractAgeUpdate := λ (r : Row $ schema students) =>
  match getValue r "age" (by header) with
  | some age =>
    match (age ≤ 12 : Bool), (age ≤ 19 : Bool) with
    | true, _ => /["age" := "kid"]
    | _, true => /["age" := "teenager"]
    | _, _ => /["age" := "adult"]
  | _ => /["age" := EMP]

#test
update [⟨("age", String), _⟩] students abstractAgeUpdate
=
Table.mk [
  /[ "Bob"   , "kid"      , "blue"         ],
  /[ "Alice" , "teenager" , "green"        ],
  /[ "Eve"   , "teenager" , "red"          ]
]

def didWellUpdate := λ (r : Row $ schema gradebook) =>
  match getValue r "midterm" (by header), getValue r "final" (by header) with
  | some (m : Nat), some (f : Nat) => /["midterm" := (85 ≤ m : Bool), "final" := (85 ≤ f : Bool)]
  | some m, none   => /["midterm" := 85 ≤ m, "final" := EMP]
  | none, some f   => /["midterm" := EMP, "final" := 85 ≤ f]
  | none, none   => /["midterm" := EMP, "final" := EMP]

#test
update [⟨("midterm", Bool), _⟩, ⟨("final", Bool), _⟩] gradebook didWellUpdate
=
Table.mk [
  /[ "Bob"   , 12  , 8     , 9     , false   , 7     , 9     , true  ],
  /[ "Alice" , 17  , 6     , 8     , true    , 8     , 7     , true  ],
  /[ "Eve"   , 13  , 7     , 9     , false   , 8     , 8     , false ]
]

-- `select`
#test
select students (λ (r : Row $ schema students) (n : {n // n < nrows students}) =>
  let colorCell : Cell "COLOR" String := Cell.fromOption $ getValue r "favorite color" (by header)
  let ageCell : Cell "AGE" Nat := Cell.fromOption $ getValue r "age" (by header)
  (Row.cons (Cell.val n.val : Cell "ID" Nat) $
  Row.cons colorCell $
  Row.cons ageCell
  Row.nil))
=
Table.mk [
  /[ 0  , "blue"  , 12  ],
  /[ 1  , "green" , 17  ],
  /[ 2  , "red"   , 13  ]
]

#test
select gradebook (λ (r : Row $ schema gradebook) (n : {n // n < nrows gradebook}) =>
  let nameCell : Cell "full name" String :=
    Cell.fromOption $ (getValue r "name" (by header)).map (· ++ " Smith")
  let mf2 : Cell "(midterm + final) / 2" Nat :=
    match getValue r "midterm" (by header), getValue r "final" (by header) with
    | some m, some f => Cell.val ((m + f) / 2)
    | _, _ => Cell.emp
  Row.cons nameCell $ Row.cons mf2 Row.nil
)
=
Table.mk [
  /[ "Bob Smith"   , 82                    ],
  /[ "Alice Smith" , 86                    ],
  /[ "Eve Smith"   , 80                    ]
]

-- `selectMany`
-- TODO: type class resolution fails if we annotate `r : Row $ schema students`
#test
selectMany students
(λ r n =>
  if n.val % 2 == 0
  then Table.mk [r]
  else head (Table.mk [r]) ⟨0, by simp [Int.abs, nrows]⟩)
(λ r₁ r₂ => r₂)
=
Table.mk [
  /[ "Bob" , 12  , "blue"         ],
  /[ "Eve" , 13  , "red"          ]
]

def repeatRow {sch : @Schema String} : Row sch → Nat → Table sch
| r, 0 => Table.mk [r]
| r, n+1 => addRows (repeatRow r n) [r]

def decertify {sch : @Schema String}
              (f : Row sch → Nat → Table sch)
              (r : Row sch)
              (nhn : {n // n < nrows gradebook}) :=
f r nhn.1

#test
selectMany gradebook (decertify repeatRow)
(λ r₁ r₂ =>
  Row.cons (Cell.fromOption (nm := "midterm") $
              getValue r₂ "midterm" (by header))
  Row.nil)
=
Table.mk [
  /[ 77      ],
  /[ 88      ],
  /[ 88      ],
  /[ 84      ],
  /[ 84      ],
  /[ 84      ]
]

-- `groupJoin`
def getName :=
λ {schema} (h : schema.HasCol ("name", String)) (r : Row schema) =>
  getValue r "name" h

-- TODO: seems like B2T2 implicitly wants a bunch of row operations that just
-- happen to be identical to table operations in their TS implementation
def Row.addColumn {η} [DecidableEq η] {schema : @Schema η} {τ}
                  (r : Row schema) (c : η) (v : τ) :
    Row (List.append schema [(c, τ)]) :=
Row.append r (Row.singleCell v)

def averageFinal := λ (r : Row $ schema students) (t : Table $ schema gradebook) =>
  r.addColumn "final"
              (average $ List.filterMap id (getColumn2 t "final" (by header)))

#test
groupJoin students gradebook (getName (by header)) (getName (by header)) averageFinal
=
Table.mk [
  /[ "Bob"   , 12  , "blue"         , 87    ],
  /[ "Alice" , 17  , "green"        , 85    ],
  /[ "Eve"   , 13  , "red"          , 77    ]
]

def nameLength' :=
λ {schema} (h : schema.HasCol ("name", String)) (r : Row schema) =>
  (getValue r "name" h).map String.length

def tableNRows := λ (r : Row $ schema students) (t : Table $ schema gradebook) =>
  Row.addColumn r "nrows" (nrows t)

#test
groupJoin students gradebook (nameLength' (by header)) (nameLength' (by header)) tableNRows
=
Table.mk [
  /[ "Bob"   , 12  , "blue"         , 2     ],
  /[ "Alice" , 17  , "green"        , 1     ],
  /[ "Eve"   , 13  , "red"          , 2     ]
]

-- `join`
def getName' :=
λ {schema} (h : schema.HasCol ("name", String)) (r : Row schema) =>
  getValue r "name" h

-- TODO: handle empty cells!
def addGradeColumn := λ (r₁ : Row $ schema students) (r₂ : Row $ schema gradebook) =>
  Row.addColumn r₁ "grade" (getValue r₂ "final" (by header)).orDefault

#test
join students gradebook (getName' (by header)) (getName' (by header)) addGradeColumn
=
Table.mk [
  /[ "Bob"   , 12  , "blue"         , 87    ],
  /[ "Bob"   , 12  , "blue"         , 77    ],
  /[ "Alice" , 17  , "green"        , 85    ],
  /[ "Eve"   , 13  , "red"          , 87    ],
  /[ "Eve"   , 13  , "red"          , 77    ]
]
