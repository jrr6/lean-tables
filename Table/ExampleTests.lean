import Table.API
import Table.ExampleTables
import Table.Notation
import Table.Widgets
import Table.TestingNotation

-- Table equality type-class resolution requires a lot of instances
set_option synthInstance.maxSize 12000000
set_option synthInstance.maxHeartbeats 0

namespace Table.Examples.Tests
open Tables

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
def hairColor := [some "brown", some "red", some "blonde"]
#test
addColumn students "hair-color" hairColor
=
Table.mk [
  /[ "Bob"   , 12  , "blue"         , "brown"    ],
  /[ "Alice" , 17  , "green"        , "red"      ],
  /[ "Eve"   , 13  , "red"          , "blonde"   ]
]

def presentation := [some 9, some 9, some 6]
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
  match getValue r "age" with
  | some age => some (12 < age && age < 20)
  | _ => some false
#test
buildColumn students "is-teenager" isTeenagerBuilder
=
Table.mk [
  /[ "Bob"   , 12  , "blue"         , false       ],
  /[ "Alice" , 17  , "green"        , true        ],
  /[ "Eve"   , 13  , "red"          , true        ]
]

def didWellOnFinal : Row (schema gradebook) → Option Bool := λ r =>
  match getValue r "final" with
  | some score => some $ 85 <= score
  | _ => some false
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
      (Cell.fromOption $ (getValue r "age").map (λ x => x + 1))
      Row.nil
  )
  : Row [("age", Nat)])

#test
vcat students (update A["age"] students increaseAge :)
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
  let midterm := getValue r "midterm"
  let final := getValue r "final"
  (Row.cons (Cell.fromOption $ curve midterm) $
     Row.cons (Cell.fromOption $ curve final) Row.nil
   : Row [("midterm", Nat), ("final", Nat)])

#test
vcat gradebook (update A["midterm", "final"] gradebook curveMidtermAndFinal :)
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
#test
hcat students (dropColumns gradebook A["name", "age"])
=
Table.mk [
  /[ "Bob"   , 12  , "blue"         , 8     , 9     , 77      , 7     , 9     , 87    ],
  /[ "Alice" , 17  , "green"        , 6     , 8     , 88      , 8     , 7     , 85    ],
  /[ "Eve"   , 13  , "red"          , 7     , 9     , 84      , 8     , 8     , 77    ]
]

#test
hcat (dropColumns students A["name", "age"]) gradebook
=
Table.mk [
  /[ "blue"         , "Bob"   , 12  , 8     , 9     , 77      , 7     , 9     , 87    ],
  /[ "green"        , "Alice" , 17  , 6     , 8     , 88      , 8     , 7     , 85    ],
  /[ "red"          , "Eve"   , 13  , 7     , 9     , 84      , 8     , 8     , 77    ]
]

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
  selectRows1 (selectColumns2 jellyAnon A[0, 1, 2]) A[0, 1]
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

-- `leftJoin`
#test
leftJoin students gradebook A["name", "age"]
=
Table.mk [
  /[ "Bob"   , 12  , "blue"         , 8     , 9     , 77      , 7     , 9     , 87    ],
  /[ "Alice" , 17  , "green"        , 6     , 8     , 88      , 8     , 7     , 85    ],
  /[ "Eve"   , 13  , "red"          , 7     , 9     , 84      , 8     , 8     , 77    ]
]

#test
leftJoin employees departments A["Department ID"]
=
Table.mk [
  /[ "Rafferty"   , 31            , "Sales"         ],
  /[ "Jones"      , 32            , EMP             ],
  /[ "Heisenberg" , 33            , "Engineering"   ],
  /[ "Robinson"   , 34            , "Clerical"      ],
  /[ "Smith"      , 34            , "Clerical"      ],
  /[ "Williams"   , EMP           , EMP             ]
]

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
getRow students 0
=
/["Bob", 12, "blue"]

#test
getRow gradebook 1
=
/["Alice", 17, 6, 8, 88, 8, 7, 85]

-- `getValue`
#test
getValue /["name" := "Bob", "age" := 12] "name"
=
some "Bob"

#test
getValue /["name" := "Bob", "age" := 12] "age"
=
some 12

-- `getColumn1`
#test
getColumn1 students 1
=
[some 12, some 17, some 13]

#test
getColumn1 gradebook 0
=
[some "Bob", some "Alice", some "Eve"]

-- `getColumn2`
#test
getColumn2 students "age"
=
[some 12, some 17, some 13]

#test
getColumn2 gradebook "name"
=
[some "Bob", some "Alice", some "Eve"]

-- `selectRows1`
#test
selectRows1 students A[2, 0, 2, 1]
=
Table.mk [
  /[ "Eve"   , 13  , "red"          ],
  /[ "Bob"   , 12  , "blue"         ],
  /[ "Eve"   , 13  , "red"          ],
  /[ "Alice" , 17  , "green"        ]
]

#test
selectRows1 gradebook A[2, 1]
=
Table.mk [
  /[ "Eve"   , 13  , 7     , 9     , 84      , 8     , 8     , 77    ],
  /[ "Alice" , 17  , 6     , 8     , 88      , 8     , 7     , 85    ]
]

-- `selectRows2`
#test
selectRows2 students [true, false, true]
=
Table.mk [
  /[ "Bob" , 12  , "blue"         ],
  /[ "Eve" , 13  , "red"          ]
]

#test
selectRows2 gradebook [false, false, true]
=
Table.mk [/["Eve", 13, 7, 9, 84, 8, 8, 77]]

-- `selectColumns1`
#test
selectColumns1 students [true, true, false]
=
Table.mk [
  /[ "Bob"   , 12  ],
  /[ "Alice" , 17  ],
  /[ "Eve"   , 13  ]
]

#test
selectColumns1 gradebook [true, false, false, false, true, false, false, true]
=
Table.mk [
  /[ "Bob"   , 77      , 87    ],
  /[ "Alice" , 88      , 85    ],
  /[ "Eve"   , 84      , 77    ]
]

-- `selectColumns2`
#test
selectColumns2 students A[2, 1]
=
Table.mk [
  /[ "blue"         , 12  ],
  /[ "green"        , 17  ],
  /[ "red"          , 13  ]
]

#test
selectColumns2 gradebook A[7, 0, 4]
=
Table.mk [
  /[ 87    , "Bob"   , 77      ],
  /[ 85    , "Alice" , 88      ],
  /[ 77    , "Eve"   , 84      ]
]

-- `selectColumns3`
#test
selectColumns3 students A["favorite color", "age"]
=
Table.mk [
  /[ "blue"         , 12  ],
  /[ "green"        , 17  ],
  /[ "red"          , 13  ]
]

#test
selectColumns3 gradebook A["final", "name", "midterm"]
=
Table.mk [
  /[ 87    , "Bob"   , 77      ],
  /[ 85    , "Alice" , 88      ],
  /[ 77    , "Eve"   , 84      ]
]

-- `head`
#test
head students 1
=
Table.mk [ /["Bob", 12, "blue"]]

#test
head students (-2)
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
distinct (selectColumns3 gradebook A["quiz3"])
=
Table.mk [ /[7], /[8] ]

-- `dropColumn`
#test
dropColumn students "age"
=
Table.mk [
  /[ "Bob"   , "blue"         ],
  /[ "Alice" , "green"        ],
  /[ "Eve"   , "red"          ]
]

#test
dropColumn gradebook "final"
=
Table.mk [
  /[ "Bob"   , 12  , 8     , 9     , 77      , 7     , 9     ],
  /[ "Alice" , 17  , 6     , 8     , 88      , 8     , 7     ],
  /[ "Eve"   , 13  , 7     , 9     , 84      , 8     , 8     ]
]

-- `dropColumns`
#test
dropColumns students A["age"]
=
Table.mk [
  /[ "Bob"   , "blue"         ],
  /[ "Alice" , "green"        ],
  /[ "Eve"   , "red"          ]
]

#test
dropColumns gradebook A["final", "midterm"]
=
Table.mk [
  /[ "Bob"   , 12  , 8     , 9     , 7     , 9     ],
  /[ "Alice" , 17  , 6     , 8     , 8     , 7     ],
  /[ "Eve"   , 13  , 7     , 9     , 8     , 8     ]
]

-- `tfilter`
def ageUnderFifteen : (Row $ schema students) → Bool := λ r =>
  match getValue r "age" with
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
  match getValue r "name" with
  | some name => String.length name > 3
  | _ => false

#test
tfilter gradebook nameLongerThan3Letters
=
Table.mk [/["Alice", 17, 6, 8, 88, 8, 7, 85]]

-- `tsort`
#test
tsort students "age" true
=
Table.mk [
  /[ "Bob"   , 12  , "blue"         ],
  /[ "Eve"   , 13  , "red"          ],
  /[ "Alice" , 17  , "green"        ]
]

#test
tsort gradebook "final" false
=
Table.mk [
  /[ "Bob"   , 12  , 8     , 9     , 77      , 7     , 9     , 87    ],
  /[ "Alice" , 17  , 6     , 8     , 88      , 8     , 7     , 85    ],
  /[ "Eve"   , 13  , 7     , 9     , 84      , 8     , 8     , 77    ]
]

-- `sortByColumns`
#test
sortByColumns students A["age"]
=
Table.mk [
  /[ "Bob"   , 12  , "blue"         ],
  /[ "Eve"   , 13  , "red"          ],
  /[ "Alice" , 17  , "green"        ]
]

#test
sortByColumns gradebook A["quiz2", "quiz1"]
=
Table.mk [
  /[ "Alice" , 17  , 6     , 8     , 88      , 8     , 7     , 85    ],
  /[ "Eve"   , 13  , 7     , 9     , 84      , 8     , 8     , 77    ],
  /[ "Bob"   , 12  , 8     , 9     , 77      , 7     , 9     , 87    ]
]

-- `orderBy`
def nameLengthOB (r : Row $ schema students) :=
  match getValue r "name" with
  | some s => String.length s
  | _ => 0

def leOB := (λ (a : Nat) b => decide $ a ≤ b)

#test
orderBy students [⟨_, nameLengthOB, leOB⟩]
=
Table.mk [
  /[ "Bob"   , 12  , "blue"         ],
  /[ "Eve"   , 13  , "red"          ],
  /[ "Alice" , 17  , "green"        ]
]

def geOB := (λ (a : Nat) b => decide $ a ≥ b)

def nameLengthOB' (r : Row $ schema gradebook) :=
  match getValue r "name" with
  | some s => String.length s
  | _ => 0

def averageOB (xs : List $ Option Nat) :=
  List.foldl (λ acc => λ | none => acc | some x => x + acc) 0 xs / xs.length

def midtermAndFinalOB (r : Row $ schema gradebook) : List $ Option Nat :=
  [getValue r "midterm", getValue r "final"]

def compareGradeOB (g1 : List $ Option Nat) (g2 : List $ Option Nat) :=
  leOB (averageOB g1) (averageOB g2)

#test
orderBy gradebook [⟨_, nameLengthOB', geOB⟩,
                   ⟨_, midtermAndFinalOB, compareGradeOB⟩]
=
Table.mk [
  /[ "Alice" , 17  , 6     , 8     , 88      , 8     , 7     , 85    ],
  /[ "Eve"   , 13  , 7     , 9     , 84      , 8     , 8     , 77    ],
  /[ "Bob"   , 12  , 8     , 9     , 77      , 7     , 9     , 87    ]
]

-- `count`
#test
count students "favorite color"
=
Table.mk [
  /[ "blue"  , 1     ],
  /[ "green" , 1     ],
  /[ "red"   , 1     ]
]

#test
count gradebook "age"
=
Table.mk [
  /[ 12    , 1     ],
  /[ 17    , 1     ],
  /[ 13    , 1     ]
]

-- `bin`
#test
bin students "age" 5
=
Table.mk [
  /[ "10 <= age < 15" , 2     ],
  /[ "15 <= age < 20" , 1     ]
]

-- TODO: tell B2T2 that there's a typo in this test ("final," not "age")
#test
bin gradebook "final" 5
=
Table.mk [
  /[ "75 <= final < 80" , 1     ],
  /[ "80 <= final < 85" , 0     ],
  /[ "85 <= final < 90" , 2     ]
]

-- `pivotTable`
def oAverage (xs : List $ Option Nat) : Option Nat := some $
  List.foldl (λ acc => λ | none => acc | some x => x + acc) 0 xs / xs.length

-- TODO: our A[] notation is not yet robust enough to handle the second argument
#test
pivotTable students A["favorite color"]
           [⟨("age-average", _), ⟨("age", _), by header⟩, oAverage⟩]
=
Table.mk [
  /[ "blue"         , 12          ],
  /[ "green"        , 17          ],
  /[ "red"          , 13          ]
]

-- Slightly modified since we aren't using decimals
def proportion (bs : List $ Option Bool) : Option Nat := some $
  (100 * (bs.filter (· = some true)).length) / bs.length

-- KC says order doesn't matter, so okay that we disagree w/ B2T2
#test
pivotTable
  jellyNamed
  A["get acne", "brown"]
  [⟨("red-proportion", _), ⟨("red", _), by header⟩, proportion⟩,
   ⟨("pink-proportion", _), ⟨("pink", _), by header⟩, proportion⟩]
=
Table.mk [
  /[ true     , false , 0              , 25              ],
  /[ false    , false , 0              , 75              ],
  /[ true     , true  , 0              , 0               ],
  /[ false    , true  , 100            , 100             ]
]

-- `groupBy`
def colorTemp : (Row $ schema students) → String := λ r =>
  match getValue r "favorite color" with
  | some "red" => "warm"
  | _ => "cool"

def nameLength : (Row $ schema students) → Nat := λ r =>
  match getValue r "name" with
  | some s => String.length s
  | _ => 0

def average (xs : List Nat) := List.foldl (·+·) 0 xs / xs.length

def aggregate := λ (k : String) vs =>
/["key" := k, "average" := average vs]

-- Verified with KC that B2T2 doesn't care about the order here
#test
groupBy students colorTemp nameLength aggregate
=
Table.mk [
  /[ "cool" , 4       ],
  /[ "warm" , 3       ]
]

def abstractAge := λ (r : Row $ schema gradebook) =>
  match getValue r "age" with
  | some age =>
    match (age ≤ 12 : Bool), (age ≤ 19 : Bool) with
    | true, _ => "kid"
    | _, true => "teenager"
    | _, _ => "adult"
  | _ => ""

def finalGrade := λ (r : Row $ schema gradebook) =>
  match getValue r "final" with
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
completeCases students "age"
=
[true, true, true]

#test
completeCases studentsMissing "age"
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
fillna studentsMissing "favorite color" "white"
=
Table.mk [
  /[ "Bob"   , EMP, "blue"],
  /[ "Alice" , 17 , "green"],
  /[ "Eve"   , 13 , "white"]
]

#test
fillna gradebookMissing "quiz1" 0
=
Table.mk [
  /[ "Bob"   , 12  , 8     , 9     , 77      , 7     , 9     , 87    ],
  /[ "Alice" , 17  , 6     , 8     , 88      , EMP   , 7     , 85    ],
  /[ "Eve"   , 13  , 0     , 9     , 84      , 8     , 8     , 77    ]
]

-- `pivotLonger`

#test
pivotLonger gradebook A["midterm", "final"] "exam" "score"
=
Table.mk [
  /[ "Bob"   , 12  , 8     , 9     , 7     , 9     , "midterm" , 77    ],
  /[ "Bob"   , 12  , 8     , 9     , 7     , 9     , "final"   , 87    ],
  /[ "Alice" , 17  , 6     , 8     , 8     , 7     , "midterm" , 88    ],
  /[ "Alice" , 17  , 6     , 8     , 8     , 7     , "final"   , 85    ],
  /[ "Eve"   , 13  , 7     , 9     , 8     , 8     , "midterm" , 84    ],
  /[ "Eve"   , 13  , 7     , 9     , 8     , 8     , "final"   , 77    ]
]

-- TODO: this takes unreasonably long if the type is not hinted
-- The issue is not with the type-level computation, since the below is fast:
--   #reduce Schema.append ((schema gradebook).removeTypedNames
--     A["quiz1", "quiz2", "quiz3", "quiz4", "midterm", "final"])
--     [("test", String), ("score", Nat)]
-- So it's something to do with the Table DecEq instance
#test
pivotLonger gradebook A["quiz1", "quiz2", "quiz3", "quiz4", "midterm", "final"]
            "test" "score"
=(Table [("name", String), ("age", Nat), ("test", String), ("score", Nat)])
Table.mk [
  /[ "Bob"   , 12  , "quiz1"   , 8     ],
  /[ "Bob"   , 12  , "quiz2"   , 9     ],
  /[ "Bob"   , 12  , "quiz3"   , 7     ],
  /[ "Bob"   , 12  , "quiz4"   , 9     ],
  /[ "Bob"   , 12  , "midterm" , 77    ],
  /[ "Bob"   , 12  , "final"   , 87    ],
  /[ "Alice" , 17  , "quiz1"   , 6     ],
  /[ "Alice" , 17  , "quiz2"   , 8     ],
  /[ "Alice" , 17  , "quiz3"   , 8     ],
  /[ "Alice" , 17  , "quiz4"   , 7     ],
  /[ "Alice" , 17  , "midterm" , 88    ],
  /[ "Alice" , 17  , "final"   , 85    ],
  /[ "Eve"   , 13  , "quiz1"   , 7     ],
  /[ "Eve"   , 13  , "quiz2"   , 9     ],
  /[ "Eve"   , 13  , "quiz3"   , 8     ],
  /[ "Eve"   , 13  , "quiz4"   , 8     ],
  /[ "Eve"   , 13  , "midterm" , 84    ],
  /[ "Eve"   , 13  , "final"   , 77    ]
]

-- TODO: `pivotWider` has type-class issues because `getColumn2` (in its type)
-- is not reducible

#test
pivotWider students "name" "age"
=(Table [("favorite color", String), ("Bob", Nat), ("Alice", Nat), ("Eve", Nat)])
Table.mk [
  /["blue", 12, EMP, EMP],
  /["green", EMP, 17, EMP],
  /["red", EMP, EMP, 13]
]

-- TODO: test freezing without the type annotation
def longerTable :
    Table [("name", String), ("age", Nat), ("test", String), ("score", Nat)] :=
  pivotLonger gradebook
              A["quiz1", "quiz2", "quiz3", "quiz4", "midterm", "final"]
              "test"
              "score"

#test pivotWider longerTable "test" "score"
=(Table [("name", String), ("age", Nat), ("quiz1", Nat), ("quiz2", Nat), ("quiz3", Nat), ("quiz4", Nat), ("midterm", Nat), ("final", Nat)])
Table.mk [
  /[ "Bob"   , 12  , 8     , 9     , 7     , 9     , 77      , 87    ],
  /[ "Alice" , 17  , 6     , 8     , 8     , 7     , 88      , 85    ],
  /[ "Eve"   , 13  , 7     , 9     , 8     , 8     , 84      , 77    ]
]

-- `flatten`
#test
flatten gradebookSeq A["quizzes"]
=
Table.mk [
  /[ "Bob"   , 12  , 8       , 77      , 87    ],
  /[ "Bob"   , 12  , 9       , 77      , 87    ],
  /[ "Bob"   , 12  , 7       , 77      , 87    ],
  /[ "Bob"   , 12  , 9       , 77      , 87    ],
  /[ "Alice" , 17  , 6       , 88      , 85    ],
  /[ "Alice" , 17  , 8       , 88      , 85    ],
  /[ "Alice" , 17  , 8       , 88      , 85    ],
  /[ "Alice" , 17  , 7       , 88      , 85    ],
  /[ "Eve"   , 13  , 7       , 84      , 77    ],
  /[ "Eve"   , 13  , 9       , 84      , 77    ],
  /[ "Eve"   , 13  , 8       , 84      , 77    ],
  /[ "Eve"   , 13  , 8       , 84      , 77    ]
]

def t := buildColumn gradebookSeq "quiz-pass?" (λ r =>
  let isPass : Nat → Bool := λ n => n >= 8
  (getValue r "quizzes").map (List.map isPass)
)

#test
flatten t A["quiz-pass?", "quizzes"]
=
Table.mk [
  /[ "Bob"   , 12  , 8       , 77      , 87    , true       ],
  /[ "Bob"   , 12  , 9       , 77      , 87    , true       ],
  /[ "Bob"   , 12  , 7       , 77      , 87    , false      ],
  /[ "Bob"   , 12  , 9       , 77      , 87    , true       ],
  /[ "Alice" , 17  , 6       , 88      , 85    , false      ],
  /[ "Alice" , 17  , 8       , 88      , 85    , true       ],
  /[ "Alice" , 17  , 8       , 88      , 85    , true       ],
  /[ "Alice" , 17  , 7       , 88      , 85    , false      ],
  /[ "Eve"   , 13  , 7       , 84      , 77    , false      ],
  /[ "Eve"   , 13  , 9       , 84      , 77    , true       ],
  /[ "Eve"   , 13  , 8       , 84      , 77    , true       ],
  /[ "Eve"   , 13  , 8       , 84      , 77    , true       ]
]

-- `transformColumn`
def addLastName := Option.map (· ++ " Smith")

#test
transformColumn students "name" addLastName
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
transformColumn gradebook "quiz1" quizScoreToPassFail
=
Table.mk [
  /[ "Bob"   , 12  , "pass" , 9     , 77      , 7     , 9     , 87    ],
  /[ "Alice" , 17  , "fail" , 8     , 88      , 8     , 7     , 85    ],
  /[ "Eve"   , 13  , "pass" , 9     , 84      , 8     , 8     , 77    ]
]

-- `renameColumns`
#test
renameColumns students A[("favorite color", "preferred color"),
                         ("name", "first name")]
=
Table.mk [
  /[ "first name" := "Bob", "age" := 12, "preferred color" := "blue"],
  /[ "Alice"    , 17  , "green"         ],
  /[ "Eve"      , 13  , "red"           ]
]

-- This test fails using convenience notation because our action list behavior
-- doesn't match the "simultaneity" of renaming B2T2 expects; we must instead
-- manually specify the correct index in the schema with an explicit proof
-- renameColumns gradebook A[("midterm", "final"), ("final", "midterm")]
#test
renameColumns gradebook
  (.cons ⟨("midterm", "final"), by name⟩
  (.cons ⟨("final", "midterm"), by repeat apply Schema.HasName.tl; constructor⟩
   .nil))
=
Table.mk [
  /[ "name" := "Bob", "age" := 12, "quiz1" := 8, "quiz2" := 9, "final" := 77, "quiz3" := 7, "quiz4" := 9, "midterm" := 87],
  /[ "Alice" , 17  , 6     , 8     , 88    , 8     , 7     , 85      ],
  /[ "Eve"   , 13  , 7     , 9     , 84    , 8     , 8     , 77      ]
]

-- `find`
#test
find A["age"] students /["age" := 13]
=
some ⟨2, by decide⟩

#test
find A["age"] students /["age" := 14]
=
none

-- `groupByRetentive`
-- Deal with ULift decidable equality
deriving instance DecidableEq for ULift

#test
groupByRetentive students "favorite color"
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
groupByRetentive jellyAnon "brown"
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
-- TODO: why does the `header` tactic fail here?
-- Interestingly, only fails when we have the equality test -- evaluating
-- `groupBySubtractive` alone works just fine
#test
(groupBySubtractive students "favorite color" :)
=
Table.mk [
  /[ULift.up "blue" , Table.mk [/["Bob"  , 12]]],
  /[ULift.up "green", Table.mk [/["Alice", 17]]],
  /[ULift.up "red",   Table.mk [/["Eve"  , 13]]]
]

#test
(groupBySubtractive jellyAnon "brown" :)
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
  match getValue r "age" with
  | some age =>
    match (age ≤ 12 : Bool), (age ≤ 19 : Bool) with
    | true, _ => /["age" := "kid"]
    | _, true => /["age" := "teenager"]
    | _, _ => /["age" := "adult"]
  | _ => /["age" := EMP]

#eval update [⟨("age", String), by name⟩] students abstractAgeUpdate

-- TODO: why are we back to needing the `:)` notation here? Also, the reducible
-- function in the `update` type is not reducing (WF recursion may be to blame?)
#test
(update A["age"] students abstractAgeUpdate :)
=[by inst]--(Table [("name", String), ("age", String), ("favorite color", String)])
Table.mk [
  /[ "Bob"   , "kid"      , "blue"         ],
  /[ "Alice" , "teenager" , "green"        ],
  /[ "Eve"   , "teenager" , "red"          ]
]

def didWellUpdate := λ (r : Row $ schema gradebook) =>
  match getValue r "midterm", getValue r "final" with
  | some (m : Nat), some (f : Nat) => /["midterm" := (85 ≤ m : Bool), "final" := (85 ≤ f : Bool)]
  | some m, none   => /["midterm" := (85 ≤ m : Bool), "final" := EMP]
  | none, some f   => /["midterm" := EMP, "final" := (85 ≤ f : Bool)]
  | none, none   => /["midterm" := EMP, "final" := EMP]

#test
(update A["midterm", "final"] gradebook didWellUpdate :)
=[by inst]
Table.mk [
  /[ "Bob"   , 12  , 8     , 9     , false   , 7     , 9     , true  ],
  /[ "Alice" , 17  , 6     , 8     , true    , 8     , 7     , true  ],
  /[ "Eve"   , 13  , 7     , 9     , false   , 8     , 8     , false ]
]

-- `select`
#test
select students (λ (r : Row $ schema students) (n : Fin (nrows students)) =>
  let colorCell : Cell "COLOR" String := Cell.fromOption $ getValue r "favorite color"
  let ageCell : Cell "AGE" Nat := Cell.fromOption $ getValue r "age"
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
select gradebook (λ (r : Row $ schema gradebook) (n : Fin (nrows gradebook)) =>
  let nameCell : Cell "full name" String :=
    Cell.fromOption $ (getValue r "name").map (· ++ " Smith")
  let mf2 : Cell "(midterm + final) / 2" Nat :=
    match getValue r "midterm", getValue r "final" with
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
  else head (Table.mk [r]) 0)
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
              (nhn : Fin (nrows gradebook)) :=
  f r nhn.1

#test
selectMany gradebook (decertify repeatRow)
(λ r₁ r₂ =>
  Row.cons (Cell.fromOption (nm := "midterm") $ getValue r₂ "midterm")
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
def getName {schema} (r : Row schema)
  (h : schema.HasCol ("name", String) := by header) :=
  getValue r "name" h

def averageFinal (r : Row $ schema students) (t : Table $ schema gradebook) :=
  r.addColumn "final"
    (some $ average $ List.filterMap id (getColumn2 t "final"))

#test
groupJoin students gradebook getName getName averageFinal
=
Table.mk [
  /[ "Bob"   , 12  , "blue"         , 87    ],
  /[ "Alice" , 17  , "green"        , 85    ],
  /[ "Eve"   , 13  , "red"          , 77    ]
]

def nameLength' {schema} (r : Row schema)
  (h : schema.HasCol ("name", String) := by header) :=
  (getValue r "name" h).map String.length

def tableNRows := λ (r : Row $ schema students) (t : Table $ schema gradebook) =>
  Row.addColumn r "nrows" (some $ nrows t)

#test
groupJoin students gradebook nameLength' nameLength' tableNRows
=
Table.mk [
  /[ "Bob"   , 12  , "blue"         , 2     ],
  /[ "Alice" , 17  , "green"        , 1     ],
  /[ "Eve"   , 13  , "red"          , 2     ]
]

-- `join`
def getName' {schema} (r : Row schema)
  (h : schema.HasCol ("name", String) := by header) :=
  getValue r "name" h

def addGradeColumn := λ (r₁ : Row $ schema students) (r₂ : Row $ schema gradebook) =>
  Row.addColumn r₁ "grade" (getValue r₂ "final")

#test
join students gradebook getName' getName' addGradeColumn
=
Table.mk [
  /[ "Bob"   , 12  , "blue"         , 87    ],
  /[ "Alice" , 17  , "green"        , 85    ],
  /[ "Eve"   , 13  , "red"          , 77    ]
]

def nameLength'' {schema} (r : Row schema)
  (h : schema.HasCol ("name", String) := by header) :=
  (getValue r "name" h).map String.length

#test
join students gradebook nameLength'' nameLength'' addGradeColumn
=
Table.mk [
  /[ "Bob"   , 12  , "blue"         , 87    ],
  /[ "Bob"   , 12  , "blue"         , 77    ],
  /[ "Alice" , 17  , "green"        , 85    ],
  /[ "Eve"   , 13  , "red"          , 87    ],
  /[ "Eve"   , 13  , "red"          , 77    ]
]
