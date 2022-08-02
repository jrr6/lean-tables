import Table.API
import Table.Notation

def students : Table [("name", String), ("age", Nat), ("favorite color", String)] :=
Table.mk [
  /["Bob"  , 12, "blue" ],
  /["Alice", 17, "green"],
  /["Eve"  , 13, "red"  ]
]

def studentsMissing : Table [("name", String), ("age", Nat), ("favorite color", String)] :=
Table.mk [
  /["Bob"  , EMP, "blue" ],
  /["Alice", 17 , "green"],
  /["Eve"  , 13 , EMP    ]
]

def employees : Table [("Last Name", String), ("Department ID", Nat)] :=
Table.mk [
  /["Rafferty"  , 31 ],
  /["Jones"     , 32 ],
  /["Heisenberg", 33 ],
  /["Robinson"  , 34 ],
  /["Smith"     , 34 ],
  /["Williams"  , EMP]
]

def departments : Table [("Department ID", Nat), ("Department Name", String)] :=
Table.mk [
  /[31, "Sales"      ],
  /[33, "Engineering"],
  /[34, "Clerical"   ],
  /[35, "Marketing"  ]
]

def jellyAnon : Table [("get acne", Bool), ("red", Bool), ("black", Bool),
                       ("white", Bool), ("green", Bool), ("yellow", Bool),
                       ("brown", Bool), ("orange", Bool), ("pink", Bool),
                       ("purple", Bool)] :=
Table.mk [
  /[true , false, false, false, true , false, false, true , false, false],
  /[true , false, true , false, true , true , false, false, false, false],
  /[false, false, false, false, true , false, false, false, true , false],
  /[false, false, false, false, false, true , false, false, false, false],
  /[false, false, false, false, false, true , false, false, true , false],
  /[true , false, true , false, false, false, false, true , true , false],
  /[false, false, true , false, false, false, false, false, true , false],
  /[true , false, false, false, false, false, true , true , false, false],
  /[true , false, false, false, false, false, false, true , false, false],
  /[false, true , false, false, false, true , true , false, true , false]
]

def jellyNamed : Table [("name", String), ("get acne", Bool), ("red", Bool),
                        ("black", Bool), ("white", Bool), ("green", Bool),
                        ("yellow", Bool), ("brown", Bool), ("orange", Bool),
                        ("pink", Bool), ("purple", Bool)] :=
Table.mk [
  /["Emily"   , true , false, false, false, true , false, false, true , false, false],
  /["Jacob"   , true , false, true , false, true , true , false, false, false, false],
  /["Emma"    , false, false, false, false, true , false, false, false, true , false],
  /["Aidan"   , false, false, false, false, false, true , false, false, false, false],
  /["Madison" , false, false, false, false, false, true , false, false, true , false],
  /["Ethan"   , true , false, true , false, false, false, false, true , true , false],
  /["Hannah"  , false, false, true , false, false, false, false, false, true , false],
  /["Matthew" , true , false, false, false, false, false, true , true , false, false],
  /["Hailey"  , true , false, false, false, false, false, false, true , false, false],
  /["Nicholas", false, true , false, false, false, true , true , false, true , false]
]

def gradebook : Table [("name", String), ("age", Nat), ("quiz1", Nat),
                       ("quiz2", Nat), ("midterm", Nat), ("quiz3", Nat),
                       ("quiz4", Nat), ("final", Nat)] :=
Table.mk [
  /["Bob"  , 12, 8, 9, 77, 7, 9, 87],
  /["Alice", 17, 6, 8, 88, 8, 7, 85],
  /["Eve"  , 13, 7, 9, 84, 8, 8, 77]
]

def gradebookMissing : Table [("name", String), ("age", Nat), ("quiz1", Nat),
                              ("quiz2", Nat), ("midterm", Nat), ("quiz3", Nat),
                              ("quiz4", Nat), ("final", Nat)] :=
Table.mk [
  /["Bob"  , 12, 8  , 9, 77, 7  , 9, 87],
  /["Alice", 17, 6  , 8, 88, EMP, 7, 85],
  /["Eve"  , 13, EMP, 9, 84, 8  , 8, 77]
]

def gradebookSeq : Table [("name", String), ("age", Nat), ("quizzes", List Nat),
                          ("midterm", Nat), ("final", Nat)] :=
Table.mk [
  /["Bob"  , 12, [8, 9, 7, 9], 77, 87],
  /["Alice", 17, [6, 8, 8, 7], 88, 85],
  /["Eve"  , 13, [7, 9, 8, 8], 84, 77]
]

def gradebookTable : Table [("name", ULift String),
                            ("age", ULift Nat),
                            ("quizzes", Table [("quiz#", Nat), ("grade", Nat)]),
                            ("midterm", ULift Nat),
                            ("final", ULift Nat)] :=
Table.mk [
  /[ULift.up "Bob"  , ULift.up 12, Table.mk [/[1, 8],
                                             /[2, 9],
                                             /[3, 7],
                                             /[4, 9]], ULift.up 77, ULift.up 87],
  /[ULift.up "Alice", ULift.up 12, Table.mk [/[1, 6],
                                             /[2, 8],
                                             /[3, 8],
                                             /[4, 7]], ULift.up 88, ULift.up 85],
  /[ULift.up "Eve"  , ULift.up 13, Table.mk [/[1, 7],
                                             /[2, 9],
                                             /[3, 8],
                                             /[4, 8]], ULift.up 84, ULift.up 77]
]
