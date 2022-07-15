import Table.CellRowTable
import Table.ExampleTables
import Lean

-- Table equality typeclass resolution requires a lot of instances
set_option synthInstance.maxSize 12000
set_option synthInstance.maxHeartbeats 0

-- TODO: come up with a better testing system
-- Based on
-- [https://github.com/pnwamk/lean4-assert-command/blob/main/AssertCmd.lean]

-- This shouldn't be necessary, but can't figure out implicit args with `decide`
def explicitDecide (p : Prop) (i : Decidable p) := @decide p i

syntax (name := test) "#test" term : command
@[commandElab test]
unsafe def elabTest : Lean.Elab.Command.CommandElab
| `(#test $t) => do
    let res ← Lean.Elab.Command.runTermElabM none (λ x => do
      -- Store env to restore
      let env ← Lean.getEnv

      -- Elaborate `decide` and the input term
      let t_expr ← Lean.Elab.Term.elabTerm t none
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing

      -- Lookup the decidability type class instance
      let inst_tp ← Lean.Meta.mkAppM `Decidable #[t_expr]
      let inst ← Lean.Meta.synthInstance inst_tp

      -- Construct the `decide` application and declare it
      let app ← Lean.Meta.mkAppM `explicitDecide #[t_expr, inst]
      let tp ← Lean.Meta.inferType app
      let decl := Lean.Declaration.defnDecl {
        name := `_test, levelParams := [], type := tp,
        value := app, hints := Lean.ReducibilityHints.opaque,
        safety := Lean.DefinitionSafety.unsafe
      }
      Lean.Elab.Term.ensureNoUnassignedMVars decl

      -- Add the declaration and evaluate it
      try Lean.addAndCompile decl;
          Lean.evalConst Bool `_test
      
      -- Restore the environment
      finally Lean.setEnv env
    )
    if res
    then Lean.Elab.logInfoAt t "Test passed"
    else Lean.Elab.logErrorAt t "Test failed!"
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
#test
nrows (@emptyTable String _) = 0

#eval nrows (@emptyTable String _) = 0
