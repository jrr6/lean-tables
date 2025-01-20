import Table.API
import Table.ExampleTables
import Table.TestingNotation
import Table.Widgets

-- TODO: set these project-wide
-- Table equality typeclass resolution requires a lot of instances
set_option synthInstance.maxSize 120000
set_option synthInstance.maxHeartbeats 0

namespace Table.Examples.Programs
open Tables

universe u_η
variable {η : Type u_η} [DecidableEq η] {sch : @Schema η}

-- `dotProduct`
def dotProduct (t : Table sch) (c1 : η) (c2 : η)
               (hc1 : sch.HasCol (c1, Nat) := by header)
               (hc2 : sch.HasCol (c2, Nat) := by header) :=
  let ns := getColumn2 t c1
  let ms := getColumn2 t c2
  List.zip ns ms |>.foldl (λ | acc, (.some n, .some m) => acc + n * m
                             | acc, _                  => acc) 0

#test dotProduct gradebook "quiz1" "quiz2"
=
183

-- `sampleRows`
-- This is very inefficiently implemented to avoid an unwieldy termination proof
def sampleRows (t : Table sch) (n : Fin (nrows t + 1)) : Table sch :=
  -- Simple LCG; seeds from cs.cmu.edu/~15122/handouts/lectures/12-hashing.pdf
  let randFinSucc (n : Nat) (seed : Nat) : Fin n.succ × Nat :=
    let newSeed := seed * 1664525 + 1013904223
    (⟨newSeed % n.succ, Nat.mod_lt _ (Nat.zero_lt_succ n)⟩, newSeed)

  let allFins (n : Nat) : List (Fin n) :=
    let rec go : Fin n.succ → List (Fin n)
    | ⟨0, _⟩ => []
    | ⟨.succ k, h⟩ =>
      ⟨k, Nat.lt_of_succ_lt_succ h⟩ :: go ⟨k, Nat.lt_of_succ_lt h⟩
    go ⟨n, Nat.lt.base n⟩

  let indices : List (Fin (nrows t)) :=
    Prod.fst $ n.val.fold
      (λ k _ acc =>
        let (acc, remainingIndices, seed) := acc
        dbg_trace acc.length + remainingIndices.length
        match hni : List.length remainingIndices with
        | 0 =>
          -- Note: this case will never be reached; it could be eliminated by
          -- maintaining proofs of suitable invariants in the accumulator
          (acc, remainingIndices, seed)
        | .succ ni =>
          let (idx, newSeed) := randFinSucc ni seed
          (List.get remainingIndices (hni ▸ idx) :: acc,
           List.eraseIdx remainingIndices idx,
           newSeed)
      ) ([], allFins (nrows t), 42)
  selectRows1 t indices

#table sampleRows gradebookMissing 2

-- `pHackingHomogeneous` and `pHackingHeterogeneous`

def fisherTest (xs : List (Bool × Bool)) :=
  let tab := xs.foldl (λ acc (x, y) =>
    let xIdx := if x then 1 else 0
    let yIdx := if y then 1 else 0
    -- Vectors would be a more elegant way to handle this
    acc.set xIdx (acc[xIdx]!.set yIdx (acc[xIdx]![yIdx]! + 1))
  ) [[0, 0], [0, 0]]
  let rec fact : Nat → Nat
  | 0 => 1
  | .succ n => n.succ * fact n
  Float.ofNat (fact (tab[0]![0]! + tab[0]![1]!)
    * fact (tab[1]![0]! + tab[1]![1]!)
    * fact (tab[0]![0]! + tab[1]![0]!)
    * fact (tab[0]![1]! + tab[1]![1]!))
  /
  Float.ofNat (fact tab[0]![0]!
    * fact tab[0]![1]!
    * fact tab[1]![0]!
    * fact tab[1]![1]!
    * fact (tab.foldl (List.foldl (·+·)) 0))

def pHacking {sch : Schema} (t : Table sch)
  (hacne : sch.HasCol ("get acne", Bool) := by header)
  (hhom : sch.Homogeneous Bool := by repeat constructor) :=
  let colAcne := getColumn2 t "get acne"
  let opts := sch.certify.certifiedMap (λ hdr hmem =>
    -- A more elegant approach would be to write a lemma that shows
    -- "inheritance" of homogeneity by subschemata
    if hdr.1.1 = "get acne" then none else
    let colJB : List (Option Bool) :=
        getColumn2 t hdr.1.1 (Schema.homogenizeHC hhom hdr.2)
    let nonempties := List.zip colAcne colJB
      |>.filterMap (λ
        | (.some x, .some y) => some (x, y)
        | _                  => none)
    let p := fisherTest nonempties
    if p < 0.05 then
      some hdr.1.1
    else
      none
  )
  opts.somes

def pHackingHomogeneous := pHacking jellyAnon

#test
pHackingHomogeneous
=
["orange"]

def pHackingHeterogeneous := pHacking (dropColumns jellyNamed A["name"])

#test
pHackingHeterogeneous
=
["orange"]

-- `quizScoreFilter`

-- TODO: in principle, there's no reason this shouldn't be able to be in `Type`
-- (which would allow us to recurse on the proof directly), but Lean freezes if
-- we try (specifically, if we include the `IsQuizSchema hs` argument for the
-- recursive constructors)
inductive IsQuizSchema : @Schema String → Prop
-- inductive IsQuizSchema : @Schema String → Type 1
  | nil      : IsQuizSchema []
  | consQuiz {nm hs} :
    nm.startsWith "quiz" = true →
    IsQuizSchema hs →
    IsQuizSchema ((nm, Nat) :: hs)
  | consNonQuiz {nm τ hs} :
    nm.startsWith "quiz" = false →
    IsQuizSchema hs →
    IsQuizSchema ((nm, τ) :: hs)

theorem gradebook_schema_is_quiz_schema : IsQuizSchema (schema gradebook) := by
  repeat (first | apply IsQuizSchema.consQuiz (by with_unfolding_all decide)
                | apply IsQuizSchema.consNonQuiz (by with_unfolding_all decide)
                | apply IsQuizSchema.nil)

-- TODO: figure out why elaboration is taking so long here
set_option maxHeartbeats 1000000
theorem quiz_col_type_eq_Nat_of_IsQuizSchema {nm : String} :
  {sch : @Schema String} → {τ : Type _} →
  IsQuizSchema sch → sch.HasCol (nm, τ) → nm.startsWith "quiz" = true → τ = Nat
  | (.(nm), .(Nat)) :: hs, .(Nat), .consQuiz heq hrest, .hd =>
    λ _ => rfl
  | (_, _) :: hs, τ, .consQuiz _ hrest, .tl hc' =>
    λ heq => quiz_col_type_eq_Nat_of_IsQuizSchema hrest hc' heq
  | (.(nm), τ) :: hs, .(τ), .consNonQuiz hneq hrest, .hd =>
    λ heq => absurd heq (Bool.not_eq_true _ ▸ hneq)
  | (nm, σ) :: hs, τ, .consNonQuiz hneq hrest, .tl hc' =>
    λ heq => quiz_col_type_eq_Nat_of_IsQuizSchema hrest hc' heq

-- We take some minor liberties with our implementation to make it more amenable
-- to casting
#test
buildColumn gradebook "average-quiz" (λ r =>
  let quizColNames : List ((nm : String) × r.schema.HasCol (nm, Nat)) :=
    r.schema.certify.filterMap (λ chdr =>
      if h : chdr.1.1.startsWith "quiz"
      then
        let chdr' : Schema.HasCol (chdr.1.1, chdr.1.2) r.schema := chdr.2
        some ⟨chdr.1.1,
              Eq.rec (motive := λ x _ => Schema.HasCol (chdr.1.1, x) r.schema)
                     chdr'
                     (quiz_col_type_eq_Nat_of_IsQuizSchema
                        gradebook_schema_is_quiz_schema chdr.2 h)⟩
      else none)
  let scores : List (Option Nat) := quizColNames.map (λ c =>
    (r.getCell c.2).toOption
  )

  some $ scores.somes.foldl (·+·) 0 / scores.length
)
=
Table.mk [
/[ "Bob"   , 12  , 8     , 9     , 77      , 7     , 9     , 87    , 8],
/[ "Alice" , 17  , 6     , 8     , 88      , 8     , 7     , 85    , 7],
/[ "Eve"   , 13  , 7     , 9     , 84      , 8     , 8     , 77    , 8]
]

-- `quizScoreSelect`
-- This is basically cheating, but we're limited by the fact that things like
-- `IsQuizSchema` can't seem to live in `Type`; we've already shown above that
-- less "cheating"-like but uglier solutions are possible
def quizNatCH (i : Fin 4) :
  (schema gradebook).HasCol ("quiz" ++ toString (i.val + 1), Nat) := by
  -- Tools like `aesop` could probably make shorter work of this
  cases i with | mk _ isLt =>
  simp only [schema]
  repeat (
    rename_i val
    cases val
    . repeat constructor
  )
  contradiction

def quizColNames : List ((s : String) × (schema gradebook).HasCol (s, Nat)) :=
  List.map
    (λ (i : Fin 4) => ⟨"quiz" ++ toString (i.val + 1), quizNatCH i⟩)
    [0, 1, 2, 3]
def quizTable :=
  selectColumns3 gradebook (quizColNames.map (λ c => ⟨(c.1, Nat), c.2⟩))

def quizAndAverage :=
  buildColumn quizTable "average" (λ r =>
    let ns := quizColNames.certifiedMap (λ ch pf =>
      -- This is particularly unpleasant because Lean fails to infer the correct
      -- function argument to `memT_map_of_memT`
      r.getCell (Schema.fromCHHasFromCH ⟨(ch.1, Nat), ch.2⟩ _
        (List.memT_map_of_memT
          (λ c => (⟨(c.1, Nat), c.2⟩ : CertifiedHeader (schema gradebook)))
          pf))
      |>.toOption
    )
    some $ ns.somes.foldl (·+·) 0 / ns.length
  )

#test addColumn gradebook "average-quiz" (getColumn2 quizAndAverage "average")
=
Table.mk [
  /["Bob", 12, 8, 9, 77, 7, 9, 87, 8],
  /["Alice", 17, 6, 8, 88, 8, 7, 85, 7],
  /["Eve", 13, 7, 9, 84, 8, 8, 77, 8]
]

-- `groupByRetentive`
def tableOfColumn {τ} (c : η) (vs : List (Option τ)) : Table [(c, τ)] :=
  Table.mk $ vs.map ((Row.cons ∘ Cell.fromOption) · Row.nil)

deriving instance DecidableEq for ULift
def groupByRetentive' {schema : @Schema η} {τ : Type u} [DecidableEq τ]
  (t : Table schema) (c : η) (hc : schema.HasCol (c, τ) := by header)
    : Table [("key", ULift.{max (u+1) u_η} τ), ("groups", Table schema)] :=
  let keys : Table [("key", τ)] :=
    tableOfColumn "key" (List.unique (getColumn2 t c hc))
  let liftedKeys : Table [("key", ULift.{max (u+1) u_η} τ)] :=
    Table.mk $
    keys.rows.map λ r => r.mapHet ULift (λ _ _ => Cell.map ULift.up)
  let makeGroup (kr : Row [("key", ULift τ)]) : Option (Table schema) :=
    let k := getValue kr "key" .hd
    tfilter t (λ r => Option.map ULift.up (getValue r c hc) = k)
  buildColumn liftedKeys "groups" makeGroup

#test
groupByRetentive' students "favorite color"
=
Table.mk [
  /[ULift.up "blue", Table.mk [/["Bob", 12, "blue"]]],
  /[ULift.up "green", Table.mk [/["Alice", 17, "green"]]],
  /[ULift.up "red", Table.mk [/["Eve", 13, "red"]]]
]

#test
groupByRetentive' jellyAnon "brown"
=
Table.mk [
  /[ULift.up false, Table.mk [
    /[true, false, false, false, true, false, false, true, false, false],
    /[true, false, true, false, true, true, false, false, false, false],
    /[false, false, false, false, true, false, false, false, true, false],
    /[false, false, false, false, false, true, false, false, false, false],
    /[false, false, false, false, false, true, false, false, true, false],
    /[true, false, true, false, false, false, false, true, true, false],
    /[false, false, true, false, false, false, false, false, true, false],
    /[true, false, false, false, false, false, false, true, false, false]
  ]],
  /[ULift.up true, Table.mk [
    /[true, false, false, false, false, false, true, true, false, false],
    /[false, true, false, false, false, true, true, false, true, false]
  ]]
]

-- A fun (?) challenge would be to *prove* that this is extensionally equal to
-- `groupByRetentive`...

-- `groupBySubtractive`
def groupBySubtractive' {schema : @Schema η} {τ : Type u} [DecidableEq τ]
  (t : Table schema) (c : η) (hc : schema.HasCol (c, τ) := by header)
    : Table [("key", ULift.{max (u+1) u_η} τ),
             ("groups", Table (Schema.removeName schema
                                (Schema.colImpliesName hc)))] :=
  let keys := tableOfColumn "key" (List.unique (getColumn2 t c hc))
  let liftedKeys : Table [("key", ULift τ)] := Table.mk $
    keys.rows.map λ r => r.mapHet ULift (λ _ _ => Cell.map ULift.up)
  let makeGroup (kr : Row [("key", ULift τ)]) :=
    let k := getValue kr "key" .hd
    let g := tfilter t (λ r => Option.map ULift.up (getValue r c hc) = k)
    some $ dropColumn g c (Schema.colImpliesName hc)
  buildColumn liftedKeys "groups" makeGroup

#test
(groupBySubtractive' students "favorite color" :)
=
Table.mk [
  /[ULift.up "blue", Table.mk [/["Bob", 12]]],
  /[ULift.up "green", Table.mk [/["Alice", 17]]],
  /[ULift.up "red", Table.mk [/["Eve", 13]]]
]

#test
(groupBySubtractive' jellyAnon "brown" :)
=
Table.mk [
  /[ULift.up false, Table.mk [
      /[true, false, false, false, true, false, true, false, false],
      /[true, false, true, false, true, true, false, false, false],
      /[false, false, false, false, true, false, false, true, false],
      /[false, false, false, false, false, true, false, false, false],
      /[false, false, false, false, false, true, false, true, false],
      /[true, false, true, false, false, false, true, true, false],
      /[false, false, true, false, false, false, false, true, false],
      /[true, false, false, false, false, false, true, false, false]
  ]],
  /[ULift.up true, Table.mk [
      /[true, false, false, false, false, false, true, false, false],
      /[false, true, false, false, false, true, false, true, false]
  ]]
]
