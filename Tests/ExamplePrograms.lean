import Table.API
import Table.Widgets
import Tests.ExampleTables
import Tests.TestingNotation

-- TODO: set these project-wide
-- Table equality typeclass resolution requires a lot of instances
set_option synthInstance.maxSize 120000
set_option synthInstance.maxHeartbeats 0

namespace Table.Examples.Programs
open Tables

universe u_η
variable {η : Type u_η} [DecidableEq η] {sch : @Schema η}

/-! `dotProduct` -/
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

/-! `sampleRows` -/

-- Simple LCG; seeds from cs.cmu.edu/~15122/handouts/lectures/12-hashing.pdf
structure LCG where
  seed : Nat

namespace LCG
def new : LCG := ⟨42⟩

def randUpTo (lcg : LCG) (max : Nat) : Fin max.succ × LCG :=
    let newSeed := lcg.seed * 1664525 + 1013904223
    (⟨newSeed % max.succ, Nat.mod_lt _ (Nat.zero_lt_succ max)⟩, ⟨newSeed⟩)
end LCG

-- Backporting `List.finRange`
theorem _root_.Fin.foldr_loop (f : Fin (n+1) → α → α) (x) (h : i+1 ≤ n+1) :
    Fin.foldr.loop (n+1) f ⟨i+1, h⟩ x =
      f 0 (Fin.foldr.loop n (fun j => f j.succ) ⟨i, Nat.le_of_succ_le_succ h⟩ x) := by
  induction i generalizing x with
  | zero => simp only [Nat.zero_add, Fin.foldr.loop, Fin.zero_eta]
  | succ i ih => simp only [Fin.foldr.loop, ih, Fin.succ_mk]

theorem _root_.Fin.foldr_succ (f : Fin (n + 1) → α → α) (x) :
    Fin.foldr (n + 1) f x = f 0 (Fin.foldr n (fun i => f i.succ) x) := Fin.foldr_loop ..

def _root_.List.ofFn {n} (f : Fin n → α) : List α := Fin.foldr n (f · :: ·) []

def _root_.List.finRange (n : Nat) : List (Fin n) := List.ofFn fun i => i

theorem _root_.List.length_ofFn {n} (f : Fin n → α) : (List.ofFn f).length = n := by
  simp only [List.ofFn]
  induction n with
  | zero => simp only [Fin.foldr, Fin.foldr.loop, List.length_nil]
  | succ n ih =>
  simp only [Fin.foldr_succ, List.length_cons, ih]

theorem _root_.List.length_finRange {n} : (List.finRange n).length = n :=
  List.length_ofFn _

-- B2T2's assumed `sample` function
-- This is very inefficiently implemented to avoid an unwieldy termination proof
def sample (xs : List α) (n : Fin (xs.length + 1)) : List α :=
  let (indices, _) := n.val.fold
    (λ _ acc =>
      let (acc, remainingIndices, lcg) := acc
      match hni : remainingIndices.length with
      -- Note: the zero case will never be reached; it could be eliminated with
      -- suitable invariants
      | 0 => (acc, remainingIndices, lcg)
      | .succ ni =>
        let (idx, lcg) := lcg.randUpTo ni
        (List.get remainingIndices (hni ▸ idx) :: acc,
          List.eraseIdx remainingIndices idx, lcg)
    ) ([], List.finRange xs.length, LCG.new)
  indices.map xs.get

def sampleRows (t : Table sch) (n : Fin (nrows t + 1)) : Table sch :=
  let indices := sample (List.finRange (nrows t)) (List.length_finRange ▸ n)
  selectRows1 t indices

#test
sampleRows gradebookMissing 2
=
Table.mk [
  /["Bob", 12, 8, 9, 77, 7, 9, 87],
  /["Alice", 17, 6  , 8, 88, EMP, 7, 85]
]

/-! `pHackingHomogeneous` and `pHackingHeterogeneous` -/

-- Lean 4.14 lacks built-in vectors, so we define them here:
inductive Vector (α : Type u) : Nat → Type u where
  | nil : Vector α 0
  | cons : α → Vector α n → Vector α (n + 1)

namespace Vector
def get : Vector α n → Fin n → α
  | .cons x _, 0 => x
  | .cons _ xs, ⟨k + 1, hk⟩ => xs.get ⟨k, Nat.le_of_succ_le_succ hk⟩

def set : Vector α n → Fin n → α → Vector α n
  | .cons _ xs, 0, y => .cons y xs
  | .cons x xs, ⟨k + 1, hk⟩, y => .cons x $ xs.set ⟨k, Nat.le_of_succ_le_succ hk⟩ y

def foldl (f : α → β → α) (init : α) : Vector β n → α
  | .nil => init
  | .cons x xs => xs.foldl f (f init x)

def ofList : (xs : List α) → Vector α xs.length
  | [] => .nil
  | x :: xs => .cons x (ofList xs)

instance : GetElem (Vector α n) Nat α (fun _ k => k < n) where
  getElem v k h := v.get ⟨k, h⟩
end Vector

def fact : Nat → Nat
  | 0 => 1
  | .succ n => n.succ * fact n

def fisherTest (xs : List (Bool × Bool)) :=
  let tab := xs.foldl (α := Vector (Vector Nat 2) 2) (λ acc (x, y) =>
    let xIdx := if x then 1 else 0
    let yIdx := if y then 1 else 0
    acc.set xIdx (acc[xIdx].set yIdx (acc[xIdx][yIdx] + 1))
  ) (.ofList [.ofList [0, 0], .ofList [0, 0]])
  Float.ofNat (fact (tab[0][0] + tab[0][1])
    * fact (tab[1][0] + tab[1][1])
    * fact (tab[0][0] + tab[1][0])
    * fact (tab[0][1] + tab[1][1]))
  /
  Float.ofNat (fact tab[0][0]
    * fact tab[0][1]
    * fact tab[1][0]
    * fact tab[1][1]
    * fact (tab.foldl (Vector.foldl (·+·)) 0))

end Examples.Programs

-- TODO: move this somewhere else (and possibly universalize it in place of existing `Subschema`? Perhaps too much to bite off now, though)
inductive Schema.IsSubschema : @Schema η → @Schema η → Type _
  | nil : IsSubschema [] []
  | cons (hdr) : IsSubschema subsch sch → IsSubschema subsch (hdr :: sch)
  | cons₂ (hdr) : IsSubschema subsch sch → IsSubschema (hdr :: subsch) (hdr :: sch)

def Schema.isSubschemaRefl : (sch : @Schema η) → Schema.IsSubschema sch sch
  | [] => .nil
  | hdr :: hs => .cons₂ hdr (isSubschemaRefl hs)

def Schema.subschemaHomogeneous :
    {sch sch' : @Schema η} → IsSubschema sch' sch → sch.Homogeneous α → sch'.Homogeneous α
  | _, _, .nil, .nil => .nil
  | _ :: _, _, .cons _ hsubsch, .cons hhom => subschemaHomogeneous hsubsch hhom
  | _ :: _, _ :: _, .cons₂ _ hsubsch, .cons hhom => .cons <| subschemaHomogeneous hsubsch hhom

def Schema.removeNameSubschema : {nm : η} → (sch : @Schema η) → (h : sch.HasName nm) → IsSubschema (Schema.removeName sch h) sch
  | _, hdr :: hs, .hd => .cons hdr (isSubschemaRefl hs)
  | _, hdr :: hs, .tl h => .cons₂ hdr (removeNameSubschema hs h)

namespace Examples.Programs
open Tables

universe u_η
variable {η : Type u_η} [DecidableEq η] {sch : @Schema η}

def pHacking {sch : Schema} (t : Table sch)
  (hacne : sch.HasCol ("get acne", Bool) := by header)
  (hhom : sch.Homogeneous Bool := by repeat constructor) : IO Unit := do
  let colAcne := getColumn2 t "get acne"
  let jellyAnon := dropColumns t (.cons ⟨"get acne", Schema.colImpliesName hacne⟩ .nil)
  for h : ⟨(nm, τ), hhdr⟩ in (schema jellyAnon).certify do
    let hhom_sub : (schema jellyAnon).Homogeneous Bool :=
      Schema.subschemaHomogeneous (Schema.removeNameSubschema _ _) hhom
    let colJB := getColumn2 jellyAnon nm (Schema.homogenizeHC hhom_sub hhdr)
    let nonempties := colAcne.zip colJB |>.filterMap (λ | (some x, some y) => some (x, y)
                                                        | _ => none)
    let p := fisherTest nonempties
    if p < 0.05 then
      IO.println <| "We found a link between " ++ nm ++ " jelly beans and acne (p < 0.05)."

def pHackingHomogeneous := pHacking jellyAnon

/-- info: We found a link between orange jelly beans and acne (p < 0.05). -/
#guard_msgs in
#eval pHackingHomogeneous

def pHackingHeterogeneous := pHacking (dropColumns jellyNamed A["name"])

/-- info: We found a link between orange jelly beans and acne (p < 0.05). -/
#guard_msgs in
#eval pHackingHeterogeneous

/-! `quizScoreFilter` -/

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

-- This is cleaner to write in term mode, but, for some reason, elaboration lags if we do so
theorem quiz_col_type_eq_Nat_of_IsQuizSchema {nm : String} :
  {sch : @Schema String} → {τ : Type _} →
  IsQuizSchema sch → sch.HasCol (nm, τ) → nm.startsWith "quiz" = true → τ = Nat := by
  intro sch τ hsch hc hnm
  induction hsch with
  | nil => nomatch hc
  | consQuiz heq hrest ih =>
    cases hc with
    | hd => rfl
    | tl h => apply ih h
  | consNonQuiz hneq hrest ih =>
    cases hc with
    | hd => nomatch hnm.symm.trans hneq
    | tl h => apply ih h

/-- Calculates the average of the non-`none` entries in `xs`. -/
def _root_.List.averageOption [Zero α] [Add α] [HDiv α Nat α] (xs : List (Option α)) :=
  xs.somes.sum / xs.length

def quizScoreFilter :=
  buildColumn gradebook "average-quiz" (λ r =>
    let quizColNames : List ((nm : String) × r.schema.HasCol (nm, Nat)) :=
      r.schema.certify.filterMap (λ ⟨(nm, _), pf⟩ =>
        if h : nm.startsWith "quiz"
        then some ⟨nm, quiz_col_type_eq_Nat_of_IsQuizSchema gradebook_schema_is_quiz_schema pf h ▸ pf⟩
        else none)
    let scores := quizColNames.map (λ c => (r.getCell c.2).toOption)
    some $ scores.averageOption)

#test
quizScoreFilter
=
Table.mk [
/[ "Bob"   , 12  , 8     , 9     , 77      , 7     , 9     , 87    , 8],
/[ "Alice" , 17  , 6     , 8     , 88      , 8     , 7     , 85    , 7],
/[ "Eve"   , 13  , 7     , 9     , 84      , 8     , 8     , 77    , 8]
]

/-! `quizScoreSelect` -/
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
    some ns.averageOption
  )

def quizScoreSelect :=
  addColumn gradebook "average-quiz" (getColumn2 quizAndAverage "average")

#test
quizScoreSelect
=
Table.mk [
  /["Bob", 12, 8, 9, 77, 7, 9, 87, 8],
  /["Alice", 17, 6, 8, 88, 8, 7, 85, 7],
  /["Eve", 13, 7, 9, 84, 8, 8, 77, 8]
]

-- `groupByRetentive`
def tableOfColumn {τ} (c : η) (vs : List (Option τ)) : Table [(c, τ)] :=
  Table.mk $ vs.map ((Row.cons ∘ Cell.fromOption) · Row.nil)

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
