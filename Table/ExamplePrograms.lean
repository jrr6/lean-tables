import Table.API
import Table.ExampleTables
import Table.TestingNotation
import Table.Widgets

-- TODO: set these project-wide
-- Table equality typeclass resolution requires a lot of instances
set_option synthInstance.maxSize 12000
set_option synthInstance.maxHeartbeats 0

universe u_η
variable {η : Type u_η} [DecidableEq η] {sch : @Schema η}

-- `dotProduct`
def dotProduct (t : Table sch) (c1 : η) (c2 : η)
               (hc1 : sch.HasCol (c1, Nat) := by header)
               (hc2 : sch.HasCol (c2, Nat) := by header) :=
  let ns := getColumn2 t c1 hc1
  let ms := getColumn2 t c2 hc2
  List.zip ns ms |>.foldl (λ | acc, (.some n, .some m) => acc + n * m
                             | acc, _                  => acc) 0

#test dotProduct gradebook "quiz1" "quiz2"
=
183

-- `sampleRows`
-- This is very inefficiently implemented to avoid an unwieldy termination proof
def sampleRows (t : Table sch) (n : Fin (nrows t).succ) : Table sch :=
  -- Bare-bones PRNG
  let randFinSucc (n : Nat) (seed : Nat) : Fin n.succ × Nat :=
    -- Seeds taken from
    -- https://www.cs.cmu.edu/~15122/handouts/lectures/12-hashing.pdf
    let newSeed := seed * 1664525 + 1013904223
    (⟨newSeed % n.succ, Nat.mod_lt _ (Nat.zero_lt_succ n)⟩, newSeed)

  let allFins (n : Nat) : List (Fin n) :=
    let rec go : Fin n.succ → List (Fin n)
    | ⟨0, _⟩ => []
    | ⟨.succ k, h⟩ =>
      ⟨k, Nat.lt_of_succ_lt_succ h⟩ :: go ⟨k, Nat.lt_of_succ_lt h⟩
    go ⟨n, Nat.lt.base n⟩

  let indices : List (Fin (nrows t)) :=
    Prod.fst $
      n.val.fold
      (λ k acc =>
        let (acc, indices, seed) := acc
        match hni : List.length indices with
        | 0 =>
          -- TODO: This case should not exist because it will never be reached
          (acc, indices, seed)
        | .succ ni =>
          let (idx, newSeed) := randFinSucc ni seed
          (List.get indices (hni ▸ idx) :: acc,
           List.eraseIdx indices idx,
           newSeed)
      ) ([], allFins (nrows t), 42)
  selectRows1 t indices

#table sampleRows gradebookMissing 2

-- `pHackingHomogeneous` and `pHackingHeterogeneous`
-- TODO: see if there's a more elegant way to handle the types

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

def pHacking {sch: Schema} (t : Table sch)
  (hacne : sch.HasCol ("get acne", Bool))
  (hall : ∀ x : CertifiedHeader sch,
    List.MemT x sch.certify → x.1.1 ≠ "name" → x.1.2 = Bool) :=
  let colAcne := getColumn2 t "get acne" hacne
  let opts := sch.certify.certifiedMap (λ hdr hmem =>
    if hdr.1.1 = "get acne" then none else
    if hnm : hdr.1.1 = "name" then none else
    let colJB : List (Option Bool) :=
      cast (congrArg (List ∘ Option) $ hall _ hmem hnm) $ getColumn2 t hdr.1.1 hdr.2
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

def pHackingHomogeneous :=
  pHacking jellyAnon (by header) (λ x hx _ => by
    repeat (
      cases hx
      simp only
      rename_i hx
    )
    contradiction
  )
#test
pHackingHomogeneous
=
["orange"]

def pHackingHeterogeneous :=
  pHacking jellyNamed (by header) (λ x hx hnm => by
    repeat (
      cases hx
      (simp only <;> contradiction)
      rename_i hx
    )
    contradiction
  )
#test
pHackingHeterogeneous
=
["orange"]

-- `quizScoreFilter`
#test
buildColumn gradebook "average-quiz" (λ r =>
  -- This trick doesn't work in Lean because we can't check that all of these
  -- columns have type `Nat` (maybe there's some clever way to dynamically
  -- attempt to infer an addition type-class instance at runtime, but it's not
  -- going to be as straightforward as B2T2's TypeScript approach)
  -- let quizColNames := List.filter (λ c =>
  --   String.startsWith c.1.1 "quiz"
  -- ) r.schema.certify
  let quizColNames : List ((c : String) × r.schema.HasCol (c, Nat)) :=
    [⟨"quiz1", by header⟩, ⟨"quiz2", by header⟩,
     ⟨"quiz3", by header⟩, ⟨"quiz4", by header⟩]
  let scores : List (Option Nat) := List.map (λ c =>
    (r.getCell c.2).toOption
  ) quizColNames
  some $ scores.somes.foldl (·+·) 0 / scores.length
)
=[by inst]
Table.mk [
/[ "Bob"   , 12  , 8     , 9     , 77      , 7     , 9     , 87    , 8         ],
/[ "Alice" , 17  , 6     , 8     , 88      , 8     , 7     , 85    , 7         ],
/[ "Eve"   , 13  , 7     , 9     , 84      , 8     , 8     , 77    , 8            ]
]

-- `quizScoreSelect`
-- This is basically cheating, but I don't see a better way
def quizNatCH : ∀ (i : Fin 4),
  (schema gradebook).HasCol ("quiz" ++ toString (i.val + 1), Nat)
| 0 | 1 | 2 | 3 => by header
def quizColNames : List (CertifiedHeader (schema gradebook)) :=
  List.map
    (λ (i : Fin 4) => ⟨("quiz" ++ toString (i.val + 1), Nat), quizNatCH i⟩)
    [0, 1, 2, 3]
def quizTable := selectColumns3 gradebook quizColNames

-- This is exactly the same issue as `quizScoreFilter`
#check Schema.hasNameOfFromCHeaders
def quizAndAverage :=
  buildColumn quizTable "average" (λ r =>
    let ns := quizColNames.certifiedMap (λ ch pf =>
      -- This is especially unpleasant
      have : ch.1.2 = Nat := by
        repeat (
          cases pf
          try rfl
          rename_i pf
        )
        contradiction
      this ▸ r.getCell (Schema.fromCHHasFromCH ch _ pf) |>.toOption
    )
    some $ ns.somes.foldl (·+·) 0 / ns.length
  )

#test addColumn gradebook "average-quiz"
        (getColumn2 quizAndAverage "average")
=[by inst]
Table.mk [
  /["Bob", 12, 8, 9, 77, 7, 9, 87, 8],
  /["Alice", 17, 6, 8, 88, 8, 7, 85, 7],
  /["Eve", 13, 7, 9, 84, 8, 8, 77, 8]
]
