import Table.BuiltinExtensions
import Table.CoreFunctions
import Table.CoreTypes

universe u_η
universe u

-- # Assumptions
def schema {η : Type u_η} [DecidableEq η]
           {sch : @Schema η}
           (t : Table sch) : @Schema η := sch

variable {η : Type u_η} [dec_η : DecidableEq η] {schema : @Schema η}

-- # Constructors
def emptyTable {α : Type u₁} [hα : DecidableEq α] : @Table α hα [] :=
  Table.mk []

def addRows (t : Table schema) (r : List (Row schema)) : Table schema :=
  {rows := t.rows ++ r}

def addColumn {τ} (t : Table schema) (c : η) (vs : List (Option τ)) :
    Table (List.append schema [(c, τ)]) :=
  {rows := (List.map (λ (olds, new) => olds.addColumn c new)
                     (List.zip t.rows vs))}

def buildColumn {τ} (t : Table schema) (c : η) (f : Row schema → Option τ) :=
  addColumn t c (List.map f t.rows)

def vcat (t1 : Table schema) (t2 : Table schema) : Table schema :=
  {rows := List.append t1.rows t2.rows}

def hcat {schema₁ schema₂}
               (t1 : @Table η dec_η schema₁) (t2 : @Table η dec_η schema₂) :
                  @Table η dec_η (List.append schema₁ schema₂) :=
  {rows := List.map (λ (r1, r2) => Row.append r1 r2) (List.zip t1.rows t2.rows)}

def values (rs : List (Row schema)) : Table schema := {rows := rs}

def crossJoin {schema₁ schema₂}
              (t1 : @Table η dec_η schema₁) (t2 : @Table η dec_η schema₂) :
                @Table η dec_η (List.append schema₁ schema₂) :=
  {rows := List.map (λ (c1, c2) => Row.append c1 c2)
                    (List.prod t1.rows t2.rows)}

def leftJoin : False := sorry -- TODO:

-- # Properties
-- TODO: Use Fin instead of ad-hoc quotients
def nrows (t : Table schema) : Nat := List.length t.rows

def ncols (t : Table schema) : Nat := List.length schema

def header (t : Table schema) : List η := Schema.names schema

-- # Access Subcomponents
-- TODO: might be nicer to build the row/column indexing into the Table type
-- itself?
def getRow : (t : Table schema) → (n : Nat) → (n < nrows t) → Row schema
| {rows := []}, n, h => absurd h (by
      intro nh
      simp [nrows] at nh
      apply Nat.not_lt_zero _ nh
    )
| {rows := r::rs}, 0, h => r
| {rows := r::rs}, Nat.succ n, h => getRow {rows := rs} n (Nat.lt_of_succ_lt_succ h)

-- TODO: it would be nice not to have to provide a proof...
-- (Also, we now have Schema.lookup -- do we still need the implicit τ arg?
-- Careful if trying to make this change, though -- might, e.g., mess up the η
-- requirement we use in pivotWider to ensure we're getting a valid header!)
def getValue {τ}
             (r : Row schema)
             (c : η)
             (h : Schema.HasCol (c, τ) schema)
    : Option τ :=
  Cell.toOption (r.getCell h)

def getColumn1 (t : Table schema)
               (n : Nat)
               (h : n < ncols t)
    : List (Option (List.nth schema n h).2) :=
  List.map (λr => Cell.toOption $ Row.nth r n h) t.rows

def getColumn2 {τ}
               (t : Table schema)
               (c : η)
               (h : Schema.HasCol (c, τ) schema)
    : List (Option τ) :=
  List.map (λ r => getValue r c h) t.rows

-- # Subtable
def selectRows1 (t : Table schema)
                      (ns : List {n : Nat // n < nrows t}) : Table schema :=
  {rows := List.map (λ n => getRow t n.val n.property) ns}

-- TODO: We don't strictly *need* the proof here ; if we want to be consistent
-- about enforcing preconditions through proof terms (do we‽), we should leave
-- it...
def selectRows2 (t : Table schema) (bs : List Bool) (h : List.length bs = nrows t)
    : Table schema :=
  {rows := List.sieve bs t.rows}

def selectColumns1 (t : Table schema)
                  (bs : List Bool)
                  (h : List.length bs = ncols t)
    : Table (List.sieve bs schema) :=
  {rows := t.rows.map (λ r => Row.sieve bs r)}

def selectColumns2 (t : Table schema)
                   (ns : List {n : Nat // n < ncols t})
    : Table (List.nths schema ns) :=
  {rows := t.rows.map (Row.nths ns)}

-- FIXME: need to figure out a better way to handle the type -- this breaks
-- (see `ExampleTests.lean`)
def selectColumns3 (t : Table schema) (cs : List (CertifiedHeader schema))
    : Table (Schema.fromCHeaders cs) :=
  {rows := t.rows.map (λ r => r.pick cs)}

-- TODO: quotient or proof? (should standardize this for other functions, too)
-- Once again, since drop/take doesn't require it, we don't strictly *need* the
-- proof...
def head (t : Table schema) (z : {z : Int // z.abs < nrows t}) : Table schema :=
  {rows :=
    if z.val < 0
    then let n := z.val.abs; t.rows.dropLastN n
    else let n := z.val.toNat; t.rows.take n
  }

-- TODO: same decidability issues as `find` (not dealing with for now)
def distinct [DecidableEq (Row schema)] : Table schema → Table schema 
| {rows := []} => {rows := []}
| {rows := r :: rs} =>
  -- Help the termination checker
  have _ : List.length (List.filter (λ r' => !decide (r = r')) rs)
           < Nat.succ (List.length rs) :=
    Nat.lt_of_le_of_lt (List.filter_length (λ r' => !decide (r = r')) rs)
                       (Nat.lt.base (List.length rs))
  {rows := (
    r :: Table.rows (distinct ({rows :=
      (rs.filter (λ r' => r ≠ r'))
    }))
  )}
termination_by distinct t => t.rows.length

-- FIXME: same issue as `selectColumn3`
def dropColumn (t : Table schema) (c : CertifiedName schema)
    : Table (schema.removeName c.property) :=
{rows := t.rows.map (Row.removeColumn c.property)}

def dropColumns (t : Table schema)
                (cs : ActionList Schema.removeCertifiedName schema)
    : Table (schema.removeNames cs) :=
{rows := t.rows.map (Row.removeColumns cs)}

def tfilter (t : Table schema) (f : Row schema → Bool) : Table schema :=
{rows := t.rows.filter f}

-- # Ordering
-- TODO: is it worth making an Option Ord typeclass instance?
def tsort {τ} [Ord τ]
          (t : Table schema)
          (c : ((c : η) × schema.HasCol (c, τ)))
          (asc : Bool)
    : Table schema :=
  let ascDesc
  | false, Ordering.lt => Ordering.gt
  | false, Ordering.gt => Ordering.lt
  | _    , ordering    => ordering
{rows :=
  t.rows.mergeSortWith (λ r₁ r₂ => 
    let ov₁ := getValue r₁ c.1 c.2
    let ov₂ := getValue r₂ c.1 c.2
    match (ov₁, ov₂) with
    | (none, none) => Ordering.eq
    | (_, none) => ascDesc asc Ordering.gt
    | (none, _) => ascDesc asc Ordering.lt
    | (some v₁, some v₂) => ascDesc asc $ compare v₁ v₂
  )
}

-- TODO: Worth creating a `CertifiedOrdHeader` type? Also, would be nice if the
-- τ in the header could be fully implicit (can still be inferred using `_`)
def sortByColumns (t : Table schema)
                  (cs : List ((h : Header) × Schema.HasCol h schema × Ord h.2))
    : Table schema :=
cs.foldr (λ ohdr acc => @tsort _ _ _ _ ohdr.2.2 acc ⟨ohdr.1.1, ohdr.2.1⟩ true) t

-- # Aggregate
-- TODO: this "dictionary" implementation could use some improvement
-- Should we enforce Ord instance so that we can get the speed-up of an RBT?
def count {τ} [DecidableEq τ]
          (t : Table schema)
          (c : ((c : η) × schema.HasCol (c, τ)))
    : Table [("value", τ), ("count", Nat)] :=
  let rowListTp := List (Row [("value", τ), ("count", Nat)])
  -- Helper function: increments the count in the row corresponding to v
  let rec incr : rowListTp → τ → rowListTp :=
    (λ | [], v => [Row.cons (Cell.val v) (Row.cons (Cell.val 1) Row.nil)]
       | (r@(Row.cons (Cell.val t) (Row.cons (Cell.val n) Row.nil))::rs), v => 
          if t = v
          then Row.cons (Cell.val t) (Row.cons (Cell.val (n + 1)) Row.nil) :: rs
          else r :: incr rs v
       | rs, _ => rs) -- we ensure this case never arises
  let col := getColumn2 t c.1 c.2
  {rows :=
    col.foldl (λ | acc, Option.none => acc
                 | acc, Option.some v => incr acc v) []
  }

-- FIXME: the necessary instances don't seem to exist for, e.g., Int, so
-- functionally we constrain τ = Nat, which is too restrictive
-- FIXME: this doesn't generate empty intermediate bins!
-- TODO: why does this depend on `Classical.choice`?
def bin [ToString η]
        {τ} [Ord τ] [HDiv τ Nat $ outParam τ] [OfNat (outParam τ) 1] [HMul (outParam τ) Nat τ] [Add (outParam τ)] [HSub τ Nat $ outParam τ] [DecidableEq τ] [ToString τ] -- [HAdd τ Nat $ outParam τ]
        (t : Table schema)
        (c : ((c : η) × schema.HasCol (c, τ)))
        (n : Nat)
    : Table [("group", String), ("count", Nat)] :=
  let col := getColumn2 t c.1 c.2
  let sorted := col |> List.filterMap id  -- get rid of empty cells
                    |> List.mergeSortWith compare
  -- match sorted with
  -- | [] => {rows := []}
  -- | s :: ss =>
  --   let max := List.getLast (s :: ss) (by simp)
  --   let min := s

  -- match sorted with
  -- | [] => {rows := []}
  -- | s :: ss =>
    -- -- Fold doesn't work b/c we need to be able to "skip" bins
    -- let qrty := sorted.foldr (λ x (acc : τ × List (τ × Nat)) =>
    --   match compare x acc.1 with
    --   | Ordering.lt => _
    --   | _ => _
    -- ) (s, [])

  let rec mk_bins : List τ → τ → List (τ × Nat) := λ
   | [], k => []
   | a :: as, k =>
     let k := 
      match compare a k with
      | Ordering.lt => k
      | _ => ((a / n) + 1) * n  -- TODO: may need to round for ℚ
     match mk_bins as k with
     | [] => [(k, 1)]
     | (k', cnt) :: bs =>
       if k = k'
       then (k, cnt + 1) :: bs
       else (k, 1) :: (k', cnt) :: bs
  
  match sorted with
  | [] => Table.mk []
  | s :: ss =>
    let bins := mk_bins (s :: ss) s
    {rows := bins.map (λ (k, cnt) =>
      Row.cons (Cell.val $
        toString (k - n) ++ " <= "
                         ++ toString c.1
                         ++ " < "
                         ++ toString k)
       (Row.singleValue cnt))}

  -- Generates counts of bin inhabitants for each bin with upper bound k
  -- let rec mk_bins : τ → List τ → Nat → List (τ × Nat) := λ
  --  | k, [], 0 => []
  --  | k, [], cur => [(k, cur)]
  --  | k, v :: vs, cur =>
  --   match compare v k with
  --   | Ordering.lt => mk_bins k vs (cur + 1)
  --   | _ => sorry -- (k, cur) :: mk_bins (k + n) (v :: vs) cur
  -- sorry

-- termination_by mk_bins t vs cur => vs.length

-- TODO: pivotTable

-- # Mising Values

def completeCases {τ} (t : Table schema) (c : ((c : η) × schema.HasCol (c, τ))) :=
  List.map (λ v => Option.isSome v) (getColumn2 t c.fst c.snd)

def dropna (t : Table schema) : Table schema :=
  {rows := t.rows.filter (λ r => !r.hasEmpty)}

-- TODO: this should work, but type class resolution is failing for some reason
-- def dropna' (t : Table schema) : Table schema :=
--   {rows := (schema.certify.map (λ ⟨(c, τ), h⟩ =>
--     @completeCases _ _ _ τ t ⟨c, h⟩ _)).foldl (λ l acc => sorry)
--   }

-- TODO: move `fillna` to the "Missing Values" section -- need to make sure
-- utilities (specifically `update`) are previously declared

-- # Utilities

-- FIXME: Lean can't infer the subschema because it's really trying to infer
-- "subschema.toSchema," which isn't definitional
-- Couple of options here. The best thing would be to figure out a way to let
-- Lean infer the (sub)schema directly, just like it does for normal schemata.
-- Alternatively, we can just make the subschema an explicit arg :(
def update {schema₁ : @Schema η}
           (schema₂ : Subschema schema₁)
           (t : Table schema₁)
           (f : Row schema₁ → Row schema₂.toSchema) : Table schema₁ :=
  {rows := t.rows.map (λ r =>
    let newCells : Row schema₂.toSchema := f r
    newCells.certifiedFoldr
      (λ {nm τ}
         (cell : Cell nm τ)
         (h : schema₂.toSchema.HasCol (nm, τ))
         (acc : Row schema₁) =>
          Row.setCell acc (Schema.schemaHasSubschema h) cell)
      r
  )}

def fillna {τ}
           (t : Table schema)
           (c : ((c : η) × schema.HasCol (c, τ)))
           (v : τ)
    : Table schema :=
  update [⟨(c.fst, τ), c.snd⟩] t
    (λ r => match Row.getCell r c.snd with
                | Cell.emp => Row.singleValue v
                | Cell.val vOld => Row.singleValue vOld)

def select {schema' : @Schema η}
           (t : Table schema)
           (f : Row schema → {n : Nat // n < nrows t} → Row schema')
    : Table schema' :=
  {rows := t.rows.verifiedEnum.map (λ (n, r) => f r n)}

def selectMany {ζ θ} [DecidableEq ζ] [DecidableEq θ]
               {schema₂ : @Schema ζ} {schema₃ : @Schema θ}
               (t : Table schema)
               (project : Row schema → {n : Nat // n < nrows t} → Table schema₂)
               (result : Row schema → Row schema₂ → Row schema₃)
    : Table schema₃ :=
{rows :=
  t.rows.verifiedEnum.flatMap (λ (n, r) =>
    let projection := project r n
    projection.rows.map (λ r' => result r r')
  )
}

def groupJoin {κ : Type u_η} [DecidableEq κ]
              {schema₁ schema₂ schema₃ : @Schema η}
              (t₁ : Table schema₁)
              (t₂ : Table schema₂)
              (getKey₁ : Row schema₁ → κ)
              (getKey₂ : Row schema₂ → κ)
              (aggregate : Row schema₁ → Table schema₂ → Row schema₃)
    : Table schema₃ :=
  select t₁ (λ r₁ _ =>
    let k := getKey₁ r₁;
    aggregate r₁ (tfilter t₂ (λ r₂ => (getKey₂ r₂) == k))
  )

def join {κ : Type u_η} [DecidableEq κ]
         {schema₁ schema₂ schema₃ : @Schema η}
         (t₁ : Table schema₁)
         (t₂ : Table schema₂)
         (getKey₁ : Row schema₁ → κ)
         (getKey₂ : Row schema₂ → κ)
         (combine : Row schema₁ → Row schema₂ → Row schema₃)
    : Table schema₃ :=
  selectMany t₁
             (λ r₁ _ =>
               let k := getKey₁ r₁
               tfilter t₂ (λ r₂ => getKey₂ r₂ == k))
             combine

-- TODO: figure out how to get these to work as local declarations in `groupBy`
-- (Lean can't unfold `findMatches` when it's locally declared as a `let rec`)
def findMatches {κ ν} [DecidableEq κ]
    : List (κ × ν) → κ → List ν × List (κ × ν) := λ
| [], _ => ([], [])
| (k, v) :: kvs, x =>
  let res := findMatches kvs x
  if k = x
  then (v :: res.1, res.2)
  else (res.1, (k, v) :: res.2)

theorem findMatches_snd_length {κ ν} [DecidableEq κ] :
    ∀ (xs : List (κ × ν)) (k : κ), (findMatches xs k).2.length ≤ xs.length :=
by intros xs k
   induction xs with
   | nil => exact Nat.le.refl
   | cons x xs ih =>
     simp only [findMatches]
     apply @Decidable.byCases (x.1=k) _
     . intros heq
       simp only [heq]
       rw [ite_true]
       simp only [Prod.snd]
       apply Nat.le_step
       exact ih
     . intros hneq
       simp only [hneq]
       rw [ite_false]
       simp only [Prod.fst]
       apply Nat.succ_le_succ
       exact ih

-- TODO: as with `count`, should we enforce some sort of constraint on κ to
-- allow for optimizations (e.g, RBTs)?
-- FIXME: we need to allow for schema' to have a different η, but this leads
-- to annoying typeclass resolution errors. Also, we probably need a distinct η'
-- in other functions where we can change schemata -- double-check!
def groupBy {η'} [DecidableEq η']
            {schema' : @Schema η'}
            {κ ν} [DecidableEq κ]
            (t : Table schema)
            (key : Row schema → κ)
            (project : Row schema → ν)
            (aggregate : κ → List ν → Row schema')
    : Table schema' :=
  let rec group : List (κ × ν) → List (κ × List ν) := λ
    | [] => []
    | (k, v) :: kvs =>
      let fms := findMatches kvs k
      have h_help : List.length (findMatches kvs k).snd
                      < Nat.succ (List.length kvs) :=
        by apply Nat.lt_of_succ_le
           apply Nat.succ_le_succ
           apply findMatches_snd_length
      (k, v :: fms.1) :: group fms.2
  let projected := t.rows.map (λ r => (key r, project r))
  let grouped := group projected
{rows := grouped.map (λ klv => aggregate klv.1 klv.2)}
termination_by group xs => xs.length
-- Use this because the default tactic (whatever it is) keeps needlessly
-- introducing dependence on `Quot.sound`
decreasing_by assumption

-- TODO: probably a more elegant/functorial/monadic way to do this
def flattenOne (t : Table schema)
               (c : ((c : η) × (τ : Type u) × schema.HasCol (c, List τ)))
    : Table (schema.flattenList c) :=
{rows :=
  t.rows.flatMap (λ (r : Row schema) =>
      match getValue r c.1 c.2.2 with
      | none => []
      | some xs => xs.foldr (λ x acc => r.retypeCell c.2.2 (Cell.val x) :: acc)
                            []
  )
}

def flatten {schema : @Schema η} :
  Table schema →
  (cs : ActionList Schema.flattenList schema) →
  Table (schema.flattenLists cs)
| t, ActionList.nil => t
| t, ActionList.cons c cs => flatten (flattenOne t c) cs

/- BEGIN: ongoing flatten work
-- Row of lists to list of rows
def rol2Lor : {schema : @Schema η} → {flattenschema : @Schema η} → Row schema → List (Row flattenschema)
| _, _, Row.nil => []
| _, _, Row.cons Cell.emp cs => rol2Lor cs
| (nm, _) :: ss, _, Row.cons (Cell.val []) cs => Row.nil :: rol2Lor cs
| _, _, Row.cons (Cell.val (x :: xs)) cs =>
  let r :: rs := rol2Lor (Row.cons (Cell.val xs) cs)
  (Row.cons (Cell.val x) r) :: rs

def allEmpty {schema : @Schema η} : Row schema → Bool
| Row.nil => true
| Row.cons Cell.emp cs => allEmpty cs
| Row.cons (Cell.val v) cs => false

def proc {s₁ s₂ s₃ : @Schema η} : Row s₁ → Row s₂ → Row s₃ → Row (List.append s₁ s₂)
| Row.nil, acc1, acc2 => if allEmpty acc2 then [acc1] else acc1 :: proc acc2 Row.nil Row.nil
| Row.cons Cell.emp cs, acc1, acc2 => proc cs (Row.append acc1 (Row.singleCell Cell.emp)) (Row.append acc2 (Row.singleCell Cell.emp))
| Row.cons (Cell.val []) cs, acc1, acc2 => proc cs (Cell.emp :: acc1) (Cell.emp :: acc2)
| Row.cons (Cell.val (x :: xs)) cs, acc1, acc2 => proc cs (Cell.emp :: acc1) (Cell.emp :: acc2)

def ActionList.mapToList {α} {sch : @Schema η}
                         {κ : @Schema η → Type u}
                         {f : ∀ (s : @Schema η), κ s → @Schema η}
                         (g : ∀ {s : @Schema η}, κ s → α)
    : ActionList f sch → List α
| nil => []
| cons x xs => g x :: mapToList g xs

#check @Row.retypeCell
def flatten' {n : Nat}
  (t : Table schema)
  (cs : ActionList (Schema.flattenList (n := n)) schema) :
  Table (schema.flattenLists cs) :=
selectMany t
(λ r n =>
  -- let ccols := selectColumns3 (Table.mk [r]) (cs.mapToList (λ {_} x => x))
  let doIter r :=
    if allEmpty r then [] else
    -- TODO: how do we say that the type of `r'` is `Row sch` where `sch` is the
    -- same as `schema` modulo some flattening?
    -- FIXME: α cannot depend on `s`; only `κ` can (so `r'` can't have the right
    -- type! -- `c` is a proof for that dependent type variable...)
    let (oneFlat, rest) := cs.foldl (λ {s : @Schema η} ((r' : Row s), acc) c =>
      match r'.getCell c.2.2 with
      -- TODO: see algorithm on iPad
      -- *Potential issue*: the proofs may become invalid as soon as we start
      -- retyping cells -- need to make sure the ActionList is correct (I feel
      -- like it might be, since the retyping is a flattening, but should make
      -- sure...)
      | Cell.emp => sorry
      | Cell.val [] => sorry
      | Cell.val [x] => sorry
      | Cell.val (x :: y :: xs) => sorry
    ) (r, r)
    oneFlat :: doIter rest
  {rows := doIter r}
)
(λ r₁ r₂ => _)

END: ongoing flatten work -/

def transformColumn {τ₁ τ₂}
                    (t : Table schema)
                    (c : ((c : η) × schema.HasCol (c, τ₁)))
                    (f : Option τ₁ → Option τ₂)
    : Table (schema.retypeColumn (Schema.colImpliesName c.snd) τ₂) :=
  {rows := t.rows.map (λ (r : Row schema) =>
    r.retypeCell c.snd (Cell.fromOption (f (getValue r c.fst c.snd)))
  )}

def renameColumns (t : Table schema)
                  (ccs : ActionList Schema.renameColumnCN schema)
    : Table (schema.renameColumns ccs) :=
{rows := t.rows.map (Row.renameCells ccs)}

-- TODO: do we need decidable equality of τ, or will the row lookup figure that
-- out for us?
def find {nm : η} {τ : Type u} {ss : @Schema η}
         [DecidableEq τ] [DecidableEq (Row ((nm, τ) :: ss))]
        : Table ((nm, τ) :: ss) → Row ((nm, τ) :: ss) → Option Nat
-- This ugliness is to help the termination checker realize that t.rows.length
-- is decreasing
| {rows := t_rows}, r =>
  match t_rows with
  | [] => none
  | r' :: rs =>
    if r = r'
    then some 0
    else match find {rows := rs} r with
         | some n => some (n + 1)
         | none => none
termination_by find t r => t.rows.length

-- FIXME: figure out how to properly handle `find`
-- def isSubRow : {schema : @Schema η} →
--                {subschema : Subschema schema} →
--                [DecidableEq $ Row subschema.toSchema] →
--                (sr : Row subschema.toSchema) →
--                (r : Row schema) →
--                Bool
-- | _, [], _, Row.nil, _ => true
-- | _, _ :: _, _, _, Row.nil => false
-- | schema, ⟨(nm, _), pf⟩ :: subsch, inst, Row.cons sc scs, r =>
--   if getCell r pf = sc
--   then @isSubRow schema subsch inst scs r
--   else false

-- def find' {schema : @Schema η}
--           (subschema : Subschema schema)
--           [DecidableEq $ Row subschema.toSchema] :
--           Table (schema) → Row (subschema.toSchema) → Option Nat
-- | {rows := []}, r => none
-- | {rows := r :: rs}, r' =>
--   if isSubRow r' r
--   then some 0
--   else (find' subschema {rows := rs} r').map (λ n => n + 1)
  

def groupByRetentive {τ : Type u} [DecidableEq τ]
                     (t : Table schema)
                     (c : ((c : η) × schema.HasCol (c, τ)))
    : Table [("key", ULift.{max (u+1) u_η} τ), ("groups", Table schema)] :=
groupBy t (λ (r : Row schema) => getValue r c.1 c.2)
          (λ (r : Row schema) => r)
          (λ (k : Option τ) (vs : List (Row schema)) =>
            Row.cons (Cell.fromOption (k.map ULift.up))
              (Row.cons (Cell.val (Table.mk vs)) Row.nil))

def groupBySubtractive {τ : Type u} [DecidableEq τ]
                       (t : Table schema)
                       (c : ((c : η) × schema.HasCol (c, τ)))
    : Table [("key", ULift.{max (u+1) u_η} τ),
             ("groups", Table (schema.removeName
                                (Schema.colImpliesName c.2)))] :=
groupBy t (λ r => getValue r c.1 c.2)
          (λ r => r)
          (λ k vs => Row.cons (Cell.fromOption (k.map ULift.up))
                        (Row.cons (Cell.val (Table.mk (vs.map (λ r =>
                            r.removeColumn (Schema.colImpliesName c.2)))))
                          Row.nil))

def pivotLonger {τ : Type u_η}
                (t : Table schema)
                (cs : ActionList (Schema.removeTypedName τ) schema)
                (c1 : η)
                (c2 : η)
    : Table (List.append (schema.removeTypedNames cs) [(c1, η), (c2, τ)]) :=
  selectMany t
    (λ r _ =>
      values ((cs.toList Schema.removeTNPres).map
        (λ (c : ((c : η) × schema.HasCol (c, τ))) =>
          let renamedCell := (r.getCell c.2).rename c2
          Row.cons (Cell.val c.1) (Row.cons renamedCell Row.nil)
      )))
    (λ (r₁ : Row schema) (r₂ : Row [(c1, η), (c2, τ)]) =>
      let remainingCells := r₁.removeTypedColumns cs
      Row.append remainingCells r₂
    )

-- def pivotWider [inst : Inhabited η]
--                (t : Table schema)
--                (c1 : (c : η) × Schema.HasCol (c, η) schema)
--                (c2 : CertifiedHeader schema)
--     : Table (List.append
--       (schema.removeNames [⟨c1.fst, Schema.colImpliesName c1.snd⟩,
--                            ⟨c2.fst.fst, Schema.colImpliesName c2.snd⟩])
--       (t.rows.map (λ (r : Row schema) =>
--         (Option.orDefault (getValue r c1.fst c1.snd), η)
--       ))) := sorry
