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

def addColumn {τ} (t : Table schema) (c : η) (vs : List τ) :
    Table (List.append schema [(c, τ)]) :=
  {rows := (List.map (λ (olds, new) =>
                      Row.append olds (Row.singleCell new))
                      (List.zip t.rows vs))}

def buildColumn {τ} (t : Table schema) (c : η) (f : Row schema → τ) :=
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

def getCell {schema : @Schema η} {c : η} {τ : Type u}
    : Row schema → Schema.HasCol (c, τ) schema → Cell c τ
| Row.cons cell cells, Schema.HasCol.hd => cell
| Row.cons cell cells, Schema.HasCol.tl h => getCell cells h

def setCell {schema : @Schema η} {τ : Type u} {c : η}
    : Row schema → Schema.HasCol (c, τ) schema → Cell c τ → Row schema
| Row.cons cell cells, Schema.HasCol.hd, newCell => Row.cons newCell cells
| Row.cons cell cells, Schema.HasCol.tl h, newCell =>
    Row.cons cell (setCell cells h newCell)

def retypeCell {schema : @Schema η} {τ₁ τ₂ : Type u} {c : η}
    : Row schema → (h : Schema.HasCol (c, τ₁) schema) → Cell c τ₂
      → Row (schema.retypeColumn (Schema.colImpliesName h) τ₂)
| Row.cons cell cells, Schema.HasCol.hd, newCell => Row.cons newCell cells
| Row.cons cell cells, Schema.HasCol.tl h, newCell =>
    Row.cons cell (retypeCell cells h newCell)

-- TODO: it would be nice not to have to provide a proof...
-- (Also, we now have Schema.lookup -- do we still need the implicit τ arg?
-- Careful if trying to make this change, though -- might, e.g., mess up the η
-- requirement we use in pivotWider to ensure we're getting a valid header!)
def getValue {τ}
             (r : Row schema)
             (c : η)
             (h : Schema.HasCol (c, τ) schema)
    : Option τ :=
  Cell.toOption (getCell r h)

-- ...but in the meantime, here's a tactic to make the proof trivial
macro "header" : tactic => `(repeat ((try apply Schema.HasCol.hd) <;> (apply Schema.HasCol.tl)))
macro "name" : tactic => `(repeat ((try apply Schema.HasName.hd) <;> (apply Schema.HasName.tl)))

def getColumn1 (t : Table schema)
               (n : Nat)
               (h : n < ncols t) :=
  List.map (λr => List.nth _ n h) t.rows

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

def schemaHasLookup : (schema : @Schema η) → (c : CertifiedName schema)
    → schema.HasCol (schema.lookup c)
| _, ⟨_, Schema.HasName.hd⟩ => Schema.HasCol.hd
| _ :: s', ⟨c, Schema.HasName.tl h⟩ => Schema.HasCol.tl (schemaHasLookup s' ⟨c, h⟩)

def Row.pick : {schema : @Schema η} → Row schema → (cs : List (CertifiedName schema)) → Row (Schema.pick schema cs)
| _, Row.nil, [] => Row.nil
| _, Row.nil, (⟨c, h⟩::cs) => by cases h
| _, Row.cons cell rs, [] => Row.nil
| (s::ss), Row.cons cell rs, (c::cs) =>
  have h := schemaHasLookup (s::ss) c;
  Row.cons (getCell (Row.cons cell rs)
                     h)
           (pick (Row.cons cell rs) cs)
termination_by Row.pick r cs => List.length cs

def selectColumns3 (t : Table schema) (cs : List (CertifiedName schema)) : Table (Schema.pick schema cs) :=
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
  have _ : List.length (List.filter (λ r' => decide (r = r')) rs)
           < Nat.succ (List.length rs) :=
    Nat.lt_of_le_of_lt (List.filter_length (λ r' => decide (r = r')) rs)
                       (Nat.lt.base (List.length rs))
  {rows := (
    r :: Table.rows (distinct ({rows :=
      (rs.filter (λ r' => r = r'))
    }))
  )}
termination_by distinct t => t.rows.length

def dropColumn (t : Table schema) (c : CertifiedName schema)
    : Table (schema.removeName c.property) :=
{rows := t.rows.map (Row.removeColumn c.property)}

-- FIXME: this issue again (see `removeNames`)...
def dropColumns (t : Table schema) (cs : List (CertifiedName schema))
    : Table (schema.removeNames cs) := sorry

def tfilter (t : Table schema) (f : Row schema → Bool) : Table schema :=
{rows := t.rows.filter f}

-- # Ordering
-- TODO: is it worth making an Option Ord typeclass instance?
def tsort {τ} [Ord τ]
          (t : Table schema)
          (c : ((c : η) × schema.HasCol (c, τ)))
          (asc : Bool)
    : Table schema :=
{rows :=
  t.rows.merge_sort_with (λ r₁ r₂ => 
    let ov₁ := getValue r₁ c.1 c.2
    let ov₂ := getValue r₂ c.1 c.2
    match (ov₁, ov₂) with
    | (none, none) => Ordering.eq
    | (_, none) => Ordering.gt
    | (none, _) => Ordering.lt
    | (some v₁, some v₂) => compare v₁ v₂
  )
}

-- TODO: Worth creating a `CertifiedOrdHeader` type? Also, would be nice if the
-- τ in the header could be fully implicit (can still be inferred using `_`)
-- FIXME: Not working! (Forgot that `merge_sort_with` is not actually stable!)
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
def bin [ToString η]
        {τ} [Ord τ] [HDiv τ Nat $ outParam τ] [OfNat (outParam τ) 1] [HMul (outParam τ) Nat τ] [Add (outParam τ)] [HSub τ Nat $ outParam τ] [DecidableEq τ] [ToString τ] -- [HAdd τ Nat $ outParam τ]
        (t : Table schema)
        (c : ((c : η) × schema.HasCol (c, τ)))
        (n : Nat)
    : Table [("group", String), ("count", Nat)] :=
  let col := getColumn2 t c.1 c.2
  let sorted := col |> List.filterMap id
                    |> List.merge_sort_with compare
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
    {rows := bins.map (λ (k, cnt) => Row.cons (Cell.val $ toString (k - n) ++ " ≤ " ++ toString c.1 ++ " < " ++ toString k) (Row.singleCell cnt))}

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
  {rows := t.rows.filter (λ r => r.hasEmpty)}

-- TODO: this should work, but type class resolution is failing for some reason
-- def dropna' (t : Table schema) : Table schema :=
--   {rows := (schema.certify.map (λ ⟨(c, τ), h⟩ =>
--     @completeCases _ _ _ τ t ⟨c, h⟩ _)).foldl (λ l acc => sorry)
--   }

-- TODO: move `fillna` to the "Missing Values" section -- need to make sure
-- utilities (specifically `update`) are previously declared

-- # Utilities

def Schema.HasCol.size : {schema : @Schema η} → {hdr : @Header η} → schema.HasCol hdr → Nat
| _, _, Schema.HasCol.hd => 0
| _, _, Schema.HasCol.tl h => 1 + size h


def schemaHasSubschema : {nm : η} → {τ : Type u} →
                         {schema : @Schema η} →
                         {subschema : Subschema schema} →
                         (h : subschema.toSchema.HasCol (nm, τ)) →
    schema.HasCol (nm, τ)
| _, _, s₁ :: ss₁, ⟨hdr, pf⟩ :: ss₂, Schema.HasCol.hd => pf
| nm, τ, schema₁, schema₂@(⟨hdr, pf⟩ :: ss), Schema.HasCol.tl h =>
  have term_helper : sizeOf h < sizeOf (@Schema.HasCol.tl η hdr _ _ _ h) := by
    simp
    rw [Nat.add_comm]
    apply Nat.lt.base;
  schemaHasSubschema h
termination_by schemaHasSubschema h => sizeOf h

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
    let newCells : Row schema₂.toSchema := f r;
    newCells.certifiedFoldr
      (λ {nm τ}
         (cell : Cell nm τ)
         (h : schema₂.toSchema.HasCol (nm, τ))
         (acc : Row schema₁) =>
          @setCell _ _ _ cell.type cell.name acc (schemaHasSubschema h) cell)
      r
  )}

def fillna {τ}
           (t : Table schema)
           (c : ((c : η) × schema.HasCol (c, τ)))
           (v : τ)
    : Table schema :=
  update [⟨(c.fst, τ), c.snd⟩] t
    (λ r => match getCell r c.snd with
                | Cell.emp => Row.singleCell v
                | Cell.val vOld => Row.singleCell vOld)

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
    (List.zip t.rows (project r n).rows).map (λ (r1, r2) => result r1 r2)
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
               let k := getKey₁ r₁;
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
   | nil => simp [findMatches]
   | cons x xs ih =>
     simp only [findMatches]
     split
     . simp only [Prod.snd]
       apply Nat.le_step
       exact ih
     . simp only [Prod.fst]
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
{rows :=
  grouped.map (λ klv => aggregate klv.1 klv.2)}
termination_by group xs => xs.length

-- TODO: probably a more elegant/functorial/monadic way to do this
def flattenOne {τ}
               (t : Table schema)
               (c : ((c : η) × schema.HasCol (c, List τ)))
    : Table (schema.retypeColumn (Schema.colImpliesName c.2) τ) :=
{rows :=
  t.rows.flatMap (λ (r : Row schema) =>
      match getValue r c.1 c.2 with
      | none => []
      | some xs => xs.foldr (λ x acc => retypeCell r c.2 (Cell.val x) :: acc) []
  )
}

-- def flatten (t : Table schema)
--             (cs : List ((τ : Type u) × ((c : η) × schema.HasCol (c, List τ))))

-- def flatten (t : Table schema) (cs : List (CertifiedName schema)) : Table _ := sorry

def transformColumn {τ₁ τ₂}
                    (t : Table schema)
                    (c : ((c : η) × schema.HasCol (c, τ₁)))
                    (f : Option τ₁ → Option τ₂)
    : Table (schema.retypeColumn (Schema.colImpliesName c.snd) τ₂) :=
  {rows := t.rows.map (λ (r : Row schema) =>
    retypeCell r c.snd (Cell.fromOption (f (getValue r c.fst c.snd)))
  )}

-- TODO: same issue as with removing columns...
def renameColumns (t : Table schema) (ccs : List (CertifiedName schema × η))
    : Table (schema.renameColumns ccs) := sorry

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

-- theorem test {τ} {cs : List {c : η // Schema.HasCol (c, τ) schema}} {remainingNames : List (CertifiedName schema)}
--   (hdef : remainingNames = (schema.certify.filter
--                       (λ (⟨(c, τ), h⟩ : CertifiedHeader schema) => not ((cs.map Subtype.val).elem c))
--                   ).map (λ (⟨(c, _), h⟩ : CertifiedHeader schema) => ⟨c, Schema.colImpliesName h⟩))
-- :
--   Schema.pick schema remainingNames = Schema.removeNames schema (List.map (fun c => Subtype.val c) cs) := by
--   rw [hdef];
--   induction schema;
--   . induction cs with
--     | nil => simp [Schema.pick, Schema.removeNames, List.map]
--     | cons s ss ih => apply ih
--                       simp [Schema.pick, Schema.removeNames, List.map, ih]

-- def Row.removeNamedCols (r : Row schema) (cs : List (CertifiedName schema)) :
--   Row (schema.removeNames (cs.map Subtype.val)) :=
--   let cnames : List η := cs.map Subtype.val;
--   let remainingHeaders := (schema.certify.filter
--                   (λ (⟨(c, τ), h⟩ : CertifiedHeader schema) => not (cnames.elem c))
--               );
--   let remainingNames : List (CertifiedName schema) := remainingHeaders.map (λ (⟨(c, _), h⟩ : CertifiedHeader schema) => ⟨c, Schema.colImpliesName h⟩);
--   have _ : Pickable remainingNames := _;
--   -- TODO: maybe we could have some sort of "Row.removeColumns" that
--   -- produces a row with the correct schema type by construction?
--   r.pick remainingNames

-- def Row.removeNamedCol : {schema : @Schema η} → (c : CertifiedName schema) → Row schema → Row (schema.removeName c.val)
-- | _, c, Row.nil => Row.nil
-- | (nm, τ)::ss, ⟨c, h⟩, Row.cons cell r => dite (c = nm)
--                           (λ ht => r)
--                           (λ _ => Row.cons cell (@removeNamedCol ss ⟨c, by
--                           cases h with
--                           | hd => contradiction
--                           | tl hss => exact hss
--                           ⟩ r))

-- theorem sp {x y : η} {τ₁ τ₂ : Type u}: Schema.pick [(x, τ₁), (y, τ₂)] [⟨x, Schema.HasName.hd⟩] = [(x, τ₁)] := rfl

-- theorem rn {n : η} {τ : Type u} {y z w : @Header η} : Schema.removeName [(n,τ),y,z,w] n = [y,z,w] := by
--   simp [Schema.removeName]

-- theorem simple {x : η} : (if x = x then (2 : Nat) else (1 : Nat)) = 2 := rfl
-- theorem simple₂ {x : η} : (dite (x = x) (λ_=>(2 : Nat)) (λ_=>1)) = 2 := rfl

-- #print sp

-- def Row.removeNamedCol {nm : η} : {schema : @Schema η} → (schema.HasName nm) → Row schema → Row (schema.removeName nm)
-- | _, Schema.HasName.hd, Row.cons cell r => r
-- | _, Schema.HasName.tl h, Row.cons cell r => Row.cons cell (removeNamedCol h r)

-- def test_rn : Row (Schema.removeName [("hi", Nat), ("there", String)] "hi") :=
--   Row.cons (Cell.val "hello") Row.nil

-- #check @Row.removeNamedCol

-- def Row.removeNamedCols2 : {schema : @Schema η} → (cs : List (CertifiedName schema)) → Row schema → Row (schema.removeNames (cs.map Sigma.fst))
-- | _, [], Row.nil => Row.nil
-- | _, [], Row.cons cell rs => Row.cons cell rs
-- | (s::ss), (c::cs), Row.cons cell rs =>
--   -- have h : Schema.HasCol ((Schema.lookup (s::ss) c).fst, (Schema.lookup (s::ss) c).snd) ss := _;
--   -- TODO: how do we tell Lean to just "go look it up!"??
--   @removeNamedCols2 (schema.removeName c.fst) cs (removeNamedCol c (Row.cons cell rs))
--   -- Row.cons (getCell rs (Schema.lookup (s::ss) c).fst h) (pick2 cs (Row.cons cell rs))

-- TODO: require that c1, c2 
-- def pivotLonger {τ}
--                 (t : Table schema)
--                 (cs : List ((c : η) × Schema.HasCol (c, τ) schema))
--                 (c1 : η)
--                 (c2 : η)
--     -- FIXME: need to remove the old columns from schema!!!
--     : Table (List.append (schema.removeNames (cs.map (λc => c.fst))) [(c1, η), (c2, τ)]) :=
--   selectMany t
--     (λ r _ =>
--       values (cs.map (λ (c : ((c : η) × Schema.HasCol (c, τ) schema)) =>
--         Row.cons (Cell.val c)
--           (Row.cons (getCell r c.snd) Row.nil)
--       )))
--     (λ (r₁ : Row schema) (r₂ : Row [(c1, η), (c2, τ)]) =>
--       -- TODO: what?
--       -- have cnames : List {c : η // Schema.HasName c schema} := cs.map (λ (⟨c, h⟩ : {c : η // Schema.HasCol (c, τ) schema})
--         -- => ⟨c, schema.colImpliesName h⟩);
--       let cnames : List η := cs.map Sigma.snd;
--       let remainingHeaders := (schema.certify.filter
--                       (λ (⟨(c, τ), h⟩ : CertifiedHeader schema) => not (cnames.elem c))
--                   );
--       let remainingNames : List (CertifiedName schema) := remainingHeaders.map (λ (⟨(c, _), h⟩ : CertifiedHeader schema) => ⟨c, Schema.colImpliesName h⟩);
--       -- TODO: maybe we could have some sort of "Row.removeColumns" that
--       -- produces a row with the correct schema type by construction?
--       let remainingCells := r₁.pick remainingNames;
--       Row.append remainingCells r₂)

def pivotWider [inst : Inhabited η]
               (t : Table schema)
               (c1 : (c : η) × Schema.HasCol (c, η) schema)
               (c2 : CertifiedHeader schema)
    : Table (List.append
      (schema.removeNames [⟨c1.fst, Schema.colImpliesName c1.snd⟩,
                           ⟨c2.fst.fst, Schema.colImpliesName c2.snd⟩])
      (t.rows.map (λ (r : Row schema) =>
        (Option.orDefault (getValue r c1.fst c1.snd), η)
      ))) := sorry

