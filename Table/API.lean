import Table.Cell
import Table.Schema
import Table.SchemaFunctions
import Table.Row
import Table.Table
import Table.BuiltinExtensions

universe u_η
universe u

namespace Table

-- # Assumptions
@[reducible]
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
    Table (Schema.append schema [(c, τ)]) :=
  {rows := (List.map (λ (olds, new) => olds.addColumn c new)
                     (List.zipExtendingNone t.rows vs))}

def buildColumn {τ} (t : Table schema) (c : η) (f : Row schema → Option τ) :=
  addColumn t c (List.map f t.rows)

def vcat (t1 : Table schema) (t2 : Table schema) : Table schema :=
  {rows := List.append t1.rows t2.rows}

def hcat {schema₁ schema₂ : @Schema η}
  (t1 : Table schema₁) (t2 : Table schema₂) :
  Table (Schema.append schema₁ schema₂) :=
  {rows := List.map (λ (r1, r2) => Row.append r1 r2) (List.zip t1.rows t2.rows)}

def values : List (Row schema) → Table schema := Table.mk

def crossJoin {schema₁ schema₂ : @Schema η}
  (t1 : Table schema₁) (t2 : Table schema₂) :
  Table (Schema.append schema₁ schema₂) :=
  {rows := List.map (λ (c1, c2) => Row.append c1 c2)
                    (List.prod t1.rows t2.rows)}

def leftJoin {schema₁ schema₂ : @Schema η}
             (t₁ : Table schema₁)
             (t₂ : Table schema₂)
             (cs : ActionList (Schema.removeOtherDecCH schema₁) schema₂)
: Table (Schema.append schema₁ (Schema.removeOtherDecCHs schema₁ schema₂ cs)) :=
  {rows := t₁.rows.flatMap (λ r₁ =>
    match findMatchingRows r₁ t₂ cs with
    | [] => [Row.append r₁ (Row.empty _)]
    | rs₂@(_ :: _) =>
      rs₂.map (λ r₂ => Row.append r₁ (Row.removeOtherSchemaCols cs r₂))
  )}
where
  findMatchingRows
      (r₁ : Row schema₁) (t₂ : Table schema₂)
      (cs : ActionList (Schema.removeOtherDecCH schema₁) schema₂) :=
    t₂.rows.filter λ r₂ =>
      (cs.toList Schema.removeOtherDecCHPres).all (λ c =>
          let _ : DecidableEq (Cell c.1.1 c.1.2) :=
            instDecidableEqCell (inst := c.2.1)
          decide $ r₁.getCell c.2.2.2 = r₂.getCell c.2.2.1)


-- # Properties
-- We use `Schema.length` instead of `List.length` because we want this function
-- to be reducible
@[reducible]
def nrows (t : Table schema) : Nat := Schema.length t.rows

theorem nrows_eq_List_length (t : Table schema) :
  nrows t = List.length t.rows :=
  Schema.length_eq_List_length ▸ rfl

@[reducible]
def ncols (t : Table schema) : Nat := Schema.length schema

def header (t : Table schema) : List η := Schema.names schema

-- # Access Subcomponents
def getRow (t : Table schema) (n : Nat) (h : n < nrows t := by decide)
  : Row schema :=
  match htr : t.rows, n with
  | [], n => by
    simp only [nrows] at h
    rw [htr] at h
    apply False.elim
    apply Nat.not_lt_zero
    apply h
  | r :: _, 0 => r
  | r :: rs, Nat.succ n =>
    getRow {rows := rs} n (Nat.lt_of_succ_lt_succ (by
      simp only [nrows, htr, List.length] at h
      exact h
    ))

def getValue {τ}
             (r : Row schema)
             (c : η)
             (h : Schema.HasCol (c, τ) schema := by header)
    : Option τ :=
  Cell.toOption (r.getCell h)

def getColumn1 (t : Table schema)
               (n : Nat)
               (h : n < ncols t := by decide)
    : List (Option (Schema.nth schema n h).2) :=
  List.map (λr => Cell.toOption $ Row.nth r n h) t.rows

def getColumn2 {τ}
               (t : Table schema)
               (c : η)
               (h : Schema.HasCol (c, τ) schema := by header)
    : List (Option τ) :=
  List.map (λ r => getValue r c h) t.rows

-- # Subtable
def selectRows1 (t : Table schema)
                (ns : List (Fin (nrows t))) : Table schema :=
  {rows := List.map (λ n => getRow t n.val n.isLt) ns}

def selectRows2 (t : Table schema) (bs : List Bool) : Table schema :=
  {rows := List.sieve bs t.rows}

def selectColumns1 (t : Table schema)
                   (bs : List Bool)
    : Table (Schema.sieve bs schema) :=
  {rows := t.rows.map (λ r => Row.sieve bs r)}

def selectColumns2 (t : Table schema)
                   (ns : List (Fin (ncols t)))
    : Table (Schema.nths schema ns) :=
  {rows := t.rows.map (Row.nths ns)}

def selectColumns3 (t : Table schema) (cs : List (CertifiedHeader schema))
    : Table (Schema.fromCHeaders cs) :=
  {rows := t.rows.map (λ r => r.pick cs)}

-- While we could enforce a bound on |z|, since drop/take doesn't require it,
-- we opt not to (and instead just add the constraint as a hypothesis in our
-- verification)
def head (t : Table schema) (z : Int) : Table schema :=
  {rows :=
    if z < 0
    then let n := z.natAbs; t.rows.dropLastN n
    else let n := z.toNat; t.rows.take n
  }

def distinct [inst : DecidableEq (Row schema)] : Table schema → Table schema
| {rows := rs} => {rows := rs.unique}

def dropColumn (t : Table schema) (c : η) (hc : schema.HasName c := by name)
    : Table (schema.removeName hc) :=
{rows := t.rows.map (Row.removeColumn hc)}

def dropColumns (t : Table schema)
                (cs : ActionList Schema.removeCertifiedName schema)
    : Table (schema.removeNames cs) :=
{rows := t.rows.map (Row.removeColumns cs)}

def tfilter (t : Table schema) (f : Row schema → Bool) : Table schema :=
{rows := t.rows.filter f}

-- # Ordering
def tsort {τ} [LE τ] [DecidableLE τ]
          (t : Table schema)
          (c : η)
          (asc : Bool)
          (hc : schema.HasCol (c, τ) := by header)
    : Table schema :=
{rows :=
  t.rows.mergeSort (λ r₁ r₂ =>
    let ov₁ := getValue r₁ c hc
    let ov₂ := getValue r₂ c hc
    match (ov₁, ov₂) with
    | (none, none) => true
    | (_, none) => asc
    | (none, _) => !asc
    | (some v₁, some v₂) => (v₁ ≤ v₂) = asc
  )
}

def sortByColumns (t : Table schema)
                  (cs : List ((h : Header) ×
                              Schema.HasCol h schema ×
                              (_ : LE h.2) ×
                              DecidableLE h.2))
    : Table schema :=
cs.foldr (λ ⟨hdr, hc, _, _⟩ acc => tsort acc hdr.1 true hc) t

def orderBy (t : Table schema)
            (cmps : List ((κ : Type u) × (Row schema → κ) × (κ → κ → Bool)))
    : Table schema :=
{rows :=
  t.rows.mergeSort (λ r₁ r₂ =>
    cmps.firstM (λ ⟨_, key, isLE⟩ =>
      if isLE (key r₁) (key r₂) then
        if isLE (key r₂) (key r₁) then none
        else some true
      else some false)
    |> (Option.getD · true)
  )
}

-- # Aggregate
-- Note that this could be made more efficient by enforcing an `Ord` instance
-- and using a data structure like an RBT.
-- Note that `τ` is restricted to `Type` because it must match the universe of
-- `Nat` (though we could make this universe-polymorphic by `ULift`ing `Nat` to
-- the appropriate universe).
def count {τ : Type} [DecidableEq τ]
          (t : Table schema)
          (c : η)
          (hc : schema.HasCol (c, τ) := by header)
    : Table [("value", τ), ("count", Nat)] :=
  let rec pairsToRow :
    List (Option τ × Nat) → List (Row [("value", τ), ("count", Nat)])
  | [] => []
  | (t, n) :: ps =>
    let cell :=
      match t with
      | none => Cell.emp
      | some v => Cell.val v
    Row.cons cell (Row.cons (Cell.val n) Row.nil) :: pairsToRow ps
  let col := getColumn2 t c hc
  {rows := pairsToRow $ col.counts}

-- Using mathlib, we could probably generalize this to some suitable algebraic
-- structure (or, at the very least, use `Int`s once the tooling for those has
-- been fleshed out). In the meantime, we'll use this replacement to indicate
-- which variables can be swapped out for a more general type.
section BinTypeScope
local notation "BinType" => Nat
def bin [ToString η]
        (t : Table schema)
        (c : η)
        (n : Nat)
        (hc : schema.HasCol (c, BinType) := by header)
        (hn : n > 0 := by decide)
    : Table [("group", String), ("count", Nat)] :=
  let col := getColumn2 t c hc
  let sorted := col |> List.somes  -- get rid of empty cells
                    |> List.mergeSort
  match sorted with
| [] => Table.mk []
| s :: ss =>
  let min := s
  let max := n * ((List.getLast (s :: ss) List.noConfusion) / n) + 1
  let rec kthBin : BinType → List BinType → List (BinType × Nat)
  | k, [] => []
  | k, x :: xs =>
    -- This case is impossible but needed for termination
    if h : k ≥ max then [(k, (x :: xs).length)] else
    let rec countBin : List BinType → Nat × List BinType
    | [] => (0, [])
    | y :: ys =>
      if y < k
      then let (cnt, rest) := countBin ys
           (cnt + 1, rest)
      else (0, y :: ys)
    let (cnt, rest) := countBin (x :: xs)

    have hterm : max - (k + n) < max - k :=
    by apply Nat.lt_of_sub_add
       . exact Nat.lt_of_not_le h
       . exact hn

    (k, cnt) :: kthBin (k + n) rest
  termination_by k xs => max - k

  let bins := kthBin (n * (s / n + 1)) (s :: ss)
  {rows := bins.map (λ (k, cnt) =>
    Row.cons (Cell.val s!"{k - n} <= {c} < {k}") (Row.singleValue cnt))}
end BinTypeScope

-- # Mising Values

def completeCases {τ} (t : Table schema)
                  (c : η) (hc : schema.HasCol (c, τ) := by header) :=
  List.map (λ v => Option.isSome v) (getColumn2 t c hc)

def dropna (t : Table schema) : Table schema :=
  {rows := t.rows.filter (λ r => !r.hasEmpty)}

-- This is a simpler version of `update` that doesn't require all the machinery
-- of the full version; the tradeoff is that this version doesn't allow retyping
-- of columns (but this is sufficient for `fillna`, where we use this)
def updateWithoutRetyping {schema₁ : @Schema η}
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
           (c : η)
           (v : τ)
           (hc : schema.HasCol (c, τ) := by header)
    : Table schema :=
  updateWithoutRetyping [⟨(c, τ), hc⟩] t
    (λ r => match Row.getCell r hc with
                | Cell.emp => Row.singleValue v
                | Cell.val vOld => Row.singleValue vOld)

-- # Utilities

-- The `RetypedSubschema` is essentially an `ActionList` in disguise, but since
-- the notion of a valid entry never changes between elements, we can avoid the
-- overhead of an actual `ActionList`
def update {schema₁ : @Schema η}
           (schema₂ : RetypedSubschema schema₁)
           (t : Table schema₁)
           (f : Row schema₁ → Row schema₂.toSchema)
  : Table $ Schema.retypedFromSubschema schema₂ :=
  {rows := t.rows.map (λ r =>
    let newCells : Row schema₂.toSchema := f r
    let rec updateCells :
      {schema : @Schema η} → {sch : RetypedSubschema schema} →
      Row schema → Row sch.toSchema → Row (Schema.retypedFromSubschema sch)
    | _, [], r, Row.nil => r
    | schema, ⟨(nm, τ), hsch⟩ :: subsch', r, Row.cons c rest =>
      have hterm :
        Row.length (@Row.retypedSubschemaPres η _ schema nm τ hsch _ rest) <
        Row.length (Row.cons c rest) :=
        Row.length_retypedSubschemaPres rest ▸ Nat.lt_succ_self _
      let newRow := updateCells (schema := schema.retypeColumn hsch τ)
        (r.retypeCellByName hsch c)
        (Row.retypedSubschemaPres rest)
      -- TODO: this casting is suboptimal
      -- Perhaps we could avoid it if we wrote a symmetric "fueled" function
      -- to the type-level one?
      (Schema.retypedFromSubschema.eq_def (η := η) _ ▸
      Schema.length_map _ _ ▸
      newRow)
    termination_by _ _ _ rs => rs.length

    updateCells r newCells
  )}

def select {η'} [DecidableEq η'] {schema' : @Schema η'}
           (t : Table schema)
           (f : Row schema → Fin (nrows t) → Row schema')
    : Table schema' :=
  {rows := t.rows.verifiedEnum.map (λ (n, r) =>
            f r (nrows_eq_List_length t ▸ n))}

def selectMany {ζ θ} [DecidableEq ζ] [DecidableEq θ]
               {schema₂ : @Schema ζ} {schema₃ : @Schema θ}
               (t : Table schema)
               (project : Row schema → Fin (nrows t) → Table schema₂)
               (result : Row schema → Row schema₂ → Row schema₃)
    : Table schema₃ :=
{rows :=
  t.rows.verifiedEnum.flatMap (λ (n, r) =>
    let projection := project r (nrows_eq_List_length t ▸ n)
    projection.rows.map (λ r' => result r r')
  )
}

def groupJoin {ζ θ} [DecidableEq ζ] [DecidableEq θ]
              {κ : Type u_η} [DecidableEq κ]
              {schema₁ : @Schema η}
              {schema₂ : @Schema ζ}
              {schema₃ : @Schema θ}
              (t₁ : Table schema₁)
              (t₂ : Table schema₂)
              (getKey₁ : Row schema₁ → κ)
              (getKey₂ : Row schema₂ → κ)
              (aggregate : Row schema₁ → Table schema₂ → Row schema₃)
    : Table schema₃ :=
  select t₁ (λ r₁ _ =>
    let k := getKey₁ r₁
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

-- As with `count`, we could enforce some constraint on κ to allow for
-- optimizations (e.g, RBTs)?
-- TODO: we need to allow for schema' to have a different η, but this leads
-- to annoying typeclass resolution errors. This is likely also an issue for
-- other functions where full generality requires allowing disparate schema-name
-- types.
-- Note that we can't stipulate that η' : Type u_η b/c there's no guarantee it
-- belongs to the same universe level as η (and, indeed, enforcing this breaks
-- things)
def groupBy {η'} [DecidableEq η']
            {schema' : @Schema η'}
            {κ ν} [DecidableEq κ]
            (t : Table schema)
            (key : Row schema → κ)
            (project : Row schema → ν)
            (aggregate : κ → List ν → Row schema')
    : Table schema' :=
  let projected := t.rows.map (λ r => (key r, project r))
  let grouped := projected.groupPairsByKey
{rows := grouped.map (λ klv => aggregate klv.1 klv.2)}

def groupByCertified {η'} [DecidableEq η']
            {schema' : @Schema η'}
            {κ ν} [DecidableEq κ]
            (t : Table schema)
            (key : (r : Row schema) → (List.MemT r t.rows) → κ)
            (project : (r : Row schema) → (List.MemT r t.rows) → ν)
            (aggregate : κ → List ν → Row schema')
    : Table schema' :=
  let projected := t.rows.certifiedMap (λ r pf => (key r pf, project r pf))
  let grouped := projected.groupPairsByKey
{rows := grouped.map (λ klv => aggregate klv.1 klv.2)}

/--
`flattenOne` takes a list of row copies and clean-row templates (i.e., a list of
row list-row tuples) `rss` and applies a flatten for the specified column `c`.
(That is, each element of `rss` is a copy of the same row with 0 or more prior
flattenings applied.) It outputs `rss'`, wherein each element `rs ∈ rss` is
mapped to `rs'`, the result of applying a flattening at `c` to each element of
`rs.1`, i.e., each element of `rs.1` receives a single element from the
flattening of the `List τ` at `c`, with extra elements inserted if `c` flattens
to more rows than yet exist; empty cells are inserted into elements of `rs.1`
for which there is no element of the flattening of `c`. `rs'.2` is the result of
retyping `rs.2` such that `c` is flattened, with the cell at `c` set to empty.
(These "clean-row" arguments are used to construct extra rows in future
iterations when a flattened sequence has more elements than yet exist. Note
that, since each single-flattening clears the selected column in rows beyond
those into which it flattens, we only need clean-row arguments to be "clean" in
rows that have already been flattened.)
-/
def flattenOne {schema : @Schema η} :
  -- list of flattened copies of each row × "clean" copy of row for all
  -- columns up to this point
  List (List (Row schema) × Row schema) →
  -- column to flatten at this iteration
  (c : (c : η) × (τ : Type u_1) × Schema.HasCol (c, List τ) schema) →
  -- flag indicating whether this is the first col to be flattened (if not, we
  -- will truncate to the length of the min-length flattened sequence)
  Bool →
  List (List (Row $ schema.flattenList c) × (Row $ schema.flattenList c))
| [], c, _ => []
| ([], _) :: rss, c, isFirst => flattenOne rss c isFirst
| (r :: rs, cleanR) :: rss, c, isFirst =>
  let vals := match r.getCell c.2.2 with
              | Cell.emp => []
              | Cell.val xs => xs
  /- Takes in the `List` value `vs` in the cell specified by `c`, and the rows
    `rs` of the table. Outputs the result of flattening `vs` across the head of
    those rows. (Precondition: `vs` should be the `c` value for the head of
    `rs`.) E.g., `setVals [1, 2] [/["a", [1, 2]]] = [/["a", 1], /["a", 2]]`. -/
  let rec setVals : List c.2.1 → List (Row schema) →
                    List (Row $ schema.flattenList c)
  | [], _ => []
  | v :: vs, [] =>
    -- for the first column only, we allow duplication
    if isFirst
    then (cleanR.retypeCell c.2.2 (Cell.val v)) :: setVals vs []
    else []
  | v :: vs, r :: rs => (r.retypeCell c.2.2 (Cell.val v)) :: setVals vs rs
  termination_by vs rs => vs.length + rs.length

  (setVals vals (r :: rs), r.retypeCell c.2.2 Cell.emp) :: flattenOne rss c isFirst

-- Note: the number of flattened copies of a given row is equal to the min
-- length of any sequence in a column specified in cs in that row
def flatten (t : Table schema) (cs : ActionList Schema.flattenList schema)
  : Table (schema.flattenLists cs) :=
  let rss := t.rows.map (λ r => ([r], r))
  let rec doFlatten {sch : @Schema η} :
    (cs : ActionList Schema.flattenList sch) →
    List (List (Row sch) × Row sch) →
    Bool →
    List (List (Row $ sch.flattenLists cs))
  | ActionList.nil, rss, _ => rss.map (λ rs => rs.1)
  | ActionList.cons c cs, rss, isFirst =>
    doFlatten cs (flattenOne rss c isFirst) false
  {rows := List.flatten (doFlatten cs rss true)}

def transformColumn {τ₁ τ₂}
                    (t : Table schema)
                    (c : η)
                    (f : Option τ₁ → Option τ₂)
                    (hc : schema.HasCol (c, τ₁) := by header)
    : Table (schema.retypeColumn (Schema.colImpliesName hc) τ₂) :=
  {rows := t.rows.map (λ (r : Row schema) =>
    r.retypeCell hc (Cell.fromOption (f (getValue r c hc)))
  )}

def renameColumns (t : Table schema)
                  (ccs : ActionList Schema.renameColumnCN schema)
    : Table (schema.renameColumns ccs) :=
{rows := t.rows.map (Row.renameCells ccs)}

-- TODO: having to maually specify the schema is really annoying -- can we make
-- this better? Also, having separate `EqSubschema` and `Subschema` types feels
-- inelegant.
def find {schema : @Schema η}
         (subschema : EqSubschema schema) :
    (t : Table schema) → Row (subschema.toSchema) → Option (Fin (nrows t))
| {rows := []}, r => none
| {rows := r :: rs}, r' =>
  if Row.isSubRow r' r
  then some ⟨0, Nat.zero_lt_succ (Schema.length rs)⟩
  else (find subschema {rows := rs} r').map (λ n =>
          ⟨n.val + 1, Nat.succ_lt_succ n.isLt⟩)

def groupByRetentive {τ : Type u} [DecidableEq τ]
                     (t : Table schema)
                     (c : η)
                     (hc : schema.HasCol (c, τ) := by header)
    : Table [("key", ULift.{max (u+1) u_η} τ), ("groups", Table schema)] :=
groupBy t (λ (r : Row schema) => getValue r c hc)
          (λ (r : Row schema) => r)
          (λ (k : Option τ) (vs : List (Row schema)) =>
            Row.cons (Cell.fromOption (k.map ULift.up))
              (Row.cons (Cell.val (Table.mk vs)) Row.nil))

def groupBySubtractive {τ : Type u} [DecidableEq τ]
                       (t : Table schema)
                       (c : η)
                       (hc : schema.HasCol (c, τ) := by header)
    : Table [("key", ULift.{max (u+1) u_η} τ),
             ("groups", Table (schema.removeName
                                (Schema.colImpliesName hc)))] :=
groupBy t (λ r => getValue r c hc)
          (λ r => r)
          (λ k vs => Row.cons (Cell.fromOption (k.map ULift.up))
                        (Row.cons (Cell.val (Table.mk (vs.map (λ r =>
                            r.removeColumn (Schema.colImpliesName hc)))))
                          Row.nil))

def pivotLonger {τ : Type u_η}
                (t : Table schema)
                (cs : ActionList (Schema.removeTypedName τ) schema)
                (c1 : η)
                (c2 : η)
    : Table (Schema.append (schema.removeTypedNames cs) [(c1, η), (c2, τ)]) :=
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

-- Note that we can't put this in `Schema.lean` because it depends on API
-- functions
def Schema.hasColOfMemPivotCol
  {τ : Type u} {t : Table schema} {lblCol : η} {lblEntry : η}
  : (hc : schema.HasCol (lblCol, η)) →
    (hmem : List.MemT (some lblEntry) (getColumn2 t lblCol hc)) →
    Schema.HasCol (lblEntry, τ) $
    (getColumn2 t lblCol hc).somes.unique.map (λ x => (x, τ)) :=
  λ hc hmem =>
    let hmemT :=
      hmem |> List.memT_somes_of_memT
           |> List.memT_unique_of_memT
           |> List.memT_map_of_memT (λ x => (x, τ))
    Schema.hasColOfMemT hmemT

def pivotWider.foldProof
  (t : Table schema) (c1 c2 : η)
  (hc1 : schema.HasCol (c1, η))
  (hc2 : (schema.removeHeader hc1).HasCol (c2, τ))
  (r : Row (Schema.fromCHeaders [⟨(c1, η), hc1⟩,
                                 ⟨(c2, τ), Schema.removeHeaderPres hc2⟩]))
  (hr : List.MemT r
        (List.map (λ r' => Row.pick r' [⟨(c1, η), hc1⟩,
                                        ⟨(c2, τ), Schema.removeHeaderPres hc2⟩])
        t.rows))
  (nm : η)
  (hnm : r.getCell .hd = .val nm)
  : List.MemT (some nm) (getColumn2 t c1 hc1) := by
  simp only [getColumn2, getValue]
  let nmCell := r.getCell .hd
  have hsomenm : some nm = Cell.toOption nmCell := by
    simp only [nmCell, Cell.toOption, hnm]
  rw [hsomenm]
  have hcelleq : nmCell = r.getCell .hd := rfl

  have hfeq :
    (λ (r : Row schema) => r.getCell hc1) =
    (λ (r : Row schema) => Row.getCell
      (r.pick [⟨(c1, η), hc1⟩, ⟨(c2, τ), Schema.removeHeaderPres hc2⟩])
      .hd) :=
    rfl

  let hcell : List.MemT nmCell $ List.map (λ r => r.getCell hc1) t.rows := by
    rw [hcelleq]
    rw [hfeq]
    have hcomp :
      (λ (r : Row schema) => Row.getCell
        (r.pick [⟨(c1, η), hc1⟩, ⟨(c2, τ), Schema.removeHeaderPres hc2⟩]) .hd) =
      (λ (r : Row schema) =>
        (λ r' => Row.getCell r' .hd) ∘
        (λ r' => r'.pick [⟨(c1, η), hc1⟩,
                          ⟨(c2, τ), Schema.removeHeaderPres hc2⟩]) $ r) :=
      rfl
    rw [hcomp, ←List.map_map]
    apply List.memT_map_of_memT (f :=
      (λ (r : Row (Schema.fromCHeaders
        [⟨(c1, η), hc1⟩, ⟨(c2, τ), Schema.removeHeaderPres hc2⟩])) =>
        Row.getCell r .hd)
    )
    exact hr

  have hcomp :
    (λ r => Cell.toOption (Row.getCell r hc1)) =
    (λ r => (Cell.toOption ∘ (λ r' => Row.getCell r' hc1)) r) :=
    rfl
  rw [hcomp, ←List.map_map]
  apply List.memT_map_of_memT
  apply hcell

-- Note: type-class resolution and other reducibility-dependent operations are
-- difficult when working with `pivotWider`, since the non-reducible function
-- `getColumns2` and likely non-reducible table `t` itself both appear in the
-- function's type
def pivotWider {τ} (t : Table schema)
               (c1 : η)
               (c2 : η)
               (hc1 : Schema.HasCol (c1, η) schema := by header)
               (hc2 : (schema.removeHeader hc1).HasCol (c2, τ) := by header)
               -- This looks ugly, but it should be doable with `inst`
               [inst : DecidableEq $ Row (schema.removeNames
                  (ActionList.cons (Schema.cNameOfCHead ⟨(c1, η), hc1⟩)
                  (ActionList.cons (Schema.cNameOfCHead ⟨(c2, τ), hc2⟩) ActionList.nil)))]
    : Table $
      Schema.append
        (schema.removeHeaders $ ActionList.cons ⟨(c1, η), hc1⟩
                                  (ActionList.cons ⟨(c2, τ), hc2⟩ ActionList.nil))
        ((getColumn2 t c1 hc1).somes.unique.map (λ x => (x, τ))) :=
let gather := (λ r pf => ⟨r.pick [⟨(c1, η), hc1⟩, ⟨(c2, τ), Schema.removeHeaderPres hc2⟩], (
    -- Lean infers the wrong mapping function here if you omit this. No idea why
    List.memT_map_of_memT (λ r' =>
        r'.pick [⟨(c1, η), hc1⟩, ⟨(c2, τ), Schema.removeHeaderPres hc2⟩])
      pf
)⟩)
groupByCertified t
  (ν :=
    ((r : Row (Schema.fromCHeaders [⟨(c1, η), hc1⟩,
                                    ⟨(c2, τ), Schema.removeHeaderPres hc2⟩]))
      × (List.MemT r (t.rows.map (λ r' =>
        r'.pick [⟨(c1, η), hc1⟩, ⟨(c2, τ), Schema.removeHeaderPres hc2⟩]))))
  )
  (λ r _ => r.removeColumns <|
    ActionList.cons (Schema.cNameOfCHead ⟨(c1, η), hc1⟩)
      (ActionList.cons (Schema.cNameOfCHead ⟨(c2, τ), hc2⟩) ActionList.nil))
  gather
  (λ k vs =>
    Row.append k (Row.empty _)
    |> vs.foldl (λ acc rowWithMem =>
        -- This would be nice, but Lean's pattern matcher isn't up to the task:
        -- | acc, Row.cons (Cell.val nm) (Row.cons val Row.nil) =>
        let r := rowWithMem.1
        let hr := rowWithMem.2
        let nmCell := r.getCell .hd
        let valCell := r.getCell (.tl .hd)
        match hnmc : nmCell with
          | .val nm =>
            acc.setCell (c := nm) (Schema.hasColOfPrepend (
              Schema.hasColOfMemPivotCol hc1
                (pivotWider.foldProof t c1 c2 hc1 hc2 r hr nm hnmc)
            )) (valCell.rename nm)
          | _ => acc)
  )

def pivotTable (t : Table schema)
  -- TODO: probably need a custom product with decidable equality instances (I
  -- think we have one already somewhere else in the code) (Could also try to
  -- just let Lean infer it using `Row $ Schema.fromCHeaders ...`, but I'm not
  -- sure it's smart enough to do that -- should test!)
  (cs : List (CertifiedHeader schema))
  (aggs : List ((c' : @Header η) ×
                (c : CertifiedHeader schema) ×
                (List (Option c.1.2) → Option c'.2)))
  [inst : DecidableEq (Row (Schema.fromCHeaders cs))]
  : Table (Schema.append (Schema.fromCHeaders cs)
                         (Schema.map (·.1) aggs)) :=
groupBy t
  (λ r => r.pick cs)
  (λ r => r)
  (λ k rs =>
    let subT := Table.mk rs
    let rec mkSubrow :
      (as : List ((c' : @Header η) ×
                  (c : CertifiedHeader schema) ×
                  (List (Option c.1.2) → Option c'.2))) →
      Row (Schema.map (·.1) as)
    | [] => Row.nil
    | ⟨c', c, f⟩ :: as =>
      let newCell : Cell c'.1 c'.2 := Cell.fromOption $
        f (getColumn2 subT c.1.1 c.2)
      let rest : Row $ Schema.map (·.1) as := mkSubrow as
      Row.cons newCell rest
    Row.append k (mkSubrow aggs)
  )
