import Table.Cell
import Table.Schema
import Table.Row
import Table.Table

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

def leftJoin {schema₁ schema₂ : @Schema η}
             (t1 : Table schema₁)
             (t2 : Table schema₂)
             (cs : ActionList (Schema.removeOtherDecCH schema₁) schema₂)
: Table (List.append schema₁ (Schema.removeOtherDecCHs schema₁ schema₂ cs)) :=
{rows :=
  t1.rows.flatMap (λ r₁ =>
    let rs2 := t2.rows.filter (λ r₂ =>
      let mismatch := (cs.toList Schema.removeOtherCHPres).find? (λ c =>
        let _ : DecidableEq (Cell c.1.1 c.1.2) :=
          instDecidableEqCell (inst := c.2.1)
        decide $ r₁.getCell c.2.2.2 ≠ r₂.getCell c.2.2.1)

      match mismatch with
      | none => true
      | _    => false
    )
    match rs2 with
    | [] => [Row.append r₁ (Row.empty _)]
    | _  =>
      rs2.map (λ r₂ =>
        let r₂' := r₂.removeOtherSchemaCols cs
        Row.append r₁ r₂')
  )
}

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
| {rows := r::rs}, Nat.succ n, h =>
  getRow {rows := rs} n (Nat.lt_of_succ_lt_succ h)

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
def selectRows2 (t : Table schema) (bs : List Bool)
                (h : List.length bs = nrows t)
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

-- TODO: with the flexibility afforded by ADTs, it might be worth modifying this
-- to allow for a more expressive ordering function
def orderBy (t : Table schema)
            (cmps : List ((κ : Type u) × (Row schema → κ) × (κ → κ → Bool)))
    : Table schema :=
{rows :=
  t.rows.mergeSortWith (λ r₁ r₂ =>
    match cmps.find? (λ | ⟨κ, key, ord⟩ => !ord (key r₁) (key r₂)) with
    | none => Ordering.lt
    | _    => Ordering.gt
  )
}

-- # Aggregate
-- TODO: this "dictionary" implementation could use some improvement
-- Should we enforce Ord instance so that we can get the speed-up of an RBT?
-- TODO: why does Lean freeze if we specify `τ : Type u`?
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

-- Once mathlib has been ported, we can find some suitable algebraic structure
-- (or, at the very least, use `Int`s once the tooling for those has been
-- fleshed out). In the meantime, we'll use this replacement to indicate which
-- variables can be swapped out for a more general type.
section BinTypeScope
local notation "BinType" => Nat
def bin [ToString η]
        (t : Table schema)
        (c : ((c : η) × schema.HasCol (c, BinType)))
        (n : {n : Nat // n > 0})
    : Table [("group", String), ("count", Nat)] :=
  let col := getColumn2 t c.1 c.2
  let sorted := col |> List.filterMap id  -- get rid of empty cells
                    |> List.mergeSortWith compare
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

    have hterm : max - (k + n.val) < max - k :=
    by apply Nat.lt_of_sub_add
       . exact Nat.lt_of_not_ge _ _ h
       . exact n.property
       
    (k, cnt) :: kthBin (k + n.val) rest
  let bins := kthBin (n * (s / n + 1)) (s :: ss)
  {rows := bins.map (λ (k, cnt) =>
    Row.cons (Cell.val $
      toString (k - n) ++ " <= "
                        ++ toString c.1
                        ++ " < "
                        ++ toString k)
      (Row.singleValue cnt))}
termination_by kthBin k xs => max - k
end BinTypeScope

-- # Mising Values

def completeCases {τ} (t : Table schema)
                  (c : ((c : η) × schema.HasCol (c, τ))) :=
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

def RetypedSubschema.updateForRetype {s : @Schema η} {nm : η} {τ} {h : s.HasName nm}
  (ss : RetypedSubschema s) : RetypedSubschema (s.retypeColumn h τ) :=
ss.map (λ | ⟨hdr, pf'⟩ => ⟨hdr, Schema.retypedRetainsHasName pf'⟩)

theorem RetypedSubschema.length_updateForRetype {s : @Schema η} {nm : η} {τ} {h : s.HasName nm} {ss : RetypedSubschema s} :
  List.length (RetypedSubschema.updateForRetype (τ := τ) (h := h) ss) = List.length ss :=
List.length_map _ _

def Schema.retypeFromSubschema (s : @Schema η) :
  RetypedSubschema s → @Schema η
| [] => s
-- | ⟨(_, τ), pf⟩ :: ss =>
--   have hterm : List.length (RetypedSubschema.updateForRetype ss)
--                 < Nat.succ (List.length ss) :=
--     by conv =>
--         lhs
--         apply RetypedSubschema.length_updateForRetype (τ := τ) (h := pf)
--        apply Nat.lt.base
--   retypeFromSubschema (s.retypeColumn pf τ) (RetypedSubschema.updateForRetype ss)
| shdr :: ss =>
  have hterm : List.length (RetypedSubschema.updateForRetype ss)
                < Nat.succ (List.length ss) :=
    by conv =>
        lhs
        apply RetypedSubschema.length_updateForRetype (τ := shdr.1.2)
                                                      (h := shdr.2)
       apply Nat.lt.base
  retypeFromSubschema (s.retypeColumn shdr.2 shdr.1.2) (RetypedSubschema.updateForRetype ss)
termination_by retypeFromSubschema s ss => ss.length
decreasing_by assumption

def Row.retypeForSubschema :
  {schema : @Schema η} →
  (ss : RetypedSubschema schema) →
  Row schema →
  Row (schema.retypeFromSubschema ss)
| _, [], r => r
| schema, ⟨(_, τ), pf⟩ :: ss, r =>
  have hterm : List.length (RetypedSubschema.updateForRetype ss)
                < Nat.succ (List.length ss) :=
    by conv =>
        lhs
        apply RetypedSubschema.length_updateForRetype (τ := τ) (h := pf)
       apply Nat.lt.base
  retypeForSubschema (RetypedSubschema.updateForRetype ss)
                     (r.retypeCell pf Cell.emp)
termination_by retypeForSubschema ss r => ss.length

/-
Want to show:
toSchema (subhdr :: ss')
=
Schema.retypeFromSubschema (Schema.retypeColumn s pf τ) (updateForRetype ss)
-/

-- TODO: this should be trivial, and yet...
-- FIXME: this is false! If we have the same name entry with different types
-- in the RetypedSubschema, then only the *second* one would appear in the final
-- retyped schema! :( Perhaps we will need some sort of ActionList after all...
def RetypedSubschema.retypedHasCol :
  {s : @Schema η} →
  {ss : RetypedSubschema s} →
  {hdr : Header} →
  Schema.HasCol hdr (RetypedSubschema.toSchema ss) →
  Schema.HasCol hdr (s.retypeFromSubschema ss)
| (nm, τ) :: schm, ⟨(.(nm), τ'), Schema.HasName.hd⟩ :: subschm, _, Schema.HasCol.hd => --Schema.HasCol.hd
by simp only [Schema.retypeFromSubschema, Schema.retypeColumn, updateForRetype]
-- := by
--   intros s ss hdr h
--   cases ss with | nil => contradiction | cons shdr ss =>
--   cases shdr with | mk shdr pf =>
--   simp only [toSchema] at h
--   simp only [Schema.retypeFromSubschema, updateForRetype]
--   cases pf with
--   | hd =>
--      simp only [Schema.retypeColumn, Schema.retypeFromSubschema, updateForRetype]

-- := by
--   intros s ss hdr h
--   cases hdr with | mk nm τ =>
--   cases ss with
--   | nil => contradiction
--   | cons subhdr rest =>
--     cases subhdr with | mk subhdr pf =>
--     cases subhdr with | mk sub_nm sub_τ =>
--     cases pf with
--     | hd =>
--       unfold Schema.retypeFromSubschema
--       simp only [RetypedSubschema.updateForRetype]

  -- Schema.HasCol.hd
  -- by simp only [Schema.retypeFromSubschema, Schema.retypeColumn, updateForRetype]
-- | s, ⟨curHdr, pf⟩ :: ss, _, Schema.HasCol.tl h =>
--   sorry

-- def Row.retypedSubrowForRetype {s : @Schema η} {nm : η} {τ} {h : s.HasName nm}
--   {ss : RetypedSubschema s}
--   (r : Row ss.toSchema) : Row (ss.updateForRetype (τ := τ) (h := h)).toSchema :=
--   r.map (λ )
-- ss.map (λ | ⟨hdr, pf'⟩ => ⟨hdr, Schema.retypedRetainsHasName pf'⟩)

theorem Nat.lt_add_right (a b c : Nat) : a < b → a < b + c :=
λ h => Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)

-- TODO: a better name might be `updateSubrowForRetype` or something, but let's
-- fix the bugs first.
def Row.retypeForRetypedSubschema :
  {sch : @Schema η} → {sub : RetypedSubschema sch} →
  {nm : η} → {h : sch.HasName nm} → {τ : Type _} →
  Row (RetypedSubschema.toSchema sub) →
  Row (RetypedSubschema.toSchema (RetypedSubschema.updateForRetype
    (h := h) (τ := τ) sub))
| _, [], _, _, _, _ => Row.nil
| _, ⟨hdr, hn⟩ :: sub', _, _, _, Row.cons c cs =>
  have hterm : sizeOf cs < sizeOf (Row.cons c cs) :=
    by simp  -- TODO: figure out a strict simp set
       rw [Nat.add_comm, ←Nat.add_assoc]
       apply Nat.lt_add_right
       apply Nat.lt.base
  Row.cons c (retypeForRetypedSubschema cs)
termination_by retypeForRetypedSubschema cs r => sizeOf r
decreasing_by assumption

-- Can also do this by `cast`, but this strikes me as not the best idea
theorem Row.retypeForRetypedSubschema'_pf
  {sch : @Schema η} {sub : RetypedSubschema sch}
  {nm : η} {h : sch.HasName nm} {τ : Type _} :
    RetypedSubschema.toSchema sub =
    RetypedSubschema.toSchema (RetypedSubschema.updateForRetype
      (h := h) (τ := τ) sub) :=
  by induction sub with
     | nil => simp only [RetypedSubschema.toSchema]
     | cons shdr ss ih =>
       simp only [RetypedSubschema.updateForRetype, List.map]
       simp only [RetypedSubschema.toSchema]
       apply congrArg (λ x => shdr.1 :: x)
       apply ih

def Row.retypeForRetypedSubschema'
  {sch : @Schema η} {sub : RetypedSubschema sch}
  {nm : η} {h : sch.HasName nm} {τ : Type _}
  (r : Row (RetypedSubschema.toSchema sub)) :
  Row (RetypedSubschema.toSchema (RetypedSubschema.updateForRetype
    (h := h) (τ := τ) sub)) :=
  cast (congrArg Row retypeForRetypedSubschema'_pf) r

-- More issues with equation generation
theorem Row.retypeForRetypedSubschema_eq_1
  {sch : @Schema η} {nm : η} {h : sch.HasName nm} {τ : Type _} :
  Row.retypeForRetypedSubschema (sch := sch) (sub := []) (h := h) (τ := τ) Row.nil = Row.nil := rfl

-- FIXME: *why* will these definitions not expand‽
theorem Row.retypeForRetypedSubschema_eq_test -- TODO: Delete once resolved
  {sch : @Schema η} {nm : η} {h : sch.HasName nm} {τ : Type _} {pf : sch.HasName hdr.1}:
  Row.retypeForRetypedSubschema (sch := sch) (sub := [⟨hdr, pf⟩]) (h := h) (τ := τ) (cons c nil) = cons c nil := rfl

theorem Row.retypeForRetypedSubschema_eq_2
  {sch : @Schema η}
  {hdr : @Header η} {hn : sch.HasName hdr.1}
  {sub' : RetypedSubschema sch}
  {nm : η} {h : sch.HasName nm} {τ : Type _}
  {c : Cell hdr.1 hdr.2} {cs : Row $ sub'.toSchema} :
  @retypeForRetypedSubschema η dec_η sch (⟨hdr, hn⟩ :: sub') nm h τ (cons c cs) =
  cons c (@retypeForRetypedSubschema η dec_η sch sub' nm h τ cs) := sorry --rfl

theorem Row.retypeForRetypedSubschema'_eq_1
  {sch : @Schema η} {nm : η} {h : sch.HasName nm} {τ : Type _} :
  retypeForRetypedSubschema' (sch := sch) (sub := []) (h := h) (τ := τ) nil = nil := rfl

theorem Row.retypeForRetypedSubschema'_eq_2 {sch : @Schema η}
  {hdr : @Header η} {hn : sch.HasName hdr.1}
  {sub' : RetypedSubschema sch}
  {nm : η} {h : sch.HasName nm} {τ : Type _}
  {c : Cell hdr.1 hdr.2} {cs : Row $ sub'.toSchema} :
  @retypeForRetypedSubschema' η dec_η sch (⟨hdr, hn⟩ :: sub') nm h τ (cons c cs) =
  cast (congrArg Row (retypeForRetypedSubschema'_pf (sub := ⟨hdr, hn⟩ :: sub'))) (cons c cs) := rfl

theorem Row.retypeForRetypedSubschema'_eq_general
  {sch : @Schema η}
  {nm : η}
  (hn : sch.HasName nm)
  (sub : RetypedSubschema sch)
  {nm' : η} {h : sch.HasName nm'} {τ : Type _}
  (r : Row sub.toSchema) :
  retypeForRetypedSubschema' (h := h) (τ := τ) r =
  cast (congrArg Row Row.retypeForRetypedSubschema'_pf) r := rfl

theorem Row.sizeOf_retypeForRetypedSubschema :
  (sub : RetypedSubschema schema) →
  (r : Row sub.toSchema) →
  sizeOf (Row.retypeForRetypedSubschema (h := h) (τ := τ) r) = sizeOf r
| [], Row.nil => rfl
| ⟨n, hn⟩ :: subs, Row.cons c cs =>
  have mainPf := congrArg (λ x => 1 + sizeOf c + x)
                          (sizeOf_retypeForRetypedSubschema subs cs)
  by rw [Row.cons.sizeOf_spec, retypeForRetypedSubschema_eq_2]; apply mainPf
  -- `simp` isn't applying `Row.cons.sizeOf_spec` for some reason

def Row.updateFromSubrow {sch : @Schema η} :
         {subsch : RetypedSubschema sch} →
    Row sch → Row (subsch.toSchema) → Row (sch.retypeFromSubschema subsch)
| [], r, Row.nil => r
| ⟨hdr, hn⟩ :: sub', r, Row.cons c cs =>
  have hterm : sizeOf (retypeForRetypedSubschema (h := hn) (τ := hdr.2) cs)
                < sizeOf (cons c cs) :=
    by rw [sizeOf_retypeForRetypedSubschema sub' cs]
       simp
       rw [Nat.add_comm (1 + sizeOf c), ←Nat.add_assoc]
       apply Nat.lt_add_right
       apply Nat.lt.base
  updateFromSubrow (subsch := RetypedSubschema.updateForRetype sub')
                   (r.retypeCell hn c)
                   (retypeForRetypedSubschema cs)
termination_by updateFromSubrow r subr => sizeOf subr

-- This doesn't work for `fillna` because it can't figure out that the types are
-- the same
def update_alt {schema₁ : @Schema η}
               (schema₂ : RetypedSubschema schema₁)
               (t : Table schema₁)
               (f : Row schema₁ → Row schema₂.toSchema) : Table (schema₁.retypeFromSubschema schema₂) :=
{rows := t.rows.map (λ r => Row.updateFromSubrow r (f r))}

-- FIXME: Lean can't infer the subschema because it's really trying to infer
-- "subschema.toSchema," which isn't definitional
-- Couple of options here. The best thing would be to figure out a way to let
-- Lean infer the (sub)schema directly, just like it does for normal schemata.
-- Alternatively, we can just make the subschema an explicit arg :(
def update {schema₁ : @Schema η}
           (schema₂ : RetypedSubschema schema₁)
           (t : Table schema₁)
           (f : Row schema₁ → Row schema₂.toSchema) : Table (schema₁.retypeFromSubschema schema₂) :=
  {rows := t.rows.map (λ r =>
    let newCells : Row schema₂.toSchema := f r
    newCells.certifiedFoldr
      (λ {nm τ}
         (cell : Cell nm τ)
         (h : schema₂.toSchema.HasCol (nm, τ))
         (acc) =>
         -- TODO: this issue of the type changing at each stage of a fold again...
         -- One solution might be to just retype `r` and replace the updated cells
         -- with empties, then go through and `setCell` (no need to retype since
         -- the base value will already be a `schema₂`)
         -- But this solution would require some sort of action list, since
         -- the proofs become invalidated as soon as we change one column...
          Row.setCell acc (RetypedSubschema.retypedHasCol h) cell)
      (r.retypeForSubschema schema₂)
  )}

def Schema.retypeColumnPair (schema : @Schema η)
                            (c : (nm : η) × schema.HasName nm × Type u) :=
  Schema.retypeColumn schema c.2.1 c.2.2

def Schema.retypeColumns :
  (schema : @Schema η) → ActionList Schema.retypeColumnPair schema → @Schema η
| schema, ActionList.nil => schema
| schema, ActionList.cons c cs => retypeColumns (schema.retypeColumnPair c) cs

-- The `induction` tactic doesn't support data, apparently
def Schema.retypeColumnPreservesName :
  {s : @Schema η} →
  {nm nm' : η} →
  {hn : HasName nm' s} →
  {τ : Type u} →
  HasName nm (retypeColumn s hn τ) →
  HasName nm s
| _ :: s, nm, nm', HasName.hd, τ, pf_orig => by
  cases pf_orig with
  | hd => apply HasName.hd
  | tl h => apply HasName.tl h
| _ :: s, nm, nm', HasName.tl h, τ, pf_orig => by
  cases pf_orig with
  | hd => apply HasName.hd
  | tl h => apply HasName.tl (retypeColumnPreservesName h)

def Schema.retypeColumnPairPres
  (s : Schema)
  (k : (nm : η) × Schema.HasName nm s × Type u)
  (c : (nm : η) × Schema.HasName nm (Schema.retypeColumnPair s k) × Type u) :
  (nm : η) × Schema.HasName nm s × Type u :=
⟨c.1, retypeColumnPreservesName c.2.1, c.2.2⟩

def Row.retypeEmptyCells {sch : @Schema η} :
  (cs : ActionList Schema.retypeColumnPair sch) →
  Row sch →
  Row (sch.retypeColumns cs)
| ActionList.nil, r => r
| ActionList.cons c cs, r => retypeEmptyCells cs (r.retypeCell c.2.1 Cell.emp)

def ActionList.columnPairListToSchema {sch : @Schema η}
  (cs : ActionList Schema.retypeColumnPair sch) : @Schema η :=
(cs.toList Schema.retypeColumnPairPres).map (λ c => (c.1, c.2.2))

def ActionList.columnPairSchema :
  {s : @Schema η} →
  {cs : ActionList Schema.retypeColumnPair s} →
  {hdr : Header} →
  Schema.HasCol hdr cs.columnPairListToSchema →
  Schema.HasCol hdr (s.retypeColumns cs) := sorry

-- TODO: I really don't think we need an ActionList...this is ending up right
-- where the regular `update` is...
def update'_alt {schema : @Schema η}
            (t : Table schema)
            (cs : ActionList Schema.retypeColumnPair schema)
            -- NOTE: this doesn't quite adhere to the spec b/c `f` is supposed
            -- to return a row *just* containing modified cells
            (f : Row schema → Row (cs.columnPairListToSchema))
    : Table (schema.retypeColumns cs) :=
{rows := t.rows.map (λ r => 
    let newCells := f r
    -- TODO: can't use `certifiedFoldr` because the type needs to change with
    -- each iteration -- the ActionList relies on this incremental type changing
    -- to provide its guarantee of validity
    newCells.certifiedFoldr
      (λ {nm τ}
         (cell : Cell nm τ)
         (h : cs.columnPairListToSchema.HasCol (nm, τ))
         (acc) =>
         -- TODO: this issue of the type changing at each stage of a fold again...
         -- One solution might be to just retype `r` and replace the updated cells
         -- with empties, then go through and `setCell` (no need to retype since
         -- the base value will already be a `schema₂`)
         -- But this solution would require some sort of action list, since
         -- the proofs become invalidated as soon as we change one column...
          Row.setCell acc h cell)
      (r.retypeEmptyCells cs)
)}

-- Alternative implementation that slightly deviates from the spec
def update' {schema : @Schema η}
            (t : Table schema)
            (cs : ActionList Schema.retypeColumnPair schema)
            -- NOTE: this doesn't quite adhere to the spec b/c `f` is supposed
            -- to return a row *just* containing modified cells
            (f : Row schema → Row (schema.retypeColumns cs))
    : Table (schema.retypeColumns cs) :=
{rows := t.rows.map (λ r => f r)}

-- This doesn't adhere to the spec b/c `f` is supposed to return a row of cells
-- with names (but not necessarily types) matching some subset of the names in
-- the original schema. However, this has proven challenging to implement, so
-- for the time being, this is a (slightly too general) workaround -- it's not
-- that hard to use `row.setCell` instead of constructing a row from scratch;
-- unfortunately, we can no longer enforce that the names in the schemata be
-- preserved.
def update'' {schema schema' : @Schema η}
             (t : Table schema)
             (f : Row schema → Row schema')
    : Table schema' :=
{rows := t.rows.map f}

def testtable : Table [("id", Nat), ("field", String)] := Table.mk [
  Row.cons (Cell.val 0) $ Row.cons (Cell.val "hi") Row.nil,
  Row.cons (Cell.val 1) $ Row.cons (Cell.val "bye") Row.nil
]

def fillna {τ}
           (t : Table schema)
           (c : ((c : η) × schema.HasCol (c, τ)))
           (v : τ)
    : Table schema :=
  update [⟨(c.fst, τ), c.snd⟩] t
    (λ r => match Row.getCell r c.snd with
                | Cell.emp => Row.singleValue v
                | Cell.val vOld => Row.singleValue vOld)
  -- update' t
  --   ActionList.nil
  --   (λ r => match Row.getCell r c.snd with
  --               | Cell.emp => r
  --               | Cell.val vOld => r.setCell c.snd $ Cell.val vOld)
  -- update'' t
  --   (λ r => match Row.getCell r c.snd with
  --               | Cell.emp => r
  --               | Cell.val vOld => r.setCell c.snd $ Cell.val vOld)
  -- update_alt [⟨(c.fst, τ), Schema.colImpliesName c.snd⟩] t
  --   (λ r => match Row.getCell r c.snd with
  --               | Cell.emp => Row.singleValue v
  --               | Cell.val vOld => Row.singleValue vOld)

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

/--
`flattenOne` takes a list of row copies and clean-row templates (i.e., a list of
row list-row tuples) `rss` and applies a flatten for the specified column `c`.
(That is, each element of `rss` is a copy of the same row with 0 or more prior
flattenings applied.) It outputs `rss'`, where each elements `rs ∈ rss` is
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
columns that have already been flattened.)
-/
def flattenOne {schema : @Schema η} :
  -- list of flattened copies of each row × "clean" copy of row for all
  -- columns up to this point
  List (List (Row schema) × Row schema) →
  (c : (c : η) × (τ : Type u_1) × Schema.HasCol (c, List τ) schema) →
  List (List (Row $ schema.flattenList c) × (Row $ schema.flattenList c))
| [], c => []
| ([], _) :: rss, c => flattenOne rss c
| (r :: rs, cleanR) :: rss, c =>
  let vals := match r.getCell c.2.2 with
              | Cell.emp => []
              | Cell.val xs => xs
  let nmPf := Schema.colImpliesName c.2.2
  let rec setVals : List c.2.1 → List (Row schema) →
                    List (Row $ schema.flattenList c)
  | [], [] => []
  | [], r :: rs => (r.retypeCell nmPf Cell.emp) :: setVals [] rs
  | v :: vs, [] => (cleanR.retypeCell nmPf (Cell.val v)) :: setVals vs []
  | v :: vs, r :: rs => (r.retypeCell nmPf (Cell.val v)) :: setVals vs rs
  
  (setVals vals (r :: rs), r.retypeCell nmPf Cell.emp) :: flattenOne rss c
termination_by setVals vs rs => vs.length + rs.length

-- TODO: could probably rewrite this to use the `selectMany` combinator
def flatten (t : Table schema) (cs : ActionList Schema.flattenList schema)
  : Table (schema.flattenLists cs) :=
  let rss := t.rows.map (λ r => ([r], r))
  let rec doFlatten {sch : @Schema η} :
    (cs : ActionList Schema.flattenList sch) →
    List (List (Row sch) × Row sch) →
    List (List (Row $ sch.flattenLists cs))
  | ActionList.nil, rss => rss.map (λ rs => rs.1)
  | ActionList.cons c cs, rss => doFlatten cs (flattenOne rss c)
  {rows := List.flatten (doFlatten cs rss)}

/- Abandoned `selectMany` approach
#check @Row.retypeCell
def flatten' {n : Nat}
  (t : Table schema)
  (cs : ActionList Schema.flattenList schema) :
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
    let rec κ_sch1 : List ((c : η) × (τ : Type _) × Schema.HasCol (c, List τ) schema) → @Schema η
    | [] => schema
    | c :: cs => (Schema.retypeColumn (κ_sch1 cs) (Schema.colImpliesName c.2.2) c.2.1)

    -- FIXME: pretty sure `toList` won't work because we need to leverage the
    -- consecutive flattening proofs of the `ActionList`
    let (oneFlat, rest) := (cs.toList _).depFoldr
      (κ := λ xs => Row (match xs with
                    | [] => schema
                    | c :: cs => (Schema.retypeColumn schema (Schema.colImpliesName c.2.2) c.2.1)) × Row schema)
      (λ c (r', acc) =>
        let pf := c.2.2
        match r'.getCell c.2.2 with
        -- TODO: see algorithm on iPad
        -- *Potential issue*: the proofs may become invalid as soon as we start
        -- retyping cells -- need to make sure the ActionList is correct (I feel
        -- like it might be, since the retyping is a flattening, but should make
        -- sure...)
        | Cell.emp | Cell.val [] => (r'.retypeCell pf Cell.emp, acc)
        | Cell.val [x] => (r'.retypeCell pf (Cell.val x), acc.setCell pf Cell.emp)
        | Cell.val (x :: y :: xs) =>
          (r'.retypeCell pf (Cell.val x), acc.setCell pf (Cell.val (y :: xs)))
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
    r.retypeCell (Schema.colImpliesName c.snd)
      (Cell.fromOption (f (getValue r c.fst c.snd)))
  )}

def renameColumns (t : Table schema)
                  (ccs : ActionList Schema.renameColumnCN schema)
    : Table (schema.renameColumns ccs) :=
{rows := t.rows.map (Row.renameCells ccs)}

-- TODO: move this somewhere else
def isSubRow : {schema : @Schema η} →
               {subschema : EqSubschema schema} →
               (sr : Row subschema.toSchema) →
               (r : Row schema) →
               Bool
| _, [], Row.nil, _ => true
| s :: ss, ⟨(nm, _), pf, _⟩ :: sbs, Row.cons sc scs, r =>
  have hterm : sizeOf scs < sizeOf (Row.cons sc scs) :=
    by conv => lhs; rw [←Nat.zero_add (sizeOf scs)]
       apply @Nat.add_lt_add_right 0 (1 + sizeOf sc) _ (sizeOf scs)
       rw [Nat.add_comm, Nat.add_one]
       apply Nat.zero_lt_succ
  if r.getCell pf = sc
  then isSubRow scs r
  else false
termination_by isSubRow sr r => sizeOf sr
decreasing_by assumption

-- TODO: having to maually specify the schema is really annoying -- can we make
-- this better? Also, having separate `EqSubschema` and `Subschema` types feels
-- inelegant.
def find {schema : @Schema η}
         (subschema : EqSubschema schema) :
    Table schema → Row (subschema.toSchema) → Option Nat
| {rows := []}, r => none
| {rows := r :: rs}, r' =>
  if isSubRow r' r
  then some 0
  else (find subschema {rows := rs} r').map (λ n => n + 1)

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

def pivotWider [inst : Inhabited η]
               (t : Table schema)
               (c1 : (c : η) × Schema.HasCol (c, η) schema)
               (c2 : CertifiedHeader (schema.removeHeader c1.2))
    : Table (List.append
      (schema.removeHeaders $ ActionList.cons ⟨(c1.1, η), c1.2⟩
                                (ActionList.cons c2 ActionList.nil))
      -- FIXME: this is wrong -- we instead want the *unique* entries in c1
      (t.rows.map (λ (r : Row schema) =>
        (Option.orDefault (getValue r c1.fst c1.snd), η)
      ))) := sorry

-- TODO: a lot of stuff to fix here...
-- TODO: we should really be able to synthesize the DecidableEq instance
-- ourselves (the client only needs to use the `inst` tactic in the test file,
-- but even that really shouldn't be necessary)
def pivotTable (t : Table schema)
  -- TODO: probably need a custom product with decidable equality instances (I
  -- think we have one already somewhere else in the code!) (Could also try to
  -- just let Lean infer it using `Row $ Schema.fromCHeaders etc`, but I'm not
  -- sure it's smart enough to do that -- should test!)
  (cs : List (CertifiedHeader schema))
  (inst : DecidableEq (Row (Schema.fromCHeaders cs)))
  (aggs : List ((c' : @Header η) ×
                (c : CertifiedHeader schema) ×
                (List (Option c.1.2) → Option c'.2)))
  : Table (List.append (Schema.fromCHeaders cs)
                       (aggs.map (λ a => a.1))) :=
                      --  (Schema.fromCHeaders (aggs.map (λ a => a.2.1)))) :=
groupBy t
  (λ r => r.pick cs)
  (λ r => r)
  (λ k rs =>
    let subT := Table.mk rs
    let rec mkSubrow :
      (as : List ((c' : @Header η) ×
                  (c : CertifiedHeader schema) ×
                  (List (Option c.1.2) → Option c'.2))) →
      Row (as.map (λ a => a.1))
      -- Row $ Schema.fromCHeaders (as.map (λ a => a.2.1))
    | [] => Row.nil
    | ⟨c', c, f⟩ :: as =>
      let newCell : Cell c'.1 c'.2 := Cell.fromOption $
        f (getColumn2 subT c.1.1 c.2)
      let rest : Row $ as.map (λ a => a.1) := mkSubrow as
      let newRow : Row $ c' :: as.map (λ a => a.1) := Row.cons newCell rest
      have h : Row (c' :: as.map (λ a => a.1)) =
               Row ((⟨c', c, f⟩ :: as).map (λ a => a.1)) := rfl
      -- TODO: why won't the type checker unfold `map`‽
      -- let newNewRow : Row $ (a :: as).map (λ a => a.1) := newRow
      -- Row.cons (newCell : Cell c'.1 c'.2) (rest : Row $ as.map (λ a => a.1)) --  : Row $ a.1 :: as.map (λ a => a.1))
      cast h newRow -- FIXME: we shouldn't need to pull out the `Eq` stops for this...
    Row.append k (mkSubrow aggs)
  )
