import Table.BuiltinExtensions
import Table.CoreFunctions
import Table.CoreTypes

universe u_η
universe u

variable {η : Type u_η} [dec_η : DecidableEq η] {schema : @Schema η}

-- Constructors
def emptyTable {α : Type u₁} [hα : DecidableEq α] : @Table α hα [] :=
  Table.mk []

def addRows (t : Table schema) (r : List (Row schema)) : Table schema :=
  {rows := List.append t.rows r}

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

-- Properties
-- TODO: Use Fin instead of ad-hoc quotients
def nrows (t : Table schema) : Nat := List.length t.rows

def ncols (t : Table schema) : Nat := List.length schema

def header (t : Table schema) : List η := List.map Prod.fst schema

-- TODO: might be nicer to build the row/column indexing into the Table type
-- itself?
-- TODO: eliminate sorry
def getRow : (t : Table schema) → (n : Nat) → (n < nrows t) → Row schema
| {rows := []}, n, h => absurd h (by
      intro nh
      simp [nrows] at nh
      apply Nat.not_lt_zero _ nh
    )
| {rows := r::rs}, 0, h => r
| {rows := r::rs}, Nat.succ n, h => getRow {rows := rs} n (by sorry : n < nrows {rows := rs})

-- Class for getting a cell from a row
class Gettable {c τ} (h : Schema.HasCol (c, τ) schema) where
  getp : Row schema → Cell c τ

instance {c τ}
    : @Gettable η dec_η ((c,τ)::schema) c τ (@Schema.HasCol.hd η c τ schema) :=
  {getp := λ (Row.cons c _) => c}

instance {c τ h r} [cls : Gettable h]
    : @Gettable η dec_η (r::schema) c τ (Schema.HasCol.tl h) :=
  {getp := λ (Row.cons c cs) => cls.getp h cs}

def getCell {τ}
            (r : Row schema)
            (c : η)
            (h : Schema.HasCol (c, τ) schema)
            [inst : Gettable h]
    : Cell c τ :=
  inst.getp h r

-- TODO: it would be nice not to have to provide a proof...
-- (Also, we now have Schema.lookup -- do we still need the implicit τ arg?
-- Careful if trying to make this change, though -- might, e.g., mess up the η
-- requirement we use in pivotWider to ensure we're getting a valid header!)
def getValue {τ}
             (r : Row schema)
             (c : η)
             (h : Schema.HasCol (c, τ) schema)
             [inst : Gettable h]
    : Option τ :=
  Cell.toOption (getCell r c h)

-- ...but in the meantime, here's a tactic to make the proof trivial
macro "header" : tactic => `(repeat ((try apply Schema.HasCol.hd) <;> (apply Schema.HasCol.tl)))
macro "name" : tactic => `(repeat ((try apply Schema.HasName.hd) <;> (apply Schema.HasName.tl)))

def getColumnIndex (t : Table schema)
                   (n : Nat)
                   (h : n < ncols t) :=
  List.map (λr => List.nth _ n h) t.rows

def getColumn {τ}
              (t : Table schema)
              (c : η)
              (h : Schema.HasCol (c, τ) schema)
              [inst : Gettable h]
    : List (Option τ) :=
  List.map (λ r => getValue r c h) t.rows

-- TODO: get rid of sorry!
def selectRowsIndices (t : Table schema)
                      (ns : List {n : Nat // n < nrows t}) : Table schema :=
  {rows := List.map (λ n => getRow t n.val n.property) ns}

-- We don't strictly *need* the proof here, but if we want to be consistent
-- about enforcing preconditions through proof terms, we should probably leave
-- it...
def selectRows (t : Table schema) (bs : List Bool) (h : List.length bs = nrows t)
    : Table schema :=
  {rows := List.sieve bs t.rows}

def selectColumns (t : Table schema)
                  (bs : List Bool)
                  (h : List.length bs = ncols t)
    : Table (List.sieve bs schema) :=
  {rows := t.rows.map (λ r => Row.sieve bs r)}

def selectColumnsN (t : Table schema)
                   (ns : List {n : Nat // n < ncols t})
    : Table (List.nths schema ns) :=
  {rows := t.rows.map (Row.nths ns)}

theorem schemaHasLookup (schema : @Schema η) (c : CertifiedName schema)
    : schema.HasCol ((schema.lookup c).fst, (schema.lookup c).snd) := by
  induction schema with
  | nil => cases c with | mk val prop => cases prop
  -- TODO: Is there a better syntax?
  | cons s ss ih => cases c with | mk val prop => cases s with | mk c τ =>
    simp [Schema.lookup]
    cases (Decidable.em (c = val)) with
    | inl h => simp [ite, h]; apply Schema.HasCol.hd
    | inr h =>
      simp [ite, h, Prod.fst, Prod.snd]
      apply Schema.HasCol.tl
      apply ih

-- TODO: This is a very, very hideous implementation of Row.pick. It feels like
-- we shouldn't need typeclasses -- the reason they arise is because we're
-- trying to avoid actually taking types/HasCols as args to pick
-- (Also, this generates terrible errors -- passing an invalid name fails via
-- typeclass resolution timeout, which is ridiculous and unhelpful.
-- EDIT: this isn't always true...it only happens if the first list element is
-- invalid or if there's a duplicate entry in `cs`. More generally, the issue
-- looks like the proof generation is part of typeclass resolution, so we don't
-- get to see the underlying issue in the error message.)
-- FIXME: Also, it fails when `cs` has duplicates -- granted this is ruled out
-- by the precondition, but should investigate why nonetheless.
class Pickable (cs : List (CertifiedName schema)) where
  pick : @Row η dec_η schema → Row (Schema.pick schema cs)

instance : Pickable ([] : List (CertifiedName schema)) where
  pick := λ _ => Row.nil

instance {schema : @Schema η} {c : CertifiedName schema} {cs : List (CertifiedName schema)} [inst : Pickable cs] 
         -- TODO: This is a really bad part of an already bad implementation
         -- (would not be surprised if this is what's failing elsewhere)
         {h : Schema.HasCol ((Schema.lookup schema c).fst, (Schema.lookup schema c).snd) schema}
         [Gettable h]
    : Pickable (c :: cs) where
  pick := λ rs =>
  -- have h : Schema.HasCol ((Schema.lookup schema c).fst, (Schema.lookup schema c).snd) schema := by apply schemaHasLookup;
  -- have _ : Gettable h := sorry;
  Row.cons (getCell rs (Schema.lookup schema c).fst h) (inst.pick rs)

def Row.pick (rs : @Row η dec_η schema)
             (cs : List (CertifiedName schema))
             [inst : Pickable cs]
    : Row (Schema.pick schema cs) :=
  inst.pick rs

-- TODO: I really think we should be able to do this without typeclasses...
def Row.pick2 : {schema : @Schema η} → Row schema → (cs : List (CertifiedName schema)) → Row (Schema.pick schema cs)
| _, Row.nil, [] => Row.nil
| _, Row.nil, (⟨c, h⟩::cs) => absurd h (by cases h)
| _, Row.cons cell rs, [] => Row.nil
| (s::ss), Row.cons cell rs, (c::cs) =>
  -- FIXME: how do we tell Lean to just "go look it up!"?? (We can't require the gettable instance in the col header --
  -- if we could figure this out, we could do away with a bunch of this typeclass nonsense!)
  have h := schemaHasLookup (s::ss) c;
  have inst : Gettable h := sorry
  Row.cons (@getCell _ _ (s::ss)
                     (Schema.lookup (s::ss) c).snd
                     (Row.cons cell rs)
                     (Schema.lookup (s::ss) c).fst
                     h
                     inst)
           (pick2 (Row.cons cell rs) cs)
termination_by Row.pick2 r cs => List.length cs

def selectColumnsH (t : Table schema) (cs : List {c : η // schema.HasName c}) [Pickable cs] : Table (Schema.pick schema cs) :=
  {rows := t.rows.map (λ r => r.pick cs)}

def completeCases {τ} (t : Table schema) (c : {c : η // schema.HasCol (c, τ)}) [Gettable c.property] :=
  List.map (λ v => Option.isSome v) (getColumn t c.val c.property)

def Row.hasEmpty {schema : @Schema η} : Row schema → Bool
| Row.nil => false
| Row.cons Cell.emp _ => true
| Row.cons _ r' => hasEmpty r'

def dropna (t : Table schema) : Table schema :=
  {rows := t.rows.filter (λ r => r.hasEmpty)}

-- TODO: this should work, but type class resolution is failing for some reason
-- def dropna' (t : Table schema) : Table schema :=
--   {rows := (schema.certify.map (λ ⟨(c, τ), h⟩ =>
--     @completeCases _ _ _ τ t ⟨c, h⟩ _)).foldl (λ l acc => sorry)
--   }

-- TODO: any way to avoid type classes?
class Settable {c τ} (h : Schema.HasCol (c, τ) schema) where
  setp : Row schema → (Cell c τ) → Row schema

-- Head instance
instance {c τ}: @Settable η dec_η ((c,τ)::schema) c τ (@Schema.HasCol.hd η c τ schema) :=
  {setp := λ (Row.cons _ rs) cell => Row.cons cell rs}

-- Tail instance
instance {c τ h r} [cls : Settable h] : @Settable η dec_η (r::schema) c τ (Schema.HasCol.tl h) :=
  {setp := λ (Row.cons c rs) newCell => Row.cons c (cls.setp h rs newCell)}

-- def get_from_proof {schema : @Schema η} {c : η} {τ : Type u}
--     : Schema.HasCol (c, τ) schema → Row schema → Option τ
-- | Schema.HasCol.hd, Row.cons cell cells => cell.toOption
-- | Schema.HasCol.tl h, Row.cons cell cells => get_from_proof h cells

theorem get_with_lookup_should_work {c : η} {τ : Type u} {xs : List (@Header η)}
  {h : Schema.HasName c ((c, τ) :: xs)} : (Schema.lookup ((c, τ) :: xs) ⟨c, h⟩).snd = τ := by
  simp [Schema.lookup, Prod.snd]

def get_with_lookup {schema : @Schema η} {c : η}
    : (h : Schema.HasName c schema) → (r : Row schema) → Option (schema.lookup ⟨c, h⟩).snd
| Schema.HasName.hd, @Row.cons _ _ _ τ rest cell cells =>
    have _ : (Schema.lookup ((c, τ) :: rest) ⟨c, _⟩).snd = τ := by apply get_with_lookup_should_work;
    (cell.toOption : Option τ)
| Schema.HasName.tl h, Row.cons cell cells => get_with_lookup h cells

-- def set_from_proof {schema : @Schema η} {c : η} {τ : Type u}
--     : Schema.HasCol (c, τ) schema → Row schema → Cell c τ → Row schema
-- | Schema.HasCol.hd, Row.cons cell cells, newCell => Row.cons newCell cells
-- | Schema.HasCol.tl h, Row.cons cell cells, newCell => Row.cons cell (set_from_proof h cells newCell)

def setCell {τ}
            (r : Row schema)
            (c : η)
            (h : schema.HasCol (c, τ))
            (cell : Cell c τ)
            [inst : Settable h]
    : Row schema := inst.setp h r cell

-- FIXME: finish
-- def update {schema₁ : @Schema η}
--            {schema₂ : Subschema schema₁}
--            (t : Table schema₁)
--            (f : Row schema₁ → Row schema₂.toSchema) : Table schema₁ :=
--   {rows := t.rows.map (λ r =>
--     let newCells := f r;
--     newCells.foldr (λ c (acc : Row schema₁) => @setCell _ _ _ c.type acc c.name sorry c _) r
--   )}

-- -- FIXME: finish - dep = update
-- def fillna {τ}
--            (t : Table schema)
--            (c : {c : η // schema.HasCol (c, τ)})
--            (v : τ)
--     : Table schema :=
--   {rows := update t (λ r => match getCell r c with
--                             | Cell.emp => _) }

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

-- def flatten (t : Table schema) (cs : List {c : η // schema.HasName c}) : Table _ := sorry

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

-- def Row.removeNamedCols2 : {schema : @Schema η} → (cs : List (CertifiedName schema)) → Row schema → Row (schema.removeNames (cs.map Subtype.val))
-- | _, [], Row.nil => Row.nil
-- | _, (⟨c, h⟩::cs), Row.nil => absurd h (by cases h)
-- | _, [], Row.cons cell rs => Row.cons cell rs
-- | (s::ss), (c::cs), Row.cons cell rs =>
--   have h : Schema.HasCol ((Schema.lookup (s::ss) c).fst, (Schema.lookup (s::ss) c).snd) ss := _;
--   -- TODO: how do we tell Lean to just "go look it up!"??
--   have _ : Gettable h := _;
--   @removeNamedCols2 (schema.removeName c.val) cs (removeNamedCol c (Row.cons cell rs))
--   -- Row.cons (getCell rs (Schema.lookup (s::ss) c).fst h) (pick2 cs (Row.cons cell rs))

-- -- TODO: require that c1, c2 
-- def pivotLonger {τ}
--                 (t : Table schema)
--                 (cs : List {c : η // Schema.HasCol (c, τ) schema})
--                 (c1 : η)
--                 (c2 : η)
--     -- FIXME: need to remove the old columns from schema!!!
--     : Table (List.append (schema.removeNames (cs.map (λc => c.val))) [(c1, η), (c2, τ)]) :=
--   selectMany t
--     (λ r _ =>
--       values (cs.map (λ (c : {c : η // Schema.HasCol (c, τ) schema}) =>
--         have _ : Gettable c.property := _;
--         Row.cons (Cell.val c)
--           (Row.cons (getCell r c.val c.property) Row.nil)
--       )))
--     (λ (r₁ : Row schema) (r₂ : Row [(c1, η), (c2, τ)]) =>
--       -- TODO: what?
--       have _ : Pickable _ := _;
--       -- have cnames : List {c : η // Schema.HasName c schema} := cs.map (λ (⟨c, h⟩ : {c : η // Schema.HasCol (c, τ) schema})
--         -- => ⟨c, schema.colImpliesName h⟩);
--       let cnames : List η := cs.map Subtype.val;
--       let remainingHeaders := (schema.certify.filter
--                       (λ (⟨(c, τ), h⟩ : CertifiedHeader schema) => not (cnames.elem c))
--                   );
--       let remainingNames : List (CertifiedName schema) := remainingHeaders.map (λ (⟨(c, _), h⟩ : CertifiedHeader schema) => ⟨c, Schema.colImpliesName h⟩);
--       -- TODO: maybe we could have some sort of "Row.removeColumns" that
--       -- produces a row with the correct schema type by construction?
--       let remainingCells := r₁.pick remainingNames;
--       Row.append remainingCells r₂)

-- def pivotWider [inst : Inhabited η]
--                (t : Table schema)
--                (c1 c2 : CertifiedHeader schema)
--                [Gettable c1.property]  -- TODO: This really shouldn't be necessary
--     : Table (List.append schema (t.rows.map (λ r =>
--               (Option.orDefault (getValue r c1.val c1.property), η)
--             ))) := sorry

