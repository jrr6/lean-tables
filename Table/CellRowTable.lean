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

def getCell {schema : @Schema η} {c : η} {τ : Type u}
    : Row schema → Schema.HasCol (c, τ) schema → Cell c τ
| Row.cons cell cells, Schema.HasCol.hd => cell
| Row.cons cell cells, Schema.HasCol.tl h => getCell cells h

def setCell {schema : @Schema η} {τ : Type u} {c : η}
    : Row schema → Schema.HasCol (c, τ) schema → Cell c τ → Row schema
| Row.cons cell cells, Schema.HasCol.hd, newCell => Row.cons newCell cells
| Row.cons cell cells, Schema.HasCol.tl h, newCell => Row.cons cell (setCell cells h newCell)

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

def getColumnIndex (t : Table schema)
                   (n : Nat)
                   (h : n < ncols t) :=
  List.map (λr => List.nth _ n h) t.rows

def getColumn {τ}
              (t : Table schema)
              (c : η)
              (h : Schema.HasCol (c, τ) schema)
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

def schemaHasLookup' : (schema : @Schema η) → (c : CertifiedName schema)
    → schema.HasCol (schema.lookup c)
| _, ⟨_, Schema.HasName.hd⟩ => Schema.HasCol.hd
| s, ⟨c, Schema.HasName.tl h⟩ => schemaHasLookup s ⟨c, h⟩

def schemaHasLookup : (schema : @Schema η) → (c : CertifiedName schema)
    → schema.HasCol ((schema.lookup c).fst, (schema.lookup c).snd)
| [], ⟨_, h⟩ => by cases h
| (nm, τ) :: ss, ⟨n, h⟩ =>
  let ih := schemaHasLookup ss;
  dite (nm = n)
       (λ htrue => by simp [Schema.lookup, htrue]; apply Schema.HasCol.hd)
      --  (λ hfalse => sorry)
      --  (λ htrue => @Schema.HasCol.hd _ (Eq.rec _ htrue) _ _)
      --  (λ hfalse => Schema.HasCol.tl)
      --  (λ htrue => by simp [Schema.lookup, htrue]
      --                 apply Schema.HasCol.hd)

      --  (λ hfalse => match ih ⟨n, (by cases h with
      --                                | hd => contradiction
      --                                | tl h' => exact h')⟩ with
      --               | Schema.HasCol.hd => x)

      (λ hfalse =>
      --   -- This is the issue with not having proof-irrelevance -- it wants the
      --   -- *same `h`!*
      --   let ih := ih ⟨n, by cases h with
      --                     | hd => contradiction
      --                     | tl h' => exact h'⟩;
      --   ih.rec sorry sorry)
        by simp [Schema.lookup, hfalse, Prod.fst, Prod.snd]
           apply Schema.HasCol.tl
           apply ih
        )
    --  (λ hfalse => by simp [Schema.lookup, hfalse, Prod.fst, Prod.snd]
    --  apply Schema.HasCol.tl
    --  apply ih)
-- termination_by schemaHasLookup schema c => List.length schema
#eval schemaHasLookup [("hi", Nat)] ⟨"hi", by name⟩
-- := by
--   intros schema c
--   induction schema with
--   | nil => cases c with | mk val prop => cases prop
--   -- TODO: Is there a better syntax?
--   | cons s ss ih => cases c with | mk val prop => cases s with | mk c τ =>
--     simp [Schema.lookup]
--     -- Can't use cases with Decidable.em because it doesn't like Type
--     apply dite (c = val)
--     . intro h
--       simp [ite, h]
--       apply Schema.HasCol.hd
--     . intro h
--       simp [ite, h, Prod.fst, Prod.snd]
--       apply Schema.HasCol.tl
--       apply ih

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

def selectColumnsH (t : Table schema) (cs : List (CertifiedName schema)) : Table (Schema.pick schema cs) :=
  {rows := t.rows.map (λ r => r.pick cs)}

def completeCases {τ} (t : Table schema) (c : ((c : η) × schema.HasCol (c, τ))) :=
  List.map (λ v => Option.isSome v) (getColumn t c.fst c.snd)

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

-- FIXME: without uniqueness of names, this can't be proven (schema₁ might have
-- (nm, τ) and (nm, τ') too) -- I think...
theorem schemaHasSubschema {nm τ}
                           {schema₁ : @Schema η}
                           {schema₂ : Subschema schema₁}
                           (h : schema₂.toSchema.HasCol (nm, τ))
    : schema₁.HasCol (nm, τ) := by
  induction schema₂ with
  | nil => cases h
  | cons phdr phdrs ih =>
    cases phdr with | mk hdr hdr_pf =>
    cases hdr with | mk nm' τ' =>
    simp only [Subschema.toSchema] at h
    apply dite (nm = nm')
    -- Head case (painful, terrible)
    . intro heq
      rw [←heq] at hdr_pf
      simp only at hdr_pf
      -- TODO: :(
      -- DON'T want IH -- it's at the head (hdr_pf should be what we want)
      induction schema₁ with
      | nil => contradiction
      | cons s ss ih₁ =>
        cases s with | mk nm₁ τ₁ =>
        apply dite (nm = nm₁)
        -- Head case schema₁
        . intro heq₁
          simp at *
          apply ih
        -- Tail case schema₁
        . intro hneq₁
          cases h with
          | hd => apply hdr_pf
          | tl h' => apply ih h'
    -- Tail case (easy)
    . intro hneq
      cases h with
      | hd => apply hdr_pf
      | tl h' => apply ih h'
    

-- FIXME: finish
def update {schema₁ : @Schema η}
           {schema₂ : Subschema schema₁}
           (t : Table schema₁)
           (f : Row schema₁ → Row schema₂.toSchema) : Table schema₁ :=
  {rows := t.rows.map (λ r =>
    let newCells : Row schema₂.toSchema := f r;
    newCells.certifiedFoldr
      (λ {nm τ}
         (cell : Cell nm τ)
         (h : schema₂.toSchema.HasCol (nm, τ))
         (acc : Row schema₁) => @setCell _ _ _ cell.type cell.name acc (by
          clear newCells f
          simp [Cell.name, Cell.type]
          simp [Subschema.toSchema] at h
          induction schema₂ with
          | nil => cases h
          | cons phdr phdrs ih =>
            cases phdr with
            -- cases hdr_w_pf with | mk hdr hyp => cases hdr with | mk nm' τ' =>
            simp [Subschema.toSchema, List.map] at h
            let l := Decidable.em (hdr_w_pf.fst = nm)
         ) cell)
      r
    -- newCells.certifiedFoldr (λ c (acc : Row schema₁) => @setCell _ _ _ c.type c.name acc sorry c) r
    --@setCell _ _ _ c.type acc c.name sorry c _) r
  )}

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

