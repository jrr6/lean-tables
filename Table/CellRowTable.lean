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

def header (t : Table schema) : List η := Schema.names schema

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

def tfilter (t : Table schema) (f : Row schema → Bool) : Table schema :=
{rows := t.rows.filter f}

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

def groupBy {schema' : @Schema η}
            (t : Table schema)
            (key : Row schema → κ)
            (project : Row schema → ν)
            (aggregate : κ → List ν → Row schema')
    : Table schema' := sorry

-- def flatten (t : Table schema) (cs : List {c : η // schema.HasName c}) : Table _ := sorry

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
        : (t : Table ((nm, τ) :: ss)) → (r : Row ((nm, τ) :: ss)) → Option Nat
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

