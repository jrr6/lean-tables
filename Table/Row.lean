import Table.Cell
import Table.Schema
import Table.SchemaFunctions

universe u u_η

inductive Row {η : Type u_η} [DecidableEq η]
    : @Schema η → Type (max u_η (u + 1))
| nil : Row []
| cons {name : η} {τ : Type u} {hs : Schema} :
    Cell name τ → Row hs → Row ((name, τ) :: hs)

-- Schema accessor -- need to declare before variable
def Row.schema {η : Type u_η} [DecidableEq η] {schema : @Schema η}
               (r : Row schema) := schema

variable {η : Type u_η} [dec_η : DecidableEq η] {schema : @Schema η}

-- Row utilities
def Row.singleCell {name : η} {τ} (c : Cell name τ) :=
  @Row.cons η dec_η name τ [] c Row.nil

def Row.singleValue {name τ} (x : τ) :=
  @Row.cons η dec_η name τ [] (Cell.val x) Row.nil

def Row.empty : (schema : @Schema η) → Row schema
| [] => Row.nil
| _ :: ss => Row.cons Cell.emp (empty ss)

def Row.append {schema₁ schema₂} :
    @Row η _ schema₁ → Row schema₂ → Row (Schema.append schema₁ schema₂)
| Row.nil, rs₂ => rs₂
| Row.cons r₁ rs₁, rs₂ => Row.cons r₁ (append rs₁ rs₂)

def Row.map {schema} (f : ∀ n α, Cell n α → @Cell η dec_η n α)
    : Row schema → @Row η dec_η schema
| Row.nil => Row.nil
| @Row.cons _ _ n τ _ r₁ rs₁ => Row.cons (f n τ r₁) (map f rs₁)

def Row.mapHet {schema} (F : Type _ → Type _)
    (f : ∀ n α, Cell n α → @Cell η dec_η n (F α))
    : Row schema → @Row η dec_η (Schema.map (λ (nm, τ) => (nm, F τ)) schema)
| Row.nil => Row.nil
| @Row.cons _ _ n τ _ r₁ rs₁ => Row.cons (f n τ r₁) (mapHet F f rs₁)

def Row.foldr {β} {schema : @Schema η}
              (f : ∀ {nm α}, @Cell η dec_η nm α → β → β)
              (z  : β)
    : Row schema → β
| Row.nil => z
| Row.cons cell rs => f cell (foldr f z rs)

def Row.certifiedFoldr {β} : {schema : @Schema η} →
              (f : ∀ {nm α}, (@Cell η dec_η nm α) →
              (schema.HasCol (nm, α)) → β → β) →
              (z  : β) →
    Row schema → β
| [], _, z, Row.nil => z
| (c, τ)::ss, f, z, @Row.cons _ _ _ _ _ cell rs =>
  f cell Schema.HasCol.hd (@certifiedFoldr β ss (λ {nm α} cell' h acc =>
    f cell' (Schema.HasCol.tl h) acc
  ) z rs)

-- It seems like B2T2 implicitly wants a bunch of row operations that just
-- happen to be identical to table operations in their TS implementation. We
-- manually reimplement them here.
def Row.addColumn {η} [DecidableEq η] {schema : @Schema η} {τ}
                  (r : Row schema) (c : η) (v : Option τ) :
    Row (Schema.append schema [(c, τ)]) :=
Row.append r (Row.singleCell $ Cell.fromOption v)

def Row.toList {schema : @Schema η} {α} (f : ∀ {n β}, @Cell η dec_η n β → α)
    : Row schema → List α
| Row.nil => []
| Row.cons c rs => f c :: toList f rs

def Row.hasEmpty {schema : @Schema η} : Row schema → Bool
| Row.nil => false
| Row.cons Cell.emp _ => true
| Row.cons _ r' => hasEmpty r'

def Row.length {schema : @Schema η} : Row schema → Nat
| Row.nil => 0
| Row.cons _ r' => r'.length + 1

def Row.sieve {schema} :
    (bs : List Bool) → Row schema → @Row η dec_η (Schema.sieve bs schema)
| [], Row.nil => Row.nil
| [], Row.cons r rs => Row.cons r rs
| true :: bs, Row.nil => Row.nil
| false :: bs, Row.nil => Row.nil
| true :: bs, Row.cons r rs => Row.cons r (sieve bs rs)
| false :: bs, Row.cons r rs => sieve bs rs

def Row.nth {schema} : (rs : @Row η dec_η schema) →
                       (n : Nat) →
                       (h : n < Schema.length schema) →
                       let (nm, τ) := Schema.nth schema n h;
                       @Cell η dec_η nm τ
| Row.nil, _, h => absurd h (by intro nh; cases nh)
| Row.cons r rs, 0, h => r
| Row.cons r rs, Nat.succ n, h => nth rs n (Nat.le_of_succ_le_succ h)

def Row.nths {schema} :
    (ns : List (Fin $ Schema.length schema))
      → Row schema
      → @Row η dec_η (Schema.nths schema ns)
| [], Row.nil => Row.nil
| [], Row.cons x xs => Row.nil
| n::ns, Row.nil => nomatch n.2
| n::ns, r => Row.cons (Row.nth r n.val n.2) (nths ns r)

def Row.getCell {schema : @Schema η} {c : η} {τ : Type u}
    : Row schema → Schema.HasCol (c, τ) schema → Cell c τ
| Row.cons cell cells, Schema.HasCol.hd => cell
| Row.cons cell cells, Schema.HasCol.tl h => getCell cells h

def Row.setCell {schema : @Schema η} {τ : Type u} {c : η}
    : Row schema → Schema.HasCol (c, τ) schema → Cell c τ → Row schema
| Row.cons cell cells, Schema.HasCol.hd, newCell => Row.cons newCell cells
| Row.cons cell cells, Schema.HasCol.tl h, newCell =>
    Row.cons cell (setCell cells h newCell)

def Row.retypeCell {schema : @Schema η} {τ₁ τ₂ : Type u} {c : η}
    : Row schema → (h : Schema.HasCol (c, τ₁) schema) → Cell c τ₂
      → Row (schema.retypeColumn (Schema.colImpliesName h) τ₂)
| Row.cons cell cells, Schema.HasCol.hd, newCell => Row.cons newCell cells
| Row.cons cell cells, Schema.HasCol.tl h, newCell =>
    Row.cons cell (retypeCell cells h newCell)

def Row.retypeCellByName {schema : @Schema η} {c : η}
    : Row schema → (h : Schema.HasName c schema) → Cell c τ₂
      → Row (schema.retypeColumn h τ₂)
| Row.cons cell cells, Schema.HasName.hd, newCell => Row.cons newCell cells
| Row.cons cell cells, Schema.HasName.tl h, newCell =>
    Row.cons cell (retypeCellByName cells h newCell)

def Row.renameCell {schema : @Schema η} {c : η}
    : Row schema → (h : Schema.HasName c schema) → (c' : η)
      → Row (schema.renameColumn h c')
| Row.cons cell cells, Schema.HasName.hd, nm' =>
  Row.cons (cell.rename nm') cells
| Row.cons cell cells, Schema.HasName.tl h, nm' =>
  Row.cons cell (renameCell cells h nm')

def Row.renameCells {schema : @Schema η}
    : (cs : ActionList Schema.renameColumnCN schema) →
      Row schema →
      Row (schema.renameColumns cs)
| ActionList.nil, r => r
| ActionList.cons c cs, r => renameCells cs (renameCell r c.2 c.1.2)

def Row.pick {schema : @Schema η} :
               Row schema →
               (cs : List (CertifiedHeader schema)) →
               Row (Schema.fromCHeaders cs)
| r, [] => Row.nil
| r, (c::cs) => Row.cons (Row.getCell r c.2) (pick r cs)

def Row.isSubRow : {schema : @Schema η} →
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
decreasing_by assumption

def Row.removeColumn {s : Schema} {c : η} :
    (h : s.HasName c) → Row s → Row (s.removeName h)
| Schema.HasName.hd, Row.cons r rs => rs
| Schema.HasName.tl h',Row.cons r rs => Row.cons r (removeColumn h' rs)

def Row.removeColumns {s : @Schema η} :
    (cs : ActionList Schema.removeCertifiedName s) →
    Row s →
    Row (s.removeNames cs)
| .nil, r => r
| .cons c cs, r => removeColumns cs (removeColumn c.2 r)

def Row.removeColumnsHeaders {s : @Schema η} :
    (cs : ActionList Schema.removeCertifiedHeader s) →
    Row s →
    Row (s.removeHeaders cs)
| .nil, r => r
| .cons c cs, r => removeColumnsHeaders cs $
                    removeColumn (Schema.colImpliesName c.2) r

def Row.removeTypedColumns {s : @Schema η} {τ : Type u} :
    (cs : ActionList (Schema.removeTypedName τ) s) →
    Row s →
    Row (s.removeTypedNames cs)
| .nil, r => r
| .cons c cs, r => removeTypedColumns cs $
                    removeColumn (Schema.colImpliesName c.2) r

def Row.removeOtherSchemaCols {schema' schema : @Schema η} :
  (cs : ActionList (Schema.removeOtherDecCH schema') schema) →
  Row schema →
  Row (Schema.removeOtherDecCHs schema' schema cs)
| ActionList.nil, r => r
| ActionList.cons c cs, r =>
  removeOtherSchemaCols cs (r.removeColumn $ Schema.colImpliesName c.2.2.1)

def Row.retypedSubschemaPres :
  ∀ {sch : @Schema η} {retNm : η} {τ : Type _} {hretNm : sch.HasName retNm}
    {rs : RetypedSubschema sch},
  Row (RetypedSubschema.toSchema rs) →
  Row (RetypedSubschema.toSchema (Schema.map (λ ⟨h, pf⟩ =>
    ⟨h, Schema.hasRetypedName (retNm := retNm) (τ := τ) (hretNm := hretNm) pf⟩
  ) rs))
| sch, retNm, τ, pf, [], Row.nil => Row.nil
| sch, retNm, τ, pf, ⟨(_, _), _⟩ :: _, Row.cons c cs =>
  have hterm : length cs < length (cons c cs) := Nat.lt_succ_self _
  Row.cons c $ retypedSubschemaPres cs
termination_by retypedSubschemaPres rs => rs.length

theorem Row.length_retypedSubschemaPres :
  ∀ {sch : @Schema η} {rs : RetypedSubschema sch}
  {retNm : η} {τ : Type _} {hretNm : sch.HasName retNm}
  (r : Row rs.toSchema),
  length (retypedSubschemaPres (retNm := retNm) (τ := τ) (hretNm := hretNm) r) =
  length r
| _, [], _, _, _, Row.nil => rfl
| _, ⟨(_, _), _⟩ :: _, _, _, _, Row.cons c r' =>
  have hterm : length r' < length (cons c r') := Nat.lt_succ_self _
  congrArg Nat.succ $ length_retypedSubschemaPres r'
termination_by length_retypedSubschemaPres r => r.length

-- Decidable equality
instance : DecidableEq (@Row η _ [])
| Row.nil, Row.nil => Decidable.isTrue rfl

instance {ss : @Schema η}
         {nm : η}
         {τ : Type u}
         [it : DecidableEq τ]
         [ic : DecidableEq (Cell nm τ)]
         [ir : DecidableEq (Row ss)]
    : DecidableEq (Row ((nm, τ) :: ss)) :=
λ (Row.cons c₁ r₁) (Row.cons c₂ r₂) =>
  let hc_dec : Decidable (c₁ = c₂) := ic _ _
  let hr_dec : Decidable (r₁ = r₂) := ir _ _
  let h_conj_dec : (Decidable (c₁ = c₂ ∧ r₁ = r₂)) := inferInstance
  congrArg Decidable (Row.cons.injEq c₁ r₁ c₂ r₂) ▸ h_conj_dec
