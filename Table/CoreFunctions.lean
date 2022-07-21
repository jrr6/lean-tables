import Table.CoreTypes
import Table.BuiltinExtensions

universe u_η
universe u

-- Schema accessor -- need to declare before variable
def Row.schema {η : Type u_η} [DecidableEq η] {schema : @Schema η}
               (r : Row schema) := schema

variable {η : Type u_η} [dec_η : DecidableEq η] {schema : @Schema η}

-- For ease of refactoring, makes these products act like subtypes
def CertifiedName.val (n : CertifiedName schema) := Sigma.fst n
def CertifiedName.property (n : CertifiedName schema) := Sigma.snd n
def CertifiedHeader.val (h : CertifiedHeader schema) := Sigma.fst h
def CertifiedHeader.property (h : CertifiedHeader schema) := Sigma.snd h

-- Cell accessor and conversion functions
def Cell.toOption {nm τ} : @Cell η dec_η nm τ → Option τ
| Cell.emp => Option.none
| Cell.val x => Option.some x

def Cell.fromOption {nm τ} : Option τ → @Cell η dec_η nm τ
| none => emp
| some x => val x

def Cell.name {nm τ} (_ : @Cell η dec_η nm τ) : η :=
  nm
def Cell.type {nm τ} (_ : @Cell η dec_η nm τ) := τ

-- This will make proofs difficult
-- def Subschema.toSchema {schm : @Schema η} (s : Subschema schm) : @Schema η := 
--   s.map (λ x => x.fst)

def Subschema.toSchema {schm : @Schema η} : Subschema schm → @Schema η
| [] => []
| ⟨hdr, _⟩ :: ss => hdr :: toSchema ss

def Schema.fromCHeaders {schema : @Schema η} (cs : List (CertifiedHeader schema)) :
  @Schema η := cs.map Sigma.fst

def Schema.HasCol.size : {schema : @Schema η} →
                         {hdr : @Header η} →
                         schema.HasCol hdr →
                         Nat
| _, _, Schema.HasCol.hd => 0
| _, _, Schema.HasCol.tl h => 1 + size h

-- Schema proof generation/manipulation functions
def Schema.certify (schema : @Schema η) : List (CertifiedHeader schema) :=
  let rec certify_elts : (subschm : @Schema η) → List (CertifiedHeader subschm)
    | [] => []
    | (c, τ) :: hs =>
      let map_subproof :=
        λ (⟨hdr, h⟩ : CertifiedHeader hs) => ⟨hdr, Schema.HasCol.tl h⟩;
      ⟨(c, τ), Schema.HasCol.hd⟩ :: (certify_elts hs).map map_subproof;
  certify_elts schema

def Schema.colImpliesName :
      {schema : @Schema η} →
      {c : η} →
      {τ : Type u} →
      schema.HasCol (c, τ) → schema.HasName c
| h :: hs, _, _, HasCol.hd => HasName.hd
| h :: hs, c, τ, HasCol.tl p => HasName.tl (colImpliesName p)
-- Can also be done in tactic mode:
-- | h :: hs, c, τ, p => by
--     cases p with
--     | hd => apply HasName.hd
--     | tl a => apply HasName.tl (colImpliesName a)

def Schema.certifyNames (schema : @Schema η) : List (CertifiedName schema) :=
  schema.certify.map (λ (⟨(c, _), h⟩ : CertifiedHeader schema) =>
                        ⟨c, colImpliesName h⟩)

def Schema.hasNameOfAppend : {sch : @Schema η} →
                                 {nm : η} →
                                 {hs : List Header} →
                                 sch.HasName nm →
  Schema.HasName nm (sch.append hs)
| _, _, _, Schema.HasName.hd => Schema.HasName.hd
| _, _, _, Schema.HasName.tl h => Schema.HasName.tl $ hasNameOfAppend h

-- Schema functions
def Schema.names {η : Type u_η} := List.map (@Prod.fst η (Type u))

-- TODO: when we come back to do uniqueness, this might be helpful
-- def Schema.removeName :
--     (s : @Schema η) → {c : η // s.HasName c} → @Schema η
/-
dite (c = nm)
       (λ _ => xs)
       (λ nh => (nm, τ) :: removeName xs ⟨c, by
        cases h with
        | hd => simp at nh
        | tl tl_h => apply tl_h
        ⟩)
-/

-- Doesn't work b/c we can't definitionally equate conditionals with their
-- evaluation, even when the equality is tautological
-- def Schema.removeName :
--     (s : @Schema η) → η → @Schema η
-- | [], _ => []
-- | (nm, τ)::xs, c => if c = nm then xs else (nm, τ) :: removeName xs c

def Schema.removeName {c : η} :
    (s : @Schema η) → (v_nm : s.HasName c) → @Schema η
| _::s, Schema.HasName.hd => s
| s::ss, Schema.HasName.tl h => s :: removeName ss h

theorem Schema.removeName_eq_1 {η : Type u_η} [DecidableEq η]
  {c : η} (hdr : @Header η) (ss : @Schema η) :
  removeName (hdr :: ss) Schema.HasName.hd = ss := rfl

theorem Schema.removeName_eq_2 {η : Type u_η} [DecidableEq η]
  {c : η} (hdr : @Header η) (ss : @Schema η)
  (h : Schema.HasName c ss) :
  removeName (hdr :: ss) (Schema.HasName.tl h) = hdr :: removeName ss h := rfl

def Schema.removeCertifiedName (s : @Schema η) (cn : CertifiedName s) :=
  removeName s cn.2

def Schema.removeCNPres_aux : {schema : @Schema η} →
                              {nm : η} →
                              {n : schema.HasName nm} →
                              {nm' : η} →
                              Schema.HasName nm' (schema.removeName n) →
                              Schema.HasName nm' schema
| _ :: _, nm, Schema.HasName.hd, nm', pf => Schema.HasName.tl pf
| (nm', τ) :: ss, nm, Schema.HasName.tl h, _, Schema.HasName.hd =>
  Schema.HasName.hd
| s :: ss, nm, Schema.HasName.tl h, nm', Schema.HasName.tl h' =>
  let ih := @removeCNPres_aux _ nm h nm' h'
  Schema.HasName.tl ih

def Schema.removeCNPres {schema : @Schema η} {nm} {n : schema.HasName nm}
                        (cn : CertifiedName $ schema.removeName n)
    : CertifiedName schema
  := ⟨cn.1, removeCNPres_aux cn.2⟩

def Schema.removeNames {η : Type u_η} [DecidableEq η] :
    (s : @Schema η) → ActionList removeCertifiedName s → @Schema η
| ss, ActionList.nil => ss
| ss, ActionList.cons cn rest => removeNames (removeName ss cn.2) rest

-- Same problem yet again
def Schema.flattenList : (schema : @Schema η) →
                         ((c : η) × (τ : Type u) × schema.HasCol (c, List τ)) →
                         @Schema η
| (_, _) :: ss, ⟨nm, τ, Schema.HasCol.hd⟩ => (nm, τ) :: ss
| hdr :: ss, ⟨nm, τ, Schema.HasCol.tl h⟩ => hdr :: flattenList ss ⟨nm, τ, h⟩

def Schema.flattenLists : (schema : @Schema η) →
                          (ActionList flattenList schema) →
                         @Schema η
| ss, ActionList.nil => ss
| ss, ActionList.cons c cs => flattenLists (flattenList ss c) cs

-- Returns the schema entry with the specified name
def Schema.lookup {η : Type u_η} [DecidableEq η]
    : (s : @Schema η) → CertifiedName s → @Header η
| hdr :: _, ⟨_, Schema.HasName.hd⟩ => hdr
| _ :: hs, ⟨c, Schema.HasName.tl h'⟩ => lookup hs ⟨c, h'⟩

-- TODO: figure out what's going on here -- these should be auto-generated
-- (also the field syntax isn't working, so using underscores instead)
theorem Schema.lookup_eq_1 {η : Type u_η} [DecidableEq η]
  (hdr : @Header η) (hs : @Schema η) :
  lookup (hdr :: hs) ⟨hdr.1, HasName.hd⟩ = hdr := rfl

theorem Schema.lookup_eq_2 {η : Type u_η} [DecidableEq η]
  (hd : @Header η) (tl : @Schema η) (c : η) {h : Schema.HasName c tl} :
  lookup (hd :: tl) ⟨c, HasName.tl h⟩ = lookup tl ⟨c, h⟩ := rfl

def Schema.pick {η : Type u_η} [DecidableEq η] (s : @Schema η)
    : List (CertifiedName s) → @Schema η
| [] => []
| c::cs => lookup s c :: pick s cs

def Schema.retypeColumn {η : Type u_η} [DecidableEq η]
    : {nm : η} → (s : @Schema η) → s.HasName nm → Type u → @Schema η
| _, (nm, τ) :: cs, Schema.HasName.hd, τ' => (nm, τ') :: cs
| _, c :: cs, Schema.HasName.tl h, τ' => c :: retypeColumn cs h τ'

def Schema.renameColumn {η : Type u_η} [DecidableEq η]
    : {nm : η} → (s : @Schema η) → s.HasName nm → η → @Schema η
| _, (nm, τ) :: cs, Schema.HasName.hd, nm' => (nm', τ) :: cs
| _, c :: cs, Schema.HasName.tl h, nm' => c :: renameColumn cs h nm'

def Schema.renameColumnCN {η : Type u_η} [DecidableEq η]
                          (s : @Schema η) (entry : CertifiedName s × η)
    : @Schema η :=
  renameColumn s entry.1.2 entry.2

def Schema.renameColumns {η : Type u_η} [DecidableEq η]
    : (s : @Schema η) → ActionList renameColumnCN s → @Schema η
| s, ActionList.nil => []
| s, ActionList.cons c ccs => renameColumns (renameColumnCN s c) ccs

theorem Schema.removeName_sublist :
  ∀ (s : @Schema η) (c : η) (hc : HasName c s),
    List.Sublist (s.removeName hc) s
| _, _, HasName.hd => List.Sublist.cons _ _ _ (List.sublist_self _)
| _, _, HasName.tl h => List.Sublist.cons2 _ _ _ (removeName_sublist _ _ h)

theorem Schema.lookup_fst_eq_nm :
  ∀ (sch : @Schema η) (c : CertifiedName sch),
    (Schema.lookup sch c).fst = c.val
| s :: ss, ⟨_, HasName.hd⟩ => rfl
| s :: ss, ⟨c, HasName.tl h⟩ => lookup_fst_eq_nm ss ⟨c, h⟩

theorem Schema.lookup_eq_lookup_append :
  ∀ (s : @Schema η) (t : @Schema η) (c : η) (h : s.HasName c),
  lookup s ⟨c, h⟩ = lookup (s.append t) ⟨c, Schema.hasNameOfAppend h⟩ :=
by intros s t c h
   induction h with
   | hd =>
     simp only [Schema.hasNameOfAppend, List.append]
     rw [Schema.lookup_eq_1, Schema.lookup_eq_1]
   | tl h' ih =>
     simp only [Schema.hasNameOfAppend, List.append]
     rw [Schema.lookup_eq_2, Schema.lookup_eq_2]
     exact ih

def Schema.schemaHasLookup : (schema : @Schema η) → (c : CertifiedName schema)
    → schema.HasCol (schema.lookup c)
| _, ⟨_, Schema.HasName.hd⟩ => Schema.HasCol.hd
| _ :: s', ⟨c, Schema.HasName.tl h⟩ => Schema.HasCol.tl (schemaHasLookup s' ⟨c, h⟩)

def Schema.schemaHasSubschema : {nm : η} → {τ : Type u} →
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

-- Row utilities
def Row.singleCell {name : η} {τ} (c : Cell name τ) :=
  @Row.cons η dec_η name τ [] c Row.nil

def Row.singleValue {name τ} (x : τ) :=
  @Row.cons η dec_η name τ [] (Cell.val x) Row.nil

def Row.empty : (schema : @Schema η) → Row schema
| [] => Row.nil
| _ :: ss => Row.cons Cell.emp (empty ss)

def Row.append {schema₁ schema₂} :
    @Row η _ schema₁ → Row schema₂ → Row (List.append schema₁ schema₂)
| Row.nil, rs₂ => rs₂
| Row.cons r₁ rs₁, rs₂ => Row.cons r₁ (append rs₁ rs₂)

def Row.map {schema} (f : ∀ n α, Cell n α → @Cell η dec_η n α)
    : Row schema → @Row η dec_η schema
| Row.nil => Row.nil
| @Row.cons _ _ n τ _ r₁ rs₁ => Row.cons (f n τ r₁) (map f rs₁)

def Row.foldr {β} {schema : @Schema η}
              (f : ∀ {nm α}, @Cell η dec_η nm α → β → β)
              (z  : β)
    : Row schema → β
| Row.nil => z
| Row.cons cell rs => f cell (foldr f z rs)

def Row.certifiedFoldr {β} : {schema : @Schema η} →
              (f : ∀ {nm α}, (@Cell η dec_η nm α) → (schema.HasCol (nm, α)) → β → β) →
              (z  : β) →
    Row schema → β
| [], _, z, Row.nil => z
| (c, τ)::ss, f, z, @Row.cons _ _ _ _ _ cell rs => 
  f cell Schema.HasCol.hd (@certifiedFoldr β ss (λ {nm α} cell' h acc =>
    f cell' (Schema.HasCol.tl h) acc
  ) z rs)

-- TODO: seems like B2T2 implicitly wants a bunch of row operations that just
-- happen to be identical to table operations in their TS implementation
def Row.addColumn {η} [DecidableEq η] {schema : @Schema η} {τ}
                  (r : Row schema) (c : η) (v : Option τ) :
    Row (List.append schema [(c, τ)]) :=
Row.append r (Row.singleCell $ Cell.fromOption v)

-- Not sure if we'll ever need this...
def Row.toList {schema : @Schema η} {α} (f : ∀ {n β}, @Cell η dec_η n β → α)
    : Row schema → List α
| Row.nil => []
| Row.cons c rs => f c :: toList f rs

def Row.hasEmpty {schema : @Schema η} : Row schema → Bool
| Row.nil => false
| Row.cons Cell.emp _ => true
| Row.cons _ r' => hasEmpty r'

-- TODO: probably makes more sense to move this to some general "collection"
-- interface rather than reimplementing for every type -- wonder if this is
-- something James is working on
-- It would also be nice if we could make this function less verbose.
-- Unfortunately, Lean's type-checker needs some help...
def Row.sieve {schema} :
    (bs : List Bool) → Row schema → @Row η dec_η (List.sieve bs schema)
| [], Row.nil => Row.nil
| [], Row.cons r rs => Row.cons r rs
| true :: bs, Row.nil => Row.nil
| false :: bs, Row.nil => Row.nil
| true :: bs, Row.cons r rs => Row.cons r (sieve bs rs)
| false :: bs, Row.cons r rs => sieve bs rs

def Row.nth {schema} : (rs : @Row η dec_η schema) →
                       (n : Nat) →
                       (h : n < List.length schema) →
                       let (nm, τ) := List.nth schema n h;
                       @Cell η dec_η nm τ
| Row.nil, _, h => absurd h (by intro nh; cases nh)
| Row.cons r rs, 0, h => r
| Row.cons r rs, Nat.succ n, h => nth rs n (Nat.le_of_succ_le_succ h)

def Row.nths {schema} :
    (ns : List {n : Nat // n < List.length schema})
      → Row schema
      → @Row η dec_η (List.nths schema ns)
| [], Row.nil => Row.nil
| [], Row.cons x xs => Row.nil
| n::ns, Row.nil => absurd n.property
                          (by intro nh; simp [List.length] at nh; contradiction)
| n::ns, r => Row.cons (Row.nth r n.val n.property) (nths ns r)

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

def Row.pick : {schema : @Schema η} →
               Row schema →
               (cs : List (CertifiedHeader schema)) →
               Row (Schema.fromCHeaders cs)
| _, Row.nil, [] => Row.nil
| _, Row.nil, (⟨c, h⟩::cs) => by cases h
| _, Row.cons cell rs, [] => Row.nil
| (s::ss), Row.cons cell rs, (c::cs) =>
  Row.cons (Row.getCell (Row.cons cell rs) c.2)
           (pick (Row.cons cell rs) cs)
termination_by Row.pick r cs => List.length cs

def Row.removeColumn {s : Schema} {c : η} :
    (h : s.HasName c) → Row s → Row (s.removeName h)
| Schema.HasName.hd, Row.cons r rs => rs
| Schema.HasName.tl h',Row.cons r rs => Row.cons r (removeColumn h' rs)

def Row.removeColumns {s : @Schema η} :
    (cs : Schema.ActionList Schema.removeCertifiedName s) →
    Row s →
    Row (s.removeNames cs)
| .nil, r => r
| .cons c cs, r => removeColumns cs (removeColumn c.2 r) 

/-------------------------------------------------------------------------------
                          Decidable Equality Instances
-------------------------------------------------------------------------------/
instance {nm : η} {τ : Type u} [inst : DecidableEq τ] : DecidableEq (Cell nm τ)
| Cell.emp, Cell.emp => isTrue rfl
| Cell.emp, (Cell.val x) => isFalse (λ hneg => Cell.noConfusion hneg)
| (Cell.val x), Cell.emp => isFalse (λ hneg => Cell.noConfusion hneg)
| (Cell.val x), (Cell.val y) =>
  Eq.mpr (congrArg Decidable $ Cell.val.injEq x y) (inst x y)

-- TODO: simplify (no pun intended)
instance : DecidableEq (@Row η _ [])
| Row.nil, Row.nil => Decidable.isTrue rfl

-- TODO: again, simplify by de-simp-lifying
-- TODO: do we explicitly need it, or will the lookup figure that out for us?
instance {ss : @Schema η}
         {nm : η}
         {τ : Type u}
         [it : DecidableEq τ]
         [ic : DecidableEq (Cell nm τ)]
         [ir : DecidableEq (Row ss)]
    : DecidableEq (Row ((nm, τ) :: ss)) :=
λ (Row.cons c₁ r₁) (Row.cons c₂ r₂) =>
  have hc_dec : Decidable (c₁ = c₂) := by apply ic;
  have hr_dec : Decidable (r₁ = r₂) := by apply ir;
  -- TODO: this is copied straight from the prelude (l. 333) - figure out how
  -- to just use that instance
  have h_conj_dec : (Decidable (c₁ = c₂ ∧ r₁ = r₂)) :=
    match hc_dec with
    | isTrue hc =>
      match hr_dec with
      | isTrue hr  => isTrue ⟨hc, hr⟩
      | isFalse hr => isFalse (fun h => hr (And.right h))
    | isFalse hc =>
      isFalse (fun h => hc (And.left h));
  by simp; apply h_conj_dec

-- TODO: simplify a la case 4 of Cell instance?
instance {sch : @Schema η} [inst : DecidableEq (Row sch)] : DecidableEq (Table sch) :=
λ {rows := r₁} {rows := r₂} =>
dite (r₁ = r₂)
     (λ htrue => isTrue $ congrArg Table.mk htrue)
     (λ hfalse => isFalse (λ hneg => absurd (Table.mk.inj hneg) hfalse))
