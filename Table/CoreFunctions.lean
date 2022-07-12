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

-- TODO: Uniqueness is evil...
-- TODO: new issue is that the input might have duplicate names...
def Schema.removeNames {η : Type u_η} [DecidableEq η] :
    (s : @Schema η) → List (CertifiedName s) → @Schema η
| ss, [] => ss
| ss, (y::ys) => sorry -- removeNames (removeName ss y.snd) ys
/-
`ys` gets changed to:
(List.map (λ (x : ((c : CertifiedName ss) × (c.fst ≠ y.fst))) => ⟨x.fst.fst, by
      induction ss with
      | nil => cases x with | mk fst snd => cases snd
      | cons x xs ih => _
⟩) ys)
-/

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

-- TODO: this issue again. Whenever our recursion looks like
-- `f_list (f_el schema modifier_el) rest_of_modifier_list`
-- bad things happen
def Schema.renameColumns {η : Type u_η} [DecidableEq η]
    : (s : @Schema η) → List (CertifiedName s × η) → @Schema η
| s, [] => []
| s, (oldPf, nm') :: ccs => sorry --renameColumns (renameColumn s oldPf.snd nm') ccs

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

-- Row utilities
def Row.singleCell {name τ} (x : τ) :=
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

-- It would be nice if Lean could figure out that we're structurally recursing,
-- but in the meantime, we have to provide a manual termination relation
def Row.nths {schema} :
    (ns : List {n : Nat // n < List.length schema})
      → Row schema
      → @Row η dec_η (List.nths schema ns)
| [], Row.nil => Row.nil
| [], Row.cons x xs => Row.nil
| n::ns, Row.nil => absurd n.property
                          (by intro nh; simp [List.length] at nh; contradiction)
| n::ns, r => Row.cons (Row.nth r n.val n.property) (nths ns r)
  termination_by nths ns r => List.length ns

def Row.removeColumn {s : Schema} {c : η} :
    (h : s.HasName c) → Row s → Row (s.removeName h)
| Schema.HasName.hd, Row.cons r rs => rs
| Schema.HasName.tl h', Row.cons r rs => Row.cons r (removeColumn h' rs)

/-------------------------------------------------------------------------------
                          Decidable Equality Instances
-------------------------------------------------------------------------------/
-- TODO: make these way simpler
instance {nm : η} {τ : Type u} [inst : DecidableEq τ] : DecidableEq (Cell nm τ)
| Cell.emp, Cell.emp => by simp only; apply Decidable.isTrue; apply True.intro
| Cell.emp, (Cell.val x) => by simp only; apply Decidable.isFalse; simp only
| (Cell.val x), Cell.emp => by simp only; apply Decidable.isFalse; simp only
| (Cell.val x), (Cell.val y) => by simp; apply inst

-- TODO: simplify (no pun intended)
instance : DecidableEq (@Row η _ []) :=
  λ r₁ r₂ => by
    cases r₁
    cases r₂
    simp only
    apply Decidable.isTrue
    apply True.intro

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
