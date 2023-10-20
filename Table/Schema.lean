import Table.BuiltinExtensions

universe u_η
universe u

def Header {η} := (η × Type u)
def Schema {η} := List (@Header η)

-- Schema column predicates
inductive Schema.HasCol {η : Type u_η} :
  @Header η → @Schema η → Type (max (u + 1) u_η)
| hd {c : η} {τ : Type u} {rs : Schema} : HasCol (c, τ) ((c, τ) :: rs)
| tl {r c τ rs} : HasCol (c, τ) rs → HasCol (c, τ) (r::rs)

inductive Schema.HasName {η : Type u_η} : η → @Schema η → Type (max (u + 1) u_η)
| hd {c : η} {rs : Schema} {τ : Type u} : HasName c ((c, τ) :: rs)
| tl {r c rs} : HasName c rs → HasName c (r::rs)

-- Schema-related convenience types
def Subschema {η : Type u_η} (schm : @Schema η) :=
  List ((h : Header) × schm.HasCol (h.fst, h.snd))

def EqSubschema {η : Type u_η} (schm : @Schema η) :=
  List ((h : Header) × schm.HasCol (h.fst, h.snd) × DecidableEq h.2)

def CertifiedName (schema : @Schema η) := ((c : η) × Schema.HasName c schema)
def CertifiedHeader (schema : @Schema η) :=
  ((h : Header) × Schema.HasCol h schema)

-- Action lists
/-
Action lists represent a collection of items to apply to a schema with a
guarantee that the validity of each proof of containment is preserved after each
action item is applied. It generalizes the following instances:
  inductive SchemaRemoveList {η : Type u_η} [DecidableEq η] :
    @Schema.{u_η, u} η → Type (max u_η (u + 1))
  | nil {schema} : SchemaRemoveList schema
  | cons {schema} : (cn : CertifiedName schema) →
                    SchemaRemoveList (schema.removeName cn.2) →
                    SchemaRemoveList schema

  inductive SchemaFlattenList {η : Type u_η} [DecidableEq η] :
    @Schema η → Type _
  | nil {schema} : SchemaFlattenList schema
  | cons {schema} : (cn : ((c : η) × (τ: Type u) × schema.HasCol (c, List τ))) →
                    SchemaFlattenList (schema.flattenList cn) →
                    SchemaFlattenList schema

  inductive SchemaRenameList {η : Type u_η} [DecidableEq η] :
    @Schema η → Type _
  | nil {schema} : SchemaRenameList schema
  | cons {schema} : (cnc : (CertifiedName schema × η))→
                    SchemaRenameList (schema.renameColumn cnc.1.2 cnc.2) →
                    SchemaRenameList schema
-/
inductive ActionList {η : Type u_η} [DecidableEq η]
                     {κ : @Schema η → Type u}
                     (f : ∀ (s : @Schema η), κ s → @Schema η)
    : @Schema η → Type _
| nil {schema}  : ActionList f schema
| cons {schema} : (entry : κ schema) →
                  ActionList f (f schema entry) →
                  ActionList f schema

inductive BiActionList {η : Type u_η} [DecidableEq η]
                       {κ : @Schema η × @Schema η → Type u}
  (f : ∀ (ss : @Schema η × @Schema η), κ ss → @Schema η × @Schema η)
    : @Schema η × @Schema η → Type _
| nil {s₁ s₂}  : BiActionList f (s₁, s₂)
| cons {s₁ s₂} : (entry : κ (s₁, s₂)) →
                  BiActionList f (f (s₁, s₂) entry) →
                  BiActionList f (s₁, s₂)

variable {η : Type u_η} [dec_η : DecidableEq η] {schema : @Schema η}

-- For ease of refactoring, makes these products act like subtypes
def CertifiedName.val (n : CertifiedName schema) := Sigma.fst n
def CertifiedName.property (n : CertifiedName schema) := Sigma.snd n
def CertifiedHeader.val (h : CertifiedHeader schema) := Sigma.fst h
def CertifiedHeader.property (h : CertifiedHeader schema) := Sigma.snd h

-- This will make proofs difficult
-- def Subschema.toSchema {schm : @Schema η} (s : Subschema schm) : @Schema η := 
--   s.map (λ x => x.fst)

def Subschema.toSchema {schm : @Schema η} : Subschema schm → @Schema η
| [] => []
| ⟨hdr, _⟩ :: ss => hdr :: toSchema ss

def EqSubschema.toSchema {schm : @Schema η} : EqSubschema schm → @Schema η
| [] => []
| ⟨hdr, _⟩ :: ss => hdr :: toSchema ss

def Schema.fromCHeaders {schema : @Schema η}
                        (cs : List (CertifiedHeader schema))
    : @Schema η :=
  cs.map Sigma.fst

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

-- There occasionally seem to be some issues with this function, too -- not sure
-- if it's the same issue as `removeName` and `lookup`, but will leave these
-- here for the time being just in case
def Schema.colImpliesName_eq_1 {sch' : @Schema η} {hdr : @Header η} :
  colImpliesName (schema := hdr :: sch') HasCol.hd = HasName.hd := rfl

def Schema.colImpliesName_eq_2 {sch' : @Schema η} {s hdr : @Header η}
                               {h : sch'.HasCol hdr}:
  colImpliesName (schema := s :: sch') (HasCol.tl h) =
  HasName.tl (colImpliesName h) := rfl

def Schema.cNameOfCHead {schema : @Schema η} :
      CertifiedHeader schema → CertifiedName schema
| ⟨(nm, τ), pf⟩ => ⟨nm, Schema.colImpliesName pf⟩

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

def Schema.hasColOfAppend : {sch : @Schema η} →
                                 {nm : η} →
                                 {τ : Type u} →
                                 {hs : List Header} →
                                 sch.HasCol (nm, τ) →
  Schema.HasCol (nm, τ) (sch.append hs)
| _, _, _, _, Schema.HasCol.hd => Schema.HasCol.hd
| _, _, _, _, Schema.HasCol.tl h => Schema.HasCol.tl $ hasColOfAppend h

def Schema.hasColOfPrepend : {sch : @Schema η} →
                                 {nm : η} →
                                 {τ : Type u} →
                                 {hs : List Header} →
                                 sch.HasCol (nm, τ) →
  Schema.HasCol (nm, τ) (hs.append sch)
| _, _, _, [], pf => pf
| _, _, _, _ :: hs', pf => .tl $ hasColOfPrepend (hs := hs') pf

def Schema.hasAppendedSingletonName :
  ∀ (sch : @Schema η) (c : η) (τ : Type _),
  HasName c (List.append sch [(c, τ)])
| [], _, _ => HasName.hd
| s :: ss, c, τ => HasName.tl (hasAppendedSingletonName ss c τ)

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

def Schema.removeHeader {c : η} {τ : Type u}
                        (s : @Schema η)
                        (hd : s.HasCol (c, τ))
    : @Schema η :=
  removeName s (Schema.colImpliesName hd)
-- | _::s, .hd => s
-- | s::ss, .tl h => s :: removeHeader ss h

-- theorem Schema.removeHeader_eq_1 {η : Type u_η} [DecidableEq η]
--   {c : η} (hdr : @Header η) (ss : @Schema η) :
--   removeHeader (hdr :: ss) Schema.HasCol.hd = ss := rfl

-- theorem Schema.removeHeader_eq_2 {η : Type u_η} [DecidableEq η]
--   {c : η} {τ : Type u} (hdr : @Header η) (ss : @Schema η)
--   (h : Schema.HasCol (c, τ) ss) :
--   removeHeader (hdr :: ss) (Schema.HasCol.tl h) = hdr :: removeHeader ss h :=
-- rfl

def Schema.removeCertifiedName (s : @Schema η) (cn : CertifiedName s) :=
  removeName s cn.2

def Schema.removeCertifiedHeader (s : @Schema η) (ch : CertifiedHeader s) :=
  removeHeader s ch.2

def Schema.removeTypedName (τ : Type u)
                           (s : @Schema η)
                           (c : ((c : η) × s.HasCol (c, τ)))
    : @Schema η :=
  removeHeader s c.2

def Schema.removeNamePres : {schema : @Schema η} →
                              {nm : η} →
                              {n : schema.HasName nm} →
                              {nm' : η} →
                              Schema.HasName nm' (schema.removeName n) →
                              Schema.HasName nm' schema
| _ :: _, nm, Schema.HasName.hd, nm', pf => Schema.HasName.tl pf
| (nm', τ) :: ss, nm, Schema.HasName.tl h, _, Schema.HasName.hd =>
  Schema.HasName.hd
| s :: ss, nm, Schema.HasName.tl h, nm', Schema.HasName.tl h' =>
  let ih := @removeNamePres _ nm h nm' h'
  Schema.HasName.tl ih

def Schema.removeCNPres {schema : @Schema η} {nm} {n : schema.HasName nm}
                        (cn : CertifiedName $ schema.removeName n)
    : CertifiedName schema
  := ⟨cn.1, removeNamePres cn.2⟩

def Schema.removeHeaderPres :
    {hdr : @Header η} → {schema : @Schema η} →
    {h : schema.HasCol hdr} →
    {hdr' : @Header η} →
    Schema.HasCol hdr' (schema.removeHeader h) →
    Schema.HasCol hdr' schema
| _, _ :: _, HasCol.hd, hdr', pf => HasCol.tl pf
| hdr, .(hdr') :: ss, HasCol.tl h, hdr', HasCol.hd => HasCol.hd
| hdr, s :: ss, HasCol.tl h, _, HasCol.tl h' => HasCol.tl (removeHeaderPres h')

def Schema.removeTNPres
  (s : Schema)
  (k : (c : η) × Schema.HasCol (c, τ) s)
  (c : (c : η) × Schema.HasCol (c, τ) (Schema.removeTypedName τ s k)) :
  (c : η) × Schema.HasCol (c, τ) s
  := ⟨c.1, removeHeaderPres c.2⟩

def Schema.removeNames {η : Type u_η} [DecidableEq η] :
    (s : @Schema η) → ActionList removeCertifiedName s → @Schema η
| ss, ActionList.nil => ss
| ss, ActionList.cons cn rest => removeNames (removeName ss cn.2) rest

def Schema.removeHeaders {η : Type u_η} [DecidableEq η] :
    (s : @Schema η) → ActionList removeCertifiedHeader s → @Schema η
| ss, ActionList.nil => ss
| ss, ActionList.cons cn rest =>
  removeHeaders (removeCertifiedHeader ss cn) rest

def Schema.removeTypedNames {τ : Type u} :
  (s : @Schema η) → ActionList (removeTypedName τ) s → @Schema η
| s, ActionList.nil => s
| s, ActionList.cons ch rest => removeTypedNames (removeTypedName τ s ch) rest

-- TODO: this is a very inelegant way of hijacking `ActionList` (the
-- alternative, though, would be to make `ActionList` even *more* abstract by
-- decoupling `κ` and the type of the argument to `f`, which would be a function
-- of `κ` or something like that...)
def Schema.removeOtherDecCH
  (schema' schema : @Schema η)
  (c : (hdr : @Header η) × DecidableEq hdr.2 ×
    schema.HasCol hdr × schema'.HasCol hdr) :
  @Schema η := schema.removeHeader c.2.2.1

def Schema.removeOtherDecCHs (schema' : @Schema η) :
  (schema : @Schema η) →
  (cs : ActionList (removeOtherDecCH schema') schema) →
  @Schema η
| s, ActionList.nil => s
| s, ActionList.cons c cs =>
  removeOtherDecCHs schema' (removeOtherDecCH schema' s c) cs

def Schema.removeOtherCHPres :
  (s : Schema) →
  (k : (hdr : Header) × DecidableEq hdr.snd ×
    HasCol hdr s × HasCol hdr schema₁) →
  (hdr : Header) × DecidableEq hdr.snd ×
    HasCol hdr (removeOtherDecCH schema₁ s k) × HasCol hdr schema₁ →
  (hdr : Header) × DecidableEq hdr.snd × HasCol hdr s × HasCol hdr schema₁ := 
λ _ _ c => ⟨c.1, c.2.1, removeHeaderPres c.2.2.1, c.2.2.2⟩

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

theorem Schema.lookup_of_colImpliesName :
  ∀ (sch : @Schema η) (hpf : sch.HasCol (nm, τ)),
  Schema.lookup sch ⟨nm, Schema.colImpliesName hpf⟩ = (nm, τ)
| _ :: ss, .hd => by
  rw [colImpliesName_eq_1 (sch' := ss) (hdr := (nm, τ)),
      lookup_eq_1]
| _ :: ss, .tl h => by
  rw [colImpliesName_eq_2, lookup_eq_2]
  apply lookup_of_colImpliesName

-- Returns the type associated with the given name.
-- Note: don't use this function to specify the return type of a function.
-- Instead, take the type implicitly and make that variable the return type.
def Schema.lookupType {η : Type u_η} [DecidableEq η]
    : (s : @Schema η) → CertifiedName s → Type u
| (_, τ) :: _, ⟨_, Schema.HasName.hd⟩ => τ
| _ :: hs, ⟨c, Schema.HasName.tl h'⟩ => lookupType hs ⟨c, h'⟩

theorem Schema.lookupType_eq_snd_lookup (s : @Schema η) (cn : CertifiedName s) :
  lookupType s cn = (lookup s cn).snd := by
  cases cn with | mk nm pf =>
  induction pf with
  | hd =>
    simp only [lookupType]
    rw [lookup_eq_1]
  | tl h ih =>
    simp only [lookupType]
    rw [lookup_eq_2]
    apply ih

def Schema.pick {η : Type u_η} [DecidableEq η] (s : @Schema η)
    : List (CertifiedName s) → @Schema η
| [] => []
| c::cs => lookup s c :: pick s cs

def Schema.retypeColumn {η : Type u_η} [DecidableEq η]
    : {nm : η} → (s : @Schema η) → s.HasName nm → Type u → @Schema η
| _, (nm, τ) :: cs, Schema.HasName.hd, τ' => (nm, τ') :: cs
| _, c :: cs, Schema.HasName.tl h, τ' => c :: retypeColumn cs h τ'

theorem Schema.retypeColumn_preserves_names :
  ∀ (s : @Schema η) {nm : η} (h : s.HasName nm) (τ : Type _),
  Schema.names (s.retypeColumn h τ) = Schema.names s
| (.(nm), _) :: ss, nm, HasName.hd, τ => rfl
| s :: ss, nm, HasName.tl h, τ =>
  congrArg (s.1 :: ·) (retypeColumn_preserves_names ss h τ)

def Schema.hasRetypedCol {τ₁ τ₂} : ∀ {sch : @Schema η}
  (c : (c : η) × sch.HasCol (c, τ₁)),
  HasCol (c.1, τ₂) (retypeColumn sch (colImpliesName c.snd) τ₂)
| [], ⟨_, pf⟩ => nomatch pf
| _ :: _, ⟨_, .hd⟩ => Schema.HasCol.hd
| _ :: _, ⟨nm, Schema.HasCol.tl htl⟩ =>
  Schema.HasCol.tl $ hasRetypedCol ⟨nm, htl⟩

-- Could use `{xs : List τ // xs.length = n}` instead of `List τ` if needed
def Schema.flattenList (schema : @Schema η)
  (c : ((c : η) × (τ : Type u) × schema.HasCol (c, List τ)))
    : @Schema η :=
  schema.retypeColumn (Schema.colImpliesName c.2.2) c.2.1

def Schema.flattenLists : (schema : @Schema η) →
                          (ActionList flattenList schema) →
                         @Schema η
| ss, ActionList.nil => ss
| ss, ActionList.cons c cs => flattenLists (flattenList ss c) cs

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
| s, ActionList.nil => s
| s, ActionList.cons c ccs => renameColumns (renameColumnCN s c) ccs

theorem Schema.removeName_sublist :
  ∀ (s : @Schema η) (c : η) (hc : HasName c s),
    List.Sublist (s.removeName hc) s
| _, _, HasName.hd => List.Sublist.cons _ _ _ (List.sublist_self _)
| _, _, HasName.tl h => List.Sublist.cons2 _ _ _ (removeName_sublist _ _ h)

theorem Schema.removeNames_sublist :
  ∀ (s : @Schema η) (cs : ActionList Schema.removeCertifiedName s),
    List.Sublist (s.removeNames cs) s
| s, ActionList.nil => List.sublist_self _
| s, ActionList.cons c cs =>
  have ih := removeNames_sublist (s.removeName c.2) cs
  List.Sublist.trans ih (Schema.removeName_sublist s c.1 c.2)

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
| _ :: s', ⟨c, Schema.HasName.tl h⟩ =>
  Schema.HasCol.tl (schemaHasLookup s' ⟨c, h⟩)

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

-- def Schema.hasColFromHeadersOfHasCol {c : η} {τ : Type u} :
--   (cs : List (CertifiedHeader sch)) →
--   (pf : sch.HasCol (c, τ)) →
--   pf ∈ cs.map (·.2) → 
--   (Schema.fromCHeaders cs).HasCol (c, τ)
-- | .head, c :: cs, .hd => .hd

-- TODO: figure out why it won't let us name the proof in the first clause
def Schema.hasNameOfFromCHeaders :
  ∀ {sch : @Schema η} {cs : List $ CertifiedHeader sch} {nm : η},
  Schema.HasName nm (Schema.fromCHeaders cs) → Schema.HasName nm sch
| [], ⟨hdr, hpf⟩ :: _, _, _ => nomatch hpf
| _ :: _, ⟨(.(nm), τ), _⟩ :: _, nm, .hd =>
  Schema.colImpliesName (τ := τ) (by assumption)
| _ :: _, ⟨hdr, hpf⟩ :: cs, nm, .tl h => hasNameOfFromCHeaders h

theorem Schema.hasNameOfFromCHeaders_eq_1 :
  @hasNameOfFromCHeaders η sch (⟨(nm, τ), hpf⟩ :: cs) nm HasName.hd =
  colImpliesName hpf := by
  cases sch with
  | nil => contradiction
  | cons s ss => simp [hasNameOfFromCHeaders]

theorem Schema.hasNameOfFromCHeaders_eq_2 :
  @hasNameOfFromCHeaders η sch (⟨hdr, hpf⟩ :: cs) nm (HasName.tl h) =
  hasNameOfFromCHeaders h := by
  cases sch with
  | nil => contradiction
  | cons s ss => simp [hasNameOfFromCHeaders]

-- `pivotWider` stuff
def Schema.hasColOfMemT : List.MemT (x, τ) xs → Schema.HasCol (x, τ) xs
  | .hd _ _ => .hd
  | .tl _ htl => .tl $ hasColOfMemT htl

def Schema.hasColOfMemPivotCol {τ : Type u} {t : Table schema} {lblCol : η} {lblEntry : η}
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

/--
Takes an ActionList along with a "preservation" function that maps action list
entries "in reverse" (i.e., enables them to be "lifted" to a schema prior to
the ActionList's associated transformation) and generates a list of action list
entries at the top-level (original, pre-transformation) schema.
-/
def ActionList.toList {sch : @Schema η} {κ : @Schema η → Type u}
    {f : ∀ (s : @Schema η), κ s → @Schema η}
    (pres : ∀ (s : @Schema η) (k : κ s), κ (f s k) → κ s)
    : ActionList f sch → List (κ sch)
| ActionList.nil => []
| ActionList.cons hdr xs =>
  have : sizeOf xs < 1 + sizeOf xs := by rw [Nat.add_comm]; exact Nat.lt.base _
  hdr :: (toList pres xs).map (pres sch hdr)
-- The default tactic needlessly introduces classical reasoning
decreasing_by assumption

def BiActionList.toList {schs : @Schema η × @Schema η}
    {κ : @Schema η × @Schema η → Type u}
    {f : ∀ (ss : @Schema η × @Schema η), κ ss → @Schema η × @Schema η}
    (pres : ∀ (ss : @Schema η × @Schema η) (k : κ ss), κ (f ss k) → κ ss)
    : BiActionList f schs → List (κ schs)
| BiActionList.nil => []
| BiActionList.cons x xs =>
  have hterm : sizeOf xs < sizeOf (cons x xs) :=
    by simp; rw [Nat.add_comm, Nat.add_one]; apply Nat.lt.base
  x :: (toList pres xs).map (pres schs x)
