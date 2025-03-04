import Table.BuiltinExtensions
import Lean

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

-- Tactics for generating terms of the above proof types
section
open Lean Lean.Meta Lean.Elab.Tactic

private def doNaiveSearch (pfTp : Name) (tacNm : String) (argNm : String) :
    TacticM Unit :=
  withMainContext do
    let tgtNF ← whnfD (← getMainTarget)
    if tgtNF.isAppOf pfTp then
      let (arg, sch) := (tgtNF.getAppArgs[1]!, tgtNF.getAppArgs[2]!)
      -- TODO: to make this more extensible, allow passing a list of
      -- constructors as args to this function, then iterate through them here
      if tacNm == "name" then
        evalTactic
          (← `(tactic| repeat (first | assumption
                                     | apply Schema.HasName.hd
                                     | apply Schema.HasName.tl)))
      else
         evalTactic
          (← `(tactic| repeat (first | assumption
                                     | apply Schema.HasCol.hd
                                     | apply Schema.HasCol.tl)))
      -- TODO: it would be better to get the main goal before searching, then
      -- checking if that particular goal has been closed
      if (← getUnsolvedGoals).length > 0 then
        throwError m!"Could not prove that {argNm} {arg} is in schema {sch}"
    else
      let goal ← getMainGoal
      throwError m!"Unsupported goal for {tacNm} tactic: {goal}"

elab "header" : tactic => doNaiveSearch `Schema.HasCol "header" "header"

elab "name" : tactic => doNaiveSearch `Schema.HasName "name" "name"
end

-- Schema-related convenience types
def Subschema {η : Type u_η} (schm : @Schema η) :=
  List ((h : Header) × schm.HasCol (h.fst, h.snd))

def EqSubschema {η : Type u_η} (schm : @Schema η) :=
  List ((h : Header) × schm.HasCol (h.fst, h.snd) × DecidableEq h.2)

@[reducible]
def RetypedSubschema {η : Type u_η} (schm : @Schema η) :=
  List ((h : Header) × schm.HasName h.fst)

@[reducible]
def CertifiedName (schema : @Schema η) := ((c : η) × Schema.HasName c schema)
@[reducible]
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

inductive ProofList (f : α → Type _) : (xs : List α) → Type _
  | nil : ProofList f []
  | cons : f x → ProofList f xs → ProofList f (x :: xs)

inductive IsActionList {η : Type u_η} [DecidableEq η]
                       {κ : η → @Schema η → Type u}
                       (f : ∀ (nm : η) (s : @Schema η), κ nm s → @Schema η) :
    @Schema η → List η → Type _
| nil {schema} : IsActionList f schema []
| cons {schema} {nm nms} : (entry : κ nm schema) →
                        IsActionList f (f nm schema entry) nms →
                        IsActionList f schema (nm :: nms)

inductive BiActionList {η : Type u_η} [DecidableEq η]
                       {κ : @Schema η × @Schema η → Type u}
  (f : ∀ (ss : @Schema η × @Schema η), κ ss → @Schema η × @Schema η)
    : @Schema η × @Schema η → Type _
| nil {s₁ s₂}  : BiActionList f (s₁, s₂)
| cons {s₁ s₂} : (entry : κ (s₁, s₂)) →
                  BiActionList f (f (s₁, s₂) entry) →
                  BiActionList f (s₁, s₂)

-- Membership predicate for action lists
inductive ActionList.MemT {η : Type u_η} [DecidableEq η]
  {κ : @Schema η → Type u}
  {f : ∀ (s : @Schema η), κ s → @Schema η}
  : ∀ {s s' : @Schema η}, κ s' → ActionList f s → Type _
| head {x : κ s} (xs : ActionList f (f s x)) : MemT x (ActionList.cons x xs)
| tail {x : κ s'} (y : κ s) (xs : ActionList f (f s y)) :
  MemT x xs → MemT x (ActionList.cons y xs)

variable {η : Type u_η} [dec_η : DecidableEq η] {schema : @Schema η}

-- For ease of refactoring, make these products act like subtypes
@[reducible] def CertifiedName.val (n : CertifiedName schema) :=
  Sigma.fst n
@[reducible] def CertifiedName.property (n : CertifiedName schema) :=
  Sigma.snd n
@[reducible] def CertifiedHeader.val (h : CertifiedHeader schema) :=
  Sigma.fst h
@[reducible] def CertifiedHeader.property (h : CertifiedHeader schema) :=
  Sigma.snd h

-- This will make proofs difficult
-- def Subschema.toSchema {schm : @Schema η} (s : Subschema schm) : @Schema η :=
--   s.map (λ x => x.fst)

def Subschema.toSchema {schm : @Schema η} : Subschema schm → @Schema η
| [] => []
| ⟨hdr, _⟩ :: ss => hdr :: toSchema ss

def EqSubschema.toSchema {schm : @Schema η} : EqSubschema schm → @Schema η
| [] => []
| ⟨hdr, _⟩ :: ss => hdr :: toSchema ss


def Schema.HasCol.size : {schema : @Schema η} →
                         {hdr : @Header η} →
                         schema.HasCol hdr →
                         Nat
| _, _, Schema.HasCol.hd => 0
| _, _, Schema.HasCol.tl h => 1 + size h

@[reducible]
def Schema.colImpliesName :
      {schema : @Schema η} →
      {c : η} →
      {τ : Type u} →
      schema.HasCol (c, τ) → schema.HasName c
| h :: hs, _, _, HasCol.hd => HasName.hd
| h :: hs, c, τ, HasCol.tl p => HasName.tl (colImpliesName p)

-- There occasionally seem to be some issues with this function, too -- not sure
-- if it's the same issue as `removeName` and `lookup`, but will leave these
-- here for the time being just in case
omit dec_η in
theorem Schema.colImpliesName_eq_1 {sch' : @Schema η} {hdr : @Header η} :
  colImpliesName (schema := hdr :: sch') HasCol.hd = HasName.hd := rfl

omit dec_η in
theorem Schema.colImpliesName_eq_2 {sch' : @Schema η} {s hdr : @Header η}
                               {h : sch'.HasCol hdr}:
  colImpliesName (schema := s :: sch') (HasCol.tl h) =
  HasName.tl (colImpliesName h) := rfl

@[reducible]
def Schema.cNameOfCHead {schema : @Schema η} :
      CertifiedHeader schema → CertifiedName schema
| ⟨(nm, τ), pf⟩ => ⟨nm, Schema.colImpliesName pf⟩

-- Schema functions
-- Note: if written point-free, dot notation fails
@[reducible]
def Schema.names {η : Type u_η} (sch : @Schema η) :=
  List.map (@Prod.fst η (Type u)) sch

@[reducible]
def Schema.memTNamesOfHasName :
  {sch : @Schema η} → Schema.HasName c sch → List.MemT c sch.names
| _, .hd => .hd _ _
| _, .tl h => .tl _ (memTNamesOfHasName h)

-- Doesn't work b/c we can't definitionally equate conditionals with their
-- evaluation, even when the equality is tautological
-- def Schema.removeName :
--     (s : @Schema η) → η → @Schema η
-- | [], _ => []
-- | (nm, τ)::xs, c => if c = nm then xs else (nm, τ) :: removeName xs c

@[reducible]
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

@[reducible]
def Schema.removeHeader {c : η} {τ : Type u}
                        (s : @Schema η)
                        (hd : s.HasCol (c, τ))
    : @Schema η :=
  removeName s (Schema.colImpliesName hd)

-- These seem to occasionally be necessary, depending on the Lean version
-- theorem Schema.removeHeader_eq_1 {η : Type u_η} [DecidableEq η]
--   {c : η} (hdr : @Header η) (ss : @Schema η) :
--   removeHeader (hdr :: ss) Schema.HasCol.hd = ss := rfl

-- theorem Schema.removeHeader_eq_2 {η : Type u_η} [DecidableEq η]
--   {c : η} {τ : Type u} (hdr : @Header η) (ss : @Schema η)
--   (h : Schema.HasCol (c, τ) ss) :
--   removeHeader (hdr :: ss) (Schema.HasCol.tl h) = hdr :: removeHeader ss h :=
-- rfl

@[reducible]
def Schema.removeCertifiedName (s : @Schema η) (cn : CertifiedName s) :=
  removeName s cn.2

@[reducible]
def Schema.removeCertifiedHeader (s : @Schema η) (ch : CertifiedHeader s) :=
  removeHeader s ch.2

@[reducible]
def Schema.removeTypedName (τ : Type u)
                           (s : @Schema η)
                           (c : ((c : η) × s.HasCol (c, τ)))
    : @Schema η :=
  removeHeader s c.2

@[reducible]
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

@[reducible]
def Schema.removeCNPres {schema : @Schema η} {nm} {n : schema.HasName nm}
                        (cn : CertifiedName $ schema.removeName n)
    : CertifiedName schema
  := ⟨cn.1, removeNamePres cn.2⟩

@[reducible]
def Schema.removeHeaderPres :
    {hdr : @Header η} → {schema : @Schema η} →
    {h : schema.HasCol hdr} →
    {hdr' : @Header η} →
    Schema.HasCol hdr' (schema.removeHeader h) →
    Schema.HasCol hdr' schema
| _, _ :: _, HasCol.hd, hdr', pf => HasCol.tl pf
| hdr, .(hdr') :: ss, HasCol.tl h, hdr', HasCol.hd => HasCol.hd
| hdr, s :: ss, HasCol.tl h, _, HasCol.tl h' => HasCol.tl (removeHeaderPres h')

@[reducible]
def Schema.hasColOfRemoveName :
  ∀ {sch : @Schema η} {nm} (c : η) (hneq : c ≠ nm),
  (hnm : sch.HasName nm) → sch.HasCol (c, τ) →
  Schema.HasCol (c, τ) (Schema.removeName sch hnm)
| _ :: sch', nm, c, hneq, .hd, .tl h => h
| _ :: sch', nm, c, hneq, .tl h, .hd => .hd
| _ :: sch', nm, c, hneq, .tl h, .tl h' =>
  .tl $ hasColOfRemoveName c hneq h h'

@[reducible]
def Schema.removeTNPres
  (s : Schema)
  (k : (c : η) × Schema.HasCol (c, τ) s)
  (c : (c : η) × Schema.HasCol (c, τ) (Schema.removeTypedName τ s k)) :
  (c : η) × Schema.HasCol (c, τ) s
  := ⟨c.1, removeHeaderPres c.2⟩

@[reducible]
def Schema.removeNames {η : Type u_η} [DecidableEq η] :
    (s : @Schema η) → ActionList removeCertifiedName s → @Schema η
| ss, ActionList.nil => ss
| ss, ActionList.cons cn rest => removeNames (removeName ss cn.2) rest

@[reducible]
def Schema.removeHeaders {η : Type u_η} [DecidableEq η] :
    (s : @Schema η) → ActionList removeCertifiedHeader s → @Schema η
| ss, ActionList.nil => ss
| ss, ActionList.cons cn rest =>
  removeHeaders (removeCertifiedHeader ss cn) rest

@[reducible] def Schema.removeTypedNames {τ : Type u} :
  (s : @Schema η) → ActionList (removeTypedName τ) s → @Schema η
| s, ActionList.nil => s
| s, ActionList.cons ch rest => removeTypedNames (removeTypedName τ s ch) rest

-- Note: this is a very inelegant way of hijacking `ActionList` (the
-- alternative, though, would be to make `ActionList` even *more* abstract by
-- decoupling `κ` and the type of the argument to `f`, which would be a function
-- of `κ` or something like that)
@[reducible]
def Schema.removeOtherDecCH
  (schema' schema : @Schema η)
  (c : (hdr : @Header η) × DecidableEq hdr.2 ×
    schema.HasCol hdr × schema'.HasCol hdr) :
  @Schema η := schema.removeHeader c.2.2.1

@[reducible]
def Schema.removeOtherDecCHs (schema' : @Schema η) :
  (schema : @Schema η) →
  (cs : ActionList (removeOtherDecCH schema') schema) →
  @Schema η
| s, ActionList.nil => s
| s, ActionList.cons c cs =>
  removeOtherDecCHs schema' (removeOtherDecCH schema' s c) cs

@[reducible]
def Schema.removeOtherDecCHPres :
  (s : Schema) →
  (k : (hdr : Header) × DecidableEq hdr.snd ×
    HasCol hdr s × HasCol hdr schema₁) →
  (hdr : Header) × DecidableEq hdr.snd ×
    HasCol hdr (removeOtherDecCH schema₁ s k) × HasCol hdr schema₁ →
  (hdr : Header) × DecidableEq hdr.snd × HasCol hdr s × HasCol hdr schema₁ :=
λ _ _ c => ⟨c.1, c.2.1, removeHeaderPres c.2.2.1, c.2.2.2⟩

-- Returns the schema entry with the specified name
@[reducible]
def Schema.lookup {η : Type u_η} [DecidableEq η]
    : (s : @Schema η) → CertifiedName s → @Header η
| hdr :: _, ⟨_, Schema.HasName.hd⟩ => hdr
| _ :: hs, ⟨c, Schema.HasName.tl h'⟩ => lookup hs ⟨c, h'⟩

-- TODO: figure out what's going on here -- these should be auto-generated, but
-- we need to manually declare them to get proofs to go through
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
@[reducible]
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
  | tl h ih =>
    simp only [lookupType]
    rw [lookup_eq_2]
    apply ih

@[reducible]
def Schema.pick {η : Type u_η} [DecidableEq η] (s : @Schema η)
    : List (CertifiedName s) → @Schema η
| [] => []
| c::cs => lookup s c :: pick s cs

@[reducible]
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

@[reducible]
def Schema.hasRetypedName {τ : Type u} :
  ∀ {retNm nm : η} {sch : @Schema η} {hretNm : sch.HasName retNm},
  sch.HasName nm →
  (retypeColumn sch hretNm τ).HasName nm
| _, _, (_, _) :: hs, .hd, .hd => .hd
| _, _, (_, _) :: hs, .hd, .tl h => .tl h
| _, _, (_, _) :: hs, .tl h, .hd => .hd
| _, _, (_, _) :: hs, .tl h, .tl h' => .tl $ hasRetypedName h'

@[reducible]
def Schema.hasRetypedCol {τ₁ τ₂} : ∀ {sch : @Schema η}
  (c : (c : η) × sch.HasCol (c, τ₁)),
  HasCol (c.1, τ₂) (retypeColumn sch (colImpliesName c.snd) τ₂)
| [], ⟨_, pf⟩ => nomatch pf
| _ :: _, ⟨_, .hd⟩ => Schema.HasCol.hd
| _ :: _, ⟨nm, Schema.HasCol.tl htl⟩ =>
  Schema.HasCol.tl $ hasRetypedCol ⟨nm, htl⟩

@[reducible]
def RetypedSubschema.toSchema {schm : @Schema η} :
  RetypedSubschema schm → @Schema η
| [] => []
| ⟨hdr, _⟩ :: ss => hdr :: toSchema ss

@[reducible]
def Schema.schemaHasRetypedSubschemaName : {nm : η} →
  {schema : @Schema η} → {rs : RetypedSubschema schema} →
  (h : rs.toSchema.HasName nm) → schema.HasName nm
| _, s₁ :: ss₁, ⟨hdr, pf⟩ :: ss₂, Schema.HasName.hd => pf
| nm, schema₁, schema₂@(⟨hdr, pf⟩ :: ss), Schema.HasName.tl h =>
  have term_helper : sizeOf h < sizeOf (@Schema.HasName.tl η hdr _ _ h) := by
    simp
  schemaHasRetypedSubschemaName h

@[reducible]
def Schema.hasNameOfRetypedHasName :
  ∀ {sch : @Schema η}
    {hn : sch.HasName nm},
    HasName c (retypeColumn sch hn τ') →
    HasName c sch
| (_, _) :: _, .hd, hn => by
  cases hn with
  | hd => exact .hd
  | tl h => exact .tl h
| (_, _) :: _, .tl h, hn => by
  cases hn with
  | hd => exact .hd
  | tl h =>
    exact .tl (hasNameOfRetypedHasName h)

@[reducible]
def Schema.hasNameOfRetypedHasName_hasRetypedName :
  ∀ {sch : @Schema η}
    {nm nm'}
    {τ}
    { h : sch.HasName nm }
    {h' : sch.HasName nm'},
  hasNameOfRetypedHasName (hasRetypedName (retNm := nm') (hretNm := h') (τ := τ) h) = h
| _, _, _, _, .hd, .hd => rfl
| _, _, _, _, .hd, .tl h => rfl
| _, _, _, _, .tl h, .hd => rfl
| _, _, _, _, .tl h, .tl h' => by
  simp only [hasRetypedName, hasNameOfRetypedHasName]
  rw [Schema.HasName.tl.injEq]
  apply hasNameOfRetypedHasName_hasRetypedName

@[reducible]
def Schema.retypedHasOtherCol :
  ∀ {sch : @Schema η}
    {c : η} {τ : Type _} {c' : η}
    (hn' : sch.HasName c'),
    c' ≠ c →
    sch.HasCol (c, τ) →
    Schema.HasCol (c, τ) (retypeColumn sch hn' τ')
| _, c, τ, c', .hd, hneq, .tl h => .tl h
| _, c, τ, c', .tl hn', hneq, .tl hc => .tl (retypedHasOtherCol hn' hneq hc)
| _, c, τ, c', .tl hn', hneq, .hd => .hd

-- Could use `{xs : List τ // xs.length = n}` instead of `List τ` if needed
@[reducible]
def Schema.flattenList (schema : @Schema η)
  (c : ((c : η) × (τ : Type u) × schema.HasCol (c, List τ)))
    : @Schema η :=
  schema.retypeColumn (Schema.colImpliesName c.2.2) c.2.1

@[reducible]
def Schema.flattenLists : (schema : @Schema η) →
                          (ActionList flattenList schema) →
                         @Schema η
| ss, ActionList.nil => ss
| ss, ActionList.cons c cs => flattenLists (flattenList ss c) cs

@[reducible]
def Schema.renameColumn {η : Type u_η} [DecidableEq η]
    : {nm : η} → (s : @Schema η) → s.HasName nm → η → @Schema η
| _, (nm, τ) :: cs, Schema.HasName.hd, nm' => (nm', τ) :: cs
| _, c :: cs, Schema.HasName.tl h, nm' => c :: renameColumn cs h nm'

@[reducible]
def Schema.renameColumnCN {η : Type u_η} [DecidableEq η]
                          (s : @Schema η)
                          (entry : (nmAndNew : η × η) × s.HasName nmAndNew.1)
    : @Schema η :=
  renameColumn s entry.2 entry.1.2

@[reducible]
def Schema.renameColumns {η : Type u_η} [DecidableEq η]
    : (s : @Schema η) → ActionList renameColumnCN s → @Schema η
| s, ActionList.nil => s
| s, ActionList.cons c ccs => renameColumns (renameColumnCN s c) ccs

@[reducible]
def Schema.hasColOfNotMemRenameColumnCN :
  ∀ {sch : @Schema η} {nm} {c : η}
    (hc : sch.HasCol (c, τ))
    (hnm : sch.HasName nm)
    (hneq : c ≠ nm),
    HasCol (c, τ) (renameColumnCN sch ⟨(nm, nm'), hnm⟩)
| (_, _) :: _, nm, c, .tl hc, .hd, hneq => .tl hc
| (_, _) :: _, nm, c, .hd, .tl hn, hneq => .hd
| (_, _) :: _, nm, c, .tl hc, .tl hn, hneq =>
  .tl $ hasColOfNotMemRenameColumnCN hc hn hneq

@[reducible]
def Schema.hasColOfNotMemRenameColumns {sch : @Schema η} {c : η}  :
  ∀ (ccs : ActionList Schema.renameColumnCN sch)
    (hc : sch.HasCol (c, τ)),
    (∀ {sch' : @Schema η} c' (hc : sch'.HasName c),
      NotT (ActionList.MemT ⟨(c, c'), hc⟩ ccs)) →
    Schema.HasCol (c, τ) (sch.renameColumns ccs)
| .nil, hc, hnmem => hc
| .cons ⟨(nm, nm'), hnm⟩ ccs, hhc, hnmem =>
  have hneq : c ≠ nm := (fun heq => Empty.elim $
      hnmem nm' (heq.symm ▸ hnm) (by subst heq; apply ActionList.MemT.head)
    )
  hasColOfNotMemRenameColumns ccs
    (hasColOfNotMemRenameColumnCN hhc hnm hneq)
    (fun c' hhnc hneg => hnmem c' hhnc (.tail _ _ hneg))

omit dec_η in
theorem Schema.removeName_sublist :
  ∀ (s : @Schema η) (c : η) (hc : HasName c s), List.Sublist (s.removeName hc) s
| _, _, HasName.hd => List.Sublist.cons _ (List.sublist_self _)
| _, _, HasName.tl h => List.Sublist.cons₂ _ (removeName_sublist _ _ h)

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

@[reducible]
def Schema.schemaHasLookup : (schema : @Schema η) → (c : CertifiedName schema)
    → schema.HasCol (schema.lookup c)
| _, ⟨_, Schema.HasName.hd⟩ => Schema.HasCol.hd
| _ :: s', ⟨c, Schema.HasName.tl h⟩ =>
  Schema.HasCol.tl (schemaHasLookup s' ⟨c, h⟩)

@[reducible]
def Schema.schemaHasLookupType :
  (schema : @Schema η) → (nm : η) → (hnm : schema.HasName nm) →
  schema.HasCol (nm, schema.lookupType ⟨nm, hnm⟩)
| _, _, .hd => .hd
| _, _, .tl h => .tl (schemaHasLookupType _ _ h)

@[reducible]
def Schema.schemaHasSubschema : {nm : η} → {τ : Type u} →
                                {schema : @Schema η} →
                                {subschema : Subschema schema} →
                                (h : subschema.toSchema.HasCol (nm, τ)) →
    schema.HasCol (nm, τ)
| _, _, s₁ :: ss₁, ⟨hdr, pf⟩ :: ss₂, Schema.HasCol.hd => pf
| nm, τ, schema₁, schema₂@(⟨hdr, pf⟩ :: ss), Schema.HasCol.tl h =>
  have term_helper : sizeOf h < sizeOf (@Schema.HasCol.tl η hdr _ _ _ h) := by
    simp
  schemaHasSubschema h

-- `removeHeader` (and, for completeness, `removeName`) preservation
-- for non-elements of the action list
-- Used for `leftJoin` spec 3 and `pivotLonger` spec 2

@[reducible]
def Schema.removeNameHasName : ∀ {sch : @Schema η} {c c'},
  c ≠ c' →
  (h : sch.HasName c') →
  HasName c sch →
  HasName c (sch.removeName h)
| _, _, _, _, .tl _, .hd => .hd
| _, _, _, hneq, .tl h', .tl h => .tl <| removeNameHasName hneq h' h
| _, _, _, _, .hd, .tl h => h

@[reducible]
def Schema.removeHeaderHasCol : ∀ {sch : @Schema η} {c τ c' τ'},
  (c, τ) ≠ (c', τ') →
  (h : sch.HasCol (c', τ')) →
  HasCol (c, τ) sch →
  HasCol (c, τ) (sch.removeHeader h)
| _, _, _, _, _, _, .tl _, .hd => .hd
| _, _, _, _, _, hneq, .tl h', .tl h => .tl <| removeHeaderHasCol hneq h' h
| _, _, _, _, _, _, .hd, .tl h => h

-- A more granular specification for `removeHeader` not used in the B2T2 specs
@[reducible]
def Schema.removeHeaderHasCol' : ∀ {sch : @Schema η} {c τ c' τ'},
  (h' : sch.HasCol (c', τ')) →
  (h : HasCol (c, τ) sch) →
  (∀ heq : (c, τ) = (c', τ'), h ≠ heq ▸ h') →
  HasCol (c, τ) (sch.removeHeader h')
| _, _, _, _, _, .tl _, .hd, _ => .hd
| s :: ss, c, τ, c', τ', .tl h', .tl h, hneq =>
  .tl <| removeHeaderHasCol' h' h (fun hneg heq =>
    (heq ▸ hneq hneg)
      (Eq.cast_distrib_fun (τ := (Schema.HasCol · ss))
        hneg.symm HasCol.tl h').symm
  )
| _, _, _, _, _, .hd, .tl h, _ => h
| _, _, _, _, _, .hd, .hd, hneq => nomatch hneq rfl

-- For `pivotLonger_spec2`, using `removeHeaderHasCol`
@[reducible]
def Schema.removeTypedNamesHasCol {sch : @Schema η} {c τ} :
  ∀ (cs : ActionList (Schema.removeTypedName τ) sch)
    (hc : sch.HasCol (c, τ)),
    (∀ {sch' : @Schema η} (hc : sch'.HasCol (c, τ)),
      NotT (ActionList.MemT ⟨c, hc⟩ cs)) →
    (sch.removeTypedNames cs).HasCol (c, τ)
| .nil, hc, hnmem => hc
| .cons ⟨nm, hnm⟩ cs, hc, hnmem => by
  unfold removeTypedNames
  unfold removeTypedName
  simp only
  apply Schema.removeTypedNamesHasCol (sch := sch.removeHeader hnm) cs
  case hc =>
    apply removeHeaderHasCol _ _ hc
    intro hneg
    cases hneg
    apply Empty.elim
    apply hnmem hnm
    exact .head _
  case a =>
    intro sch' hc' hneg
    apply hnmem hc'
    apply ActionList.MemT.tail
    exact hneg

-- `pivotWider` stuff
@[reducible]
def Schema.hasColOfMemT : List.MemT (x, τ) xs → Schema.HasCol (x, τ) xs
  | .hd _ _ => .hd
  | .tl _ htl => .tl $ hasColOfMemT htl


-- Unique schemata
-- A *unique* schema is one with distinct header names. Unique schemata are
-- required by the B2T2 spec.
abbrev Schema.Unique {η : Type u_η} (ss : @Schema η) := List.Unique ss.names

/- Homogeneous Schemata -/
inductive Schema.Homogeneous (τ : Type _) : @Schema η → Type _
  | nil : Schema.Homogeneous τ []
  | cons : Schema.Homogeneous τ hs → Schema.Homogeneous τ ((nm, τ) :: hs)

-- Turn an arbitrarily-typed header proof for a homogeneous schema into a
-- homogeneously-typed one
@[reducible]
def Schema.homogenizeHC {nm τ} :
    {σ : Type _} → {sch : @Schema η} →
    sch.Homogeneous τ →
    sch.HasCol (nm, σ) →
    sch.HasCol (nm, τ)
  | .(τ), _ :: _, .cons _, .hd => .hd
  | _, _ :: _, .cons hh', .tl hc' => .tl $ homogenizeHC hh' hc'

/- ActionList helpers -/

def ActionList.length {sch : @Schema η} {κ : @Schema η → Type u}
    {f : ∀ (s : @Schema η), κ s → @Schema η} :
    ActionList f sch → Nat
  | .nil => 0
  | .cons _ tl => 1 + length tl

/--
Takes an ActionList along with a "preservation" function that maps action list
entries "in reverse" (i.e., enables them to be "lifted" to a schema prior to
the ActionList's associated transformation) and generates a list of action list
entries at the top-level (original, pre-transformation) schema.
-/
@[semireducible] def ActionList.toList {sch : @Schema η} {κ : @Schema η → Type u}
    {f : ∀ (s : @Schema η), κ s → @Schema η}
    (pres : ∀ (s : @Schema η) (k : κ s), κ (f s k) → κ s)
    : ActionList f sch → List (κ sch)
| ActionList.nil => []
| ActionList.cons hdr xs => hdr :: (toList pres xs).map (pres sch hdr)

def BiActionList.toList {schs : @Schema η × @Schema η}
    {κ : @Schema η × @Schema η → Type u}
    {f : ∀ (ss : @Schema η × @Schema η), κ ss → @Schema η × @Schema η}
    (pres : ∀ (ss : @Schema η × @Schema η) (k : κ ss), κ (f ss k) → κ ss)
    : BiActionList f schs → List (κ schs)
| BiActionList.nil => []
| BiActionList.cons x xs =>
  have hterm : sizeOf xs < sizeOf (cons x xs) := by simp
  x :: (toList pres xs).map (pres schs x)
