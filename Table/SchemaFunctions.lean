import Table.Schema

universe u_η
universe u

variable {η : Type u_η} [dec_η : DecidableEq η] {schema : @Schema η}

/- # Reducible Reimplementations of List Functions

A number of non-reducible list functions are reimplemented here as reducible
`Schema` functions, as Lean 4 doesn't allow us to modify the reducibility
attribute of functions from outside the modules in which they are declared.

This file also contains schema functions and proofs that depend upon such
functions. -/

@[reducible]
def Schema.append {α} : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: append xs ys

theorem Schema.append_eq_List_append :
  ∀ (s s' : List α), Schema.append s s' = List.append s s'
  | [], _ => rfl
  | h :: hs, hs' => congrArg (h :: ·) $ append_eq_List_append hs hs'

@[reducible]
def Schema.map {α β} : (α → β) → List α → List β
  | _, [] => []
  | f, x :: xs => f x :: map f xs

-- @[simp]
theorem Schema.map_eq_List_map : @Schema.map = @List.map := by
  funext _ _ _ xs
  induction xs with
  | nil => rfl
  | cons _ _ ih =>
    simp only [map, List.map]
    exact congrArg _ ih

@[reducible]
def Schema.length {α} : List α → Nat
  | [] => 0
  | _ :: xs => length xs + 1

theorem Schema.length_eq_List_length : @Schema.length = @List.length := by
  funext _ xs
  induction xs with
  | nil => rfl
  | cons _ _ ih =>
    simp only [length, List.length]
    exact congrArg _ ih

@[reducible]
def Schema.nth {α} : (xs : List α) → (n : Nat) →
                     (n < Schema.length xs) → α
| x :: xs, 0, h => x
| x :: xs, Nat.succ n, h => nth xs n (Nat.le_of_succ_le_succ h)

theorem Schema.nth_eq_get :
  ∀ (xs : List α) (n : Nat) (hn : n < Schema.length xs),
  Schema.nth xs n hn = xs.get ⟨n, Schema.length_eq_List_length ▸ hn⟩
| x :: xs, 0, h => rfl
| x :: xs, Nat.succ n, h => nth_eq_get xs n (Nat.le_of_succ_le_succ h)

@[reducible]
def Schema.nths {α} (xs : List α) (ns : List (Fin $ Schema.length xs))
  : List α :=
  Schema.map (λ n => Schema.nth xs n.1 n.2) ns

theorem Schema.length_nths (xs : List α) (ns : List (Fin $ Schema.length xs)) :
  List.length (Schema.nths xs ns) = List.length ns := by
  rw [nths, Schema.map_eq_List_map]
  apply List.length_map

@[reducible]
def Schema.sieve {α} : List Bool → List α → List α
| [], xs => xs
| _, [] => []
| true :: bs, x :: xs => x :: sieve bs xs
| false :: bs, _ :: xs => sieve bs xs

theorem Schema.sieve_eq_List_sieve : @Schema.sieve = @List.sieve :=
funext λ τ => funext λ bs => funext λ xs =>
  let rec pf : ∀ bs xs, sieve bs xs = List.sieve bs xs := λ
    | [], xs => by rw [sieve]; simp only [List.sieve]
    | _ :: _, [] => by rw [sieve] <;> simp [List.sieve]
    | true :: bs, x :: xs => congrArg (x :: ·) (pf bs xs)
    | false :: bs, _ :: xs => pf bs xs
  pf bs xs

-- Schema proof generation/manipulation functions
@[reducible]
def Schema.certify : (schema : @Schema η) → List (CertifiedHeader schema)
  | [] => []
  | (c, τ) :: hs =>
    let mapSubproof :=
      λ (⟨hdr, h⟩ : CertifiedHeader hs) => ⟨hdr, Schema.HasCol.tl h⟩
    ⟨(c, τ), Schema.HasCol.hd⟩ :: Schema.map mapSubproof (certify hs)

@[reducible]
def Schema.certifyNames (schema : @Schema η) : List (CertifiedName schema) :=
  schema.certify
    |> Schema.map (λ (⟨(c, _), h⟩ : CertifiedHeader schema) =>
                    ⟨c, colImpliesName h⟩)

/- -------------------- -/

theorem List.length_rw {T : α → Type _} {s t : α} :
  ∀ (xs : List (T s)) (h : s = t), xs.length = (h ▸ xs).length
  | _, .refl _ => rfl


-- Lemmas for selectColumns2_spec2

theorem Schema.get_map_nths_eq_get_get :
  ∀ (xs : List (α × β)) (ns : List (Fin $ Schema.length xs)) (i : Nat)
    (hi : i < ns.length),
  (List.map Prod.fst (nths xs ns)).get ⟨i,
    List.length_map (nths xs ns) Prod.fst ▸ length_nths xs ns ▸ hi
  ⟩ =
  (List.map Prod.fst xs).get ⟨(ns.get ⟨i, hi⟩).val,
    (List.length_map xs Prod.fst) ▸
    (Eq.subst (Schema.length_eq_List_length ▸ rfl)
              (List.get ns ⟨i, hi⟩).isLt)
  ⟩
| xs, n :: ns, 0, hi => by
  simp only [nths, map, get]
  rw [nth_eq_get]
  simp only [List.get]
  rw [List.get_map Prod.fst]
| xs, n :: ns, .succ i, hi => by
  simp only [nths, map, get]
  have ih := get_map_nths_eq_get_get xs ns i (Nat.lt_of_succ_lt_succ hi)
  simp only [List.get]
  rw [←ih]

@[reducible]
def Schema.hasAppendedHead :
  ∀ (sch : @Schema η) (c : η) (τ : Type _) (hs : List Header),
  HasCol (c, τ) (Schema.append sch ((c, τ) :: hs))
| [], _, _, _ => .hd
| s :: ss, c, τ, _ => .tl (hasAppendedHead ss c τ _)

@[reducible]
def Schema.hasNameOfAppend : {sch : @Schema η} →
                                 {nm : η} →
                                 {hs : @Schema η} →
                                 sch.HasName nm →
  -- Schema.HasName nm (Schema.append sch hs)
  Schema.HasName nm (Schema.append sch hs)
| _, _, _, Schema.HasName.hd => Schema.HasName.hd
| _, _, _, Schema.HasName.tl h => Schema.HasName.tl $ hasNameOfAppend h

@[reducible]
def Schema.hasColOfAppend : {sch : @Schema η} →
                                 {nm : η} →
                                 {τ : Type u} →
                                 {hs : List Header} →
                                 sch.HasCol (nm, τ) →
  Schema.HasCol (nm, τ) (Schema.append sch hs)
| _, _, _, _, Schema.HasCol.hd => Schema.HasCol.hd
| _, _, _, _, Schema.HasCol.tl h => Schema.HasCol.tl $ hasColOfAppend h

@[reducible]
def Schema.hasColOfPrepend : {sch : @Schema η} →
                                 {nm : η} →
                                 {τ : Type u} →
                                 {hs : @Schema η} →
                                 sch.HasCol (nm, τ) →
  Schema.HasCol (nm, τ) (Schema.append hs sch)
| _, _, _, [], pf => pf
| _, _, _, _ :: hs', pf => .tl $ hasColOfPrepend (hs := hs') pf

theorem Schema.lookup_eq_lookup_append :
  ∀ (s : @Schema η) (t : @Schema η) (c : η) (h : s.HasName c),
  lookup s ⟨c, h⟩ = lookup (Schema.append s t) ⟨c, Schema.hasNameOfAppend h⟩ :=
by intros s t c h
   induction h with
   | hd =>
     simp only [Schema.hasNameOfAppend]
   | tl h' ih =>
     simp only [Schema.hasNameOfAppend]
     rw [Schema.lookup_eq_2, Schema.lookup_eq_2]
     exact ih

-- Used in `dropColumn_spec2` proof
omit dec_η in
theorem Schema.mem_map_of_HasName : ∀ (sch : @Schema η) (nm : η),
  Schema.HasName nm sch → nm ∈ Schema.map Prod.fst sch := by
  intro sch nm h
  induction h with
  | hd =>
    apply List.Mem.head
  | tl _ ih =>
    apply List.Mem.tail
    apply ih


@[simp] theorem Schema.length_map : ∀ (f : α → β) (xs : List α),
  Schema.length (Schema.map f xs) = Schema.length xs
  | f, [] => rfl
  | f, x :: xs => congrArg (·+1) $ length_map f xs

@[reducible]
def Schema.retypedFromSubschemaFueled :
  ∀ {sch : @Schema η}, Nat → RetypedSubschema sch → @Schema η
| hs, 0, _ => hs
| hs, _, [] => hs
| hs, n + 1, ⟨(_, ρ), pf⟩ :: rs =>
  @retypedFromSubschemaFueled (hs.retypeColumn pf ρ) n
    (Schema.map (λ ⟨h, pf⟩ => ⟨h, Schema.hasRetypedName pf⟩) rs)

@[reducible]
def Schema.retypedFromSubschema {sch : @Schema η} (rs : RetypedSubschema sch) :
    @Schema η :=
  retypedFromSubschemaFueled (Schema.length rs) rs

/- Retype from subschema: `update` -/
-- FIXME: despite it being marked reducible, type-class resolution can't see
-- through this function
-- @[reducible]
-- def Schema.retypedFromSubschema :
--   ∀ {sch : @Schema η}, RetypedSubschema sch → @Schema η
-- | hs, [] => hs
-- | hs, ⟨(_, ρ), pf⟩ :: rs =>
--   have := Schema.length_map
--     (α := (h : Header) × hs.HasName h.fst)
--     (β := (h : Header) × (hs.retypeColumn pf ρ).HasName h.fst)
--     (λ ⟨h, pf⟩ => ⟨h, Schema.hasRetypedName pf⟩)
--     rs
--   @retypedFromSubschema (hs.retypeColumn pf ρ)
--     (Schema.map (λ ⟨h, pf⟩ => ⟨h, Schema.hasRetypedName pf⟩) rs)
-- termination_by retypedFromSubschema rs => Schema.length rs

def Schema.retypedSubschemaFueledHasSchemaName :
  ∀ {sch : @Schema η} {nm : η} (n : Nat) (rs : RetypedSubschema sch),
  n = Schema.length rs → HasName nm sch → HasName nm (Schema.retypedFromSubschemaFueled n rs)
| sch, nm, n, [], hn, hnm => hn ▸ hnm
| (_, _) :: _, nm, n + 1, ⟨(_, _), _⟩ :: rs', hn, pf =>
  retypedSubschemaFueledHasSchemaName n (Schema.map _ rs')
    (Schema.length_map _ rs' ▸ Nat.succ.inj hn) (Schema.hasRetypedName pf)

@[reducible]
def Schema.retypedSubschemaHasSchemaName
    {sch : @Schema η} {nm : η} (rs : RetypedSubschema sch)
    (hnm : HasName nm sch) : HasName nm (Schema.retypedFromSubschema rs) :=
  retypedSubschemaFueledHasSchemaName _ _ rfl hnm
-- @[reducible]
-- def Schema.retypedSubschemaHasSchemaName :
--   ∀ {sch : @Schema η} {nm : η} (rs : RetypedSubschema sch),
--   HasName nm sch → HasName nm (Schema.retypedFromSubschema rs)
-- | sch, nm, [], hnm => hnm
-- | (_, _) :: _, nm, ⟨(_, _), _⟩ :: rs', pf =>
--   retypedSubschemaHasSchemaName (Schema.map _ rs') (Schema.hasRetypedName pf)
-- termination_by _ _ rs h => Schema.length rs

@[reducible]
def Schema.retypedFromSubschemaHasNameOfRSToSchema :
  ∀ {sch : @Schema η} {rs : RetypedSubschema sch} {nm : η},
  HasName nm rs.toSchema → HasName nm (Schema.retypedFromSubschema rs)
| [], ⟨_, hrs⟩ :: _, _, _ => nomatch hrs
| (_, _) :: _, [_], _, .tl h => nomatch h
| sch, ⟨hdr, hnm⟩ :: rest, nmToFind, hntf =>
  let hsch := Schema.schemaHasRetypedSubschemaName hntf
  retypedSubschemaHasSchemaName _ hsch

theorem Schema.retypedFromSubschema_preserves_names :
  ∀ (sch : @Schema η) (rs : RetypedSubschema sch),
  Schema.names (Schema.retypedFromSubschema rs) = Schema.names sch
| ss, [] => rfl
| (_, _) :: ss, ⟨(nm, τ), pf⟩ :: rs =>
  by
    unfold retypedFromSubschema
    unfold retypedFromSubschemaFueled
    rw [← Schema.length_map]
    have := retypedFromSubschema_preserves_names (Schema.retypeColumn _ pf τ)
      (Schema.map (fun ⟨h, pf⟩ => ⟨h, hasRetypedName pf⟩) rs)
    rw [this]
    simp only [retypeColumn_preserves_names]
-- We don't bother with a two-stage fueled definition here, since for theorems, well-founded
-- recursion isn't a problem, and we don't need this theorem for the fueled helper function
termination_by sch rs => Schema.length rs

@[reducible]
def Schema.memTMapRetypedNameOfMemThasNameOfRetypedHasName
  {nm nm' : η} {τ τ' : Type u} {hn' : sch.HasName nm'}
  {hnm : HasName nm (retypeColumn sch hn' τ')} {rs : RetypedSubschema sch} :
  List.MemT (⟨(nm, τ), hnm⟩ : (h : Header) ×
                              HasName h.fst (retypeColumn sch hn' τ'))
            (map (fun x => ⟨x.1, hasRetypedName x.2⟩) rs) →
  List.MemT ⟨(nm, τ), hasNameOfRetypedHasName hnm⟩ rs := by
  intro h
  cases rs with
  | nil => contradiction
  | cons r rs =>
    simp only [map] at h
    rcases r with ⟨⟨rnm, rτ⟩, rpf⟩
    cases h with
    | hd =>
      rw [hasNameOfRetypedHasName_hasRetypedName]
      apply List.MemT.hd
    | tl h =>
      apply List.MemT.tl
      apply memTMapRetypedNameOfMemThasNameOfRetypedHasName
      assumption

@[reducible]
def Schema.retypedFromSubschemaHasColOfNotMemTFueled :
  ∀ {sch : @Schema η} (subsch : RetypedSubschema sch) (n : Nat),
    n = Schema.length subsch →
    (∀ τ' hn, NotT (List.MemT ⟨(c, τ'), hn⟩ subsch)) →
    sch.HasCol (c, τ) →
    Schema.HasCol (c, τ) (Schema.retypedFromSubschemaFueled n subsch)
| _, [], 0, hn, h, hc => hc
| _, [], n + 1, hn, h, hc => hc
| .((c, τ)) :: hs, ⟨(nm', τ'), hn'⟩ :: rs, n + 1, hn, hnmem, .hd =>
  have hneq : nm' ≠ c := fun heq =>
    Empty.elim $ hnmem τ' (heq ▸ hn') (by subst heq; apply List.MemT.hd)
  retypedFromSubschemaHasColOfNotMemTFueled
    (map (fun x => ⟨x.fst, hasRetypedName x.snd⟩) rs)
    n
    (Nat.succ.inj (Schema.length_map _ _ |>.symm ▸ hn))
    (fun τ'' hn hneg =>
      hnmem τ'' (hasNameOfRetypedHasName hn) (.tl _ $
        memTMapRetypedNameOfMemThasNameOfRetypedHasName hneg))
    (retypedHasOtherCol hn' hneq .hd)
| _ :: hs, ⟨(nm', τ'), hn'⟩ :: rs, n + 1, hn, hnmem, .tl h =>
  have hneq : nm' ≠ c := fun heq =>
    Empty.elim $ hnmem τ' (heq ▸ hn') (by subst heq; apply List.MemT.hd)
  retypedFromSubschemaHasColOfNotMemTFueled
    (map (fun x => ⟨x.fst, hasRetypedName x.snd⟩) rs)
    n
    (Nat.succ.inj (Schema.length_map _ _ |>.symm ▸ hn))
    (fun τ'' hn hneg =>
      hnmem τ'' (hasNameOfRetypedHasName hn) (.tl _ $
        memTMapRetypedNameOfMemThasNameOfRetypedHasName hneg))
    (retypedHasOtherCol hn' hneq (.tl h))

@[reducible]
def Schema.retypedFromSubschemaHasColOfNotMemT
    {sch : @Schema η} (subsch : RetypedSubschema sch)
    (hnmem : ∀ τ' hn, NotT (List.MemT ⟨(c, τ'), hn⟩ subsch))
    (hc : sch.HasCol (c, τ)) :
    Schema.HasCol (c, τ) (Schema.retypedFromSubschema subsch) :=
  retypedFromSubschemaHasColOfNotMemTFueled subsch (Schema.length subsch) rfl hnmem hc

/- fromCHeaders -/
@[reducible]
def Schema.fromCHeaders {schema : @Schema η}
                        (cs : List (CertifiedHeader schema))
    : @Schema η :=
  Schema.map Sigma.fst cs

-- def Schema.hasColFromHeadersOfHasCol {c : η} {τ : Type u} :
--   (cs : List (CertifiedHeader sch)) →
--   (pf : sch.HasCol (c, τ)) →
--   pf ∈ cs.map (·.2) →
--   (Schema.fromCHeaders cs).HasCol (c, τ)
-- | .head, c :: cs, .hd => .hd

@[reducible]
def Schema.hasNameOfFromCHeaders :
  ∀ {sch : @Schema η} {cs : List $ CertifiedHeader sch} {nm : η},
  Schema.HasName nm (Schema.fromCHeaders cs) → Schema.HasName nm sch
| [], ⟨hdr, hpf⟩ :: _, _, _ => nomatch hpf
| _ :: _, ⟨(nm, τ), hpf⟩ :: _, .(nm), .hd =>
  Schema.colImpliesName (τ := τ) hpf
| _ :: _, ⟨hdr, hpf⟩ :: cs, nm, .tl h => hasNameOfFromCHeaders h

omit dec_η in
theorem Schema.hasNameOfFromCHeaders_eq_1 :
  @hasNameOfFromCHeaders η sch (⟨(nm, τ), hpf⟩ :: cs) nm HasName.hd =
  colImpliesName hpf := by
  cases sch with
  | nil => contradiction
  | cons s ss => rw [hasNameOfFromCHeaders]

omit dec_η in
theorem Schema.hasNameOfFromCHeaders_eq_2 :
  @hasNameOfFromCHeaders η sch (⟨hdr, hpf⟩ :: cs) nm (HasName.tl h) =
  hasNameOfFromCHeaders h := by
  cases sch with
  | nil => contradiction
  | cons s ss => rw [hasNameOfFromCHeaders]

@[reducible]
def Schema.fromCHHasFromCH :
  ∀ {sch : @Schema η} (h : CertifiedHeader sch) (hs : List (CertifiedHeader sch)),
  List.MemT h hs → Schema.HasCol h.1 (Schema.fromCHeaders hs)
| _ :: _, ⟨(n, σ), pf⟩, _ :: hs, .hd _ _ => .hd
| _ :: _, ⟨(n, σ), pf⟩, _ :: hs, .tl _ htl => .tl $ fromCHHasFromCH _ hs htl

-- For `leftJoin_spec3`
@[reducible]
def Schema.removeOtherDecCHHasCol {s₁ s₂ : @Schema η} :
  ∀ (x : (hdr : @Header η) × DecidableEq hdr.2 × s₂.HasCol hdr × s₁.HasCol hdr)
    (hc : s₂.HasCol (c, τ)),
    (c, τ) ≠ x.1 →
    Schema.HasCol (c, τ) (s₁.removeOtherDecCH s₂ x) :=
  λ x hc hneq => Schema.removeHeaderHasCol hneq _ hc

@[reducible]
def Schema.removeOtherDecCHsHasCol {s₁ s₂ : @Schema η} :
  ∀ (cs : ActionList (Schema.removeOtherDecCH s₁) s₂)
    (hc : s₂.HasCol (c, τ)),
    (∀ {sch' : @Schema η} hdec hpf (hc : sch'.HasCol (c, τ)),
      NotT (ActionList.MemT ⟨(c, τ), hdec, hc, hpf⟩ cs)) →
    Schema.HasCol (c, τ) (s₁.removeOtherDecCHs s₂ cs)
| .nil, hc, hnmem => hc
| .cons x xs, hc, hnmem =>
  by
  unfold removeOtherDecCHs
  apply removeOtherDecCHsHasCol
  case hc =>
    apply removeOtherDecCHHasCol _ hc
    intro hneg
    cases x with | mk hdr rest =>
    cases rest with | mk x1 rest =>
    cases rest with | mk x2 x3 =>
    cases hdr with | mk nm τ' =>
    cases hneg
    apply Empty.elim
    apply hnmem x1 x3 x2
    apply ActionList.MemT.head
  . intro sch' hdec hpf hotherpf hneg
    apply hnmem hdec hpf hotherpf
    apply ActionList.MemT.tail
    exact hneg

-- For `leftJoin_spec4`
@[reducible]
def Schema.listCHOfActionListRemoveOtherDecCH {s₁ s₂ : @Schema η}
    (cs : ActionList (Schema.removeOtherDecCH s₁) s₂) :
  List (CertifiedHeader s₂) :=
  cs.toList Schema.removeOtherDecCHPres
  |>.map (λ | ⟨hdr, _, pf, _⟩ => ⟨hdr, pf⟩)

-- For `selectColumns3_spec2`
theorem Schema.lookupType_of_colImpliesName :
  ∀ {sch: @Schema η} (nm : η) (τ : Type u) (h : sch.HasCol (nm, τ)),
  lookupType sch ⟨nm, colImpliesName h⟩ = τ
| (nm, τ) :: _, .(nm), .(τ), .hd => rfl
| (nm, τ) :: sch', nm', τ', .tl h => lookupType_of_colImpliesName nm' τ' h

theorem Schema.lookupTypeFromCHeadersUnique :
  ∀ {sch : @Schema η} (cs : List (CertifiedHeader sch))
    (c : CertifiedName (Schema.fromCHeaders cs)),
    Schema.lookupType sch ⟨c.1, Schema.hasNameOfFromCHeaders c.2⟩ =
    Schema.lookupType (Schema.fromCHeaders cs) c
| [], [], ⟨_, h⟩ => nomatch h
| (nm, τ) :: hs, ⟨_, .hd⟩ :: cs, ⟨_, .hd⟩ => by
  simp only [lookupType]
  simp only [hasNameOfFromCHeaders_eq_1]
| (nm, τ) :: hs, ⟨(ch_nm, ch_τ), .tl h⟩ :: cs, ⟨.(ch_nm), .hd⟩ =>
  by
  simp only [lookupType]
  simp only [hasNameOfFromCHeaders_eq_1]
  rw [@colImpliesName_eq_2 η hs (nm, τ) (ch_nm, ch_τ) h]
  simp only [lookupType]
  apply lookupType_of_colImpliesName
| (nm, τ) :: hs, ⟨_, pf⟩ :: cs, ⟨s_nm, .tl hn⟩ => by
  simp only [lookupType]
  simp only [hasNameOfFromCHeaders_eq_2]
  exact lookupTypeFromCHeadersUnique cs ⟨s_nm, hn⟩

@[reducible]
def Schema.hasNthCol :
  ∀ {schema : @Schema η} (n : Fin $ Schema.length schema),
  schema.HasCol (Schema.nth schema n.val n.isLt)
| h :: hs, ⟨0, hlt⟩ => .hd
| h :: hs, ⟨.succ n, hlt⟩ => .tl (hasNthCol ⟨n, Nat.lt_of_succ_lt_succ hlt⟩)

@[reducible]
def Schema.hasNthName :
  ∀ {schema : @Schema η} (n : Fin $ Schema.length schema),
  schema.HasName (Schema.nth schema n.val n.isLt).1
| h :: hs, ⟨0, hlt⟩ => .hd
| h :: hs, ⟨.succ n, hlt⟩ => .tl (hasNthName ⟨n, Nat.lt_of_succ_lt_succ hlt⟩)

@[reducible]
def Schema.hasNameEqHeadOrTail :
  ∀ {nm : η} {hs : Schema},
  Schema.HasName nm ((nm', τ) :: hs) → nm' ≡ nm ⊕ HasName nm hs
| _, _, .hd => .inl (.refl _)
| _, _, .tl htl => .inr htl

@[reducible]
def Schema.hasNameOfNthsHasName :
  ∀ {schema : @Schema η} {ns : List (Fin $ Schema.length schema)} {nm : η},
    Schema.HasName nm (Schema.nths schema ns) →
    schema.HasName nm
| [], ⟨_, hlt⟩ :: ns, hdr, h => nomatch hlt
-- TODO: the better approach would be to directly pattern-match on `h`, but this
-- doesn't currently work:
| hs, n :: ns, hdr, h =>
  match hasNameEqHeadOrTail h with
    | .inl (.refl _) => hasNthName n
    | .inr hhnm => hasNameOfNthsHasName hhnm

theorem Schema.lookup_nth :
  ∀ {schema : @Schema η} (n : Nat) (hn : n < Schema.length schema),
    (Schema.nth schema n hn).snd =
    Schema.lookupType schema ⟨(Schema.nth schema n hn).fst,
                               Schema.hasNthName ⟨n, hn⟩⟩
| h :: hs, 0, hn => rfl
| h :: hs, .succ n, hn =>
  lookup_nth n (Nat.lt_of_succ_lt_succ hn)

theorem Schema.hasNameEqHeadOrTail_inl (h : Schema.HasName nm ((nm, τ) :: hs)) :
  (Schema.hasNameEqHeadOrTail h ≡ .inl (.refl _)) → h = .hd := by
  intro eqt
  simp only [hasNameEqHeadOrTail] at eqt
  cases h
  . rfl
  . contradiction

theorem Schema.hasNameEqHeadOrTail_inr
  (h : Schema.HasName nm (h :: hs))
  (htl) :
  (Schema.hasNameEqHeadOrTail h ≡ .inr htl) → h = .tl htl := by
  intro eqt
  simp only [hasNameEqHeadOrTail] at eqt
  cases h
  . contradiction
  . simp only at eqt
    cases eqt
    rfl

theorem Schema.lookupType_nths_eq_lookupType :
  ∀ {sch : @Schema η}
    (ns : List (Fin (Schema.length sch)))
    (nm : η)
    (pf : Schema.HasName nm (Schema.nths sch ns)),
  Schema.lookupType (Schema.nths sch ns) ⟨nm, pf⟩ =
  Schema.lookupType sch ⟨nm, Schema.hasNameOfNthsHasName pf⟩
| sch, [], nm, pf => nomatch pf
| (snm, sτ) :: sch, ⟨0, hlt⟩ :: ns, .(snm), .hd => by
  simp only [Schema.lookupType]
  unfold Schema.hasNameOfNthsHasName
  simp only [Schema.hasNameEqHeadOrTail, Schema.hasNthName, Schema.lookupType]
| (snm, sτ) :: sch, ⟨0, hlt⟩ :: ns, nm, .tl h => by
  conv =>
    lhs
    simp only [Schema.nths, Schema.map, Schema.lookupType]
  conv =>
    rhs
    unfold Schema.hasNameOfNthsHasName
    simp only [Schema.hasNameEqHeadOrTail]
  apply lookupType_nths_eq_lookupType
| (snm, sτ) :: sch, ⟨.succ n, pf⟩ :: ns, nm, hnths =>
  match h : Schema.hasNameEqHeadOrTail hnths with
  | .inr hhnm => by
    conv =>
      rhs
      unfold Schema.hasNameOfNthsHasName
      simp only [h]
    have htoprove : hnths = .tl hhnm :=
      Schema.hasNameEqHeadOrTail_inr _ _ (EqT.ofEq h)
    conv =>
      lhs
      simp only [Schema.nths, Schema.map, htoprove, Schema.lookupType]
    apply lookupType_nths_eq_lookupType
  | .inl heqt => by
    cases heqt
    have htoprove : hnths = .hd :=
      Schema.hasNameEqHeadOrTail_inl hnths (EqT.ofEq h)
    simp only [Schema.nths, Schema.map, Schema.lookupType, htoprove]
    unfold Schema.hasNameOfNthsHasName
    simp only [Schema.hasNameEqHeadOrTail, Schema.hasNthName, Schema.lookupType]
    apply Schema.lookup_nth
