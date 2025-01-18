import Table.API
import Init.Data.List.Lemmas

namespace Table

universe u u_η

variable {η : Type u_η} [dec_η : DecidableEq η] {sch : @Schema η}

-- `emptyTable`

theorem emptyTable_spec1 : @schema η dec_η _ emptyTable = [] := rfl

theorem emptyTable_spec2 : @nrows η dec_η _ emptyTable = 0 := rfl

-- `addRows`

-- We omit the precondition because it is enforced by the type system
theorem addRows_spec1 :
  ∀ (t : Table sch) (rs : List (Row sch)), schema (addRows t rs) = schema t :=
λ t rs => rfl

theorem addRows_spec2 :
  ∀ (t : Table sch) (rs : List (Row sch)),
    nrows (addRows t rs) = nrows t + rs.length := by
  intro t rs
  simp only [nrows, Schema.length_eq_List_length]
  exact List.length_append t.rows rs

-- `addColumn`

-- We omit the precondition because it is not required for this portion of the
-- spec
theorem addColumn_spec1 :
  ∀ {τ : Type u} (t : Table sch) (c : η) (vs : List (Option τ)),
    header (addColumn t c vs) = List.append (header t) [c]
:= by
  intros τ t c vs
  simp [header, addColumn, Schema.names]
  induction sch with
  | nil => simp [List.map, List.append]
  | cons s ss ih =>
    simp only [List.map]
    rw [ih]
    simp [List.append]
    -- We could avoid this by proving a separate lemma about schemata that
    -- doesn't take the (unused) table argument
    exact dropColumn t _

theorem addColumn_spec2 :
  ∀ {τ : Type u}
    (t : Table sch)
    (c : η)
    (vs : List $ Option τ)
    (c' : η)
    -- This is equivalent to `c ∈ header t`. (Unfortunately, we can't take the
    -- hypothesis in that form because creating a `HasName` therefrom would
    -- require large elimination from `Prop`)
    (h' : sch.HasName c'),
      (schema t).lookup ⟨c', h'⟩ =
      (schema (addColumn t c vs)).lookup ⟨c', Schema.hasNameOfAppend h'⟩ :=
λ t c vs c' h' => Schema.lookup_eq_lookup_append _ _ _ _

theorem addColumn_spec3 {τ : Type u} :
  ∀ (t : Table sch) (c : η) (vs : List $ Option τ),
    (schema (addColumn t c vs)).lookupType
      ⟨c, Schema.colImpliesName $ sch.hasAppendedHead c τ []⟩ = τ := by
  intros t c vs
  induction sch with
  | nil =>
    simp only [Schema.lookupType]
  | cons s ss ih =>
    simp only [Schema.lookupType]
    -- Again, this could be avoided by isolating the relevant proof into a
    -- separate lemma
    apply ih (dropColumn t _)

theorem addColumn_spec4 :
  ∀ {τ : Type u} (t : Table sch) (c : η) (vs : List $ Option τ),
    vs.length = nrows t →
    nrows (addColumn t c vs) = nrows t := by
  intros τ t c vs h
  simp only [nrows, addColumn, Schema.length_eq_List_length] at *
  simp only [List.length_map]
  rw [List.length_zipExtendingNone]

-- `buildColumn`

-- Spec 1 is enforced by the type system
theorem buildColumn_spec2 :
  ∀ {τ : Type u} (t : Table sch) (c : η) (f : Row sch → Option τ),
    header (buildColumn t c f) = List.append (header t) [c] :=
by intros τ t c f
   simp [header, Schema.names]
   induction sch with
  | nil => simp [List.map, List.append]
  | cons s ss ih =>
    simp only [List.map]
    rw [ih]
    simp [List.append]
    exact Table.mk []
    exact (λ x => f (Row.cons Cell.emp x))

theorem buildColumn_spec3 :
  ∀ {τ : Type u}
    (t : Table sch)
    (c : η)
    (f : Row sch → Option τ)
    (c' : η)
    (h' : sch.HasName c'),
      (schema t).lookup ⟨c', h'⟩ =
      (schema (buildColumn t c f)).lookup ⟨c', Schema.hasNameOfAppend h'⟩ :=
λ t c vs c' h' => Schema.lookup_eq_lookup_append _ _ _ _

theorem buildColumn_spec4 {τ : Type u} [DecidableEq τ] :
  ∀ (t : Table sch) (c : η) (f : Row sch → Option τ),
    (schema (buildColumn t c f)).lookupType
      ⟨c, Schema.colImpliesName $ sch.hasAppendedHead c τ []⟩ = τ := by
  intros t c f
  induction sch with
  | nil =>
    simp only [Schema.lookupType]
  | cons s ss ih =>
    simp only [Schema.lookupType]
    apply ih
    . exact (dropColumn t _)
    . exact f ∘ (Row.cons Cell.emp)

theorem buildColumn_spec5 :
  ∀ {τ : Type u} (t : Table sch) (c : η) (f : Row sch → Option τ),
    nrows (buildColumn t c f) = nrows t :=
by intros τ t c f
   simp only [buildColumn]
   rw [addColumn_spec4]
   rw [List.length_map]
   simp only [nrows, Schema.length_eq_List_length]

-- `vcat`

theorem vcat_spec1 :
  ∀ (t1 : Table sch) (t2 : Table sch),
    schema (vcat t1 t2) = schema t1 :=
λ _ _ => rfl

theorem vcat_spec2 :
  ∀ (t1 : Table sch) (t2 : Table sch),
    nrows (vcat t1 t2) = nrows t1 + nrows t2 := by
  intro t1 t2
  simp only [nrows, Schema.length_eq_List_length]
  exact List.length_append t1.rows t2.rows

-- `hcat`

-- This is precisely the type signature, but we can state it anyway
theorem hcat_spec1 :
  ∀ {sch₁ : @Schema η} {sch₂ : @Schema η} (t₁ : Table sch₁) (t₂ : Table sch₂),
    schema (hcat t₁ t₂) = List.append (schema t₁) (schema t₂) :=
λ _ _ => Schema.append_eq_List_append _ _ ▸ rfl

theorem hcat_spec2 :
  ∀ {sch₁ : @Schema η} {sch₂ : @Schema η} (t₁ : Table sch₁) (t₂ : Table sch₂),
    nrows t₁ = nrows t₂ → nrows (hcat t₁ t₂) = nrows t₁ :=
by intros sch₁ sch₂ t₁ t₂ h
   simp only [nrows, hcat, Schema.length_eq_List_length] at *
   rw [List.length_map]
   apply List.zip_length_eq_of_length_eq _ _ h

-- `values`

theorem values_spec1 :
  ∀ (rs : List (Row sch)),
    (h : rs ≠ []) → schema (values rs) = Row.schema (rs.head h) :=
λ rs h => rfl

theorem values_spec2 :
  ∀ (rs : List (Row sch)), nrows (values rs) = rs.length :=
λ rs => Schema.length_eq_List_length ▸ rfl

-- `crossJoin`

theorem crossJoin_spec1 :
  ∀ {sch₁ : @Schema η} {sch₂ : @Schema η} (t₁ : Table sch₁) (t₂ : Table sch₂),
    schema (crossJoin t₁ t₂) = List.append (schema t₁) (schema t₂) :=
λ _ _ => Schema.append_eq_List_append _ _ ▸ rfl

theorem crossJoin_spec2 :
  ∀ {sch₁ : @Schema η} {sch₂ : @Schema η} (t₁ : Table sch₁) (t₂ : Table sch₂),
    nrows (crossJoin t₁ t₂) = nrows t₁ * nrows t₂ :=
by intros sch₁ sch₂ t₁ t₂
   simp only [nrows, crossJoin, List.length_map, Schema.length_eq_List_length]
   apply List.length_prod

-- `leftJoin`

-- This is the closest we can approximate the spec given uniqueness issues
theorem leftJoin_spec1 {s₁ s₂ : @Schema η} :
  ∀ (t₁ : Table s₁) (t₂ : Table s₂)
    (cs : ActionList (Schema.removeOtherDecCH s₁) s₂),
  schema (leftJoin t₁ t₂ cs) =
  List.append (schema t₁)
              (Schema.removeOtherDecCHs (schema t₁) (schema t₂) cs) :=
λ _ _ _ => Schema.append_eq_List_append _ _ ▸ rfl

theorem leftJoin_spec2 {s₁ s₂ : @Schema η} :
  ∀ (t₁ : Table s₁) (t₂ : Table s₂)
    (cs : ActionList (Schema.removeOtherDecCH s₁) s₂)
    (c : η)
    (h : s₁.HasName c),
      (schema t₁).lookup ⟨c, h⟩ =
      (schema (leftJoin t₁ t₂ cs)).lookup ⟨c, Schema.hasNameOfAppend h⟩ :=
λ _ _ _ _ _ => Schema.lookup_eq_lookup_append _ _ _ _

def leftJoin_spec3 {s₁ s₂ : @Schema η}
  (t₁ : Table s₁) (t₂ : Table s₂)
  (cs : ActionList (Schema.removeOtherDecCH s₁) s₂)
  (c : η) (hc : s₂.HasCol (c, τ))
  (hnmem : ∀ {sch' : @Schema η} hdec hpf (hc : sch'.HasCol (c, τ)),
    NotT (ActionList.MemT ⟨(c, τ), hdec, hc, hpf⟩ cs)) :
  (schema (leftJoin t₁ t₂ cs)).HasCol (c, τ) :=
  Schema.hasColOfPrepend (Schema.removeOtherDecCHsHasCol cs hc hnmem)

-- This is a helper lemma for spec 4:
theorem unique_rows_of_distinct [DecidableEq (Row sch)] {t : Table sch} :
    distinct t = t → List.Unique t.rows := by
  intro h
  rcases t with ⟨rs⟩
  simp only [distinct, Table.mk.injEq, List.unique_eq_unique'] at h
  simp only
  rw [←h]
  apply List.unique'_Unique

theorem leftJoin_spec4.pick_lemma {s₁ s₂ : @Schema η}
  (t₂ : Table s₂) (r : Row s₁)
  (xs : List ((hdr : Header) × DecidableEq hdr.snd × Schema.HasCol hdr s₂ ×
              Schema.HasCol hdr s₁))
  :
  let pred :=
      (fun r₂ : Row s₂ =>
        xs.all fun c =>
          @decide (r.getCell c.snd.snd.snd = r₂.getCell c.snd.snd.fst)
            (@instDecidableEqCell η dec_η c.fst.fst c.fst.snd c.snd.fst
              (r.getCell c.snd.snd.snd) (r₂.getCell c.snd.snd.fst)
              : Decidable (r.getCell c.snd.snd.snd = r₂.getCell c.snd.snd.fst)))
  ∀ r' ∈ t₂.rows.filter pred,
  ∀ s' ∈ t₂.rows.filter pred,
  r'.pick (List.map (fun x => ⟨x.fst, x.2.2.fst⟩) xs) =
  s'.pick (List.map (fun x => ⟨x.fst, x.2.2.fst⟩) xs) := by
  intro pred r' hr' s' hs'
  cases xs with
  | nil => simp [Row.pick]
  | cons x xs =>
    simp only [Row.pick]
    have : r'.getCell x.2.2.1 = s'.getCell x.2.2.1 := by
      have hr'_pred : pred r' := List.filter_mem_pred_true t₂.rows _ _ hr'
      have hs'_pred : pred s' := List.filter_mem_pred_true t₂.rows _ _ hs'
      simp only [pred] at hr'_pred hs'_pred
      let inst (r' : Row s₂) : DecidablePred fun (x : (hdr : Header) ×
                                          DecidableEq hdr.snd ×
                                          Schema.HasCol hdr s₂ ×
                                          Schema.HasCol hdr s₁) =>
            r.getCell x.snd.snd.snd = r'.getCell x.snd.snd.fst :=
          λ c => @instDecidableEqCell η dec_η c.fst.fst c.fst.snd c.snd.fst
                    (r.getCell c.snd.snd.snd) (r'.getCell c.snd.snd.fst)
      apply Eq.trans (b := r.getCell x.2.2.2)
      · have hr_all := (@List.all_pred _ _ (inst r') _).mp hr'_pred
        apply Eq.symm
        apply hr_all
        apply List.Mem.head
      · have hs_all := (@List.all_pred _ _ (inst s') _).mp hs'_pred
        apply hs_all
        apply List.Mem.head
    apply congr (congrArg _ this)
    apply pick_lemma t₂ r
    . apply List.mem_filter_of_mem_filter_imp _ hr'
      intro x hx
      simp only [pred, List.all, Bool.and_eq_true] at hx
      exact hx.right
    . apply List.mem_filter_of_mem_filter_imp _ hs'
      intro x hx
      simp only [pred, List.all, Bool.and_eq_true] at hx
      exact hx.right

-- TODO: investigate why applications of `distinct` cannot resolve the necessary
-- decidable-equality instance when actually evaluating the expressions in the
-- antecedent below, even if `listCHOfActionListRemoveOtherDecCH` is rewritten
-- to use exclusively reducible functions (indeed, even unfolding that
-- definition and `ActionList.toList` in place -- so that the only remaining
-- definition is `Schema.map` -- gives the same error)
theorem leftJoin_spec4 {s₁ s₂ : @Schema η}
    (t₁ : Table s₁) (t₂ : Table s₂)
    (cs : ActionList (Schema.removeOtherDecCH s₁) s₂)
    [DecidableEq (Row (Schema.fromCHeaders
      (Schema.listCHOfActionListRemoveOtherDecCH cs)))] :
    distinct (selectColumns3 t₂ (Schema.listCHOfActionListRemoveOtherDecCH cs))
      = selectColumns3 t₂ (Schema.listCHOfActionListRemoveOtherDecCH cs) →
    nrows (leftJoin t₁ t₂ cs) = nrows t₁ := by
  intro hdistinct
  simp only [nrows]
  rw [Schema.length_eq_List_length, leftJoin, List.length_flatMap]
  unfold Function.comp
  rw [List.sum_map_const 1]
  . apply Nat.one_mul
  . intro r hr
    let pred :=
      (fun r₂ : Row s₂ =>
        (ActionList.toList Schema.removeOtherDecCHPres cs).all fun c =>
          @decide (r.getCell c.snd.snd.snd = r₂.getCell c.snd.snd.fst)
            (@instDecidableEqCell η dec_η c.fst.fst c.fst.snd c.snd.fst
              (r.getCell c.snd.snd.snd) (r₂.getCell c.snd.snd.fst)
              : Decidable (r.getCell c.snd.snd.snd = r₂.getCell c.snd.snd.fst)))
    match hmatch : t₂.rows.filter pred with
    | [] => simp only [List.length, leftJoin.findMatchingRows, hmatch]
    | f :: fs =>
      simp only [hmatch, leftJoin.findMatchingRows]
      suffices hnil : fs = [] by simp only [List.length_map, hnil, List.length]
      have huniq : List.Unique (t₂.rows.map
          (·.pick (Schema.listCHOfActionListRemoveOtherDecCH cs))) :=
        unique_rows_of_distinct hdistinct
      have h_filt_uniq : List.Unique $ (t₂.rows.filter pred).map
          (·.pick (Schema.listCHOfActionListRemoveOtherDecCH cs)) :=
        List.unique_sublist huniq (List.map_sublist_of_sublist _ _ _
                                    (List.filter_sublist _))
      have h_filt_eq :
        ∀ r' ∈ (t₂.rows.filter pred).map
          (·.pick (Schema.listCHOfActionListRemoveOtherDecCH cs)),
        ∀ s' ∈ (t₂.rows.filter pred).map
          (·.pick (Schema.listCHOfActionListRemoveOtherDecCH cs)),
        r' = s' := by
        simp only [List.mem_map, forall_exists_index, and_imp,
                   forall_apply_eq_imp_iff₂]
        intro r' hr' s' hs'
        simp only [Schema.listCHOfActionListRemoveOtherDecCH]
        apply leftJoin_spec4.pick_lemma _ _ _ _ hr' _ hs'
      cases List.nil_singleton_of_all_eq_unique h_filt_eq h_filt_uniq with
      | inl hnil => simp [hmatch] at hnil
      | inr hsing =>
        rw [hmatch] at hsing
        rcases hsing with ⟨x, hx⟩
        unfold List.map at hx
        cases fs with
        | cons _ _ => simp at hx
        | nil => rfl

-- The spec for `getValue` (as nearly as it can be approximated up to uniqueness
-- issues) is enforced by types

-- `getColumn1`

theorem getColumn1_spec1 :
  ∀ (t : Table sch) (n : Nat) (h : n < ncols t),
    List.length (getColumn1 t n h) = nrows t := by
  intro t n h
  simp only [getColumn1, nrows, Schema.length_eq_List_length]
  apply List.length_map

-- Spec 2 is encoded in the return type of `getColumn1`

-- `getColumn2`

-- Spec 1 is encoded in the return type of `getColumn2`

theorem getColumn2_spec2 :
  ∀ {τ : Type u} (t : Table sch) (c : η) (h : sch.HasCol (c, τ)),
    List.length (getColumn2 t c h) = nrows t := by
  intro τ t c h
  simp only [getColumn2, nrows, Schema.length_eq_List_length]
  apply List.length_map

-- `selectRows1`

-- Precondition is enforced by subtype
theorem selectRows1_spec1 :
  ∀ (t : Table sch) (ns : List (Fin (nrows t))),
    schema (selectRows1 t ns) = schema t :=
λ t ns => rfl

theorem selectRows1_spec2 :
  ∀ (t : Table sch) (ns : List (Fin (nrows t))),
    nrows (selectRows1 t ns) = ns.length := by
  intro t ns
  rw [selectRows1, nrows, Schema.length_eq_List_length]
  apply List.length_map

-- `selectRows2`

theorem selectRows2_spec1 :
  ∀ (t : Table sch) (bs : List Bool),
    schema (selectRows2 t bs) = schema t :=
λ t bs => rfl

theorem selectRows2_spec2 :
  ∀ (t : Table sch) (bs : List Bool),
    bs.length = nrows t →
    nrows (selectRows2 t bs) = (bs.removeAllEq [false]).length := by
  intro t bs h
  simp only [nrows, selectRows2, Schema.length_eq_List_length]
  apply List.sieve_removeAllEq
  rw [nrows, Schema.length_eq_List_length] at h
  exact h

-- `selectColumns1`

theorem selectColumns1_spec1 :
  ∀ (t : Table sch) (bs : List Bool),
    List.Sublist (header (selectColumns1 t bs)) (header t) := by
  intro t bs
  simp only [header, Schema.names, Schema.sieve_eq_List_sieve]
  exact List.map_sublist_of_sublist _ _ Prod.fst $ List.sieve_sublist bs sch

-- Helper for `selectColumns1_spec2`
theorem ncols_eq_header_length :
  ∀ (t : Table sch), ncols t = (header t).length := by
  intro t
  simp only [ncols, Schema.length_eq_List_length]
  apply Eq.symm
  apply List.length_map

theorem selectColumns1_spec2 :
  ∀ (hs : Schema.Unique sch) (t : Table sch) (bs : List Bool)
    (h : bs.length = ncols t) (i : Nat) (hlt : i < ncols t),
  (header t).get ⟨i, ncols_eq_header_length t ▸ hlt⟩
    ∈ header (selectColumns1 t bs)
  ↔ bs.get ⟨i, h ▸ hlt⟩ = true :=
λ hu t bs h i hlt => by
  simp only [header, Schema.sieve_eq_List_sieve]
  exact List.sieve_map_mem_iff_true_unique (Schema.length_eq_List_length ▸ hlt)
          (h.symm ▸ hlt) Prod.fst hu

theorem selectColumns1_spec3 :
  ∀ (t : Table sch) (bs : List Bool),
    List.Sublist (schema (selectColumns1 t bs)) (schema t) :=
λ t bs => by
  simp only [schema, Schema.sieve_eq_List_sieve]
  apply List.sieve_sublist

theorem selectColumns1_spec4 :
  ∀ (t : Table sch) (bs : List Bool),
    nrows (selectColumns1 t bs) = nrows t := by
  intro t bs
  simp only [nrows, selectColumns1, Schema.length_eq_List_length]
  apply List.length_map

-- `selectColumns2`

theorem selectColumns2_spec1 :
  ∀ (t : Table sch) (ns : List (Fin (ncols t))),
    ncols (selectColumns2 t ns) = ns.length := by
  intro t ns
  simp only [ncols, Schema.length_eq_List_length, Schema.nths,
             Schema.map_eq_List_map]
  apply List.length_map

-- Helper for `selectColumns2_spec2`
def finHeaderLengthOfFinNcols (t : Table sch) : Fin (ncols t) →
  Fin ((header t).length)
| ⟨i, hi⟩ => ⟨i, ncols_eq_header_length t ▸ hi⟩

theorem selectColumns2_spec2 :
  ∀ (t : Table sch) (ns : List (Fin (ncols t))) (i : Nat) (hi : i < ns.length),
    (header (selectColumns2 t ns)).get
      ⟨i, ncols_eq_header_length (selectColumns2 t ns)
          ▸ selectColumns2_spec1 t ns
          ▸ hi⟩
    = (header t).get (finHeaderLengthOfFinNcols t $ ns.get ⟨i, hi⟩) := by
  intro t ns i hi
  simp only [header]
  simp only [finHeaderLengthOfFinNcols]
  apply Schema.get_map_nths_eq_get_get

theorem selectColumns2_spec3 :
  ∀ {sch : @Schema η} (t : Table sch)
    (ns : List (Fin (ncols t))),
  ∀ (c : CertifiedName (schema (selectColumns2 t ns))),
    (schema (selectColumns2 t ns)).lookupType c
    = (schema t).lookupType ⟨c.1, Schema.hasNameOfNthsHasName c.2⟩ := by
  intro sch t ns c
  unfold schema at *
  apply Schema.lookupType_nths_eq_lookupType

theorem selectColumns2_spec4 :
  ∀ (t : Table sch) (ns : List (Fin (ncols t))),
    nrows (selectColumns2 t ns) = nrows t := by
  intro t ns
  simp only [nrows, selectColumns2, Schema.length_eq_List_length]
  apply List.length_map

-- `selectColumns3`

theorem selectColumns3_spec1 :
  ∀ (t : Table sch) (cs : List (CertifiedHeader sch)),
    header (selectColumns3 t cs) = cs.map (Prod.fst ∘ Sigma.fst) :=
by intros t cs
   simp only [header, selectColumns3, Schema.names]
   induction cs with
   | nil => simp only [Schema.pick, List.map]
   | cons c cs ih =>
     simp only [Schema.pick, List.map, List.cons.injEq]
     apply And.intro
     . simp only [Function.comp, Schema.lookup_fst_eq_nm, CertifiedName.val]
     . exact ih

theorem selectColumns3_spec2 :
  ∀ (t : Table sch)
    (cs : List (CertifiedHeader sch)),
  ∀ (c : CertifiedName $ schema (selectColumns3 t cs)),
    (schema t).lookupType ⟨c.1, Schema.hasNameOfFromCHeaders c.2⟩ =
    (schema (selectColumns3 t cs)).lookupType c := by
  intro t cs c
  unfold schema
  unfold Schema.fromCHeaders
  simp only [schema] at c
  apply Schema.lookupTypeFromCHeadersUnique

theorem selectColumns3_spec3 :
  ∀ (t : Table sch) (cs : List (CertifiedHeader sch)),
    nrows (selectColumns3 t cs) = nrows t := by
  intro t cs
  simp only [nrows, selectColumns3, Schema.length_eq_List_length]
  apply List.length_map


-- `head`

theorem head_spec1 : ∀ (t : Table sch) (z : {z : Int // z.natAbs < nrows t}),
  schema (head t z) = schema t :=
λ _ _ => rfl

theorem head_spec2 : ∀ (t : Table sch) (z : {z : Int // z.natAbs < nrows t}),
  z.val ≥ 0 → nrows (head t z) = z.val :=
by intros t z h
   cases z with | mk z prop =>
   simp only [head]
   have h_not_neg : ¬ (z < 0) := by
     intro hcontra
     cases z with
     | ofNat n => contradiction
     | negSucc n => contradiction
   simp only [ite_false, h_not_neg]
   simp only [List.take, nrows, Schema.length_eq_List_length]
   rw [List.length_take_of_lt]
   . exact Int.toNat_of_nonneg h
   . unfold nrows at prop
     rw [Int.natAbs_of_nonneg_eq_toNat] at prop
     . exact Schema.length_eq_List_length ▸ prop
     . exact h

-- This is changed slightly from B2T2 to avoid casting. The exact statement
-- would be:
-- z.val < 0 → nrows (head t z) = nrows t + z.val
theorem head_spec3 : ∀ (t : Table sch) (z : {z : Int // z.natAbs < nrows t}),
  z.val < 0 → nrows (head t z) = nrows t - z.val.natAbs := by
  intros t z h
  cases z with | mk z prop =>
  simp only at h
  simp only [nrows, Schema.length_eq_List_length] at prop
  simp only [head, nrows, List.dropLastN, Function.comp, h,
             Schema.length_eq_List_length, ite_true]
  rw [List.length_reverse, List.length_drop, List.length_reverse]

-- `distinct`

theorem distinct_spec : ∀ (t : Table sch) [DecidableEq $ Row sch],
  schema (distinct t) = schema t :=
λ t => rfl

-- `dropColumn`

theorem dropColumn_spec1 : ∀ (t : Table sch) (c : η) (hc : sch.HasName c),
  nrows (dropColumn t c hc) = nrows t := by
  intros
  simp only [nrows, dropColumn, Schema.length_eq_List_length]
  apply List.length_map

-- In the case that our schema is not unique, this is the best we can do:
theorem dropColumn_spec2 : ∀ (t : Table sch) (c : η) (hc : sch.HasName c),
  header (dropColumn t c hc) = Schema.names (sch.removeName hc) :=
λ _ _ _ => rfl

-- If our schema is unique, we can meet the full B2T2 spec:
theorem dropColumn_spec2_unique :
  ∀ (hsch : sch.Unique) (t : Table sch) (c : η) (hc : sch.HasName c),
  header (dropColumn t c hc) = List.removeAllEq (header t) [c] := by
  intro hsch t c hc
  simp only [List.removeAllEq, header]
  unfold Schema.Unique at hsch
  induction hc with
  | @hd nm s' τ =>
    simp only [List.filter, List.elem]
    cases hsch with | cons hnmem hu =>
    simp only at hnmem
    have : (decide (nm ∉ [nm])) = false :=
      by simp only [decide_not, List.mem_singleton, decide_True,
                    decide_False, not]
    rw [this]
    simp only [Schema.names, List.map]
    have : List.filter (λ x => x ∉ [nm]) (List.map Prod.fst s')
            = List.removeAllEq (List.map Prod.fst s') [nm] := rfl
    rw [this, List.removeAllEq_singleton_nonelem_eq]
    exact hnmem
  | @tl hdr nm s' h ih =>
    simp only [Schema.names, List.map]
    cases hdr with | mk nm₁ τ₁ =>
    cases Decidable.em (nm₁ = nm) with
    | inl heq =>
      rw [heq] at hsch
      cases hsch with | cons hnmem hu =>
      simp only at hnmem
      have := Schema.map_eq_List_map ▸ Schema.mem_map_of_HasName _ _ h
      contradiction
    | inr hneq =>
      rw [←List.removeAllEq]
      rw [List.removeAllEq_singleton_hd_neq]
      . congr
        apply ih
        . cases hsch; assumption
        . exact Table.mk []
      . exact hneq

theorem dropColumn_spec3 : ∀ (t : Table sch) (c : η) (hc : sch.HasName c),
  List.Sublist (schema (dropColumn t c hc)) (schema t) :=
λ _ c hc => Schema.removeName_sublist sch c hc

-- `dropColumns`

theorem dropColumns_spec1 :
  ∀ (t : Table sch) (cs : ActionList Schema.removeCertifiedName sch),
  nrows (dropColumns t cs) = nrows t := by
  intro t cs
  simp only [nrows, dropColumns, Schema.length_eq_List_length]
  apply List.length_map

-- Approximation for non-unique schemata
theorem dropColumns_spec2 :
  ∀ (t : Table sch) (cs : ActionList Schema.removeCertifiedName sch),
  header (dropColumns t cs) = Schema.names (sch.removeNames cs) :=
λ t cs => rfl

theorem dropColumns_spec3 :
  ∀ (t : Table sch) (cs : ActionList Schema.removeCertifiedName sch),
  List.Sublist (schema $ dropColumns t cs) (schema t) :=
λ _ cs => Schema.removeNames_sublist sch cs

-- `tfilter`

-- Spec 1 is enforced by types
theorem tfilter_spec2 : ∀ (t : Table sch) (f : Row sch → Bool),
  schema (tfilter t f) = schema t :=
λ t f => rfl

-- `tsort`

theorem tsort_spec1 : ∀ {τ : Type u} [LE τ] [DecidableLE τ]
                        (t : Table sch)
                        (b : Bool)
                        (c : η)
                        (hc : sch.HasCol (c, τ)),
  nrows (tsort t c b hc) = nrows t := by
  intro τ _ _ t b c hc
  simp only [nrows, Schema.length_eq_List_length]
  exact List.length_mergeSort t.rows

theorem tsort_spec2 : ∀ {τ : Type u} [LE τ] [DecidableLE τ]
                        (t : Table sch)
                        (b : Bool)
                        (c : η)
                        (hc : sch.HasCol (c, τ)),
  schema (tsort t c b hc) = schema t :=
λ t c b hc => rfl

-- `sortByColumns`

theorem sortByColumns_spec1 :
  ∀ (t : Table sch)
    (hs : List ((h : Header) × sch.HasCol h × (_ : LE h.2) × DecidableLE h.2)),
    nrows (sortByColumns t hs) = nrows t :=
by intros t hs
   simp only [nrows, sortByColumns]
   apply List.foldr_invariant (λ x => nrows x = nrows t)
   -- Initialization
   . rfl
   -- Preservation
   . intros x acc h
     rw [←h]
     rcases x with ⟨_, _, _, _⟩
     apply tsort_spec1

theorem sortByColumns_spec2 :
  ∀ (t : Table sch)
    (hs : List ((h : Header) × sch.HasCol h × (_ : LE h.2) × DecidableLE h.2)),
    schema (sortByColumns t hs) = schema t :=
λ t hs => rfl

-- `orderBy`

-- Spec 1 is enforced by types
theorem orderBy_spec2 :
  ∀ (t : Table sch)
    (cmps : List ((κ : Type u) × (Row sch → κ) × (κ → κ → Bool))),
    schema (orderBy t cmps) = schema t :=
λ _ _ => rfl

theorem orderBy_spec3 :
  ∀ (t : Table sch)
    (cmps : List ((κ : Type u) × (Row sch → κ) × (κ → κ → Bool))),
    nrows (orderBy t cmps) = nrows t := by
  intro t _
  simp only [nrows, orderBy, Schema.length_eq_List_length]
  exact List.length_mergeSort t.rows

-- `count`

theorem count_spec1 :
  ∀ {τ} [DecidableEq τ]
    (t : Table sch) (c : η) (hc : sch.HasCol (c, τ)),
    header (count t c hc) = ["value", "count"] :=
λ t c hc => rfl

-- This can't yet be in tactic mode because the `induction` tactic doesn't
-- support `(nm, τ)` as an index
theorem count_spec2 :
  ∀ {sch : @Schema η} {τ} [DecidableEq τ]
    (t : Table sch) (c : η) (hc : sch.HasCol (c, τ)),
  (schema (count t c hc)).lookupType ⟨"value", Schema.HasName.hd⟩ =
  sch.lookupType ⟨c, Schema.colImpliesName hc⟩
| _ :: _, _, _, t, _, Schema.HasCol.hd => rfl
  -- As with prior proofs, the table in the IH doesn't matter
| _ :: _, τ, _, t, nm, Schema.HasCol.tl h => count_spec2 (Table.mk []) nm h

theorem count_spec3 {τ} [DecidableEq τ] :
  ∀ (t : Table sch) (c : η) (hc : sch.HasCol (c, τ)),
  (schema (count t c hc)).lookupType ⟨"count", .tl .hd⟩ = Nat :=
λ _ _ _ => rfl

-- Helper lemma for `count_spec4`
theorem length_count_pairsToRow : ∀ (xs : List (Option τ × Nat)),
  List.length (count.pairsToRow xs) = xs.length
| [] => rfl
| x :: xs => congrArg (·+1) (length_count_pairsToRow xs)

theorem count_spec4 {τ} [DecidableEq τ] :
  ∀ (t : Table sch) (c : η) (hc : sch.HasCol (c, τ)),
  nrows (count t c hc) = (getColumn2 t c hc).unique.length := by
  intro t c hc
  simp only [nrows, count, Schema.length_eq_List_length]
  exact Eq.trans (length_count_pairsToRow _) (List.length_counts _)

-- `bin`

theorem bin_spec1 [ToString η] :
  ∀ (t : Table sch)
    (c : η)
    (n : Nat)
    (hc : Schema.HasCol (c, Nat) sch)
    (hn : n > 0),
    header (bin t c n hc hn) = ["group", "count"] :=
λ _ _ _ _ _ => rfl

theorem bin_spec2 [ToString η] :
  ∀ (t : Table sch)
    (c : η)
    (n : Nat)
    (hc : Schema.HasCol (c, Nat) sch)
    (hn : n > 0),
    (schema (bin t c n hc hn)).lookupType ⟨"group", Schema.HasName.hd⟩
      = String :=
λ _ _ _ _ _ => rfl

theorem bin_spec3 [ToString η] :
  ∀ (t : Table sch)
    (c : η)
    (n : Nat)
    (hc : Schema.HasCol (c, Nat) sch)
    (hn : n > 0),
    (schema (bin t c n hc hn)).lookupType
      ⟨"count", Schema.HasName.tl Schema.HasName.hd⟩ = Nat :=
λ _ _ _ _ _ => rfl

-- `pivotTable`

-- Spec 1 is enforced by types
theorem pivotTable_spec2 :
  ∀ (t : Table sch)
    (cs : List $ CertifiedHeader sch)
    [inst : DecidableEq (Row (Schema.fromCHeaders cs))]
    (aggs : List ((c' : Header) ×
                  (c : CertifiedHeader sch) ×
                  (List (Option c.fst.snd) → Option c'.snd))),
  header (pivotTable t cs aggs) =
  List.append (cs.map (·.1.1)) (aggs.map (·.1.1)) := by
  intro t cs inst aggs
  simp only [header, Schema.names, Schema.fromCHeaders,
             Schema.append_eq_List_append, Schema.map_eq_List_map]
  exact List.map_map_append cs aggs Prod.fst Sigma.fst Sigma.fst

theorem pivotTable_spec3_aux :
  ∀ (cs : List $ CertifiedHeader sch)
    (aggs : List ((c' : Header) × (c : CertifiedHeader sch) ×
                  (List (Option c.fst.snd) → Option c'.snd)))
    (cn : CertifiedName (Schema.fromCHeaders cs)),
  Schema.lookup
    (Schema.append (Schema.fromCHeaders cs) (Schema.map (·.fst) aggs))
    ⟨cn.fst, Schema.hasNameOfAppend cn.snd⟩ =
  Schema.lookup sch ⟨cn.fst, Schema.hasNameOfFromCHeaders cn.snd⟩
| ⟨(.(nm), τ), _⟩ :: cs, aggs, ⟨nm, .hd⟩ => by
  simp only [Schema.fromCHeaders, List.map, List.append, Schema.hasNameOfAppend]
  rw [Schema.lookup_eq_1,
      Schema.hasNameOfFromCHeaders_eq_1,
      Schema.lookup_of_colImpliesName]
| ⟨_, _⟩ :: cs, aggs, ⟨nm, .tl _⟩ => by
  simp only [Schema.fromCHeaders, List.map, List.append, Schema.hasNameOfAppend]
  rw [Schema.lookup_eq_2,
      Schema.hasNameOfFromCHeaders_eq_2]
  apply pivotTable_spec3_aux cs aggs ⟨nm, _⟩

theorem pivotTable_spec3 :
  ∀ (t : Table sch)
    (cs : List $ CertifiedHeader sch)
    [inst : DecidableEq (Row (Schema.fromCHeaders cs))]
    (aggs : List ((c' : Header) ×
                  (c : CertifiedHeader sch) ×
                  (List (Option c.fst.snd) → Option c'.snd)))
    (cn : CertifiedName (Schema.fromCHeaders cs)),
    (schema $ pivotTable t cs aggs).lookup
      ⟨cn.1, Schema.hasNameOfAppend cn.2⟩ =
    (schema t).lookup ⟨cn.1, Schema.hasNameOfFromCHeaders cn.2⟩ :=
λ t cs aggs => pivotTable_spec3_aux cs

-- Spec 4 is enforced by types

-- `groupBy`

-- Specs 1 and 2 are enforced by types
-- Spec 3 is also enforced by types, but since it is actually expressible as an
-- (albeit trivial) proof, we state it here for completeness
theorem groupBy_spec3  {η'} [DecidableEq η'] {sch' : @Schema η'}
                       {κ ν} [DecidableEq κ] :
  ∀ (t : Table sch)
    (key : Row sch → κ)
    (project : Row sch → ν)
    (aggregate : κ → List ν → Row sch')
    (k : κ) (vs : List ν),
  schema (groupBy t key project aggregate) = (aggregate k vs).schema :=
λ _ _ _ _ _ _ => rfl

theorem groupBy_spec4 {η'} [DecidableEq η'] {sch' : @Schema η'}
                      {κ ν} [DecidableEq κ] :
  ∀ (t : Table sch)
    (key : Row sch → κ)
    (project : Row sch → ν)
    (aggregate : κ → List ν → Row sch'),
  nrows (groupBy t key project aggregate) = (t.rows.map key).unique.length :=
by intros t key proj agg
   simp only [nrows, groupBy, Schema.length_eq_List_length]
   rw [List.length_map, List.length_groupPairsByKey]
   apply congrArg
   apply congrArg
   rw [List.map_map]
   apply congr _ rfl
   apply congrArg
   unfold Function.comp
   simp only

-- `completeCases`

theorem completeCases_spec {τ : Type u} :
  ∀ (t : Table sch) (c : η) (hc : sch.HasCol (c, τ)),
  (completeCases t c hc).length = nrows t :=
λ t c hc => by
  simp only [nrows, Schema.length_eq_List_length]
  exact Eq.trans (List.length_map _ _) (List.length_map _ _)

-- `dropna`

theorem dropna_spec : ∀ (t : Table sch), schema (dropna t) = schema t :=
λ t => rfl

-- `fillna`

theorem fillna_spec1 {τ : Type u} :
  ∀ (t : Table sch)
    (c : η)
    (v : τ)
    (hc : sch.HasCol (c, τ)),
    schema (fillna t c v hc) = schema t :=
λ _ _ _ _ => rfl

theorem fillna_spec2 {τ : Type u} :
  ∀ (t : Table sch)
    (c : η)
    (v : τ)
    (hc : sch.HasCol (c, τ)),
    nrows (fillna t c v hc) = nrows t := by
  intros
  simp only [nrows, fillna, Schema.length_eq_List_length]
  apply List.length_map

-- `pivotLonger`

-- Closest approximation given uniqueness limitations
theorem pivotLonger_spec1 :
  ∀ (t : Table sch) (cs : ActionList (Schema.removeTypedName τ) sch)
    (c1 : η) (c2 : η),
  header (pivotLonger t cs c1 c2) =
  (sch.removeTypedNames cs).names ++ [c1, c2] :=
λ t cs c1 c2 => by
  simp only [header, Schema.names]
  rw [Schema.append_eq_List_append]
  have := List.map_append Prod.fst (sch.removeTypedNames cs) [(c1, η), (c2, τ)]
  simp only [HAppend.hAppend, Append.append] at this
  rw [this]
  rfl

def pivotLonger_spec2 {c τ}
    (t : Table sch)
    (cs : ActionList (Schema.removeTypedName τ) sch)
    (c₁ c₂ : η)
    (hc : sch.HasCol (c, τ))
    (hnmem : ∀ {sch' : @Schema η} (hc : sch'.HasCol (c, τ)),
      NotT (ActionList.MemT ⟨c, hc⟩ cs)) :
    (schema (pivotLonger t cs c₁ c₂)).HasCol (c, τ) :=
  Schema.hasColOfAppend (Schema.removeTypedNamesHasCol cs hc hnmem)


-- Approximation without using `lookupType`
def pivotLonger_spec3 {τ : Type u_η} :
  ∀ (t : Table sch) (cs : ActionList (Schema.removeTypedName τ) sch)
    (c1 : η) (c2 : η),
  (schema (pivotLonger t cs c1 c2)).HasCol (c1, η) :=
λ _ _ _ _ => Schema.hasAppendedHead _ _ _ _

-- Approximation without using `lookupType`
def pivotLonger_spec4 {τ : Type u_η} :
  ∀ (t : Table sch) (cs : ActionList (Schema.removeTypedName τ) sch)
    (c1 : η) (c2 : η),
  (schema (pivotLonger t cs c1 c2)).HasCol (c2, τ) := by
  intro t cs c1 c2
  simp only [schema]
  have := List.append_cons (Schema.removeTypedNames sch cs) (c1, η) [(c2, τ)]
  simp only [HAppend.hAppend, Append.append, ←Schema.append_eq_List_append]
    at this
  rw [this]
  apply Schema.hasAppendedHead

-- `pivotWider`

-- pivotWider specs are approximated given uniqueness limitations
theorem pivotWider_spec1 :
  ∀ (t : Table sch) (c1 c2 : η) (hc1 : sch.HasCol (c1, η))
    (hc2 : (sch.removeHeader hc1).HasCol (c2, τ))
    [inst : DecidableEq $ Row (sch.removeNames
      (ActionList.cons (Schema.cNameOfCHead ⟨(c1, η), hc1⟩)
      (ActionList.cons (Schema.cNameOfCHead ⟨(c2, τ), hc2⟩) ActionList.nil)))],
  header (pivotWider t c1 c2 hc1 hc2) =
    Schema.names (
      sch.removeNames (.cons (Schema.cNameOfCHead ⟨(c1, η), hc1⟩)
                      (.cons (Schema.cNameOfCHead ⟨(c2, τ), hc2⟩) .nil)))
    ++ List.unique (List.somes (getColumn2 t c1 hc1)) := by
  intro t c1 c2 hc1 hc2 inst
  simp only [header, Schema.names]
  rw [Schema.append_eq_List_append]
  have := List.map_append Prod.fst
    (Schema.removeHeaders sch
      (ActionList.cons { fst := (c1, η), snd := hc1 }
        (ActionList.cons { fst := (c2, τ), snd := hc2 } ActionList.nil)))
    (List.map (fun x => (x, τ)) (List.unique (List.somes (getColumn2 t c1 hc1))))
  simp only [HAppend.hAppend, Append.append] at this
  rw [this]
  rw [List.map_map]
  have hf : (Prod.fst ∘ fun x => (x, τ)) = @id η := funext (λ _ => rfl)
  rw [hf]
  rw [List.map_id]
  rfl

def pivotWider_spec2 {τ τ'} :
  ∀ (t : Table sch) (c1 c2 : η) (hc1 : sch.HasCol (c1, η))
    (hc2 : (sch.removeHeader hc1).HasCol (c2, τ))
    [inst : DecidableEq $ Row (sch.removeNames
      (ActionList.cons (Schema.cNameOfCHead ⟨(c1, η), hc1⟩)
      (ActionList.cons (Schema.cNameOfCHead ⟨(c2, τ), hc2⟩) ActionList.nil)))],
  ∀ (c : η) (hc : sch.HasCol (c, τ')),
    NotT (List.MemT c [c1, c2]) →
    Schema.HasCol (c, τ') (schema (pivotWider t c1 c2 hc1 hc2)) := by
  intro t c1 c2 hc1 hc2 inst c hc hnmem
  apply Schema.hasColOfAppend
  apply Schema.hasColOfRemoveName
  . intro hneg
    rw [hneg] at hnmem
    apply Empty.rec (motive := λ _ => False)
    apply hnmem
    exact List.MemT.tl _ (List.MemT.hd _ _)
  apply Schema.hasColOfRemoveName
  . intro hneg
    rw [hneg] at hnmem
    apply Empty.rec (motive := λ _ => False)
    apply hnmem
    exact .hd _ _
  exact hc

def pivotWider_spec3 {τ} :
  ∀ (t : Table sch) (c1 c2 : η) (hc1 : sch.HasCol (c1, η))
    (hc2 : (sch.removeHeader hc1).HasCol (c2, τ))
    [inst : DecidableEq $ Row (sch.removeNames
      (ActionList.cons (Schema.cNameOfCHead ⟨(c1, η), hc1⟩)
      (ActionList.cons (Schema.cNameOfCHead ⟨(c2, τ), hc2⟩) ActionList.nil)))],
  List.MemT (some c) (getColumn2 t c1 hc1) →
  Schema.HasCol (c, τ) (schema (pivotWider t c1 c2 hc1 hc2)) := by
  intro t c1 c2 hc1 hc2 inst hmem
  simp only [schema]
  apply Schema.hasColOfPrepend
  apply Schema.hasColOfMemT
  apply List.memT_map_of_memT (λ x => (x, τ))
  apply List.memT_unique_of_memT
  apply List.memT_somes_of_memT
  assumption

-- `flatten`

theorem flatten_spec1 :
  ∀ (t : Table sch) (cs : ActionList Schema.flattenList sch),
  header (flatten t cs) = header t := by
  intros t cs
  simp only [flatten, header, Schema.names]
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [ih]
    simp only [Schema.flattenList]
    apply Schema.retypeColumn_preserves_names
    exact Table.mk []

/-
Spec 2 of `flatten` does not hold because we may flatten the same column
multiple times: if `List (List τ)` is the initial type of a column, the spec
would require that `List τ` be its type in the output, but double-flattening
would instead yield `τ`.

Were spec 2 true, we could state it thus:

def flatten_spec2 {sch' : @Schema η} {nm τ pf} :
  ∀ (t : Table sch) (cs : ActionList Schema.flattenList sch),
  ActionList.MemT (⟨nm, τ, pf⟩ :
                    ((c : η) × (τ : Type u) × (sch'.HasCol (c, List τ))))
                  cs →
  Schema.HasCol (nm, τ) (schema (flatten t cs))
-/

-- `transformColumn`

theorem transformColumn_spec1 {τ₁ τ₂} :
  ∀ (t : Table sch)
    (c : (c : η) × sch.HasCol (c, τ₁))
    (f : Option τ₁ → Option τ₂),
  sch.lookupType ⟨c.1, Schema.colImpliesName c.2⟩ = τ₁ :=
λ t c f => Eq.trans (Schema.lookupType_eq_snd_lookup sch
                        ⟨c.1, Schema.colImpliesName c.2⟩)
                    (Eq.subst (motive := λ a => a.snd = τ₁)
                        (Eq.symm $ Schema.lookup_of_colImpliesName sch c.2)
                        rfl)

theorem transformColumn_spec2 {τ₁ τ₂} :
  ∀ (t : Table sch)
    (c : η)
    (f : Option τ₁ → Option τ₂)
    (hc : sch.HasCol (c, τ₁)),
  header (transformColumn t c f hc) = header t :=
λ t c f hc => sch.retypeColumn_preserves_names _ _

-- Closest approximation given uniqueness issues
-- The first bullet point in the written spec is ensured by the type
theorem transformColumn_spec3 : ∀ {sch} {τ₁ τ₂}
    (t : Table sch)
    (c : η)
    (f : Option τ₁ → Option τ₂)
    (hc : sch.HasCol (c, τ₁)),
  (schema $ transformColumn t c f hc).removeHeader
    (Schema.hasRetypedCol ⟨c, hc⟩)
  = sch.removeHeader hc
| _, _, _, t, _, f, .hd => rfl
| _, _, _, t, nm, f, .tl htl =>
  have ih := transformColumn_spec3 (Table.mk []) nm f htl
  congrArg _ ih

theorem transformColumn_spec4 :
  ∀ (t : Table sch)
    (c : η)
    (f : Option τ₁ → Option τ₂)
    (hc : sch.HasCol (c, τ₁)),
  nrows (transformColumn t c f hc) = nrows t := by
  intro t c f hc
  simp only [nrows, transformColumn, Schema.length_eq_List_length]
  apply List.length_map

-- `renameColumns`

/-
`renameColumns` spec 1 does not hold because we may rename the same column
multiple times. If spec 1 held, we could state it thus:

def renameColumns_spec1 {c c'} {hc : sch.HasName c} :
  ∀ (t : Table sch) (ccs : ActionList Schema.renameColumnCN sch),
  sch.HasName c →
  ccs.MemT ⟨(c, c'), hc⟩ →
  (schema (renameColumns t ccs)).HasName c'

The first half of spec 2 also does not hold due to the possibility of repeated
renamings (we don't attempt to state it here). However, the second half of spec
2 does hold; we prove it below:
-/
def renameColumns_spec2_part2 :
  ∀ (c : η)
    (t : Table sch)
    (ccs : ActionList Schema.renameColumnCN sch),
    (hc : sch.HasCol (c, τ)) →
    (∀ {sch' : @Schema η} c' (hc : sch'.HasName c),
      NotT (ActionList.MemT ⟨(c, c'), hc⟩ ccs)) →
    Schema.HasCol (c, τ) (schema (renameColumns t ccs)) :=
  λ c t => Schema.hasColOfNotMemRenameColumns (sch := schema t) (c := c)

theorem renameColumns_spec3 :
  ∀ (t : Table sch)
    (ccs : ActionList Schema.renameColumnCN sch),
  nrows (renameColumns t ccs) = nrows t := by
  intros
  simp only [nrows, renameColumns, Schema.length_eq_List_length]
  apply List.length_map

-- `find`

-- The specification for `find` is contained in its type (`Option` corresponds
-- to "Error," and `Fin` restricts the range of the output)

-- `groupByRetentive`

theorem groupByRetentive_spec1 [DecidableEq τ] :
  ∀ (t : Table sch) (c : η) (hc : sch.HasCol (c, τ)),
  header (groupByRetentive t c hc) = ["key", "groups"] :=
λ _ _ _ => rfl

theorem groupByRetentive_spec2
  {η : Type u_η} [DecidableEq η] {sch : @Schema η}
  {τ : Type u} [DecidableEq τ] :
  ∀ (t : Table sch) (c : η) (hc : sch.HasCol (c, τ)),
  (schema (groupByRetentive t c hc)).lookupType ⟨"key", Schema.HasName.hd⟩
    = ULift.{max (u+1) u_η} τ :=
λ _ _ _ => rfl

theorem groupByRetentive_spec3
  {η : Type u_η} [DecidableEq η] {sch : @Schema η}
  {τ : Type u} [DecidableEq τ] :
  ∀ (t : Table sch) (c : η) (hc : sch.HasCol (c, τ)),
    (schema (groupByRetentive t c hc)).lookupType ⟨"groups", .tl .hd⟩
    = Table sch :=
λ _ _ _ => rfl

-- Need decidable equality of `ULift`s for `groupBy{Retentive,Subtractive}`
deriving instance DecidableEq for ULift

theorem groupByRetentive_spec4 [inst : DecidableEq τ] :
  ∀ (t : Table sch) (c : η) (hc : sch.HasCol (c, τ)),
  (getColumn2 (groupByRetentive t c hc) "key" Schema.HasCol.hd).Unique
    := by
  intros t c hc
  simp only [groupByRetentive, groupBy, getColumn2]
  rw [List.map_map]
  simp only [Function.comp, getValue]
  conv =>
    rhs
    lhs
    apply funext (g := _) _
    apply (λ x => Option.map ULift.up x.fst)
    -- `intros` doesn't seem to be working in `conv` mode?
    apply (λ x => Cell.toOption_fromOption _)
  conv =>
    rhs
    lhs
    apply funext (g := _) _
    apply (λ x => Option.map ULift.up ∘ Prod.fst)
    apply (λ x => rfl)
  rw [←List.map_map]
  apply List.unique_of_map_injective_unique
  -- Show `Option.map ULift.up` is injective
  . intros x y hxy
    cases x
    . cases y
      . rfl
      . contradiction
    . cases y
      . contradiction
      . cases hxy; rfl
  . apply List.groupPairsByKey_fsts_no_duplicates

theorem groupByRetentive_spec5
  {η : Type u_η} {τ : Type u} [dec_η : DecidableEq η]
  {sch : @Schema η} [DecidableEq τ] :
  ∀ (t : Table sch) (c : η) (hc : sch.HasCol (c, τ)),
  ∀ t', t' ∈ (getColumn2 (groupByRetentive t c hc) "groups" (.tl .hd)).somes →
  schema t' = sch :=
λ _ _ _ _ _ => rfl

theorem groupByRetentive_spec6
  {η : Type u_η} {τ : Type u} [dec_η : DecidableEq η]
  {sch : @Schema η} [DecidableEq τ] :
  ∀ (t : Table sch) (c : η) (hc : sch.HasCol (c, τ)),
  nrows (groupByRetentive t c hc) = (getColumn2 t c hc).unique.length :=
λ t c hc =>
  groupBy_spec4 (sch' := [("key", ULift.{max (u+1) u_η} τ),
                          ("groups", Table sch)])
    t
    (λ r => getValue r c hc)
    (λ r => r)
    (λ k vs => Row.cons (Cell.fromOption (Option.map ULift.up k))
                        (Row.cons (Cell.val (Table.mk vs)) Row.nil))

-- `groupBySubtractive`

theorem groupBySubtractive_spec1 [DecidableEq τ] :
  ∀ (t : Table sch) (c : η) (hc : sch.HasCol (c, τ)),
  header (groupBySubtractive t c hc) = ["key", "groups"] :=
λ _ _ _ => rfl

theorem groupBySubtractive_spec2
  {η : Type u_η} [DecidableEq η] {sch : @Schema η}
  {τ : Type u} [DecidableEq τ] :
  ∀ (t : Table sch) (c : η) (hc : sch.HasCol (c, τ)),
  (schema (groupBySubtractive t c hc)).lookupType ⟨"key", Schema.HasName.hd⟩
    = ULift.{max (u+1) u_η} τ :=
λ _ _ _ => rfl

theorem groupBySubtractive_spec3
  {η : Type u_η} [DecidableEq η] {sch : @Schema η}
  {τ : Type u} [DecidableEq τ] :
  ∀ (t : Table sch) (c : η) (hc : sch.HasCol (c, τ)),
  (schema (groupBySubtractive t c hc)).lookupType ⟨"groups", .tl .hd⟩ =
  Table (sch.removeName (Schema.colImpliesName hc)) :=
λ _ _ _ => rfl

-- There may be a way to consolidate this with `groupByRetentive_spec4`
theorem groupBySubtractive_spec4 [inst : DecidableEq τ] :
  ∀ (t : Table sch) (c : η) (hc : sch.HasCol (c, τ)),
  (getColumn2 (groupBySubtractive t c hc) "key" Schema.HasCol.hd).Unique
  := by
  intros t c hc
  simp only [groupBySubtractive, groupBy, getColumn2]
  rw [List.map_map]
  simp only [Function.comp, getValue]
  conv =>
    rhs
    lhs
    apply funext (g := _) _
    apply (λ x => Option.map ULift.up x.fst)
    -- `intros` doesn't seem to be working in `conv` mode?
    apply (λ x => Cell.toOption_fromOption _)
  conv =>
    rhs
    lhs
    apply funext (g := _) _
    apply (λ x => Option.map ULift.up ∘ Prod.fst)
    apply (λ x => rfl)
  rw [←List.map_map]
  apply List.unique_of_map_injective_unique
  -- Show `Option.map ULift.up` is injective
  . intros x y hxy
    cases x
    . cases y
      . rfl
      . contradiction
    . cases y
      . contradiction
      . cases hxy; rfl
  . apply List.groupPairsByKey_fsts_no_duplicates

-- Closest approximation possible given uniqueness issues
theorem groupBySubtractive_spec5
  {η : Type u_η} [DecidableEq η] {sch : @Schema η}
  {τ : Type u} [DecidableEq τ] :
  ∀ (t : Table sch) (c : η) (hc : sch.HasCol (c, τ)),
  ∀ t', t' ∈ (getColumn2 (groupBySubtractive t c hc) "groups" (.tl .hd)).somes →
  header t' = Schema.names (sch.removeName (Schema.colImpliesName hc)) :=
λ _ _ _ _ _ => rfl

theorem groupBySubtractive_spec6
  {η : Type u_η} {τ : Type u} [dec_η : DecidableEq η]
  {sch : @Schema η} [DecidableEq τ] :
  ∀ (t : Table sch) (c : η) (hc : sch.HasCol (c, τ)),
  ∀ t', t' ∈ (getColumn2 (groupBySubtractive t c hc) "groups" (.tl .hd)).somes →
  List.Sublist (schema t') sch :=
λ _ c hc _ _ => Schema.removeName_sublist sch c (Schema.colImpliesName hc)

theorem groupBySubtractive_spec7
  {η : Type u_η} {τ : Type u} [dec_η : DecidableEq η]
  {sch : @Schema η} [DecidableEq τ] :
  ∀ (t : Table sch) (c : η) (hc : sch.HasCol (c, τ)),
  nrows (groupBySubtractive t c hc) = (getColumn2 t c hc).unique.length :=
λ t c hc =>
  groupBy_spec4
    t
    (λ r => getValue r c hc)
    (λ r => r)
    (λ k vs => Row.cons (Cell.fromOption (Option.map ULift.up k))
                        (Row.cons (Cell.val (Table.mk (vs.map (λ r =>
                          Row.removeColumn (Schema.colImpliesName hc) r))))
                        Row.nil))

-- `update`

-- `update` spec 1 is enforced by types
theorem update_spec2 :
  ∀ (subsch : RetypedSubschema sch) (t : Table sch)
    (f : Row sch → Row subsch.toSchema),
  header (update subsch t f) = header t :=
λ subsch t f =>
    Schema.retypedFromSubschema_preserves_names sch subsch

-- The first half of `update` spec 3 does not hold because `RetypedSubschema`ta
-- may repeat column names (`retypedFromSubschema` takes the last). The second
-- half, which we formalize below, does hold:
def update_spec3_part2 {c τ} :
  ∀ (subsch : RetypedSubschema sch) (t : Table sch)
    (f : Row sch → Row subsch.toSchema),
    NotT (List.MemT c (header (update subsch t f))) →
    sch.HasCol (c, τ) →
    (schema (update subsch t f)).HasCol (c, τ) := by
  intro subsch t f hmem hc
  simp only [schema, update]
  refine Schema.retypedFromSubschemaHasColOfNotMemT subsch ?_ hc
  . intro _ hhn
    simp only at hhn
    intro hneg
    apply hmem
    simp only [header]
    suffices Schema.HasName c (Schema.retypedFromSubschema subsch) by
      apply Schema.memTNamesOfHasName this
    apply Schema.retypedSubschemaHasSchemaName
    exact hhn

theorem update_spec4 :
  ∀ (subsch : RetypedSubschema sch) (t : Table sch)
    (f : Row sch → Row subsch.toSchema),
    nrows (update subsch t f) = nrows t := by
  intros
  simp only [nrows, update, Schema.length_eq_List_length]
  apply List.length_map

-- `select`

-- Specs 1, 2, and 3 are enforced by types
theorem select_spec4 {sch' : @Schema η} :
  ∀ (t : Table sch) (f : Row sch → Fin (nrows t) → Row sch'),
  nrows (select t f) = nrows t := by
  intros
  simp only [nrows, select, Schema.length_eq_List_length]
  exact Eq.trans (List.length_map _ _) (List.length_verifiedEnum _)

-- `selectMany`

-- All `selectMany` specifications are enforced by types

-- `groupJoin`

-- Specs 1 through 5 are enforced by types
theorem groupJoin_spec6
  {κ} [DecidableEq κ] {ν : Type _} {s₁ s₂ s₃ : @Schema η} :
  ∀ (t₁ : Table s₁) (t₂ : Table s₂)
    (getKey₁ : Row s₁ → κ) (getKey₂ : Row s₂ → κ)
    (aggregate : Row s₁ → Table s₂ → Row s₃),
  nrows (groupJoin t₁ t₂ getKey₁ getKey₂ aggregate) =
  nrows t₁ :=
λ _ _ _ _ _ => select_spec4 _ _

-- `join`

-- All `join` specifications are enforced by types
