import Table.CellRowTable

universe u u_η

variable {η : Type u_η} [dec_η : DecidableEq η] {sch : @Schema η}

theorem emptyTable_spec1 : @schema η dec_η _ emptyTable = [] := rfl

theorem emptyTable_spec2 : @nrows η dec_η _ emptyTable = 0 := rfl

-- We omit the precondition because it is enforced by the type system
theorem addRows_spec1 :
  ∀ (t : Table sch) (rs : List (Row sch)), schema (addRows t rs) = schema t :=
λ t rs => rfl

theorem addRows_spec2 :
  ∀ (t : Table sch) (rs : List (Row sch)),
    nrows (addRows t rs) = nrows t + rs.length :=
λ t rs => List.length_append (t.rows) rs

-- TODO: deal with precondition 1
-- We must enforce decidable equality of τ to state this theorem
-- We omit the precondition because it is not required for this portion of the
-- spec
theorem addColumn_spec1 :
  ∀ {τ : Type u} [DecidableEq τ] (t : Table sch) (c : η) (vs : List τ),
    header (addColumn t c vs) = List.append (header t) [c] := by
  intros τ inst t c vs
  simp [header, addColumn, Schema.names]
  induction sch with
  | nil => simp [List.map, List.append]
  | cons s ss ih =>
    simp only [List.map]
    -- TODO: after updating to Lean 4 m4, these unfolds become necessary...
    unfold HAppend.hAppend at ih
    unfold instHAppend at ih
    unfold Append.append at ih
    unfold List.instAppendList at ih
    simp only at ih
    rw [ih]
    simp [List.append]
    -- FIXME: why does it want a Table ss?
    exact Table.mk []

-- ⟨cc.val,
-- by cases cc with | mk val prop =>
--    induction prop with
--    | hd => apply Schema.HasName.hd
--    | @tl r c' rs h ih =>
--     apply Schema.HasName.tl
--     simp only [schema, addColumn] at ih
-- ⟩

theorem addColumn_spec2 :
  ∀ {τ : Type u}
    (t : Table sch)
    (c : η)
    (vs : List τ)
    (c' : η)
    (h' : sch.HasName c'),
    c ∈ header t →
      (schema t).lookup ⟨c', h'⟩ =
      (schema (addColumn t c vs)).lookup ⟨c', Schema.hasNameOfAppend h'⟩ :=
λ t c vs c' h' h => Schema.lookup_eq_lookup_append _ _ _ _

-- FIXME: how to show c is certifed?
-- theorem addColumn_spec3 :
--   ∀ {τ : Type u} [DecidableEq τ] (t : Table sch) (c : η) (vs : List τ),
--     (schema (addColumn t c vs)).lookup c = τ := rfl

theorem addColumn_spec4 :
  ∀ {τ : Type u} [DecidableEq τ] (t : Table sch) (c : η) (vs : List τ),
    vs.length = nrows t →
    nrows (addColumn t c vs) = nrows t := by
  intros τ inst t c vs h
  simp only [nrows, addColumn, List.length_map]
  rw [List.zip_length_eq_of_length_eq]
  exact Eq.symm h

-- theorem addColumn_spec1' :
--   ∀ {τ : Type u} [DecidableEq τ] (t : Table sch) (c : η) (vs : List τ),
--     header (addColumn t c vs) = List.append (header t) [c] :=
-- λ t c vs =>
--   match sch with
--   | [] => by cases t with | mk rows => cases rows with | nil => simp [header, addColumn, Schema.names, List.map, List.append]
--                                                        | cons s ss => simp [header, addColumn, Schema.names, List.map, List.append]
--   | s :: ss =>
--     have h := @addColumn_spec1' _ _ ss _ _ t c vs
--     sorry

-- Spec 1 is enforced by the type system
theorem buildColumn_spec2 :
  ∀ {τ : Type u} (t : Table sch) (c : η) (f : Row sch → τ),
    header (buildColumn t c f) = List.append (header t) [c] :=
by intros τ t c f
   simp [header, Schema.names]
   induction sch with
  | nil => simp [List.map, List.append]
  | cons s ss ih =>
    simp only [List.map]
    -- TODO: same issue with the ih
    unfold HAppend.hAppend at ih
    unfold instHAppend at ih
    unfold Append.append at ih
    unfold List.instAppendList at ih
    simp only at ih
    rw [ih]
    simp [List.append]
    -- FIXME: why does it want all of this?
    exact Table.mk []
    exact (λ x => f (Row.cons Cell.emp x))

theorem buildColumn_spec5 :
  ∀ {τ : Type u} (t : Table sch) (c : η) (f : Row sch → τ),
    nrows (buildColumn t c f) = nrows t :=
by intros τ t c f
   simp only [nrows, buildColumn, addColumn]
   rw [List.length_map, List.zip_length_eq_of_length_eq]
   apply Eq.symm
   apply List.length_map

-- TODO: come back to buildColumn

-- Spec 1 is enforced by the type system
theorem vcat_spec2 :
  ∀ (t1 : Table sch) (t2 : Table sch),
    nrows (vcat t1 t2) = nrows t1 + nrows t2 :=
λ t1 t2 => List.length_append t1.rows t2.rows

-- This is precisely the type signature, but we can state it anyway
theorem hcat_spec1 :
  ∀ {sch₁ : @Schema η} {sch₂ : @Schema η} (t₁ : Table sch₁) (t₂ : Table sch₂),
    schema (hcat t₁ t₂) = List.append (schema t₁) (schema t₂) :=
λ _ _ => rfl

theorem hcat_spec2 :
  ∀ {sch₁ : @Schema η} {sch₂ : @Schema η} (t₁ : Table sch₁) (t₂ : Table sch₂),
    nrows t₁ = nrows t₂ → nrows (hcat t₁ t₂) = nrows t₁ :=
by intros sch₁ sch₂ t₁ t₂ h
   simp only [nrows, hcat]
   rw [List.length_map]
   apply List.zip_length_eq_of_length_eq _ _ h

theorem values_spec1 :
  ∀ (rs : List (Row sch)),
    (h : rs ≠ []) → schema (values rs) = Row.schema (rs.head h) :=
λ rs h => rfl

theorem values_spec2 :
  ∀ (rs : List (Row sch)), nrows (values rs) = rs.length :=
λ rs => rfl

theorem crossJoin_spec1 :
  ∀ {sch₁ : @Schema η} {sch₂ : @Schema η} (t₁ : Table sch₁) (t₂ : Table sch₂),
    schema (crossJoin t₁ t₂) = List.append (schema t₁) (schema t₂) :=
λ _ _ => rfl

theorem crossJoin_spec2 :
  ∀ {sch₁ : @Schema η} {sch₂ : @Schema η} (t₁ : Table sch₁) (t₂ : Table sch₂),
    nrows (crossJoin t₁ t₂) = nrows t₁ * nrows t₂ :=
by intros sch₁ sch₂ t₁ t₂
   simp only [nrows, crossJoin, List.length_map]
   apply List.length_prod

theorem getColumn1_spec1 :
  ∀ (t : Table sch) (n : Nat) (h : n < ncols t),
    List.length (getColumn1 t n h) = nrows t :=
λ t n h => List.length_map _ _

-- TODO: gC1 spec 2

-- TODO: gC2 spec 1
theorem getColumn2_spec2 :
  ∀ {τ : Type u} (t : Table sch) (c : η) (h : sch.HasCol (c, τ)),
    List.length (getColumn2 t c h) = nrows t :=
λ t c h => List.length_map _ _

-- Precondition is enforced by subtype
theorem selectRows1_spec1 :
  ∀ (t : Table sch) (ns : List {n // n < nrows t}),
    schema (selectRows1 t ns) = schema t :=
λ t ns => rfl

theorem selectRows1_spec2 :
  ∀ (t : Table sch) (ns : List {n // n < nrows t}),
    nrows (selectRows1 t ns) = ns.length :=
λ t ns => List.length_map _ _

-- Precondition is enforced by `h`
theorem selectRows2_spec1 :
  ∀ (t : Table sch) (bs : List Bool) (h : bs.length = nrows t),
    schema (selectRows2 t bs h) = schema t :=
λ t bs h => rfl

theorem selectRows2_spec2 :
  ∀ (t : Table sch) (bs : List Bool) (h : bs.length = nrows t),
    nrows (selectRows2 t bs h) = (bs.removeAll [false]).length :=
λ t bs h => List.sieve_removeAll _ _ h

theorem selectColumns1_spec1 :
  ∀ (t : Table sch) (bs : List Bool) (h : bs.length = ncols t),
    List.Sublist (header (selectColumns1 t bs h)) (header t) :=
λ t bs h => List.sublist_of_map_sublist _ _ Prod.fst $ List.sieve_sublist bs sch

-- FIXME: there must be a better way
theorem ncols_eq_header_length :
  ∀ (t : Table sch), ncols t = (header t).length :=
λ t => Eq.symm (List.length_map _ _)
theorem selectColumns1_spec2 :
  ∀ (t : Table sch) (bs : List Bool) (h : bs.length = ncols t) (i : Nat) (h' : i < ncols t),
  (List.get (header t) ⟨i, (ncols_eq_header_length t).subst h'⟩) ∈ (header (selectColumns1 t bs h)) ↔
   List.get bs ⟨i, Eq.subst h.symm h'⟩ = true := sorry

theorem selectColumns1_spec3 :
  ∀ (t : Table sch) (bs : List Bool) (h : bs.length = ncols t),
    List.Sublist (schema (selectColumns1 t bs h)) (schema t) :=
λ t bs h => List.sieve_sublist _ _

theorem selectColumns1_spec4 :
  ∀ (t : Table sch) (bs : List Bool) (h : bs.length = ncols t),
    nrows (selectColumns1 t bs h) = nrows t :=
λ t bs h => List.length_map _ _

theorem selectColumns2_spec1 :
  ∀ (t : Table sch) (ns : List {n // n < ncols t}),
    ncols (selectColumns2 t ns) = ns.length :=
λ t ns => List.length_map _ _

-- TODO: sc2 specs 2 and 3

theorem selectColumns2_spec4 :
  ∀ (t : Table sch) (ns : List {n // n < ncols t}),
    nrows (selectColumns2 t ns) = nrows t :=
λ t ns => List.length_map _ _

theorem selectColumns3_spec1 :
  ∀ (t : Table sch) (cs : List (CertifiedName sch)),
    header (selectColumns3 t cs) = cs.map Sigma.fst :=
by intros t cs
   simp only [header, selectColumns3, Schema.names]
   induction cs with
   | nil => simp only [Schema.pick, List.map]
   | cons c cs ih =>
     simp only [Schema.pick, List.map, List.cons.injEq]
     apply And.intro
     . simp only [Schema.lookup_fst_eq_nm, CertifiedName.val]
     . exact ih

-- TODO: sc3 spec 2

theorem selectColumns3_spec3 :
  ∀ (t : Table sch) (cs : List (CertifiedName sch)),
    nrows (selectColumns3 t cs) = nrows t :=
λ t cs => List.length_map _ _

-- Spec 1 is enforced by types
theorem head_spec2 : ∀ (t : Table sch) (z : {z : Int // z.abs < nrows t}),
  z.val ≥ 0 → nrows (head t z) = z.val :=
by intros t z h
   cases z with | mk z prop =>
   simp only [head]
   have h_not_neg : ¬ (z < 0) := by
     intro contra
     cases z with
     | ofNat n => contradiction
     | negSucc n => contradiction
   simp only [ite_false, h_not_neg]
   simp only [List.take, nrows]
   rw [List.length_take]
   . exact Int.toNat_of_ofNat_inj z h
   . unfold nrows at prop
     rw [Int.abs_of_nonneg_eq_toNat] at prop
     . exact prop
     . exact h

-- TODO: changed slightly from B2T2 b/c casting is a pain (should this be redone
-- to match the spec exactly?)
theorem head_spec3 : ∀ (t : Table sch) (z : {z : Int // z.abs < nrows t}),
  z.val < 0 → nrows (head t z) = nrows t - z.val.abs :=
by intros t z h
   cases z with | mk z prop =>
   simp only [head, nrows, h, ite_true, List.dropLastN, Function.comp]
   rw [List.length_reverse, List.length_drop, List.length_reverse]
   rw [List.length_reverse]
   exact prop

-- theorem head_spec3' : ∀ (t : Table sch) (z : {z : Int // z.abs < nrows t}),
--   z.val < 0 → nrows (head t z) = nrows t + z.val :=
-- by intros t z h
--    rw [Int.add_neg_eq_sub]
--    cases z with | mk z prop =>
--    cases z with
--    | ofNat n => contradiction
--    | negSucc n =>
--      simp only [Int.abs]

theorem distinct_spec : ∀ (t : Table sch) [DecidableEq $ Row sch],
  schema (distinct t) = schema t :=
λ t => rfl

theorem dropColumn_spec1 : ∀ (t : Table sch) (c : CertifiedName sch),
  nrows (dropColumn t c) = nrows t :=
λ t c => List.length_map _ _

-- TODO: dC spec 2 (not currently true because of duplicate issues)

theorem dropColumn_spec3 : ∀ (t : Table sch) (c : CertifiedName sch),
  List.Sublist (schema (dropColumn t c)) (schema t) :=
λ _ c => Schema.removeName_sublist sch c.val c.property

-- Spec 1 is enforced by types
theorem tfilter_spec2 : ∀ (t : Table sch) (f : Row sch → Bool),
  schema (tfilter t f) = schema t :=
λ t f => rfl

theorem tsort_spec1 : ∀ {τ : Type u} [Ord τ]
                        (t : Table sch)
                        (c : ((c : η) × sch.HasCol (c, τ)))
                        (b : Bool),
  nrows (tsort t c b) = nrows t :=
λ t c b => List.length_merge_sort_with _ t.rows

theorem tsort_spec2 : ∀ {τ : Type u} [Ord τ]
                        (t : Table sch)
                        (c : ((c : η) × sch.HasCol (c, τ)))
                        (b : Bool),
  schema (tsort t c b) = schema t :=
λ t c b => rfl

theorem sortByColumns_spec1 :
  ∀ (t : Table sch) (hs : List ((h : Header) × sch.HasCol h × Ord h.snd)),
    nrows (sortByColumns t hs) = nrows t :=
by intros t hs
   simp only [nrows, sortByColumns]
   apply List.foldr_invariant (λ x => nrows x = nrows t)
   -- Initialization
   . rfl
   -- Preservation
   . intros x acc h
     rw [←h]
     apply @tsort_spec1 _ _ _ _ x.snd.snd

theorem sortByColumns_spec2 :
  ∀ (t : Table sch) (hs : List ((h : Header) × sch.HasCol h × Ord h.snd)),
    schema (sortByColumns t hs) = schema t :=
λ t hs => rfl
