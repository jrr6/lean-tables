import Table.API

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
  ∀ {τ : Type u} [DecidableEq τ]
    (t : Table sch) (c : η) (vs : List $ Option τ),
    header (addColumn t c vs) = List.append (header t) [c]
:= by
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
    -- TODO: Can we avoid this somehow? (Arises because of induction on schema
    -- used as index in Table type. Could use empty table instead, but this
    -- seems more suggestive.)
    exact dropColumn t ⟨_, Schema.HasName.hd⟩

-- ⟨cc.val,
-- by cases cc with | mk val prop =>
--    induction prop with
--    | hd => apply Schema.HasName.hd
--    | @tl r c' rs h ih =>
--     apply Schema.HasName.tl
--     simp only [schema, addColumn] at ih
-- ⟩

-- TODO: maybe use `lookupType` for this and `buildColumn_spec3`?
theorem addColumn_spec2 :
  ∀ {τ : Type u}
    (t : Table sch)
    (c : η)
    (vs : List $ Option τ)
    (c' : η)
    -- This is equivalent to `c ∈ header t`. (Unfortunately, we can't take the
    -- hypothesis in that form beecause creating a `HasName` therefrom would
    -- require large elimination from `Prop`)
    (h' : sch.HasName c'),
      (schema t).lookup ⟨c', h'⟩ =
      (schema (addColumn t c vs)).lookup ⟨c', Schema.hasNameOfAppend h'⟩ :=
λ t c vs c' h' => Schema.lookup_eq_lookup_append _ _ _ _

theorem addColumn_spec3 {τ : Type u} [DecidableEq τ] :
  ∀ (t : Table sch) (c : η) (vs : List $ Option τ),
    (schema (addColumn t c vs)).lookupType
      ⟨c, sch.hasAppendedSingletonName c τ⟩ = τ := by
  intros t c vs
  induction sch with
  | nil =>
    simp only [Schema.hasAppendedSingletonName, Schema.lookupType]
  | cons s ss ih =>
    simp only [Schema.hasAppendedSingletonName, Schema.lookupType]
    -- TODO: again, could use `Table.mk []`, but this is more suggestive?
    apply ih (dropColumn t ⟨_, Schema.HasName.hd⟩)

theorem addColumn_spec4 :
  ∀ {τ : Type u} [DecidableEq τ] (t : Table sch) (c : η) (vs : List $ Option τ),
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
  ∀ {τ : Type u} (t : Table sch) (c : η) (f : Row sch → Option τ),
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
      ⟨c, sch.hasAppendedSingletonName c τ⟩ = τ := by
  intros t c f
  induction sch with
  | nil =>
    simp only [Schema.hasAppendedSingletonName, Schema.lookupType]
  | cons s ss ih =>
    simp only [Schema.hasAppendedSingletonName, Schema.lookupType]
    apply ih
    . exact (dropColumn t ⟨_, Schema.HasName.hd⟩)
    . exact f ∘ (Row.cons Cell.emp)

theorem buildColumn_spec5 :
  ∀ {τ : Type u} (t : Table sch) (c : η) (f : Row sch → Option τ),
    nrows (buildColumn t c f) = nrows t :=
by intros τ t c f
   simp only [nrows, buildColumn, addColumn]
   rw [List.length_map, List.zip_length_eq_of_length_eq]
   apply Eq.symm
   apply List.length_map

theorem vcat_spec1 :
  ∀ (t1 : Table sch) (t2 : Table sch),
    schema (vcat t1 t2) = schema t1 :=
λ _ _ => rfl

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

-- This is the closest we can approximate the spec given uniqueness issues
theorem leftJoin_spec1 {s₁ s₂ : @Schema η} :
  ∀ (t₁ : Table s₁) (t₂ : Table s₂)
    (cs : ActionList (Schema.removeOtherDecCH s₁) s₂),
  schema (leftJoin t₁ t₂ cs) =
  List.append (schema t₁)
              (Schema.removeOtherDecCHs (schema t₁) (schema t₂) cs) :=
λ _ _ _ => rfl

-- TODO: again, should we use `lookupType`?
theorem leftJoin_spec2 {s₁ s₂ : @Schema η} :
  ∀ (t₁ : Table s₁) (t₂ : Table s₂)
    (cs : ActionList (Schema.removeOtherDecCH s₁) s₂)
    (c : η)
    (h : s₁.HasName c),
      (schema t₁).lookup ⟨c, h⟩ =
      (schema (leftJoin t₁ t₂ cs)).lookup ⟨c, Schema.hasNameOfAppend h⟩ :=
λ _ _ _ _ _ => Schema.lookup_eq_lookup_append _ _ _ _

-- TODO: spec 3

-- TODO: Spec 4 appears to be wrong. Consider the following SQLite queries:
/-
CREATE TABLE demo (
  id INTEGER NOT NULL PRIMARY KEY AUTOINCREMENT,
  name VARCHAR(100) NOT NULL,
  age INTEGER NOT NULL
);

CREATE TABLE demo2 (
  id INTEGER NOT NULL PRIMARY KEY AUTOINCREMENT,
  name VARCHAR(100) NOT NULL,
  location VARCHAR(100) NOT NULL
);

INSERT INTO demo VALUES (NULL, "Bob", 18);
INSERT INTO demo2 VALUES (NULL, "Bob", "USA");
INSERT INTO demo2 VALUES (NULL, "Bob", "UK");

SELECT *
FROM demo
LEFT JOIN demo2
ON demo.name=demo2.name;
-/
-- theorem leftJoin_spec4 {s₁ s₂ : @Schema η} :
--   ∀ (t₁ : Table s₁) (t₂ : Table s₂)
--     (cs : ActionList (Schema.removeOtherDecCH s₁) s₂),
--   nrows (leftJoin t₁ t₂ cs) = nrows t₁ := by
--   intros t₁ t₂ cs
--   simp only [leftJoin, nrows]

-- The spec for `getValue` (as nearly as it can be approximated up to uniqueness
-- issues) is enforced by types

theorem getColumn1_spec1 :
  ∀ (t : Table sch) (n : Nat) (h : n < ncols t),
    List.length (getColumn1 t n h) = nrows t :=
λ t n h => List.length_map _ _

-- Spec 2 is encoded in the return type of `getColumn1`

-- Spec 1 is encoded in the return type of `getColumn2`

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

-- Helper for `selectColumns1_spec2`
theorem ncols_eq_header_length :
  ∀ (t : Table sch), ncols t = (header t).length :=
λ t => Eq.symm (List.length_map _ _)

theorem selectColumns1_spec2 :
  ∀ (hs : Schema.Unique sch) (t : Table sch) (bs : List Bool)
    (h : bs.length = ncols t) (i : Nat) (hlt : i < ncols t),
  (header t).get ⟨i, ncols_eq_header_length t ▸ hlt⟩
    ∈ header (selectColumns1 t bs h)
  ↔ bs.get ⟨i, h ▸ hlt⟩ = true :=
λ hu t bs h i hlt =>
  List.sieve_map_mem_iff_true_unique hlt (h.symm ▸ hlt) Prod.fst hu

theorem selectColumns1_spec3 :
  ∀ (t : Table sch) (bs : List Bool) (h : bs.length = ncols t),
    List.Sublist (schema (selectColumns1 t bs h)) (schema t) :=
λ t bs h => List.sieve_sublist _ _

theorem selectColumns1_spec4 :
  ∀ (t : Table sch) (bs : List Bool) (h : bs.length = ncols t),
    nrows (selectColumns1 t bs h) = nrows t :=
λ t bs h => List.length_map _ _

theorem selectColumns2_spec1 :
  ∀ (t : Table sch) (ns : List (Fin (ncols t))),
    ncols (selectColumns2 t ns) = ns.length :=
λ t ns => List.length_map _ _

-- Helper for `selectColumns2_spec2`
def finHeaderLengthOfFinNcols (t : Table sch) : Fin (ncols t) →
  Fin ((header t).length)
| ⟨i, hi⟩ => ⟨i, ncols_eq_header_length t ▸ hi⟩

-- TODO: Why does this depend on `Classical.choice`?
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
  apply List.get_map_nths_eq_get_get

-- TODO: sc2 spec 3

theorem selectColumns2_spec4 :
  ∀ (t : Table sch) (ns : List (Fin (ncols t))),
    nrows (selectColumns2 t ns) = nrows t :=
λ t ns => List.length_map _ _

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

-- TODO: sc3 spec 2
#check @selectColumns3

variable (t : table sch) (cs : List (CertifiedHeader sch))

-- theorem selectColumns3_spec2 :
--   ∀ (t : Table sch) (cs : List (CertifiedHeader sch)),
--     ∀ c, c ∈ cs →
--       (schema t).lookup (Schema.cNameOfCHead c) =
--       (schema (selectColumns3 t cs)).lookup
--         ⟨c.1.1, Schema.colImpliesName c.2⟩ := sorry

theorem selectColumns3_spec3 :
  ∀ (t : Table sch) (cs : List (CertifiedHeader sch)),
    nrows (selectColumns3 t cs) = nrows t :=
λ t cs => List.length_map _ _

theorem head_spec1 : ∀ (t : Table sch) (z : {z : Int // z.abs < nrows t}),
  schema (head t z) = schema t :=
λ _ _ => rfl

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
   -- Need separate `rw`s here so that the equality proof can be auto-generated
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

-- dC spec 2 is not currently true because of duplicate issues. This is the best
-- approximation we can get instead:
theorem dropColumn_spec2 : ∀ (t : Table sch) (c : CertifiedName sch),
  header (dropColumn t c) = Schema.names (sch.removeName c.2) :=
λ t c => rfl

theorem dropColumn_spec3 : ∀ (t : Table sch) (c : CertifiedName sch),
  List.Sublist (schema (dropColumn t c)) (schema t) :=
λ _ c => Schema.removeName_sublist sch c.val c.property

theorem dropColumns_spec1 :
  ∀ (t : Table sch) (cs : ActionList Schema.removeCertifiedName sch),
  nrows (dropColumns t cs) = nrows t :=
λ t cs => List.length_map _ _

-- dCs spec 2 has the same issue as dC spec 2.
theorem dropColumns_spec2 :
  ∀ (t : Table sch) (cs : ActionList Schema.removeCertifiedName sch),
  header (dropColumns t cs) = Schema.names (sch.removeNames cs) :=
λ t cs => rfl

theorem dropColumns_spec3 :
  ∀ (t : Table sch) (cs : ActionList Schema.removeCertifiedName sch),
  List.Sublist (schema $ dropColumns t cs) (schema t) :=
λ _ cs => Schema.removeNames_sublist sch cs

-- Spec 1 is enforced by types
theorem tfilter_spec2 : ∀ (t : Table sch) (f : Row sch → Bool),
  schema (tfilter t f) = schema t :=
λ t f => rfl

theorem tsort_spec1 : ∀ {τ : Type u} [inst : Ord τ]
                        (t : Table sch)
                        (c : ((c : η) × sch.HasCol (c, τ)))
                        (b : Bool),
  nrows (tsort t c b) = nrows t :=
λ t c b => List.length_mergeSortWith _ t.rows

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
     apply tsort_spec1 (inst := x.snd.snd)

theorem sortByColumns_spec2 :
  ∀ (t : Table sch) (hs : List ((h : Header) × sch.HasCol h × Ord h.snd)),
    schema (sortByColumns t hs) = schema t :=
λ t hs => rfl

-- Spec 1 is enforced by types
theorem orderBy_spec2 :
  ∀ (t : Table sch)
    (cmps : List ((κ : Type u) × (Row sch → κ) × (κ → κ → Bool))),
    schema (orderBy t cmps) = schema t :=
λ _ _ => rfl

theorem orderBy_spec3 :
  ∀ (t : Table sch)
    (cmps : List ((κ : Type u) × (Row sch → κ) × (κ → κ → Bool))),
    nrows (orderBy t cmps) = nrows t :=
λ t _ => List.length_mergeSortWith _ t.rows

theorem count_spec1 :
  ∀ {τ} [DecidableEq τ]
    (t : Table sch) (c : ((c : η) × sch.HasCol (c, τ))),
    header (count t c) = ["value", "count"] :=
λ t c => rfl

-- This can't yet be in tactic mode because the `induction` tactic doesn't
-- support `(nm, τ)` as an index
theorem count_spec2 :
  ∀ {sch : @Schema η} {τ} [DecidableEq τ]
    (t : Table sch) (c : ((c : η) × sch.HasCol (c, τ))),
  (schema (count t c)).lookupType ⟨"value", Schema.HasName.hd⟩ =
  Option (sch.lookupType ⟨c.1, Schema.colImpliesName c.2⟩)
| _ :: _, _, _, t, ⟨_, Schema.HasCol.hd⟩ => rfl
  -- As with prior proofs, the table in the IH doesn't matter
| _ :: _, τ, _, t, ⟨nm, Schema.HasCol.tl h⟩ => count_spec2 (Table.mk []) ⟨nm, h⟩

theorem count_spec3 {τ} [DecidableEq τ] :
  ∀ (t : Table sch) (c : (c : η) × sch.HasCol (c, τ)),
  (schema (count t c)).lookupType ⟨"count", .tl .hd⟩ = Nat :=
λ _ _ => rfl

-- TODO: move this somewhere
theorem length_count_pairsToRow : ∀ (xs : List (Option τ × Nat)),
  List.length (count.pairsToRow xs) = xs.length
| [] => rfl
| x :: xs => congrArg (·+1) (length_count_pairsToRow xs)

theorem count_spec4 {τ} [DecidableEq τ] :
  ∀ (t : Table sch) (c : (c : η) × sch.HasCol (c, τ)),
  nrows (count t c) = (getColumn2 t c.1 c.2).unique.length :=
λ t c => Eq.trans (length_count_pairsToRow _) (List.length_counts _)

theorem bin_spec1 [ToString η] :
  ∀ (t : Table sch)
    (c : (c : η) × Schema.HasCol (c, Nat) sch)
    (n : { n // n > 0 }),
    header (bin t c n) = ["group", "count"] :=
λ _ _ _ => rfl

theorem bin_spec2 [ToString η] :
  ∀ (t : Table sch)
    (c : (c : η) × Schema.HasCol (c, Nat) sch)
    (n : { n // n > 0 }),
    (schema (bin t c n)).lookupType ⟨"group", Schema.HasName.hd⟩ = String :=
λ _ _ _ => rfl

theorem bin_spec3 [ToString η] :
  ∀ (t : Table sch)
    (c : (c : η) × Schema.HasCol (c, Nat) sch)
    (n : { n // n > 0 }),
    (schema (bin t c n)).lookupType
      ⟨"count", Schema.HasName.tl Schema.HasName.hd⟩ = Nat :=
λ _ _ _ => rfl

-- Spec 1 is enforced by types
theorem pivotTable_spec2 :
  ∀ (t : Table sch)
    (cs : List $ CertifiedHeader sch)
    (inst : DecidableEq (Row (Schema.fromCHeaders cs)))
    (aggs : List ((c' : Header) ×
                  (c : CertifiedHeader sch) ×
                  (List (Option c.fst.snd) → Option c'.snd))),
  header (pivotTable t cs inst aggs) =
  List.append (cs.map (·.1.1)) (aggs.map (·.1.1)) :=
λ t cs inst aggs => List.map_map_append cs aggs Prod.fst Sigma.fst Sigma.fst

-- TODO: get rid of `Classical.choice` (termination proof)
theorem pivotTable_spec3_aux :
  ∀ (cs : List $ CertifiedHeader sch)
    (aggs : List ((c' : Header) × (c : CertifiedHeader sch) ×
                  (List (Option c.fst.snd) → Option c'.snd)))
    (cn : CertifiedName (Schema.fromCHeaders cs)),
  Schema.lookup
    (List.append (Schema.fromCHeaders cs) (aggs.map (fun a => a.fst)))
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
    (inst : DecidableEq (Row (Schema.fromCHeaders cs)))
    (aggs : List ((c' : Header) ×
                  (c : CertifiedHeader sch) ×
                  (List (Option c.fst.snd) → Option c'.snd)))
    (cn : CertifiedName (Schema.fromCHeaders cs)),
    (schema $ pivotTable t cs inst aggs).lookup
      ⟨cn.1, Schema.hasNameOfAppend cn.2⟩ =
    (schema t).lookup ⟨cn.1, Schema.hasNameOfFromCHeaders cn.2⟩ :=
λ t cs inst => pivotTable_spec3_aux cs

-- Spec 4 is enforced by types

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
   simp only [nrows, groupBy]
   rw [List.length_map, List.length_groupByKey]
   apply congrArg
   apply congrArg
   rw [List.map_map]
   apply congr _ rfl
   apply congrArg
   simp only [Function.comp]

theorem completeCases_spec {τ : Type u} :
  ∀ (t : Table sch) (c : (c : η) × sch.HasCol (c, τ)),
  (completeCases t c).length = nrows t :=
λ t c => Eq.trans (List.length_map _ _) (List.length_map _ _)

theorem dropna_spec : ∀ (t : Table sch), schema (dropna t) = schema t :=
λ t => rfl

theorem fillna_spec1 {τ : Type u} :
  ∀ (t : Table sch)
    (c : (c : η) × sch.HasCol (c, τ))
    (v : τ),
    schema (fillna t c v) = schema t :=
λ _ _ _ => rfl

theorem fillna_spec2 {τ : Type u} :
  ∀ (t : Table sch)
    (c : (c : η) × sch.HasCol (c, τ))
    (v : τ),
    nrows (fillna t c v) = nrows t :=
λ _ _ _ => List.length_map _ _

-- TODO: `pivotLonger`
-- Spec 1 may not hold because of uniqueness issues?

-- Specs 3 and 4 are enforced by types

-- TODO: `pivotWider`
-- Spec 1 may not hold because of uniqueness issues?

theorem flatten_spec1 :
  ∀ (t : Table sch) (cs : ActionList Schema.flattenList sch),
  header (flatten t cs) = header t := by
  intros t cs
  simp only [flatten, header, Schema.names]
  induction cs with
  | nil => simp only [Schema.flattenLists]
  | cons c cs ih =>
    simp only [Schema.flattenLists]
    rw [ih]
    simp only [Schema.flattenList]
    apply Schema.retypeColumn_preserves_names
    -- TODO: this shouldn't be necessary with more careful induction
    exact []
    exact Table.mk []

-- TODO: `flatten` spec 2

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
    (c : (c : η) × sch.HasCol (c, τ₁))
    (f : Option τ₁ → Option τ₂),
  header (transformColumn t c f) = header t :=
λ t c f => sch.retypeColumn_preserves_names _ _

-- Closest approximation given uniqueness issues
-- The first bullet point in the written spec is ensured by the type
theorem transformColumn_spec3 : ∀ {sch} {τ₁ τ₂}
    (t : Table sch)
    (c : (c : η) × sch.HasCol (c, τ₁))
    (f : Option τ₁ → Option τ₂),
  (schema $ transformColumn t c f).removeHeader (Schema.hasRetypedCol c) =
    sch.removeHeader c.2
| _, _, _, t, ⟨_, .hd⟩, f => rfl
| _, _, _, t, ⟨nm, .tl htl⟩, f =>
  have ih := transformColumn_spec3 (Table.mk []) ⟨nm, htl⟩ f
  congrArg _ ih
  /- Tactic mode:
  rename_i τ₁ τ₂ hdr hs
  simp only [schema]
  simp only [Schema.removeHeader]
  simp only [Schema.retypeColumn]
  have h := @Schema.colImpliesName_eq_2 η hs hdr (nm, τ₁) htl
  simp only [h]
  simp only [Schema.removeName]
  apply congrArg
  apply ih
  -/

theorem transformColumn_spec4 :
  ∀ (t : Table sch)
    (c : (c : η) × sch.HasCol (c, τ₁))
    (f : Option τ₁ → Option τ₂),
  nrows (transformColumn t c f) = nrows t :=
λ t c f => List.length_map _ _

-- TODO: `renameColumns` specs 1 and 2

theorem renameColumns_spec3 :
  ∀ (t : Table sch)
    (ccs : ActionList Schema.renameColumnCN sch),
  nrows (renameColumns t ccs) = nrows t :=
λ _ _ => List.length_map _ _

-- The specification for `find` is contained in its type (`Option` corresponds
-- to "Error," and `Fin` restricts the range of the output)

theorem groupByRetentive_spec1 [DecidableEq τ] :
  ∀ (t : Table sch) (c : (c : η) × sch.HasCol (c, τ)),
  header (groupByRetentive t c) = ["key", "groups"] :=
λ _ _ => rfl

theorem groupByRetentive_spec2
  {η : Type u_η} [DecidableEq η] {sch : @Schema η}
  {τ : Type u} [DecidableEq τ] :
  ∀ (t : Table sch) (c : (c : η) × sch.HasCol (c, τ)),
  (schema (groupByRetentive t c)).lookupType ⟨"key", Schema.HasName.hd⟩
    = ULift.{max (u+1) u_η} τ :=
λ _ _ => rfl

theorem groupByRetentive_spec3
  {η : Type u_η} [DecidableEq η] {sch : @Schema η}
  {τ : Type u} [DecidableEq τ] :
  ∀ (t : Table sch) (c : (c : η) × sch.HasCol (c, τ)),
  (schema (groupByRetentive t c)).lookupType ⟨"groups", .tl .hd⟩ = Table sch :=
λ _ _ => rfl

-- Need decidable equality of `ULift`s for `groupBy{Retentive,Subtractive}`
deriving instance DecidableEq for ULift

theorem groupByRetentive_spec4 [inst : DecidableEq τ] :
  ∀ (t : Table sch) (c : (c : η) × sch.HasCol (c, τ)),
  (getColumn2 (groupByRetentive t c) "key" Schema.HasCol.hd).NoDuplicates := by
  intros t c
  simp only [groupByRetentive, groupBy, getColumn2]
  rw [List.map_map]
  -- FIXME: trying to unfold `Row.getCell` causes Lean to throw an assertion
  -- violation (this is a Lean bug)
  simp only [Function.comp, getValue]
  -- simp only [Function.comp, getValue, Row.getCell]
  conv =>
    rhs
    lhs
    apply funext (f₂ := _) _
    apply (λ x => Option.map ULift.up x.fst)
    -- `intros` doesn't seem to be working in `conv` mode?
    apply (λ x => Cell.toOption_fromOption _)
  conv =>
    rhs
    lhs
    apply funext (f₂ := _) _
    apply (λ x => Option.map ULift.up ∘ Prod.fst)
    apply (λ x => rfl)
  rw [←List.map_map]
  apply List.no_dups_map_injective
  -- Show `Option.map ULift.up` is injective
  . intros x y hxy
    cases x
    . cases y
      . rfl
      . contradiction
    . cases y
      . contradiction
      . cases hxy; rfl
  . apply List.groupByKey_fsts_no_duplicates

theorem groupByRetentive_spec5
  {η : Type u_η} {τ : Type u} [dec_η : DecidableEq η]
  {sch : @Schema η} [DecidableEq τ] :
  ∀ (t : Table sch) (c : (c : η) × sch.HasCol (c, τ)),
  ∀ t', t' ∈ (getColumn2 (groupByRetentive t c) "groups" (.tl .hd)).somes →
  schema t' = sch :=
λ _ _ _ _ => rfl

theorem groupByRetentive_spec6
  {η : Type u_η} {τ : Type u} [dec_η : DecidableEq η]
  {sch : @Schema η} [DecidableEq τ] :
  ∀ (t : Table sch) (c : (c : η) × sch.HasCol (c, τ)),
  nrows (groupByRetentive t c) = (getColumn2 t c.1 c.2).unique.length :=
λ t c =>
  groupBy_spec4 (sch' := [("key", ULift.{max (u+1) u_η} τ),
                          ("groups", Table sch)])
    t
    (λ r => getValue r c.1 c.2)
    (λ r => r)
    (λ k vs => Row.cons (Cell.fromOption (Option.map ULift.up k))
                        (Row.cons (Cell.val (Table.mk vs)) Row.nil))

theorem groupBySubtractive_spec1 [DecidableEq τ] :
  ∀ (t : Table sch) (c : (c : η) × sch.HasCol (c, τ)),
  header (groupBySubtractive t c) = ["key", "groups"] :=
λ _ _ => rfl

theorem groupBySubtractive_spec2
  {η : Type u_η} [DecidableEq η] {sch : @Schema η}
  {τ : Type u} [DecidableEq τ] :
  ∀ (t : Table sch) (c : (c : η) × sch.HasCol (c, τ)),
  (schema (groupBySubtractive t c)).lookupType ⟨"key", Schema.HasName.hd⟩
    = ULift.{max (u+1) u_η} τ :=
λ _ _ => rfl

theorem groupBySubtractive_spec3
  {η : Type u_η} [DecidableEq η] {sch : @Schema η}
  {τ : Type u} [DecidableEq τ] :
  ∀ (t : Table sch) (c : (c : η) × sch.HasCol (c, τ)),
  (schema (groupBySubtractive t c)).lookupType ⟨"groups", .tl .hd⟩ =
  Table (sch.removeName (Schema.colImpliesName c.snd)) :=
λ _ _ => rfl

-- TODO: See if there's a way to unify this with `groupByRetentive_spec4` rather
-- than copy/pasting
theorem groupBySubtractive_spec4 [inst : DecidableEq τ] :
  ∀ (t : Table sch) (c : (c : η) × sch.HasCol (c, τ)),
  (getColumn2 (groupBySubtractive t c) "key" Schema.HasCol.hd).NoDuplicates :=
  by
  intros t c
  simp only [groupBySubtractive, groupBy, getColumn2]
  rw [List.map_map]
  -- FIXME: trying to unfold `Row.getCell` causes Lean to throw an assertion
  -- violation (this is a Lean bug)
  simp only [Function.comp, getValue]
  -- simp only [Function.comp, getValue, Row.getCell]
  conv =>
    rhs
    lhs
    apply funext (f₂ := _) _
    apply (λ x => Option.map ULift.up x.fst)
    -- `intros` doesn't seem to be working in `conv` mode?
    apply (λ x => Cell.toOption_fromOption _)
  conv =>
    rhs
    lhs
    apply funext (f₂ := _) _
    apply (λ x => Option.map ULift.up ∘ Prod.fst)
    apply (λ x => rfl)
  rw [←List.map_map]
  apply List.no_dups_map_injective
  -- Show `Option.map ULift.up` is injective
  . intros x y hxy
    cases x
    . cases y
      . rfl
      . contradiction
    . cases y
      . contradiction
      . cases hxy; rfl
  . apply List.groupByKey_fsts_no_duplicates

-- Closest approximation possible given uniqueness issues
theorem groupBySubtractive_spec5
  {η : Type u_η} [DecidableEq η] {sch : @Schema η}
  {τ : Type u} [DecidableEq τ] :
  ∀ (t : Table sch) (c : (c : η) × sch.HasCol (c, τ)),
  ∀ t', t' ∈ (getColumn2 (groupBySubtractive t c) "groups" (.tl .hd)).somes →
  header t' = Schema.names (sch.removeName (Schema.colImpliesName c.2)) :=
λ _ _ _ _ => rfl

theorem groupBySubtractive_spec6
  {η : Type u_η} {τ : Type u} [dec_η : DecidableEq η]
  {sch : @Schema η} [DecidableEq τ] :
  ∀ (t : Table sch) (c : (c : η) × sch.HasCol (c, τ)),
  ∀ t', t' ∈ (getColumn2 (groupBySubtractive t c) "groups" (.tl .hd)).somes →
  List.Sublist (schema t') sch :=
λ _ c _ _ => Schema.removeName_sublist sch c.1 (Schema.colImpliesName c.2)

theorem groupBySubtractive_spec7
  {η : Type u_η} {τ : Type u} [dec_η : DecidableEq η]
  {sch : @Schema η} [DecidableEq τ] :
  ∀ (t : Table sch) (c : (c : η) × sch.HasCol (c, τ)),
  nrows (groupBySubtractive t c) = (getColumn2 t c.1 c.2).unique.length :=
λ t c =>
  groupBy_spec4
    t
    (λ r => getValue r c.1 c.2)
    (λ r => r)
    (λ k vs => Row.cons (Cell.fromOption (Option.map ULift.up k))
                        (Row.cons (Cell.val (Table.mk (vs.map (λ r =>
                          Row.removeColumn (Schema.colImpliesName c.snd) r))))
                        Row.nil))

-- TODO: `update` (once correctly implemented)

-- Specs 1, 2, and 3 are enforced by types
theorem select_spec4 {sch' : @Schema η} :
  ∀ (t : Table sch) (f : Row sch → Fin (nrows t) → Row sch'),
  nrows (select t f) = nrows t :=
λ t f => Eq.trans (List.length_map _ _) (List.length_verifiedEnum _)

-- All `selectMany` specifications are enforced by types

-- Specs 1 through 5 are enforced by types
theorem groupJoin_spec6
  {κ} [DecidableEq κ] {ν : Type _} {s₁ s₂ s₃ : @Schema η} :
  ∀ (t₁ : Table s₁) (t₂ : Table s₂)
    (getKey₁ : Row s₁ → κ) (getKey₂ : Row s₂ → κ)
    (aggregate : Row s₁ → Table s₂ → Row s₃),
  nrows (groupJoin t₁ t₂ getKey₁ getKey₂ aggregate) =
  nrows t₁ :=
λ _ _ _ _ _ => select_spec4 _ _

-- All `join` specifications are enforced by types
