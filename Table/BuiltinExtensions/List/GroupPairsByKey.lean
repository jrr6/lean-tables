import Table.BuiltinExtensions.Logic
import Table.BuiltinExtensions.List.Filtering
import Table.BuiltinExtensions.List.Predicates

/-!
Implementation of and lemmas about `groupPairsByKey`, used in the `groupBy` function.
Contains infrastructure for `groupBy`, as well as some extra proofs that
aren't used but might be useful in the future.
-/

/-
Takes a list `kvs` consisting of (key, value) pairs and a key `k` and returns
a tuple `(vs, kvs')` where `vs` are all values having key `k` and `kvs'` is the
sublist of `kvs` with key entries not equal to `k`.
-/
def List.matchKey {κ ν} [DecidableEq κ]
    : List (κ × ν) → κ → List ν × List (κ × ν)
| [], _ => ([], [])
| (k, v) :: kvs, x =>
  let res := matchKey kvs x
  if k = x
  then (v :: res.1, res.2)
  else (res.1, (k, v) :: res.2)

theorem List.matchKey_snd_length {κ ν} [DecidableEq κ] :
    ∀ (xs : List (κ × ν)) (k : κ), (matchKey xs k).2.length ≤ xs.length :=
by intros xs k
   induction xs with
   | nil => exact Nat.le.refl
   | cons x xs ih =>
     simp only [matchKey]
     apply @Decidable.byCases (x.1=k) _
     . intros heq
       simp only [heq]
       rw [ite_true]
       simp only [Prod.snd]
       apply Nat.le_step
       exact ih
     . intros hneq
       simp only [hneq]
       rw [ite_false]
       simp only [Prod.fst]
       apply Nat.succ_le_succ
       exact ih

theorem List.matchKey_lengths_sum {κ ν} [inst : DecidableEq κ] :
  ∀ (xs : List (κ × ν)) (k : κ),
  (matchKey xs k).1.length + (matchKey xs k).2.length = xs.length :=
by intros xs k
   induction xs with
   | nil => rfl
   | cons x xs ih =>
     simp only [matchKey]
     cases inst x.1 k with
     | isFalse hfalse =>
       simp only [hfalse, ite_false, List.length]
       rw [←Nat.add_assoc]
       apply congrArg (·+1) ih
     | isTrue htrue =>
       simp only [htrue, ite_true, List.length]
       rw [Nat.add_assoc, Nat.add_comm 1, ←Nat.add_assoc]
       apply congrArg (·+1) ih

theorem List.not_mem_matchKey_self_map_snd {κ ν} [DecidableEq κ]
  (k : κ) (kvs : List (κ × ν)) :
  k ∉ map Prod.fst (matchKey kvs k).snd := by
  intro hneg
  induction kvs with
  | nil => cases hneg
  | cons kv kvs ih =>
    apply ih
    simp only [matchKey] at hneg
    cases Decidable.em (kv.fst = k) with
    | inl heq =>
      simp only [heq, ite_true] at hneg
      assumption
    | inr hneq =>
      simp only [hneq, ite_false] at hneg
      simp only [map] at hneg
      cases hneg with
      | head => exact absurd rfl hneq
      | tail _ h => exact h

theorem List.fst_mem_of_pair_mem : ∀ (x : α) (y : β) (ps : List (α × β)),
  (x, y) ∈ ps → x ∈ (map Prod.fst ps)
| x, y, [], hxy => by contradiction
| x, y, _ :: ps, List.Mem.head _ => List.Mem.head _
| x, y, _ :: ps, List.Mem.tail a h => Mem.tail _ $ fst_mem_of_pair_mem x y ps h

theorem List.matchKey_snd_keys_neq_k [DecidableEq κ] (xs : List (κ × ν)) :
  ∀ e, e ∈ (matchKey xs k).snd → e.fst ≠ k := λ e he hneg =>
  absurd (List.fst_mem_of_pair_mem e.1 e.2 (matchKey xs k).snd he)
         (hneg ▸ not_mem_matchKey_self_map_snd k xs)

def List.uniqueFoldl [DecidableEq α] (xs : List α) :=
  xs.foldl (λ acc x => if x ∈ acc then acc else acc ++ [x]) []

-- theorem List.unique_eq_uniqueFold_aux [DecidableEq α] :
--   ∀ (xs : List α) (acc : List α),
--   uniqueAux xs acc =
--     foldl (λ acc x => if x ∈ acc then acc else acc ++ [x]) (reverse acc) xs := sorry
  --   by
  -- intros xs acc
  -- induction xs generalizing acc with
  -- | nil => simp [uniqueAux, foldl]
  -- | cons x xs ih =>
  --   simp only [uniqueAux, foldl]
  --   cases Decidable.em (x ∈ acc) with
  --   | inl h =>
  --     simp only [h, ite_true]
  --     conv =>
  --       rhs
  --       lhs
  --       have : (if x ∈ reverse acc then reverse acc else reverse acc ++ [x]) =
  --              if x ∈ acc then reverse acc else reverse acc ++ [x] := by rw [← mem_reverse]


-- theorem List.unique_eq_uniqueFold [DecidableEq α] :
--   ∀ (xs : List α), unique xs = uniqueFoldl xs := by
--   intros xs
--   induction xs with
--   | nil => simp [unique, uniqueFoldl, uniqueAux, foldl]
--   | cons x xs ih =>
--     simp only [unique, uniqueFoldl, uniqueAux]
--     simp only [List.not_mem_nil, ite_false]
--     rw [unique_eq_uniqueFold_aux]
--     simp only [foldl]
--     apply congrArg
--     rfl

theorem List.all_pred {p : α → Prop} [DecidablePred p] {xs : List α} :
  xs.all (λ x => decide (p x)) ↔ ∀ x, x ∈ xs → p x :=
  ⟨λ h x hx => of_decide_eq_true (List.all_eq_true.mp h x hx),
   λ h => List.all_eq_true.mpr (λ x hx => decide_eq_true (h x hx))⟩

theorem List.length_sublist_le {α} {xs ys : List α} :
  xs <+ ys → xs.length ≤ ys.length
  | .slnil => .refl
  | .cons _ hsubl => Nat.le_succ_of_le (length_sublist_le hsubl)
  | .cons₂ _ hsubl => Nat.succ_le_succ (length_sublist_le hsubl)

theorem List.matchKey_fst_eq_filter_k_map_snd {κ ν} [inst : DecidableEq κ] :
  ∀ (xs : List (κ × ν)) (k : κ),
    (matchKey xs k).1 = (xs.filter (λ x => x.1 = k)).map Prod.snd :=
by intros xs k
   induction xs with
   | nil => rfl
   | cons x xs ih =>
     simp only [matchKey]
     cases inst x.1 k with
     | isFalse hfalse =>
       simp only [hfalse, ite_false, ih, filter]
       exact rfl
     | isTrue htrue =>
       simp [htrue, ite_true, filter, ih, map]

theorem List.matchKey_length_lt {κ} [DecidableEq κ] {ν}
                                (k : κ) (kvs : List (κ × ν)) :
  (matchKey kvs k).2.length < kvs.length.succ :=
  Nat.lt_of_succ_le $ Nat.succ_le_succ $ matchKey_snd_length kvs k

def List.groupPairsByKey {κ} [DecidableEq κ] {ν} : List (κ × ν) → List (κ × List ν)
| [] => []
| (k, v) :: kvs =>
  have h_help : (matchKey kvs k).2.length < kvs.length.succ :=
    matchKey_length_lt k kvs

  let fms := matchKey kvs k
  (k, v :: fms.1) :: groupPairsByKey fms.2
termination_by xs => xs.length
decreasing_by assumption

theorem List.groupPairsByKey_matchKey_snd_length_cons [DecidableEq κ]
  (k : κ) (v : ν) (xs : List (κ × ν)) :
  1 + length (groupPairsByKey (matchKey ((k, v) :: xs) k).snd)
    = (groupPairsByKey ((k, v) :: xs)).length :=
calc
  1 + length (groupPairsByKey (matchKey ((k, v) :: xs) k).2)
  = 1 + length (groupPairsByKey (matchKey xs k).2) :=
    by simp only [matchKey, length, ite_true]
  _ = length (groupPairsByKey (matchKey xs k).2) + 1 := Nat.add_comm _ _
  _ = length ((k, v :: (matchKey xs k).1) :: groupPairsByKey (matchKey xs k).2) :=
    rfl
  _ = length (groupPairsByKey ((k, v) :: xs)) := by simp only [matchKey, groupPairsByKey]

theorem List.length_uniqueAux_matchKey {κ ν} [DecidableEq κ]
  (xs : List (κ × ν)) (k : κ) :
  ∀ (acc : List κ) (hk : k ∈ acc),
  (uniqueAux (map Prod.fst xs) acc).length
  = (uniqueAux (map Prod.fst (matchKey xs k).snd) acc).length :=
by induction xs with
   | nil => intros; simp [uniqueAux]
   | cons x xs ih =>
     intros acc hk
     simp only [length, uniqueAux]
     cases Decidable.em (x.fst ∈ acc) with
     | inl hin =>
       simp only [hin, ite_true, matchKey]
       rw [ih _ hk]
       cases Decidable.em (x.1 = k) with
       | inl heq => simp only [heq, ite_true]
       | inr hneq => simp only [hneq, ite_false, map, uniqueAux, hin, ite_true]
     | inr hout =>
       simp only [hout, ite_false, matchKey]
       cases Decidable.em (x.1 = k) with
       | inl heq =>
         apply absurd hk
         rw [heq] at hout
         exact hout
       | inr hneq =>
         rw [ih _ (List.Mem.tail _ hk)]
         simp only [hneq, ite_false, uniqueAux, hout]

instance (y : Nat) : Decidable (∀ x : Nat, x - y = x) :=
  if h : y = 0
  then Decidable.isTrue (λ x => by rw [h]; simp)
  else Decidable.isFalse (λ x => by
    have h1 : 1 - y = 1 := x 1
    have : y > 0 := Nat.zero_lt_of_ne_zero h
    have := Nat.sub_lt (Nat.lt.base 0) this
    apply absurd h1
    apply Nat.ne_of_lt this)

theorem List.length_groupPairsByKey {κ} [DecidableEq κ] {ν} :
  ∀ (xs : List (κ × ν)),
  length (groupPairsByKey xs) = (xs.map Prod.fst).unique.length
| [] => by simp only [groupPairsByKey, unique, uniqueAux, length]
| (k, v) :: xs => by
  have hterm : length (matchKey xs k).snd < Nat.succ (length xs) :=
    Nat.lt_of_succ_le $ Nat.succ_le_succ $ matchKey_snd_length xs k
  have ih := length_groupPairsByKey (matchKey xs k).2
  simp only [map, unique, uniqueAux, List.not_mem_nil, ite_false, groupPairsByKey]
  -- This needs to be a separate `simp` to ensure proper ordering
  simp only [length]
  rw [length_uniqueAux_matchKey _ k _ $ List.Mem.head _]
  rw [ih]
  apply Eq.symm
  apply List.length_uniqueAux (acc := [k])
  intro x
  rw [mem_singleton]
  intro hmem hneg
  have := not_mem_matchKey_self_map_snd x xs
  rw [←hneg] at hmem
  exact this hmem
termination_by xs => length xs
decreasing_by assumption
-- END `groupPairsByKey` - `groupBy` spec 4

-- BEGIN `groupByRetentive` spec 4 (this might simplify some stuff above?)

theorem List.matchKey_snd_sublist [DecidableEq κ] :
  ∀ (k : κ) (kvs : List (κ × ν)), (matchKey kvs k).snd <+ kvs
| _, [] => Sublist.slnil
| k, (kv :: kvs) =>
  have ih := matchKey_snd_sublist k kvs
  if h : kv.fst = k
  then by simp only [matchKey, h, ite_true]; exact Sublist.cons _ ih
  else by simp only [matchKey, h, ite_true]; exact Sublist.cons₂ _ ih

theorem List.matchKey_snd_sublist_of_sublist [DecidableEq κ] :
  ∀ (k : κ) (xs ys : List (κ × ν)),
  xs <+ ys → (matchKey xs k).snd <+ (matchKey ys k).snd := by
  intro k xs ys h
  induction h with
  | slnil => constructor
  | cons x' h' ih =>
    simp only [matchKey]
    cases Decidable.em (x'.fst = k) with
    | inl heq => simp only [heq, ite_true]; apply ih
    | inr hneq => simp only [hneq, ite_false]; apply Sublist.cons _ ih
  | cons₂ x' h' ih =>
    simp only [matchKey]
    cases Decidable.em (x'.fst = k) with
    | inl heq => simp only [heq, ite_true]; assumption
    | inr hneq =>
      simp only [hneq, ite_false]
      apply Sublist.cons₂ _ ih

theorem List.fst_groupPairsByKey_sublist [DecidableEq κ] : ∀ (kvs : List (κ × ν)),
  map Prod.fst (groupPairsByKey kvs) <+ map Prod.fst kvs
| [] => groupPairsByKey.eq_1 (κ := κ) ▸ Sublist.slnil
| (k, v) :: kvs =>
  have hterm := matchKey_length_lt k kvs
  have ih := fst_groupPairsByKey_sublist (matchKey kvs k).snd
  have hsubl := matchKey_snd_sublist k kvs
  by
    simp only [groupPairsByKey]
    exact Sublist.cons₂ _ $
    Sublist.trans ih (map_sublist_of_sublist _ _ _ hsubl)
termination_by kvs => kvs.length

-- It would be nice to do this fully in tactic mode, but there doesn't seem to
-- be a way to retain unused `have`s as termination hints in tactic mode
theorem List.mem_fst_matchKey_key_or_snd [DecidableEq κ] :
  ∀ {ys : List (κ × ν)} {x : κ},
  x ∈ map Prod.fst ys → ∀ k, x = k ∨ x ∈ map Prod.fst (matchKey ys k).snd :=
λ {ys x} hx k =>
  if h : x = k
  then Or.inl h
  else Or.inr $
    match ys with
    | (k', v) :: ys =>
      have h_term : length (matchKey ys k).snd < Nat.succ (length ys) :=
        matchKey_length_lt k ys
      have h_term' : length ys < Nat.succ (length ys) := Nat.le.refl
      by
      simp only [matchKey]
      cases Decidable.em (k' = k) with
      | inl hkeq =>
        simp only [hkeq, ite_true]
        have : x ∈ map Prod.fst ys := by
          cases hx with
          | head => contradiction
          | tail => assumption
        have ih := mem_fst_matchKey_key_or_snd this k
        cases ih with
        | inl => contradiction
        | inr hmem => exact hmem
      | inr hkneq =>
        simp only [hkneq, ite_false]
        simp only [map]
        cases Decidable.em (x = k') with
        | inl hxeq => rw [hxeq]; apply Mem.head
        | inr hxneq =>
          apply Mem.tail
          have : x ∈ map Prod.fst (matchKey ys k).snd := by
            cases hx with
            | head => contradiction
            | tail _ htail =>
              have := mem_fst_matchKey_key_or_snd htail k
              cases this with
              | inl => contradiction
              | inr => assumption
          have ih := mem_fst_matchKey_key_or_snd this k'
          cases ih with
          | inl => contradiction
          | inr => assumption
termination_by ys x hx k => ys.length

-- TODO: avoid copy/paste?
theorem List.mem_fst_groupPairsByKey_key_or_snd [DecidableEq κ] :
  ∀ {ys : List (κ × ν)} {x : κ},
  x ∈ map Prod.fst ys →
    ∀ k, x = k ∨ x ∈ map Prod.fst (groupPairsByKey (matchKey ys k).snd) :=
λ {ys x} hx k =>
  if h : x = k
  then Or.inl h
  else Or.inr $
    match ys with
    | (k', v) :: ys =>
      have h_term : length (matchKey ys k).snd < Nat.succ (length ys) :=
        matchKey_length_lt k ys
      have h_term' : length ys < Nat.succ (length ys) := Nat.le.refl
      by
      simp only [matchKey]
      cases Decidable.em (k' = k) with
      | inl hkeq =>
        simp only [hkeq, ite_true]
        have : x ∈ map Prod.fst ys := by
          cases hx with
          | head => contradiction
          | tail => assumption
        have ih := mem_fst_groupPairsByKey_key_or_snd this k
        cases ih with
        | inl => contradiction
        | inr hmem => exact hmem
      | inr hkneq =>
        simp only [hkneq, ite_false]
        simp only [groupPairsByKey]
        simp only [map]
        cases Decidable.em (x = k') with
        | inl hxeq => rw [hxeq]; apply Mem.head
        | inr hxneq =>
          apply Mem.tail
          have : x ∈ map Prod.fst (matchKey ys k).snd := by
            cases hx with
            | head => contradiction
            | tail _ htail =>
              have := mem_fst_matchKey_key_or_snd htail k
              cases this with
              | inl => contradiction
              | inr => assumption
          have ih := mem_fst_groupPairsByKey_key_or_snd this k'
          cases ih with
          | inl => contradiction
          | inr => assumption
termination_by ys x hx k => ys.length

/-
Although tempting, the stronger claim
  `xs <+ ys → map Prod.fst (groupPairsByKey xs) <+ map Prod.fst (groupPairsByKey ys)`
does not hold, as the following counterexample illustrates:

* `List.groupPairsByKey [("a", 1), ("b", 2), ("a", 3)]`
* `List.groupPairsByKey [("b", 2), ("a", 3)]`

Also, the initial hypothesis is a bit stricter than it needs to be:
`(∀ x, x ∈ xs → x ∈ ys)` would suffice.
-/
unseal List.groupPairsByKey in
theorem List.all_in_map_fst_groupPairsByKey_of_sublist [DecidableEq κ] :
  ∀ {xs ys : List (κ × ν)},
  xs <+ ys →
    ∀ x, x ∈ map Prod.fst (groupPairsByKey xs) → x ∈ map Prod.fst (groupPairsByKey ys)
| _, _, @Sublist.cons _ xs ys (k, v) hsubl, x, hx =>
  if heq : x = k
  then heq ▸ Mem.head _
  else
    have hterm : ys.length < Nat.succ ys.length := Nat.le.refl
    have ih := all_in_map_fst_groupPairsByKey_of_sublist hsubl x hx
    have hor : x = k ∨ x ∈ map Prod.fst (groupPairsByKey (matchKey ys k).snd) :=
      mem_fst_groupPairsByKey_key_or_snd
        (Sublist.mem ih (fst_groupPairsByKey_sublist ys)) k
    Mem.tail k $
    match hor with
    | .inl hxeq => absurd hxeq heq
    | .inr hmem => hmem
| _, _, @Sublist.cons₂ _ xs ys (k, v) hsubl, x, hx => by
    simp only [groupPairsByKey]
    simp only [map]
    simp only [groupPairsByKey] at hx
    simp only [map] at hx
    cases hx with
    | head => constructor
    | tail _ htail =>
      apply Mem.tail
      have : (matchKey xs k).snd <+ (matchKey ys k).snd :=
        matchKey_snd_sublist_of_sublist _ _ _ hsubl
      have hterm := matchKey_length_lt k ys
      apply all_in_map_fst_groupPairsByKey_of_sublist this
      assumption
termination_by xs ys hsubl x hx => ys.length

-- #check @List.not_mem_matchKey_self_snd
-- #check @List.matchKey_snd_sublist
-- #check @List.matchKey_snd_sublist_of_sublist
-- theorem List.map_groupPairsByKey_matchKey_wip [DecidableEq κ] {k : κ} {kvs : List (κ × ν)} :
--   ∀ x, x ∈ map Prod.fst (groupPairsByKey (matchKey kvs k).snd) → x ∈ map Prod.fst (groupPairsByKey kvs) := by
--   intro x hx
--   induction kvs with
--   | nil => simp only [groupPairsByKey, map] at hx; contradiction
--   | cons kv kvs ih =>
--     cases kv with | mk k' v =>
--     -- simp only [matchKey] at hx
--     simp only [groupPairsByKey]
--     simp only [map]
--     cases Decidable.em (x = k') with
--     | inl heq =>
--       rw [heq]
--       apply Mem.head
--     | inr hneq =>
--       simp only [matchKey] at hx
--       apply Mem.tail
--       cases Decidable.em (k' = k) with
--       | inl heq' =>
--         simp only [heq', ite_true] at hx
--         rw [heq']
--         apply hx
--       | inr hneq' =>
--         simp only [hneq', ite_false] at hx
--         simp only [groupPairsByKey] at hx
--         simp only [map] at hx
--         have := matchKey_snd_sublist k' (matchKey kvs k).snd
--         sorry

-- The converse is also true, but we don't need it here
unseal List.groupPairsByKey in
theorem List.mem_fsts_of_mem_fsts_groupPairsByKey [DecidableEq κ] (kvs : List (κ × ν)) :
  k ∈ map Prod.fst (groupPairsByKey kvs) → k ∈ map Prod.fst kvs := by
  intro h
  induction kvs with
  | nil => contradiction
  | cons kv kvs ih =>
    cases kv with | mk k₀ v₀ =>
    simp only [groupPairsByKey] at h
    simp only [map] at h
    simp only [map]
    cases h with
    | head => apply Mem.head
    | tail _ htail =>
      apply Mem.tail
      apply ih
      apply all_in_map_fst_groupPairsByKey_of_sublist (matchKey_snd_sublist k₀ kvs)
      assumption

-- Instead of being separate, this could just be folded into
-- `groupPairsByKey_fsts_no_duplicates`
theorem List.key_not_mem_fst_groupPairsByKey_matchKey_snd [DecidableEq κ]
  (kvs : List (κ × ν)) (k : κ) :
  k ∉ map Prod.fst (groupPairsByKey (matchKey kvs k).snd) :=
  mt (List.mem_fsts_of_mem_fsts_groupPairsByKey (matchKey kvs k).snd)
    (List.not_mem_matchKey_self_map_snd _ _)

-- TODO: almost certainly need something more general for the induction
unseal List.groupPairsByKey in
theorem List.groupPairsByKey_fsts_no_duplicates [DecidableEq κ] :
  ∀ (kvs : List (κ × ν)), Unique $ (groupPairsByKey kvs).map Prod.fst
| [] => Unique.nil
| (k, v) :: kvs =>
  have h_help : (matchKey kvs k).2.length < kvs.length.succ :=
    matchKey_length_lt k kvs
  Unique.cons
    (List.key_not_mem_fst_groupPairsByKey_matchKey_snd _ _)
    (groupPairsByKey_fsts_no_duplicates (matchKey kvs k).2)
termination_by xs => xs.length
decreasing_by assumption

theorem List.mem_of_mem_injective_map (f : α → β) (hf : Injective f) :
  ∀ (x : α) (xs : List α),
  f x ∈ map f xs ↔ x ∈ xs :=
λ _ xs => Iff.intro
  (λ h =>
    have ⟨_, hb⟩ := mem_map.mp h
    have hbeqx := hf _ _ hb.right
    Eq.subst (motive := λ a => a ∈ xs) hbeqx hb.left
  )
  (mem_map_of_mem _)

theorem List.unique_of_map_injective_unique
  (f : α → β) (hf : Injective f) : ∀ (xs : List α) (hxs : Unique xs),
  Unique $ map f xs
| [], hxs => Unique.nil
| x :: xs, Unique.cons hxnin hndxs =>
  Unique.cons
    (λ hneg => absurd ((mem_of_mem_injective_map f hf x xs).mp hneg) hxnin)
    (unique_of_map_injective_unique f hf xs hndxs)
-- END `groupByRetentive` spec 4
