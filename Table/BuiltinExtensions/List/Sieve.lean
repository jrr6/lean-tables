import Table.BuiltinExtensions.List.Filtering

/-!
Contains `List.sieve` and associated lemmas.
-/

def List.sieve {α} : List Bool → List α → List α
| [], xs => xs
| _, [] => []
| true :: bs, x :: xs => x :: sieve bs xs
| false :: bs, _ :: xs => sieve bs xs

theorem List.sieve_sublist : (bs : List Bool) → (xs : List α) →
  Sublist (List.sieve bs xs) xs
| [], [] => Sublist.slnil
| [], x :: xs => List.sublist_self (x :: xs)
| true :: bs, [] => Sublist.slnil
| false :: bs, [] => Sublist.slnil
| true :: bs, x :: xs => Sublist.cons₂ x (sieve_sublist bs xs)
| false :: bs, x :: xs => Sublist.cons x (sieve_sublist bs xs)

theorem List.sieve_removeAllEq : (bs : List Bool) → (xs : List α) →
  length bs = length xs →
    length (sieve bs xs) = length (removeAllEq bs [false])
| [], [], h => rfl
| b :: bs, [], h => by cases h
| [], x :: xs, h => by cases h
| true :: bs, x :: xs, h =>
  have ih := sieve_removeAllEq bs xs (Nat.succ.inj h)
  by rw [removeAllEq_singleton_hd_neq]
     . simp only [length]
       apply congrArg (λ x => x + 1)
       exact ih
     . apply Bool.noConfusion
| false :: bs, x :: xs, h =>
  have ih := sieve_removeAllEq bs xs (Nat.succ.inj h)
  by rw [removeAllEq_singleton_hd_eq]
     . simp only [length, sieve]
       exact ih

-- BEGIN lemmas for `selectColumns1_spec2`
theorem List.sieve_mem_iff_true_unique :
  ∀ {i} {xs : List α} {bs : List Bool} (pf1 pf2) (hu : List.Unique xs),
  xs.get ⟨i, pf1⟩ ∈ bs.sieve xs ↔ bs.get ⟨i, pf2⟩ = true
| 0, x :: xs, false :: bs, pf1, pf2, .cons hnmem hu' =>
  Iff.intro
    (λ hf =>
      have not_mem_sieve_of_not_mem :=
        mt (Sublist.mem.swap (sieve_sublist bs xs))
      False.elim $ not_mem_sieve_of_not_mem hnmem hf)
    (λ hb => nomatch hb)
| 0, x :: xs, true :: bs, pf1, pf2, .cons hnmem hu' =>
  Iff.intro
    (λ _ => rfl)
    (λ _ => List.Mem.head _)
| .succ n, x :: xs, false :: bs, pf1, pf2, .cons hnmem hu' =>
  have pf1' := Nat.lt_of_succ_lt_succ pf1
  have pf2' := Nat.lt_of_succ_lt_succ pf2
  Iff.intro
    (λ hf => (sieve_mem_iff_true_unique pf1' pf2' hu').mp hf)
    (λ hb => (sieve_mem_iff_true_unique pf1' pf2' hu').mpr hb)
| .succ n, x :: xs, true :: bs, pf1, pf2, .cons hnmem hu' =>
  Iff.intro
    (λ hf => by
      simp only [get, sieve] at *
      apply Iff.mp
      apply sieve_mem_iff_true_unique
      . apply Nat.lt_of_succ_lt_succ pf1
      . exact hu'
      . exact List.get_mem_cons_of_head_not_mem_getee hf hnmem)
    (λ hb => by
      simp only [get, sieve] at *
      apply Mem.tail
      apply Iff.mpr
      apply sieve_mem_iff_true_unique
      . apply Nat.lt_of_succ_lt_succ pf2
      . exact hu'
      . exact hb)
termination_by i xs bs pf1 pf2 hu => sizeOf xs + sizeOf bs

theorem List.mem_map_sieve_of_mem_map {f : α → β} {x : α}
  : ∀ {xs : List α} {bs : List Bool}, f x ∈ map f (sieve bs xs) → f x ∈ map f xs
| [], [], h => nomatch h
| x' :: xs, [], h => h
| x' :: xs, false :: bs, h => Mem.tail _ $ mem_map_sieve_of_mem_map h
| x' :: xs, true :: bs, h =>
  match mem_cons.mp h with
  | .inl heq => heq ▸ Mem.head _
  | .inr hmem => Mem.tail _ $ mem_map_sieve_of_mem_map hmem

theorem List.sieve_map_mem_iff_true_unique :
  ∀ {i} {xs : List α} {bs : List Bool} (pf1 pf2) (f : α → β)
    (hu : List.Unique (xs.map f)),
  (xs.map f).get ⟨i, length_map xs f ▸ pf1⟩ ∈ (bs.sieve xs).map f
  ↔ bs.get ⟨i, pf2⟩ = true := by
  intro i xs bs pf1 pf2 f hu
  apply Iff.intro
  . intro hf
    induction i generalizing xs bs with
    | zero =>
      match bs, xs, hu with
      | b :: bs, x :: xs, .cons hnmem hu =>
      cases b with
      | true => simp only [get, sieve] at *
      | false =>
        simp only [get, sieve] at *
        rw [Bool.false_eq_true]
        exact mt mem_map_sieve_of_mem_map hnmem hf
    | succ i ih =>
      match bs, xs, hu with
      | b :: bs, x :: xs, .cons hnmem hu =>
      cases b with
      | true =>
        simp only [get, sieve, map] at *
        apply ih
        . exact hu
        . apply get_mem_cons_of_head_not_mem_getee hf hnmem
        . apply Nat.lt_of_succ_lt_succ pf1
      | false =>
        simp only [get, sieve, map] at *
        apply ih
        . exact hu
        . exact hf
        . apply Nat.lt_of_succ_lt_succ pf1
  . intro hget
    induction i generalizing xs bs with
    | zero =>
      match bs, xs with
      | b :: bs, x :: xs =>
      cases b with
      | true => exact Mem.head _
      | false => simp [get, map] at hget
    | succ i ih =>
      match bs, xs, hu with
      | b :: bs, x :: xs, .cons hnmem hu =>
      cases b with
      | true =>
        simp only [get, sieve, map] at *
        apply Mem.tail
        apply ih
        . apply Nat.lt_of_succ_lt_succ pf1
        . exact hu
        . exact hget
      | false =>
        simp only [get, map, sieve] at *
        apply ih
        . apply Nat.lt_of_succ_lt_succ pf1
        . exact hu
        . exact hget
-- END lemmas for `selectColumns1_spec2`
