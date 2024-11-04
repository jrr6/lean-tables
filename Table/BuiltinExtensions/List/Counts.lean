import Table.BuiltinExtensions.List.Basic
import Table.BuiltinExtensions.List.Filtering

/-!
`List.counts`, helper functions, and associated theorems.
TODO: these proofs could probably be cleaned up a lot.
-/

def List.incrCounts {α} [DecidableEq α] :
  List (α × Nat) → α → List (α × Nat)
| [], v => [(v, 1)]
| (t, n) :: rs, v =>
  if t = v then (t, n + 1) :: rs else (t, n) :: incrCounts rs v

def List.counts {α} [DecidableEq α] (xs : List α) : List (α × Nat) :=
  xs.foldl (λ acc v => incrCounts acc v) []

theorem List.map_fst_incrCounts_eq_map_fst [DecidableEq α] (x : α) :
  ∀ (as : List (α × Nat)) (h : x ∈ map Prod.fst as),
  map Prod.fst (incrCounts as x) = map Prod.fst as
| (.(x), _) :: as, List.Mem.head _ => by simp only [map, incrCounts]
| a :: as, List.Mem.tail _ h' =>
  have ih := map_fst_incrCounts_eq_map_fst x as h'
  match Decidable.em (a.1 = x) with
  | .inl heq => by simp only [map, incrCounts, heq, ite_true, map]
  | .inr hneq => by
      simp only [hneq, ite_false, map, incrCounts]
      exact congrArg _ ih

theorem List.map_fst_incrCounts_eq_cons_fst [DecidableEq α] (x : α) :
  ∀ (as : List (α × Nat)) (h : x ∉ map Prod.fst as),
  map Prod.fst (incrCounts as x) = map Prod.fst as ++ [x] := by
  intros as h
  induction as with
  | nil =>
    simp only [incrCounts, map, HAppend.hAppend, Append.append, List.append]
  | cons a as ih =>
    simp only [map, incrCounts]
    cases Decidable.em (a.1 = x) with
    | inl heq =>
      apply absurd h
      apply not_not
      simp only [map, heq]
      apply List.Mem.head
    | inr hneq =>
      simp only [hneq, ite_false, map]
      apply congrArg
      apply ih
      . intros hneg
        apply h
        apply List.Mem.tail _ hneg

theorem List.length_uniqueAux_congr_append_cons_acc [DecidableEq α]
  (x y : α) (as xs : List α) (cs : List α) :
  length (uniqueAux xs (cs ++ x :: (as ++ [y]))) =
  length (uniqueAux xs (cs ++ y :: x :: as)) := by
  induction xs generalizing cs with
  | nil =>
    simp [uniqueAux]
    rw [Nat.add_assoc,
        Nat.add_comm (length cs),
        ←Nat.add_assoc]
  | cons z zs ih =>
    have rearrange_mem :
      (z ∈ cs ++ x :: (as ++ [y])) ↔ (z ∈ cs ++ y :: x :: as) := by
      apply Iff.intro
      . intros h
        cases mem_append.mp h with
        | inl hcs => exact mem_append_of_mem_left _ hcs
        | inr hcons =>
          apply mem_append_of_mem_right
          rw [←cons_append] at hcons
          cases mem_append.mp hcons with
          | inl hxas => exact List.Mem.tail _ hxas
          | inr hy =>
            cases hy with
            | tail _ _ => contradiction
            | head _ => exact List.Mem.head _
      . intros h
        cases mem_append.mp h with
        | inl hcs => exact mem_append_of_mem_left _ hcs
        | inr hcons =>
          apply mem_append_of_mem_right
          cases hcons with
          | head _ =>
            apply List.Mem.tail
            apply mem_append_of_mem_right
            apply List.mem_singleton.mpr rfl
          | tail _ hcons' =>
            rw [←cons_append]
            exact mem_append_of_mem_left _ hcons'

    simp only [uniqueAux]
    cases Decidable.em (z ∈ cs ++ x :: (as ++ [y])) with
    | inl hin =>
      simp only [hin, rearrange_mem.mp hin, ite_true]
      apply ih
    | inr hout =>
      simp only [hout, rearrange_mem.not_iff_not_of_iff.mp hout, ite_false]
      have rw_help (stuff) : (z :: (cs ++ stuff)) = ((z :: cs) ++ stuff) := rfl
      rw [rw_help, rw_help]
      apply ih

theorem List.length_counts_aux [DecidableEq α]
  (xs : List α) (acc : List (α × Nat)) :
  List.length (foldl (λ acc v => incrCounts acc v) acc xs) =
  List.length (uniqueAux xs (acc.map Prod.fst)) := by
  induction xs generalizing acc with
  | nil => simp [foldl, uniqueAux]
  | cons x xs ih =>
    simp only [uniqueAux, foldl]
    cases acc with
    | nil =>
      simp only [incrCounts, map, List.not_mem_nil, ite_false]
      apply ih
    | cons a as =>
      simp only [incrCounts]
      cases Decidable.em (a.1 = x) with
      | inl htrue =>
        simp only [htrue, ite_true, incrCounts, map]
        rw [if_pos]
        . apply ih
        . exact List.Mem.head _
      | inr hfalse =>
        simp only [hfalse, ite_false, incrCounts, map]
        rw [ih]
        cases Decidable.em (x ∈ map Prod.fst as) with
        | inl hin =>
          have : x ∈ a.1 :: map Prod.fst as := List.Mem.tail _ hin
          simp only [this, ite_true, map, uniqueAux]
          apply congrArg
          apply congrArg
          apply congrArg
          exact map_fst_incrCounts_eq_map_fst x as hin
        | inr hout =>
          have : ¬ (x ∈ a.1 :: map Prod.fst as) := by
            intros hneg; cases hneg; repeat contradiction
          simp only [this, ite_false, map]
          rw [map_fst_incrCounts_eq_cons_fst _ _ hout]
          apply List.length_uniqueAux_congr_append_cons_acc _ _ _ _ []

theorem List.length_counts [DecidableEq α] (xs : List α) :
  xs.counts.length = xs.unique.length :=
  length_counts_aux xs []
