import Table.BuiltinExtensions.Logic
import Table.BuiltinExtensions.List.Basic
import Table.BuiltinExtensions.List.Predicates

/-!
Contains theorems about `List.filter` as well as implementation of and theorems
about filtering-like functions (`List.removeAllEq` and `List.unique` and its
variants).
-/

def List.removeAllEq [DecidableEq α] (xs ys : List α) : List α :=
  xs.filter (fun x => x ∉ ys)

-- TODO: should we use `List.eraseDups` instead? (Uses BEq instead of DEq.)
def List.uniqueAux {α} [DecidableEq α] : List α → List α → List α
| [], acc => acc.reverse
| x :: xs, acc => if x ∈ acc then uniqueAux xs acc else uniqueAux xs (x :: acc)

def List.unique {α} [inst : DecidableEq α] (xs : List α) := uniqueAux xs []

def List.unique' {α} [DecidableEq α] : List α → List α
| [] => []
| x :: xs =>
  have : length (filter (fun x_1 => !decide (x_1 = x)) xs) < length xs + 1 :=
    Nat.lt_succ_of_le (length_filter_le _ _)
  x :: unique' (xs.filter (· ≠ x))
termination_by xs => xs.length

def List.filterSpec (p : α → Bool) : List α → List α
| [] => []
| x :: xs => if p x then x :: filterSpec p xs else filterSpec p xs

theorem List.length_filterTR_le {α} (g : α → Bool) (xs : List α) :
    ∀ rs : List α, List.length (List.filterTR.loop g xs rs)
                   <= List.length xs + List.length rs :=
by
  induction xs with
  | nil =>
    intro rs
    simp only [filter, filterTR.loop]
    rw [List.length_reverse]
    simp only [length, Nat.zero_add]
    apply Nat.le.refl
  | cons x xs ih =>
    intro rs
    simp only [filter, filterTR.loop]
    cases (g x) with
    | true => simp only
              apply Nat.le_trans (ih (x::rs))
              simp only [length]
              rw [Nat.add_comm (length rs), Nat.add_assoc]
              apply Nat.le.refl
    | false => simp only [length]
               apply Nat.le_trans (ih rs)
               rw [Nat.add_comm (length xs) 1,
                   Nat.add_assoc 1,
                   Nat.add_comm 1,
                   Nat.add_one]
               apply Nat.le.step
               apply Nat.le.refl


theorem List.filter_eq_filterSpec : filter p xs = filterSpec p xs :=
by induction xs with
   | nil => simp [filter, filterSpec]
   | cons x xs ih =>
     simp only [filter, filterSpec]
     cases p x with
     | true => simp only [ite_true, ih]
     | false => simp only [Bool.false_eq_true, ite_false, ih]

theorem List.removeAll_singleton_hd_neq {α : Type _} [BEq α] :
  ∀ (x : α) (y : α) (xs : List α),
    ((x == y) = false) → removeAll (x :: xs) [y] = x :: removeAll xs [y] :=
by intros x y xs hneq
   simp only [removeAll, filter, elem, hneq, not]

theorem List.removeAll_singleton_hd_eq [DecidableEq α] :
  ∀ (x: α) (xs : List α), removeAll (x :: xs) [x] = removeAll xs [x] :=
by intros x xs
   simp [removeAll, filter, elem] -- previous filterAux too

theorem List.removeAllEq_singleton_hd_eq [DecidableEq α] :
  ∀ (x: α) (xs : List α), removeAllEq (x :: xs) [x] = removeAllEq xs [x] := by
  intros x xs
  simp [removeAllEq, filter, elem] -- previous filterAux too

theorem List.removeAllEq_singleton_hd_neq {α : Type _} [DecidableEq α] :
  ∀ (x : α) (y : α) (xs : List α),
    x ≠ y → removeAllEq (x :: xs) [y] = x :: removeAllEq xs [y] :=
by intro x y xs hneq
   simp only [removeAllEq, filter, mem_singleton, hneq, not_false_eq_true,
              decide_True, decide_not]

theorem List.removeAllEq_singleton_nonelem_eq {α} [DecidableEq α] :
  ∀ (xs : List α) (x : α), x ∉ xs → List.removeAllEq xs [x] = xs := by
  intro xs x hnmem
  induction xs with
  | nil => rfl
  | cons x' xs ih =>
    rw [removeAllEq_singleton_hd_neq]
    congr
    apply ih
    intro hneg
    apply hnmem
    apply Mem.tail
    . exact hneg
    . intro hneg'
      rw [hneg'] at hnmem
      apply hnmem
      apply Mem.head

-- BEGIN theorems originally used as helpers for `groupByKey`
theorem List.uniqueAux_acc_append_filter {α} [DecidableEq α] :
  ∀ (xs acc : List α),
  uniqueAux xs acc = reverse acc ++ unique (xs.filter (· ∉ acc))
| [], acc => by rw [filter, unique, uniqueAux, uniqueAux, reverse_nil,
                    append_nil]
| x :: xs, acc =>
  have hterm : length (filter (λ a => !decide (a ∈ acc)) xs)
                < Nat.succ (length xs) :=
    Nat.lt_of_le_of_lt (m := length xs) (length_filter_le _ _) (Nat.lt.base _)
  have hterm' : length xs < (length xs).succ := Nat.le.refl
  have ih₁ := uniqueAux_acc_append_filter xs acc
  have ih₂ := uniqueAux_acc_append_filter xs (x :: acc)
  have ih₃ :=
    uniqueAux_acc_append_filter (filter (λ a => decide ¬a ∈ acc) xs) [x]
  by
    simp only [uniqueAux, filter]  -- previously filterAux
    cases Decidable.em (x ∈ acc) with
    | inl hin =>
      simp only [hin, ite_true, not_true_eq_false, decide_False]
      rw [ih₁]
    | inr hout =>
      -- Case x is not already in the accumulator
      simp only [hout, ite_false, not_false_eq_true, decide_True]
      -- next line previously filterAux
      simp only [reverse_singleton, singleton_append, unique,
                 uniqueAux, List.not_mem_nil, ite_false]
      rw [ih₂]
      simp only [reverse_cons, append_assoc, singleton_append]
      apply congrArg
      simp only [unique]
      rw [ih₃]
      simp [unique]
termination_by xs ac => xs.length

theorem List.uniqueAux_acc_append {α} [DecidableEq α] (xs : List α)
  (acc : List α) (h : ∀ x, x ∈ xs → ¬ (x ∈ acc)) :
  uniqueAux xs acc = reverse acc ++ unique xs := by
  have : filter (fun a => decide ¬a ∈ acc) xs = xs := by
    induction xs with
    | nil => simp [filter]
    | cons x xs ih =>
      simp only [filter]
      have : decide (¬x ∈ acc) = true := by simp [h x (Mem.head _)]
      rw [this]
      simp only
      rw [ih]
      . intros x hx
        apply h x (Mem.tail _ hx)
  rw [uniqueAux_acc_append_filter]
  cases xs with
  | nil => apply congrArg; simp [filter]
  | cons x xs =>
    apply congrArg
    rw [this]

theorem List.length_uniqueAux {α} [DecidableEq α]
  (xs : List α) (acc : List α) (h : ∀ x, x ∈ xs → ¬ (x ∈ acc)) :
  length (uniqueAux xs acc) = length (unique xs) + length acc := by
  rw [uniqueAux_acc_append _ _ h, length_append, length_reverse, Nat.add_comm]

def List.memT_filter_false_of_memT {α} {x : α} {p : α → Bool} :
  ∀ {xs : List α}, MemT x xs → p x = true → MemT x (filter p xs)
| _, .hd _ _, heq => by
  simp only [filter, heq]
  apply MemT.hd
| x' :: xs, .tl _ htl, heq =>
  if h : p x'
  then by
    simp only [filter, h]
    apply MemT.tl
    apply memT_filter_false_of_memT htl heq
  else by
    simp only [filter, h]
    apply memT_filter_false_of_memT htl heq

-- TODO: if we want `pivotWider` to run in a reasonable amount of time, probably
-- want to write this as a proof term
def List.memT_unique_of_memT {α} [DecidableEq α]
  : ∀ {x : α} {xs : List α}, MemT x xs → MemT x xs.unique
| x, .(x) :: xs, .hd _ _ => by
  unfold unique
  unfold uniqueAux
  simp only [not_mem_nil, ite_false]
  rw [uniqueAux_acc_append_filter]
  apply MemT.hd _ _
| x, y :: xs, .tl .(y) htl =>
  -- TODO: we keep using this...probably make it a separate simp lemma
  have hterm : length (filter (λ a => !decide (a = y)) xs) < length xs + 1 :=
    Nat.lt_of_le_of_lt (m := length xs) (length_filter_le _ _) (Nat.lt.base _)
  by
  simp only [unique, uniqueAux, not_mem_nil, ite_false]
  simp only [uniqueAux_acc_append_filter]
  simp only [reverse_singleton, singleton_append]
  apply Decidable.byCases (p := x = y)
  . intro heq
    rw [←heq]
    apply MemT.hd
  . intro hneq
    apply MemT.tl
    apply memT_unique_of_memT
    apply memT_filter_false_of_memT
    exact htl
    have hnin : ¬ x ∈ [y] := by
      intro hneg
      cases hneg <;>
      contradiction
    simp only [hnin, not_false_eq_true, decide_True]
termination_by x xs hmem => xs.length
-- END `groupByKey

-- BEGIN `leftJoin` spec 4 helpers
theorem List.mem_filter_of_mem_filter_imp {p q : α → Bool} {y : α}
  {xs : List α} :
  (∀ x, p x → q x) → y ∈ xs.filter p → y ∈ xs.filter q := by
  intro hpq hp
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    cases Decidable.em (p x) with
    | inl htrue =>
      have hq := hpq x htrue
      simp only [htrue, List.filter_cons_of_pos, List.mem_cons, hq] at hp ⊢
      cases hp with
      | inl heq => exact .inl heq
      | inr htl => exact .inr (ih htl)
    | inr hfalse =>
      simp only [List.filter, hfalse] at hp
      cases Decidable.em (q x) with
      | inl hqtrue =>
        simp only [List.filter, hqtrue]
        apply List.Mem.tail
        apply ih hp
      | inr hqfalse =>
        simp only [List.filter, hqfalse]
        exact ih hp

theorem List.not_mem_filter_neq [DecidableEq α] (y : α) : ∀ (xs : List α),
  y ∉ filter (· ≠ y) xs
  | x :: xs, h => by
    simp only [filter] at h
    cases hdec : decide (x = y) with
    | true =>
      simp only [ne_eq, decide_not, hdec, Bool.not_true] at h
      simp only [←decide_not, ←ne_eq] at h
      exact not_mem_filter_neq _ _ h
    | false =>
      simp only [ne_eq, decide_not, hdec, Bool.not_false, mem_cons] at h
      cases h with
      | inl heq => cases heq; simp only [decide_True, Bool.true_eq_false] at hdec
      | inr hmem =>
        simp only [←decide_not, ←ne_eq] at hmem
        exact not_mem_filter_neq _ _ hmem

theorem List.filter_mem_pred_true :
  ∀ (xs : List α) (pred : α → Bool), ∀ r ∈ xs.filter pred, pred r = true
  | [], pred => λ r hr => nomatch hr
  | x :: xs, pred =>
    if h : pred x
    then by
      intro r hr
      simp only [filter, h] at hr
      cases hr with
      | head => exact h
      | tail _ htl =>
        apply filter_mem_pred_true _ _ _ htl
    else λ r hr => by
      simp only [filter, h] at hr
      apply filter_mem_pred_true _ _ _ hr


theorem List.unique_sublist {xs ys : List α} :
    Unique ys → xs <+ ys → Unique xs := by
  intro hunique hsubl
  induction hsubl with
  | slnil => exact .nil
  | cons x hsubl' ih =>
    apply ih
    cases hunique
    repeat assumption
  | cons₂ x hsubl' ih =>
    constructor
    . cases hunique
      intro hneg
      have := Sublist.mem hneg hsubl'
      contradiction
    . apply ih
      cases hunique
      repeat assumption

unseal List.unique' in
theorem List.unique_eq_unique' [DecidableEq α] : ∀ (xs : List α),
  unique xs = unique' xs
  | [] => rfl
  | x :: xs =>
  by
    simp only [unique, unique', uniqueAux, not_mem_nil, ite_false]
    rw [uniqueAux_acc_append_filter, reverse_singleton, singleton_append]
    apply congrArg
    simp only [mem_cons, not_mem_nil, or_false, decide_not, ne_eq]
    have : length (filter (fun x_1 => !decide (x_1 = x)) xs) < 1 + length xs :=
    by
      apply Nat.lt_of_le_of_lt
      apply length_filter_le
      rw [Nat.add_comm]
      apply Nat.lt.base
    apply unique_eq_unique'
termination_by xs => xs.length

unseal List.unique' in
theorem List.unique'_sublist [DecidableEq α] : ∀ (xs : List α),
  List.unique' xs <+ xs
  | [] => .slnil
  | x :: xs =>
    have : (filter (fun x_1 => !decide (x_1 = x)) xs).length < xs.length + 1 :=
      Nat.lt_succ_of_le (length_filter_le _ _)
    Sublist.cons₂ _ $
      Sublist.trans (List.unique'_sublist _) (List.filter_sublist _)
termination_by xs => xs.length

unseal List.unique' in
theorem List.unique'_Unique [DecidableEq α] : ∀ (xs : List α),
  Unique xs.unique'
  | [] => .nil
  | x :: xs =>
    have : (filter (fun x_1 => !decide (x_1 = x)) xs).length < xs.length + 1 :=
      Nat.lt_succ_of_le (length_filter_le _ _)
    .cons (mt (Sublist.mem.swap (unique'_sublist _)) (not_mem_filter_neq x xs))
          (unique'_Unique _)
termination_by xs => xs.length
-- END `leftJoin` spec 4 helpers

theorem List.length_uniqueAux_le [DecidableEq α] (xs : List α) :
  ∀ as, length (uniqueAux xs as) ≤ length xs + length as := by
  induction xs with
  | nil => simp [uniqueAux]
  | cons x xs ih =>
    intros as
    cases Decidable.em (x ∈ as) with
    | inl h =>
      simp only [length, uniqueAux, h, ite_true]
      apply Nat.le_trans
      apply ih
      rw [Nat.add_assoc, Nat.add_comm 1, ←Nat.add_assoc]
      apply Nat.le_step
      simp
    | inr h =>
      simp only [length, uniqueAux, h, ite_false]
      apply Nat.le_trans
      apply ih
      simp only [length]
      rw [Nat.add_comm _ 1, Nat.add_assoc]
      apply Nat.le_refl

theorem List.length_unique_le [DecidableEq α] (xs : List α) :
  length (unique xs) ≤ length xs :=
List.length_uniqueAux_le xs []
