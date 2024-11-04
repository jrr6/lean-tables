/-!
Useful predicates on lists, including type-valued ones.
-/

-- List utilities
inductive List.All {α} (p : α → Prop) : List α → Prop
| vac      : All p []
| cons {x xs} : p x → All p xs → All p (x::xs)

inductive List.Unique {α} : List α → Prop
  | nil : List.Unique []
  | cons {x xs} : x ∉ xs → List.Unique xs → List.Unique (x :: xs)

inductive List.UniqueT {α} : List α → Type _
  | nil : List.UniqueT []
  | cons {x xs} : x ∉ xs → List.UniqueT xs → List.UniqueT (x :: xs)

inductive List.MemT {α : Type u} : α → List α → Type u
| hd (x : α) (xs : List α) : List.MemT x (x :: xs)
| tl (x : α) {y : α} {xs : List α} : List.MemT y xs → List.MemT y (x :: xs)

infix:65 " <+ " => List.Sublist

/-
Below we include "structural" theorems about these predicates that don't rely on
other list functions:
-/

theorem List.mem_of_memT {x : α} {xs : List α} : List.MemT x xs → List.Mem x xs
| .hd _ _ => .head _
| .tl _ h => .tail _ $ mem_of_memT h

theorem List.neq_of_mem_not_mem {x y : α} {xs : List α} :
  x ∈ xs → y ∉ xs → x ≠ y :=
  λ hxs => mt (λ heq => heq ▸ hxs)

theorem List.nil_singleton_of_all_eq_unique {xs : List α} :
  (∀ x ∈ xs, ∀ y ∈ xs, x = y) →
  Unique xs →
  xs = [] ∨ ∃ x, xs = [x] := by
  intro h hunique
  cases hunique with
  | nil => left; rfl
  | @cons x xs hmem huniq =>
    simp only [reduceCtorEq, cons.injEq, exists_and_right, exists_eq', true_and,
               false_or]
    cases xs with
    | nil => rfl
    | cons x' xs =>
      have : x' ≠ x := λ heq => (heq ▸ hmem) (.head _)
      have : x' = x := h x' (by simp only [mem_cons, or_true, true_or])
                         x (by simp only [mem_cons, true_or])
      contradiction
