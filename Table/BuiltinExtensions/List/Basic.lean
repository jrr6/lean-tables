import Table.BuiltinExtensions.List.Predicates
import Table.BuiltinExtensions.Numeric

/-!
Basic list functions and lemmas.
-/

def List.certifiedMap {α β} :
  (xs : List α) → ((x : α) → List.MemT x xs → β) → List β
| [], f => []
| x :: xs, f =>
  f x (MemT.hd x xs) :: certifiedMap xs (λ x' pf => f x' $ MemT.tl _ pf)

def List.prod {α β} : List α → List β → List (α × β)
| [], _ => []
| _, [] => []
| [x], y :: ys => (x, y) :: prod [x] ys
| x :: x' :: xs, ys =>
  have h₁ : Nat.succ 0 + length ys <
            Nat.succ (Nat.succ (length xs)) + length ys :=
    by apply Nat.add_lt_add_right
       apply Nat.succ_lt_succ $ Nat.succ_pos (length xs)
  have h₂ : Nat.succ (length xs) + length ys <
            Nat.succ (Nat.succ (length xs)) + length ys :=
    by apply Nat.add_lt_add_right
       apply Nat.succ_lt_succ
       apply Nat.lt.base
  prod [x] ys ++ prod (x' :: xs) ys
termination_by xs ys => xs.length + ys.length

def List.dropLastN {α} : Nat → List α → List α :=
  (λ n => reverse ∘ List.drop n ∘ reverse)

def List.toSingletons : List α → List (List α)
| [] => []
| x :: xs => [x] :: toSingletons xs

def List.somes : List (Option α) → List α
| [] => []
| none :: xs => somes xs
| some x :: xs => x :: somes xs

-- From a failed approach to `pivotTable` -- keeping around just in case
def List.depFoldr {κ : List α → Type _} :
  (xs : List α) →
  (∀ {xs : List α} (x : α), κ xs → κ (x :: xs)) →
  κ [] →
  κ xs
| [], f, z => z
| x :: xs, f, z => f x (depFoldr xs f z)

def List.memT_somes_of_memT {α} : ∀ {x : α} {xs : List (Option α)},
  List.MemT (some x) xs → List.MemT x xs.somes
| x, .(some x) :: xs, .hd .(some x) .(xs) => .hd x xs.somes
| x, (some y) :: xs, .tl .(some y) htl => .tl y $ memT_somes_of_memT htl
| x, none :: xs, .tl _ htl => @memT_somes_of_memT α x xs htl

def List.memT_map_of_memT {α β} (f : α → β) {x : α} :
  ∀ {xs : List α}, MemT x xs → MemT (f x) (map f xs)
| .(x) :: xs, .hd _ _ => .hd _ _
| _ :: xs, .tl _ htl => .tl _ <| memT_map_of_memT _ htl

def List.vEnumFrom (xs : List α) :
  (n : Nat) → (ys : List α) → (n + ys.length ≤ xs.length) →
  List (Fin xs.length × α)
| n, [], _ => []
| n, y :: ys, pf =>
  (⟨n, Nat.lt_of_lt_add_left pf⟩, y) ::
  vEnumFrom xs (n + 1) ys (Eq.subst (motive := (· ≤ length xs))
                  (Nat.add_right_comm n (length ys) 1) pf)

def List.verifiedEnum (xs : List α) : List (Fin xs.length × α) :=
  vEnumFrom xs 0 xs (Eq.subst (Nat.zero_add _) (Nat.le_refl _))

theorem List.length_vEnumFrom (xs : List α) :
  ∀ (ys : List α) (n : Nat) (pf : n + ys.length ≤ xs.length),
  (vEnumFrom xs n ys pf).length = ys.length
| [], _, _ => rfl
| y :: ys, n, pf => congrArg (·+1) (length_vEnumFrom xs ys (n + 1) _)

theorem List.length_verifiedEnum : ∀ (xs : List α),
  xs.verifiedEnum.length = xs.length
| [] => rfl
| x :: xs => congrArg (·+1) (length_vEnumFrom _ _ _ _)

theorem List.zip_length_eq_of_length_eq :
  ∀ (xs : List α) (ys : List β) (h : xs.length = ys.length),
    (List.zip xs ys).length = xs.length
| [], [], _ => rfl
| (x :: xs), (y :: ys), h =>
  have ih := zip_length_eq_of_length_eq xs ys (by
    simp only [List.length] at h
    apply Nat.succ.inj
    apply h
  )
  congrArg (λ x => x + 1) ih

theorem List.length_prod : ∀ (xs : List α) (ys : List β),
  List.length (List.prod xs ys) = xs.length * ys.length
| [], _ => by simp [prod, length]
| x :: xs, [] => by simp [prod, length]
| [x], y :: ys =>
  have ih := length_prod [x] ys
  by simp only [prod]
     unfold length  -- adding `length` to the simp above does bad things
     rw [ih]
     simp only [length]
     rw [Nat.one_mul, Nat.one_mul]
| x :: x' :: xs, y :: ys =>
  have h_term₁ : Nat.succ 0 + Nat.succ (length ys) <
                 Nat.succ (Nat.succ (length xs)) + Nat.succ (length ys) :=
    by apply Nat.add_lt_add_right
       apply Nat.succ_lt_succ $ Nat.succ_pos (length xs)
  have h_term₂ : Nat.succ (length xs) + Nat.succ (length ys) <
                 Nat.succ (Nat.succ (length xs)) + Nat.succ (length ys) :=
    by apply Nat.add_lt_add_right
       apply Nat.succ_lt_succ
       apply Nat.lt.base
  have ih₁ := length_prod [x] (y :: ys)
  have ih₂ := length_prod (x' :: xs) (y :: ys)
  by unfold prod
     simp only
     rw [List.length_append, ih₁, ih₂]
     simp only [length]
     rw [←Nat.add_mul, Nat.zero_add, Nat.add_comm 1]
termination_by xs ys => xs.length + ys.length

theorem List.length_take_of_lt :
  ∀ (n : Nat) (xs : List α) (h : n < xs.length),
    length (List.take n xs) = n
| _, [], h => by cases h
| 0, _, _ => by simp only [take, length]
| Nat.succ n, x :: xs, h =>
  have ih : length (take n xs) = n :=
    length_take_of_lt n xs (Nat.lt_of_succ_lt_succ h)
  by simp only [take, length]
     apply congrArg Nat.succ ih

theorem List.reverse_singleton (x : α) : reverse [x] = [x] := rfl

theorem List.map_map_append {α β γ δ : Type _} :
  ∀ (xs : List α) (ys : List β) (f : γ → δ) (g : α → γ) (h : β → γ),
  map f (map g xs ++ map h ys) = map (f ∘ g) xs ++ map (f ∘ h) ys
| [], ys, f, g, h => map_map f h ys
| x :: xs, ys, f, g, h => congrArg (f (g x) :: ·) (map_map_append xs ys f g h)

theorem List.sum_map_const {xs : List α} {f} (k : Nat) :
  (∀ x ∈ xs, f x = k) → (xs.map f).sum = k * xs.length := by
  intro heq
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [map, List.sum_cons]
    simp only [List.sum, List.length]
    specialize ih (λ y hy => heq y (.tail _ hy))
    rw [heq x (.head _), ← sum, ih, Nat.mul_add, Nat.add_comm, Nat.mul_one]

theorem List.length_flatMap {α β} {f : α → List β} {xs : List α} :
    List.length (xs.flatMap f) = (xs.map (List.length ∘ f)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap, List.map, List.flatten]
    cases h : f x with
    | nil =>
      rw [List.nil_append, Function.comp, h, List.length_nil, List.sum, foldr,
          Nat.zero_add]
      exact ih
    | cons y ys =>
      rw [List.length_append, Function.comp, h, List.sum]
      exact congrArg _ ih

theorem List.sublist_self : ∀ (xs : List α), Sublist xs xs
| [] => Sublist.slnil
| x :: xs => Sublist.cons₂ x (sublist_self xs)

theorem List.singleton_sublist_of_mem (y : α) :
  ∀ (xs : List α), y ∈ xs → Sublist [y] xs
| .(y) :: xs, List.Mem.head _ => Sublist.cons₂ y (nil_sublist xs)
| x :: xs, List.Mem.tail .(x) h =>
  Sublist.cons x (singleton_sublist_of_mem y xs h)

theorem List.map_sublist_of_sublist :
  (xs : List α) → (ys : List α) → (f : α → β) → Sublist xs ys →
    Sublist (xs.map f) (ys.map f)
| [], ys, f, h => nil_sublist (map f ys)
| xs, x :: ys, f, Sublist.cons _ h =>
  have ih := map_sublist_of_sublist xs ys f h
  Sublist.cons (f x) ih
| x :: xs, _ :: ys, f, Sublist.cons₂ _ h =>
  have ih := map_sublist_of_sublist xs ys f h
  Sublist.cons₂ (f x) ih

theorem List.get_mem_cons_of_head_not_mem_getee {y :α} {xs ys : List α} {i} :
  xs.get i ∈ y :: ys → y ∉ xs → xs.get i ∈ ys :=
  λ hget hnmem =>
  have hget_lem := get_mem xs i.val i.isLt
  have hneq_lem := neq_of_mem_not_mem hget_lem hnmem
  match mem_cons.mp hget with
  | .inr htl => htl
  | .inl heq => absurd heq hneq_lem

theorem List.mem_append_singleton : ∀ (x : α) (xs : List α), x ∈ xs ++ [x]
| x, [] => List.Mem.head _
| x, y :: ys => List.Mem.tail _ (mem_append_singleton x ys)

theorem List.mem_append_comm {v : α} {xs ys : List α} :
  v ∈ xs ++ ys ↔ v ∈ ys ++ xs :=
have flip : ∀ {as bs}, v ∈ as ++ bs → v ∈ bs ++ as :=
  (λ h => h |> mem_append.mp |> Or.comm.mp |> mem_append.mpr)
Iff.intro flip flip

-- Slightly over-generalized "loop invariant" (we could make the preservation
-- portion more specific, e.g., by providing `x ∈ xs` as an extra hypothesis)
theorem List.foldr_invariant :
  ∀ (p : β → Prop) (f : α → β → β) (z : β) (xs : List α),
  p z → (∀ x a, p a → p (f x a)) → p (List.foldr f z xs)
| _, _, _, [], h_init, _ => h_init
| p, f, z, x :: xs, h_init, h_pres =>
  h_pres x (foldr f z xs) (foldr_invariant p f z xs h_init h_pres)
