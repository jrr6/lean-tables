-- Variant on orElse that's useful for de-option-ifying cell values
def Option.orDefault {α} [Inhabited α] : Option α → α
| some x => x
| none => default

-- Type-level negation for use with type-valued predicates
def NotT (α : Type _) := α → Empty

-- List utilities
inductive List.All {α} (p : α → Prop) : List α → Prop
| vac      : All p []
| cons {x xs} : p x → All p xs → All p (x::xs)

inductive List.Sublist {α} : List α → List α → Prop
| nil : Sublist [] []
| cons (xs ys x) : Sublist xs ys → Sublist xs (x :: ys)
| cons2 (xs ys x) : Sublist xs ys → Sublist (x :: xs) (x :: ys)

inductive List.Unique {α} : List α → Prop
  | nil : List.Unique []
  | cons {x xs} : x ∉ xs → List.Unique xs → List.Unique (x :: xs)

inductive List.UniqueT {α} : List α → Type _
  | nil : List.UniqueT []
  | cons {x xs} : x ∉ xs → List.UniqueT xs → List.UniqueT (x :: xs)

inductive List.MemT {α : Type u} : α → List α → Type u
| hd (x : α) (xs : List α) : List.MemT x (x :: xs)
| tl (x : α) {y : α} {xs : List α} : List.MemT y xs → List.MemT y (x :: xs)

def List.mem_of_memT {x : α} {xs : List α} : List.MemT x xs → List.Mem x xs
| .hd _ _ => .head _
| .tl _ h => .tail _ $ mem_of_memT h

def List.certifiedMap {α β} :
  (xs : List α) → ((x : α) → List.MemT x xs → β) → List β
| [], f => []
| x :: xs, f =>
  f x (MemT.hd x xs) :: certifiedMap xs (λ x' pf => f x' $ MemT.tl _ pf)

infix:65 " <+ " => List.Sublist

instance (k : Nat) : OfNat (Fin k.succ) n :=
  if h : n < k.succ
  then ⟨n, h⟩
  else ⟨0, Nat.zero_lt_succ k⟩

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

def List.sieve {α} : List Bool → List α → List α
| [], xs => xs
| _, [] => []
| true :: bs, x :: xs => x :: sieve bs xs
| false :: bs, _ :: xs => sieve bs xs

def List.flatten {α} : List (List α) → List α
| [] => []
| [] :: ys => flatten ys
| (x :: xs) :: ys => x :: flatten (xs :: ys)

def List.sum : List Nat → Nat
| [] => 0
| x :: xs => x + sum xs

def List.toSingletons : List α → List (List α)
| [] => []
| x :: xs => [x] :: toSingletons xs

def List.somes : List (Option α) → List α
| [] => []
| none :: xs => somes xs
| some x :: xs => x :: somes xs

def List.memT_somes_of_memT {α} : ∀ {x : α} {xs : List (Option α)},
  List.MemT (some x) xs → List.MemT x xs.somes
| x, .(some x) :: xs, .hd .(some x) .(xs) => .hd x xs.somes
| x, (some y) :: xs, .tl .(some y) htl => .tl y $ memT_somes_of_memT htl
| x, none :: xs, .tl _ htl => @memT_somes_of_memT α x xs htl

def Injective (f : α → β) := ∀ a a', f a = f a' → a = a'

def List.memT_map_of_memT {α β} (f : α → β) {x : α} :
  ∀ {xs : List α}, MemT x xs → MemT (f x) (map f xs)
| .(x) :: xs, .hd _ _ => .hd _ _
| _ :: xs, .tl _ htl => .tl _ <| memT_map_of_memT _ htl

-- Basic fact about equality used in `removeHeaderHasCol'`
theorem Eq.cast_distrib_fun {α} {x y : α} {σ τ : α → Type _}
    (h : x = y) (f : ∀ {z}, τ z → σ z) (t : τ x) :
    h ▸ (f t) = f (h ▸ t) :=
  h.rec (Eq.refl (f t))

-- Based on `buffer.lt_aux_1` in Lean 3's `lib/lean/library/data/buffer.lean`
theorem Nat.lt_of_lt_add_left {a b c : Nat} (h : a + c < b) : a < b :=
Nat.lt_of_le_of_lt (Nat.le_add_right a c) h

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

theorem List.filter_length {α} (g : α → Bool) (xs : List α) :
    List.length (List.filter g xs) <= List.length xs :=
by induction xs with
   | nil => simp [length]
   | cons x xs ih =>
      simp only [filter]
      cases (g x) with
      | true =>
        simp only
        apply Nat.succ_le_succ
        exact ih
      | false =>
        simp only
        apply Nat.le.step
        exact ih

-- Temporary merge sort algorithm until the full sorting library gets ported

def List.split {α} : List α → List α × List α
| [] => ([], [])
| [x] => ([x], [])
| x₁ :: x₂ :: xs =>
  let (ys, zs) := split xs;
  (x₁ :: ys, x₂ :: zs)

theorem List.split_length_fst' {α} :
    ∀ (xs : List α), (split xs).fst.length ≤ xs.length
| [] => Nat.le.refl
| [x] => Nat.le.refl
| x₁ :: x₂ :: xs =>
  have ih := split_length_fst' xs;
  by simp only [split, length]
     apply Nat.le.step
     apply Nat.succ_le_succ
     apply ih

theorem List.split_length_fst {α} :
    ∀ (xs : List α), xs.length ≤ 1 ∨ (split xs).fst.length < xs.length
| [] => .inl (Nat.zero_le _)
| [x] => .inl Nat.le.refl
| [x, y] => .inr (Nat.lt.base _)
| [x, y, z] => .inr (Nat.lt.base _)
| x₁ :: x₂ :: x :: x' :: xs =>
  have ih := split_length_fst (x :: x' :: xs);
  by simp only [split, length]
     apply Or.intro_right
     apply Nat.succ_lt_succ
     simp only [length, Nat.add] at ih
     apply Nat.lt.step
     cases ih with
     | inl _ => contradiction
     | inr h => apply h

theorem List.split_length_snd {α} :
    ∀ (xs : List α), xs = [] ∨ (split xs).snd.length < xs.length
| [] => .inl rfl
| [x] => .inr (Nat.lt.base _)
| [x, y] => .inr (Nat.lt.base _)
| x₁ :: x₂ :: x :: xs =>
  have ih := split_length_snd (x :: xs);
  by simp only [split, length]
     apply Or.intro_right
     apply Nat.succ_lt_succ
     simp at ih
     apply Nat.lt.step
     apply ih

theorem List.split_length_snd' {α} :
    ∀ (xs : List α), (split xs).snd.length ≤ xs.length
| [] => Nat.le.refl
| [x] => Nat.le.step Nat.le.refl
| x₁ :: x₂ :: xs =>
  have ih := split_length_snd' xs;
  by simp only [split, length]
     apply Nat.le.step
     apply Nat.succ_le_succ
     apply ih

def List.mergeWith {α} : (α → α → Ordering) → List α × List α → List α
| _, ([], ys) => ys
| _, (xs, []) => xs
| cmp, (x :: xs, y :: ys) =>
  have h1 : ys.length + (x :: xs).length <
            (x :: xs).length + (y :: ys).length :=
    by simp only [length]
       rw [Nat.add_comm]
       apply Nat.lt.base
  have h2 : (y :: ys).length + xs.length <
            (x :: xs).length + (y :: ys).length :=
    by simp only [length]
       rw [Nat.add_comm (length xs + 1)]
       apply Nat.lt.base
  match cmp x y with
  | Ordering.gt => y :: mergeWith cmp (ys, x :: xs)
  | _ => x :: mergeWith cmp (y :: ys, xs)
termination_by cmp prd => prd.fst.length + prd.snd.length

def List.mergeSortWith {α} : (α → α → Ordering) → List α → List α
| _, [] => []
| _, [x] => [x]
| cmp, x₁ :: x₂ :: xs =>
  have _ : (split (x₁::x₂::xs)).fst.length < (x₁::x₂::xs).length :=
    match xs with
    | [] => Nat.lt.base _
    | [xs] => Nat.lt.base _
    | y :: y' :: ys =>
      match split_length_fst (y :: y' :: ys) with
      | Or.inl _ => by contradiction
      | Or.inr h =>
        by simp only [length] at *
           apply Nat.lt.step
           apply Nat.succ_lt_succ
           exact h

   have _ : (split (x₁::x₂::xs)).snd.length < (x₁::x₂::xs).length :=
    match xs with
    | [] => Nat.lt.base _
    | [xs] => Nat.lt.step (Nat.lt.base _)
    | y :: y' :: ys =>
      match split_length_snd (y :: y' :: ys) with
      | Or.inl _ => by contradiction
      | Or.inr h =>
        by simp only [length] at *
           apply Nat.lt.step
           apply Nat.succ_lt_succ
           exact h

  let xs_split := split (x₁ :: x₂ :: xs)
  mergeWith cmp (mergeSortWith cmp (xs_split.fst),
                  mergeSortWith cmp (xs_split.snd))
termination_by cmp xs => xs.length

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

theorem List.length_take :
  ∀ (n : Nat) (xs : List α) (h : n < xs.length),
    length (List.take n xs) = n
| _, [], h => by cases h
| 0, _, _ => by simp only [take, length]
| Nat.succ n, x :: xs, h =>
  have ih : length (take n xs) = n :=
    length_take n xs (Nat.lt_of_succ_lt_succ h)
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
    simp only [List.sum, List.length]
    specialize ih (λ y hy => heq y (.tail _ hy))
    rw [heq x (.head _), ih, Nat.mul_add, Nat.add_comm, Nat.mul_one]

theorem List.length_bind {α β} {f : α → List β} {xs : List α} :
    List.length (xs.bind f) = (xs.map (List.length ∘ f)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.bind, List.map, List.join]
    cases h : f x with
    | nil =>
      rw [List.nil_append, Function.comp, h, List.length_nil, List.sum,
          Nat.zero_add]
      exact ih
    | cons y ys =>
      rw [List.length_append, Function.comp, h, List.sum]
      exact congrArg _ ih

theorem List.sublist_self : ∀ (xs : List α), Sublist xs xs
| [] => Sublist.nil
| x :: xs => Sublist.cons2 xs xs x (sublist_self xs)

theorem List.nil_sublist : ∀ (xs : List α), Sublist [] xs
| [] => Sublist.nil
| x :: xs => Sublist.cons [] xs x $ nil_sublist xs

theorem List.singleton_sublist_of_mem (y : α) :
  ∀ (xs : List α), y ∈ xs → Sublist [y] xs
| .(y) :: xs, List.Mem.head _ => Sublist.cons2 [] xs y (nil_sublist xs)
| x :: xs, List.Mem.tail .(x) h =>
  Sublist.cons _ xs x (singleton_sublist_of_mem y xs h)

-- Adapted from ll. 953-962 of `data/list/basic.lean` of Mathlib 3
theorem List.Sublist.trans {l₁ l₂ l₃ : List α}
  (h₁ : Sublist l₁ l₂) (h₂ : Sublist l₂ l₃) : Sublist l₁ l₃ :=
Sublist.recOn
  (motive := λ l₂ l₃ h₂ => (l₁ : List α) → (Sublist l₁ l₂) → Sublist l₁ l₃)
  h₂
  (λ _ s => s)
  (λ l₂ l₃ a h₂ IH l₁ h₁ => Sublist.cons _ _ _ (IH l₁ h₁))
  (λ l₂ l₃ a h₂ IH l₁ h₁ =>
    Sublist.casesOn
      (motive := λl₁ l₂' _ => l₂' = a :: l₂ → Sublist l₁ (a :: l₃))
      h₁
      (λ_ => nil_sublist _)
      (λl₁ l₂' a' h₁' e =>
        match a', l₂', e, h₁' with
          | _, _, rfl, h₁ => Sublist.cons _ _ _ (IH _ h₁))
      (λl₁ l₂' a' h₁' e => match a', l₂', e, h₁' with
        | _, _, rfl, h₁ => Sublist.cons2 _ _ _ (IH _ h₁)) rfl)
  l₁ h₁

theorem List.sieve_sublist : (bs : List Bool) → (xs : List α) →
  Sublist (List.sieve bs xs) xs
| [], [] => Sublist.nil
| [], x :: xs => List.sublist_self (x :: xs)
| true :: bs, [] => Sublist.nil
| false :: bs, [] => Sublist.nil
| true :: bs, x :: xs => Sublist.cons2 (sieve bs xs) xs x (sieve_sublist bs xs)
| false :: bs, x :: xs => Sublist.cons (sieve bs xs) xs x (sieve_sublist bs xs)

theorem List.map_sublist_of_sublist :
  (xs : List α) → (ys : List α) → (f : α → β) → Sublist xs ys →
    Sublist (xs.map f) (ys.map f)
| [], ys, f, h => nil_sublist (map f ys)
| xs, x :: ys, f, Sublist.cons _ _ _ h =>
  have ih := map_sublist_of_sublist xs ys f h
  Sublist.cons (map f xs) (map f ys) (f x) ih
| x :: xs, _ :: ys, f, Sublist.cons2 _ _ _ h =>
  have ih := map_sublist_of_sublist xs ys f h
  Sublist.cons2 (map f xs) (map f ys) (f x) ih

def List.filterSpec (p : α → Bool) : List α → List α
| [] => []
| x :: xs => if p x then x :: filterSpec p xs else filterSpec p xs

theorem List.filter_eq_filterSpec : filter p xs = filterSpec p xs :=
by induction xs with
   | nil => simp [filter, filterSpec]
   | cons x xs ih =>
     simp only [filter, filterSpec]
     cases p x with
     | true => simp only [ite_true, ih]
     | false => simp only [ite_false, ih]

theorem List.reverseAux_spec (xs acc : List α) :
  reverseAux xs acc = reverse xs ++ acc := by
  induction xs generalizing acc with
  | nil => simp [reverse, reverseAux]
  | cons x xs ih =>
    simp only [reverse, reverseAux]
    simp only [ih]
    rw [←singleton_append, append_assoc]

def List.reverseSpec : List α → List α
| [] => []
| x :: xs => reverseSpec xs ++ [x]

theorem List.reverse_eq_reverseSpec (xs : List α) :
  reverse xs = reverseSpec xs := by
  induction xs with
  | nil => simp [reverse, reverseAux, reverseSpec]
  | cons x xs ih =>
    simp only [reverse, reverseSpec, reverseAux]
    rw [reverseAux_spec]
    exact congrArg (· ++ [x]) ih

def List.removeAllEq [DecidableEq α] (xs ys : List α) : List α :=
  xs.filter (fun x => x ∉ ys)

theorem List.removeAll_singleton_hd_neq {α : Type _} [BEq α] :
  ∀ (x : α) (y : α) (xs : List α),
    ((x == y) = false) → removeAll (x :: xs) [y] = x :: removeAll xs [y] :=
by intros x y xs hneq
   simp only [removeAll, filter, notElem, elem, hneq, not]

theorem List.removeAll_singleton_hd_eq [DecidableEq α] :
  ∀ (x: α) (xs : List α), removeAll (x :: xs) [x] = removeAll xs [x] :=
by intros x xs
   simp [removeAll, filter, notElem, elem] -- previous filterAux too

theorem List.mem_singleton_iff (x y : α) : x ∈ [y] ↔ x = y := by
  apply Iff.intro
  . intro hmem
    cases hmem
    . rfl
    . contradiction
  . intro heq
    rw [heq]
    constructor

theorem decide_true : decide True = true := rfl

theorem List.nil_singleton_of_all_eq_unique {xs : List α} :
  (∀ x ∈ xs, ∀ y ∈ xs, x = y) →
  Unique xs →
  xs = [] ∨ ∃ x, xs = [x] := by
  intro h hunique
  cases hunique with
  | nil => left; rfl
  | @cons x xs hmem huniq =>
    simp only [cons.injEq, exists_and_right, exists_eq', true_and, false_or]
    cases xs with
    | nil => rfl
    | cons x' xs =>
      have : x' ≠ x := λ heq => (heq ▸ hmem) (.head _)
      have : x' = x := h x' (by simp only [mem_cons, or_true, true_or])
                         x (by simp only [mem_cons, true_or])
      contradiction

theorem List.removeAllEq_singleton_hd_eq [DecidableEq α] :
  ∀ (x: α) (xs : List α), removeAllEq (x :: xs) [x] = removeAllEq xs [x] := by
  intros x xs
  simp [removeAllEq, filter, notElem, elem] -- previous filterAux too

theorem List.removeAllEq_singleton_hd_neq {α : Type _} [DecidableEq α] :
  ∀ (x : α) (y : α) (xs : List α),
    x ≠ y → removeAllEq (x :: xs) [y] = x :: removeAllEq xs [y] :=
by intro x y xs hneq
   simp only [removeAllEq, filter, notElem, elem, hneq, not]
   cases Decidable.em (x ∈ [y]) with
   | inl hmem =>
      rw [mem_singleton_iff] at hmem
      contradiction
   | inr hnmem =>
      simp [hnmem, decide_true, not_false_eq_true]

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

theorem List.length_mergeWith : ∀ (cmp : α → α → Ordering)
                                   (xs ys : List α),
  length (mergeWith cmp (xs, ys)) = length xs + length ys
| cmp, [], ys => by simp only [mergeWith, length, Nat.zero_add]
| cmp, x :: xs, [] => rfl
| cmp, x :: xs, y :: ys =>
have ih₁ := length_mergeWith cmp (y :: ys) xs
have ih₂ := length_mergeWith cmp ys (x :: xs)
by simp only [mergeWith]
   cases cmp x y with
   | lt =>
     simp only
     have h₁ : length (x :: mergeWith cmp (y :: ys, xs)) =
               length (mergeWith cmp (y :: ys, xs)) + 1 := rfl
     have h₂ : length (x :: xs) = length xs + 1 := rfl
     rw [h₁, h₂, Nat.add_comm (length xs + 1), ←Nat.add_assoc]
     apply congrArg (λ x => x + 1)
     exact ih₁
   | eq =>
     simp only
     have h₁ : length (x :: mergeWith cmp (y :: ys, xs)) =
               length (mergeWith cmp (y :: ys, xs)) + 1 := rfl
     have h₂ : length (x :: xs) = length xs + 1 := rfl
     rw [h₁, h₂, Nat.add_comm (length xs + 1), ←Nat.add_assoc]
     apply congrArg (λ x => x + 1)
     exact ih₁
   | gt =>
     simp only [length]
     simp only [length] at ih₂
     rw [←Nat.add_assoc]
     apply congrArg (λ x => x + 1)
     rw [Nat.add_comm]
     exact ih₂
termination_by length_mergeWith xs ys => xs.length + ys.length

theorem List.length_split : ∀ (xs : List α),
  length ((split xs).1) + length ((split xs).2) = length xs
| [] => rfl
| [x] => rfl
| x :: y :: xs =>
  have ih := length_split xs
  by simp only [split, length]
     rw [Nat.add_assoc (length xs),
         Nat.add_assoc (length (split xs).1),
         Nat.add_comm 1,
         Nat.add_assoc (length (split xs).2),
         ←Nat.add_assoc (length (split xs).1)]
     apply congrArg (λ x => x + (1 + 1))
     exact ih

theorem List.length_mergeSortWith : ∀ (cmp : α → α → Ordering) (xs : List α),
  length (mergeSortWith cmp xs) = length xs
| _, [] => rfl
| _, [x] => rfl
| cmp, x :: y :: xs =>
  have term₁ : Nat.succ (length (split xs).fst) <
               Nat.succ (Nat.succ (length xs)) :=
    Nat.succ_le_succ (Nat.succ_le_succ $ split_length_fst' xs)
  have term₂ : Nat.succ (length (split xs).snd) <
               Nat.succ (Nat.succ (length xs)) :=
    Nat.succ_le_succ (Nat.succ_le_succ $ split_length_snd' xs)
  have ih₁ := length_mergeSortWith cmp (x :: (split xs).1)
  have ih₂ := length_mergeSortWith cmp (y :: (split xs).2)
  -- TODO: we shouldn't need to do a "step" of length_split again here
  by simp only [mergeSortWith, mergeWith, split, length_mergeWith, length]
     rw [ih₁, ih₂]
     simp only [length]
     rw [Nat.add_assoc (length (split xs).1),
         Nat.add_comm 1,
         Nat.add_assoc (length (split xs).2),
         ←Nat.add_assoc (length (split xs).1),
         Nat.add_assoc (length xs)]
     apply congrArg (λ x => x + (1 + 1))
     apply length_split
termination_by cmp xs => xs.length

-- Slightly over-generalized "loop invariant" (we could make the preservation
-- portion more specific, e.g., by providing `x ∈ xs` as an extra hypothesis)
theorem List.foldr_invariant :
  ∀ (p : β → Prop) (f : α → β → β) (z : β) (xs : List α),
  p z → (∀ x a, p a → p (f x a)) → p (List.foldr f z xs)
| _, _, _, [], h_init, _ => h_init
| p, f, z, x :: xs, h_init, h_pres =>
  h_pres x (foldr f z xs) (foldr_invariant p f z xs h_init h_pres)

-- From a failed approach to `pivotTable` -- keeping around just in case
def List.depFoldr {κ : List α → Type _} :
  (xs : List α) →
  (∀ {xs : List α} (x : α), κ xs → κ (x :: xs)) →
  κ [] →
  κ xs
| [], f, z => z
| x :: xs, f, z => f x (depFoldr xs f z)

-- Reproducing `algebra/order/sub.lean` for Nats

-- Based on `tsub_le_iff_left` in `algebra/order/sub.lean` in Mathlib 3
theorem Nat.sub_le_iff_left {a b c : Nat} : a - b ≤ c ↔ a ≤ b + c :=
by apply Iff.intro
   . intros h
     rw [Nat.add_comm]
     apply Nat.le_add_of_sub_le
     exact h
   . intros h
     apply Nat.sub_le_of_le_add
     rw [Nat.add_comm]
     exact h

-- Based on `le_add_tsub`
theorem Nat.le_add_sub {a b : Nat} : a ≤ b + (a - b) :=
Nat.sub_le_iff_left.mp $ Nat.le_refl _

-- Based on `tsub_add_eq_tsub_tsub`
theorem Nat.sub_add_eq_sub_sub {a b c : Nat} : a - (b + c) = a - b - c :=
by apply Nat.le_antisymm (Nat.sub_le_iff_left.mpr _)
                         (Nat.sub_le_iff_left.mpr $ Nat.sub_le_iff_left.mpr _)
   . rw [Nat.add_assoc]
     apply Nat.le_trans Nat.le_add_sub (Nat.add_le_add_left Nat.le_add_sub _)
   . rw [←Nat.add_assoc]
     apply Nat.le_add_sub

theorem Nat.lt_of_sub_add : ∀ (m k n : Nat),
  k < m →
  n > 0 →
  m - (k + n) < m - k := by
  intros m k n hkm hn
  -- have h1 : m - (k + n) ≤ m - k - n :=
  apply Nat.lt_of_le_of_lt (m := m - k - n)
  . apply Nat.le_of_eq (@Nat.sub_add_eq_sub_sub m k n)
  . apply Nat.sub_lt
    . exact Nat.zero_lt_sub_of_lt hkm
    . exact hn

def Int.abs : Int → Nat
| Int.ofNat n => n
| Int.negSucc n => n.succ

theorem Int.toNat_of_ofNat_inj : ∀ z : Int, z ≥ 0 → Int.ofNat (z.toNat) = z :=
by intros z h
   cases z with
   | ofNat n => simp [toNat, ofNat]
   | negSucc n => contradiction

theorem Int.abs_of_nonneg_eq_toNat : ∀ z : Int, z ≥ 0 → z.abs = z.toNat :=
by intros z h
   cases z with
   | ofNat n => simp [toNat, ofNat, abs]
   | negSucc n => contradiction

theorem Int.neg_succ_eq_neg_ofNat_succ (n : Nat) :
  Int.negSucc n = -(Int.ofNat n.succ) :=
by unfold Neg.neg
   unfold instNegInt
   unfold Int.neg
   simp only [negOfNat]

theorem Int.add_neg_eq_sub (m n : Int) : n < 0 → m + n = m - n.abs :=
by intros h
   cases n with
   | ofNat n => contradiction
   | negSucc n =>
     unfold HSub.hSub
     unfold instHSub
     unfold Sub.sub
     unfold Int.instSub
     unfold Int.sub
     simp only [abs]
     rw [neg_succ_eq_neg_ofNat_succ]
     simp only [Nat.succ_eq_add_one, ofNat_eq_coe, natCast_add, Nat.cast_ofNat_Int]

-- BEGIN `groupByKey`
-- (Contains infrastructure for `groupBy`, as well as some extra proofs that
-- aren't used but might be useful in the future.)

theorem not_or_distrib : ¬ (a ∨ b) ↔ ¬a ∧ ¬b :=
Iff.intro
(λ h => And.intro (λ ha => h (Or.intro_left _ ha))
                  (λ hb => h (Or.intro_right _ hb)))
(λ h => λ hneg =>
  match hneg with
  | Or.inl ha => h.left ha
  | Or.inr hb => h.right hb)

theorem Iff.not_iff_not_of_iff : (p ↔ q) → (¬ p ↔ ¬ q) := λ hpq =>
  Iff.intro (λ hnp hq => hnp $ hpq.mpr hq) (λ hnq hp => hnq $ hpq.mp hp)

theorem Decidable.prop_eq_of_decide_eq (p q : Prop)
  [ip : Decidable p] [iq : Decidable q] :
  p = q → decide p = decide q := λ h =>
  by cases h
     apply congr
     . simp
     . apply eq_of_heq
       apply Subsingleton.helim
       rfl

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

-- TODO: should we use `List.eraseDups` instead? (Uses BEq instead of DEq.)
def List.uniqueAux {α} [DecidableEq α] : List α → List α → List α
| [], acc => acc.reverse
| x :: xs, acc => if x ∈ acc then uniqueAux xs acc else uniqueAux xs (x :: acc)

def List.unique {α} [inst : DecidableEq α] (xs : List α) := uniqueAux xs []

def List.unique' {α} [DecidableEq α] : List α → List α
| [] => []
| x :: xs =>
  have : length (filter (fun x_1 => !decide (x_1 = x)) xs) < length xs + 1 :=
    Nat.lt_succ_of_le (filter_length _ _)
  x :: unique' (xs.filter (· ≠ x))
termination_by xs => xs.length

def List.no_duplicates [DecidableEq α] (xs : List α) := unique xs = xs

inductive List.NoDuplicates {α} : List α → Prop
| nil : NoDuplicates []
| cons x xs : x ∉ xs → NoDuplicates xs → NoDuplicates (x :: xs)

def List.uniqueFoldl [DecidableEq α] (xs : List α) :=
  xs.foldl (λ acc x => if x ∈ acc then acc else acc ++ [x]) []

theorem List.mem_append_singleton : ∀ (x : α) (xs : List α), x ∈ xs ++ [x]
| x, [] => List.Mem.head _
| x, y :: ys => List.Mem.tail _ (mem_append_singleton x ys)

theorem List.mem_append_front :
  ∀ (x : α) (xs ys : List α), x ∈ xs → x ∈ xs ++ ys
| x, _ :: xs, ys, List.Mem.head _ => List.Mem.head _
| x, x' :: xs, ys, List.Mem.tail _ h =>
  List.Mem.tail x' (mem_append_front x xs ys h)

theorem Or.assoc : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R :=
  Iff.intro (λ h => h.elim (λ hpq => hpq.elim Or.inl (Or.inr ∘ Or.inl))
                           (Or.inr ∘ Or.inr))
            (λ h => h.elim (Or.inl ∘ Or.inl)
                           (λ hqr => hqr.elim (Or.inl ∘ Or.inr) Or.inr))

-- Taken from Lean 3 mathlib lib/lean/library/init/data/list/lemmas.lean 112
theorem List.mem_append : ∀ {xs ys : List α} {a : α}, a ∈ xs ++ ys ↔ a ∈ xs ∨ a ∈ ys
| [], ys, a => Iff.intro Or.inr (λ h => h.elim (λ h' => nomatch h') id)
| x :: xs, ys, a =>
  have ih := mem_append (xs := xs) (ys := ys) (a := a)
  Iff.intro
    (λ h => match h with
            | .head _ => Or.inl $ Mem.head _
            | .tail _ htail =>
              match ih.mp htail with
              | .inl hxs => Or.inl $ Mem.tail _ hxs
              | .inr hys => Or.inr hys)
    (λ h => match h with
            | .inl (Mem.head _) => Mem.head _
            | .inl (Mem.tail _ htail) => Mem.tail _ $ ih.mpr (Or.inl htail)
            | .inr hys => Mem.tail _ $ ih.mpr (Or.inr hys))

theorem List.mem_append_comm {v : α} {xs ys : List α} :
  v ∈ xs ++ ys ↔ v ∈ ys ++ xs :=
let flip : ∀ {as bs}, v ∈ as ++ bs → v ∈ bs ++ as :=
  (λ h => h |> mem_append.mp |> Or.comm.mp |> mem_append.mpr)
Iff.intro flip flip

theorem List.mem_reverse_iff (x : α) (xs : List α) :
  x ∈ xs ↔ x ∈ reverse xs := by
  rw [reverse_eq_reverseSpec]
  apply Iff.intro
  . intro hf
    induction hf with
    | head xs =>
      simp only [reverseSpec]
      apply mem_append_singleton
    | @tail y ys h_x_ys ih =>
      simp only [reverseSpec]
      apply mem_append_front _ _ _ ih
  . intro hb
    induction xs with
    | nil => contradiction
    | cons y ys ih =>
      simp only [reverseSpec] at hb
      rw [List.mem_append_comm] at hb
      simp only [HAppend.hAppend, Append.append, List.append] at hb
      cases hb with
      | head => exact Mem.head _
      | tail _ htail => exact Mem.tail _ (ih htail)

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
  --              if x ∈ acc then reverse acc else reverse acc ++ [x] := by rw [mem_reverse_iff]


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

-- TODO: when switching to Lean 4.5, delete the first simp, then switch the
-- `foldr` simps to `all` simps
theorem List.all_pred {p : α → Prop} [DecidablePred p] {xs : List α} :
  xs.all (λ x => decide (p x)) ↔ ∀ x, x ∈ xs → p x :=
  ⟨λ h x hx => of_decide_eq_true (List.all_eq_true.mp h x hx),
   λ h => List.all_eq_true.mpr (λ x hx => decide_eq_true (h x hx))⟩

@[instance] def List.forAllDecidable (xs : List α) (p : α → Prop)
  [DecidablePred p] : Decidable (∀x, x ∈ xs → p x) :=
if h : xs.all p
then Decidable.isTrue (List.all_pred.mp h)
else Decidable.isFalse (h ∘ List.all_pred.mpr)

theorem List.filter_sublist {α} (p) :
  ∀ (xs : List α), List.filter p xs <+ xs
| [] => .nil
| x :: xs =>
  if h : p x
  then by
    simp only [filter, h]
    apply Sublist.cons2 _ _ _ (filter_sublist _ _)
  else by
    simp only [filter, h]
    apply Sublist.cons _ _ _ (filter_sublist _ _)

theorem List.length_sublist_le {α} {xs ys : List α} :
  xs <+ ys → xs.length ≤ ys.length
  | .nil => .refl
  | .cons _ _ _ hsubl => Nat.le_succ_of_le (length_sublist_le hsubl)
  | .cons2 _ _ _ hsubl => Nat.succ_le_succ (length_sublist_le hsubl)

theorem List.mem_cons_iff_mem_singleton_or_tail (y : α) (ys : List α) (x : α) :
  x ∈ y :: ys ↔ x ∈ [y] ∨ x ∈ ys := by
  apply Iff.intro
  . intro hf
    cases hf with
    | head => apply Or.intro_left _ (Mem.head _)
    | tail _ h => apply Or.intro_right _ h
  . intro hb
    cases hb with
    | inl h => rw [(mem_singleton_iff x y).mp h]; apply Mem.head
    | inr h => apply Mem.tail _ h

-- TODO: it would make more sense to use `&&` instead of `∧` since this is a
-- "data function." However, `∧` is better for the `length_groupByKey` proof, so
-- I'm leaving it, at least for now.
theorem List.filter_filter (p₁ p₂ : α → Bool) (xs : List α) :
  filter p₁ (filter p₂ xs) = filter (λ x => p₂ x ∧ p₁ x) xs := by
  rw [filter_eq_filterSpec, filter_eq_filterSpec, filter_eq_filterSpec]
  induction xs with
  | nil => simp [filterSpec]
  | cons x xs ih =>
    cases h₂ : p₂ x with
    | false =>
      simp only [filterSpec, h₂, ite_false]
      exact ih
    | true =>
      simp only [filterSpec, h₂, ite_true]
      cases h₁ : p₁ x with
      | false =>
        simp only [filterSpec, h₁, h₂, ite_false]
        exact ih
      | true =>
        simp only [filterSpec, h₁, h₂, ite_true]
        exact congrArg _ ih

theorem List.uniqueAux_acc_append_filter {α} [DecidableEq α] :
  ∀ (xs acc : List α),
  uniqueAux xs acc = reverse acc ++ unique (xs.filter (· ∉ acc))
| [], acc => by simp [uniqueAux, reverse, reverseAux, unique]
| x :: xs, acc =>
  have hterm : length (filter (λ a => !decide (a ∈ acc)) xs)
                < Nat.succ (length xs) :=
    Nat.lt_of_le_of_lt (m := length xs) (filter_length _ _) (Nat.lt.base _)
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
      rw [reverse_singleton, singleton_append, filter_filter]
      -- TODO: this was just `by simp` in Lean 4.0.0...what happened?
      have : (λ x_1 => decide (
              (decide ¬x_1 ∈ acc) = true ∧ (decide ¬x_1 ∈ [x]) = true)
             ) = (λ x_1 => decide (¬x_1 ∈ acc ∧ ¬x_1 ∈ [x])) := by
        apply funext
        intro x_1
        simp only [decide_not, Bool.not_eq_true']
        cases Decidable.em (x_1 ∈ acc) with
        | inl hmem =>
          simp only [hmem, decide_True, not_true_eq_false, false_and]
        | inr hnmem =>
          simp only [hnmem, decide_False, not_false_eq_true, true_and,
                     decide_not]
          cases Decidable.em (x_1 ∈ [x]) with
          | inl hmem' => simp only [hmem', decide_True, decide_False, not]
          | inr hnmem' => simp only [hnmem', decide_True, decide_False, not]
      rw [this, ←unique]
      apply congrArg
      apply congrArg
      have h_mem_iff := mem_cons_iff_mem_singleton_or_tail x acc
      have h_mem_iff_neg := (λ x => Iff.not_iff_not_of_iff $ h_mem_iff x)
      apply congr _ rfl
      apply congr rfl
      apply funext
      intros a
      apply Decidable.prop_eq_of_decide_eq
      rw [h_mem_iff_neg, not_or_distrib, And.comm]
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
    Nat.lt_of_le_of_lt (m := length xs) (filter_length _ _) (Nat.lt.base _)
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

def List.groupByKey {κ} [DecidableEq κ] {ν} : List (κ × ν) → List (κ × List ν)
| [] => []
| (k, v) :: kvs =>
  have h_help : (matchKey kvs k).2.length < kvs.length.succ :=
    matchKey_length_lt k kvs

  let fms := matchKey kvs k
  (k, v :: fms.1) :: groupByKey fms.2
termination_by xs => xs.length
decreasing_by assumption

theorem List.groupByKey_matchKey_snd_length_cons [DecidableEq κ]
  (k : κ) (v : ν) (xs : List (κ × ν)) :
  1 + length (groupByKey (matchKey ((k, v) :: xs) k).snd)
    = (groupByKey ((k, v) :: xs)).length :=
calc
  1 + length (groupByKey (matchKey ((k, v) :: xs) k).2)
  = 1 + length (groupByKey (matchKey xs k).2) :=
    by simp only [matchKey, length, ite_true]
  _ = length (groupByKey (matchKey xs k).2) + 1 := Nat.add_comm _ _
  _ = length ((k, v :: (matchKey xs k).1) :: groupByKey (matchKey xs k).2) :=
    rfl
  _ = length (groupByKey ((k, v) :: xs)) := rfl

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

theorem List.length_groupByKey {κ} [DecidableEq κ] {ν} :
  ∀ (xs : List (κ × ν)),
  length (groupByKey xs) = (xs.map Prod.fst).unique.length
| [] => rfl
| (k, v) :: xs => by
  have hterm : length (matchKey xs k).snd < Nat.succ (length xs) :=
    Nat.lt_of_succ_le $ Nat.succ_le_succ $ matchKey_snd_length xs k
  have ih := length_groupByKey (matchKey xs k).2
  simp only [map, unique, uniqueAux, List.not_mem_nil, ite_false, groupByKey]
  -- This needs to be a separate `simp` to ensure proper ordering
  simp only [length]
  rw [length_uniqueAux_matchKey _ k _ $ List.Mem.head _]
  rw [ih]
  apply Eq.symm
  apply List.length_uniqueAux (acc := [k])
  intro x
  rw [mem_singleton_iff]
  intro hmem hneg
  have := not_mem_matchKey_self_map_snd x xs
  rw [←hneg] at hmem
  exact this hmem
termination_by xs => length xs
decreasing_by assumption
-- END `groupByKey` - `groupBy` spec 4
-- BEGIN `groupByRetentive` spec 4 (this might simplify some stuff above?)

def Function.injective (f : α → β) := ∀ {x y}, f x = f y → x = y
def Function.biInjective (f : α → β → γ) := ∀ x₁ x₂ y₁ y₂,
  f x₁ x₂ = f y₁ y₂ → x₁ = y₁ ∧ x₂ = y₂

theorem List.matchKey_snd_sublist [DecidableEq κ] :
  ∀ (k : κ) (kvs : List (κ × ν)), (matchKey kvs k).snd <+ kvs
| _, [] => Sublist.nil
| k, (kv :: kvs) =>
  have ih := matchKey_snd_sublist k kvs
  if h : kv.fst = k
  then by simp only [matchKey, h, ite_true]; exact Sublist.cons _ _ _ ih
  else by simp only [matchKey, h, ite_true]; exact Sublist.cons2 _ _ _ ih

theorem List.matchKey_snd_sublist_of_sublist [DecidableEq κ] :
  ∀ (k : κ) (xs ys : List (κ × ν)),
  xs <+ ys → (matchKey xs k).snd <+ (matchKey ys k).snd := by
  intro k xs ys h
  induction h with
  | nil => constructor
  | cons xs' ys' x' h' ih =>
    simp only [matchKey]
    cases Decidable.em (x'.fst = k) with
    | inl heq => simp only [heq, ite_true]; apply ih
    | inr hneq => simp only [hneq, ite_false]; apply Sublist.cons _ _ _ ih
  | cons2 xs' ys' x' h' ih =>
    simp only [matchKey]
    cases Decidable.em (x'.fst = k) with
    | inl heq => simp only [heq, ite_true]; assumption
    | inr hneq =>
      simp only [hneq, ite_false]
      apply Sublist.cons2 _ _ _ ih

theorem List.mem_of_mem_sublist {xs ys : List α} {x : α} :
  xs <+ ys → x ∈ xs → x ∈ ys
| .cons _ _ x' hsub, hmem => Mem.tail x' (mem_of_mem_sublist hsub hmem)
| .cons2 _ ys _ _, Mem.head _ => Mem.head ys
| .cons2 _ _ _ hsub, Mem.tail _ hmem =>
  Mem.tail _ (mem_of_mem_sublist hsub hmem)

theorem List.fst_groupByKey_sublist [DecidableEq κ] : ∀ (kvs : List (κ × ν)),
  map Prod.fst (groupByKey kvs) <+ map Prod.fst kvs
| [] => Sublist.nil
| (k, v) :: kvs =>
  have hterm := matchKey_length_lt k kvs
  have ih := fst_groupByKey_sublist (matchKey kvs k).snd
  have hsubl := matchKey_snd_sublist k kvs
  Sublist.cons2 _ _ _ $
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
theorem List.mem_fst_groupByKey_key_or_snd [DecidableEq κ] :
  ∀ {ys : List (κ × ν)} {x : κ},
  x ∈ map Prod.fst ys →
    ∀ k, x = k ∨ x ∈ map Prod.fst (groupByKey (matchKey ys k).snd) :=
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
        have ih := mem_fst_groupByKey_key_or_snd this k
        cases ih with
        | inl => contradiction
        | inr hmem => exact hmem
      | inr hkneq =>
        simp only [hkneq, ite_false]
        simp only [groupByKey]
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
          have ih := mem_fst_groupByKey_key_or_snd this k'
          cases ih with
          | inl => contradiction
          | inr => assumption
termination_by ys x hx k => ys.length

/-
Although tempting, the stronger claim
  `xs <+ ys → map Prod.fst (groupByKey xs) <+ map Prod.fst (groupByKey ys)`
does not hold, as the following counterexample illustrates:

* `List.groupByKey [("a", 1), ("b", 2), ("a", 3)]`
* `List.groupByKey [("b", 2), ("a", 3)]`

Also, the initial hypothesis is a bit stricter than it needs to be:
`(∀ x, x ∈ xs → x ∈ ys)` would suffice.
-/

theorem List.all_in_map_fst_groupByKey_of_sublist [DecidableEq κ] :
  ∀ {xs ys : List (κ × ν)},
  xs <+ ys →
    ∀ x, x ∈ map Prod.fst (groupByKey xs) → x ∈ map Prod.fst (groupByKey ys)
| _, _, .cons xs ys (k, v) hsubl, x, hx =>
  if heq : x = k
  then heq ▸ Mem.head (map Prod.fst (groupByKey (matchKey ys k).snd))
  else
    have hterm : ys.length < Nat.succ ys.length := Nat.le.refl
    have ih := all_in_map_fst_groupByKey_of_sublist hsubl x hx
    have hor : x = k ∨ x ∈ map Prod.fst (groupByKey (matchKey ys k).snd) :=
      mem_fst_groupByKey_key_or_snd
        (mem_of_mem_sublist (fst_groupByKey_sublist ys) ih) k
    Mem.tail k $
    match hor with
    | .inl hxeq => absurd hxeq heq
    | .inr hmem => hmem
| _, _, .cons2 xs ys (k, v) hsubl, x, hx => by
    simp only [groupByKey]
    simp only [map]
    simp only [groupByKey] at hx
    simp only [map] at hx
    cases hx with
    | head => constructor
    | tail _ htail =>
      apply Mem.tail
      have : (matchKey xs k).snd <+ (matchKey ys k).snd :=
        matchKey_snd_sublist_of_sublist _ _ _ hsubl
      have hterm := matchKey_length_lt k ys
      apply all_in_map_fst_groupByKey_of_sublist this
      assumption
termination_by xs ys hsubl x hx => ys.length

-- #check @List.not_mem_matchKey_self_snd
-- #check @List.matchKey_snd_sublist
-- #check @List.matchKey_snd_sublist_of_sublist
-- theorem List.map_groupByKey_matchKey_wip [DecidableEq κ] {k : κ} {kvs : List (κ × ν)} :
--   ∀ x, x ∈ map Prod.fst (groupByKey (matchKey kvs k).snd) → x ∈ map Prod.fst (groupByKey kvs) := by
--   intro x hx
--   induction kvs with
--   | nil => simp only [groupByKey, map] at hx; contradiction
--   | cons kv kvs ih =>
--     cases kv with | mk k' v =>
--     -- simp only [matchKey] at hx
--     simp only [groupByKey]
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
--         simp only [groupByKey] at hx
--         simp only [map] at hx
--         have := matchKey_snd_sublist k' (matchKey kvs k).snd
--         sorry

-- The converse is also true, but we don't need it here
theorem List.mem_fsts_of_mem_fsts_groupByKey [DecidableEq κ] (kvs : List (κ × ν)) :
  k ∈ map Prod.fst (groupByKey kvs) → k ∈ map Prod.fst kvs := by
  intro h
  induction kvs with
  | nil => contradiction
  | cons kv kvs ih =>
    cases kv with | mk k₀ v₀ =>
    simp only [groupByKey] at h
    simp only [map] at h
    simp only [map]
    cases h with
    | head => apply Mem.head
    | tail _ htail =>
      apply Mem.tail
      apply ih
      apply all_in_map_fst_groupByKey_of_sublist (matchKey_snd_sublist k₀ kvs)
      assumption

-- Instead of being separate, this could just be folded into
-- `groupByKey_fsts_no_duplicates`
theorem List.key_not_mem_fst_groupByKey_matchKey_snd [DecidableEq κ]
  (kvs : List (κ × ν)) (k : κ) :
  k ∉ map Prod.fst (groupByKey (matchKey kvs k).snd) :=
  mt (List.mem_fsts_of_mem_fsts_groupByKey (matchKey kvs k).snd)
    (List.not_mem_matchKey_self_map_snd _ _)

-- TODO: almost certainly need something more general for the induction
theorem List.groupByKey_fsts_no_duplicates [DecidableEq κ] :
  ∀ (kvs : List (κ × ν)), NoDuplicates $ (groupByKey kvs).map Prod.fst
| [] => NoDuplicates.nil
| (k, v) :: kvs =>
  have h_help : (matchKey kvs k).2.length < kvs.length.succ :=
    matchKey_length_lt k kvs

  NoDuplicates.cons k ((groupByKey (matchKey kvs k).2).map Prod.fst)
    (List.key_not_mem_fst_groupByKey_matchKey_snd _ _)
    (groupByKey_fsts_no_duplicates (matchKey kvs k).2)
termination_by xs => xs.length
decreasing_by assumption

theorem List.mem_of_mem_injective_map (f : α → β) (hf : f.injective) :
  ∀ (x : α) (xs : List α),
  f x ∈ map f xs ↔ x ∈ xs :=
λ _ xs => Iff.intro
  (λ h =>
    have ⟨_, hb⟩ := mem_map.mp h
    have hbeqx := hf hb.right
    Eq.subst (motive := λ a => a ∈ xs) hbeqx hb.left
  )
  (mem_map_of_mem _)

theorem List.no_dups_map_injective
  (f : α → β) (hf : f.injective) : ∀ (xs : List α) (hxs : NoDuplicates xs),
  NoDuplicates $ map f xs
| [], hxs => NoDuplicates.nil
| x :: xs, NoDuplicates.cons _ _ hxnin hndxs =>
  NoDuplicates.cons (f x) (map f xs)
    (λ hneg => absurd ((mem_of_mem_injective_map f hf x xs).mp hneg) hxnin)
    (no_dups_map_injective f hf xs hndxs)
-- END spec 4

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
  | nil => exact .nil
  | cons xs' ys x hsubl' ih =>
    apply ih
    cases hunique
    repeat assumption
  | cons2 xs' ys x hsubl' ih =>
    constructor
    . cases hunique
      intro hneg
      have := mem_of_mem_sublist hsubl' hneg
      contradiction
    . apply ih
      cases hunique
      repeat assumption

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
      apply filter_length
      rw [Nat.add_comm]
      apply Nat.lt.base
    apply unique_eq_unique'
termination_by xs => xs.length

theorem List.unique'_sublist [DecidableEq α] : ∀ (xs : List α),
  List.unique' xs <+ xs
  | [] => .nil
  | x :: xs =>
    have : (filter (fun x_1 => !decide (x_1 = x)) xs).length < xs.length + 1 :=
      Nat.lt_succ_of_le (filter_length _ _)
    Sublist.cons2 _ _ _ $
      Sublist.trans (List.unique'_sublist _) (List.filter_sublist _ _)
termination_by xs => xs.length

theorem List.unique'_Unique [DecidableEq α] : ∀ (xs : List α),
  Unique xs.unique'
  | [] => .nil
  | x :: xs =>
    have : (filter (fun x_1 => !decide (x_1 = x)) xs).length < xs.length + 1 :=
      Nat.lt_succ_of_le (filter_length _ _)
    .cons (mt (mem_of_mem_sublist (unique'_sublist _)) (not_mem_filter_neq x xs))
          (unique'_Unique _)
termination_by xs => xs.length
-- END `leftJoin` spec 4 helpers

-- `List.counts`, helper functions, and associated theorems
-- TODO: these proofs could probably be cleaned up a lot.
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

theorem not_not (p : Prop) : p → ¬¬p := λ hp hneg => hneg hp

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

theorem List.mem_append_back (x : α) : ∀ (xs ys : List α),
  x ∈ ys → x ∈ xs ++ ys
| [], ys, hin => hin
| z :: xs, ys, hin => List.Mem.tail _ (mem_append_back x xs ys hin)

theorem List.mem_append_iff {x : α} {xs ys : List α} :
  (x ∈ xs ∨ x ∈ ys) ↔ x ∈ xs ++ ys := by
  apply Iff.intro
  . intros hf
    cases hf with
    | inl hxs => apply mem_append_front _ _ _ hxs
    | inr hys => apply mem_append_back _ _ _ hys
  . intros hb
    induction xs with
    | nil => exact Or.intro_right _ hb
    | cons z xs ih =>
      cases hb with
      | head _ => apply Or.intro_left _ (List.Mem.head _)
      | tail _ h' =>
        cases ys with
        | nil =>
          apply Or.intro_left
          apply List.Mem.tail
          simp at h'
          exact h'
        | cons y ys =>
          simp at h'
          cases ih h' with
          | inl hxxs =>
            apply Or.intro_left
            exact List.Mem.tail _ hxxs
          | inr hxys =>
            exact Or.intro_right _ hxys

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
        cases mem_append_iff.mpr h with
        | inl hcs => exact List.mem_append_front _ _ _ hcs
        | inr hcons =>
          apply List.mem_append_back
          rw [←cons_append] at hcons
          cases mem_append_iff.mpr hcons with
          | inl hxas => exact List.Mem.tail _ hxas
          | inr hy =>
            cases hy with
            | tail _ _ => contradiction
            | head _ => exact List.Mem.head _
      . intros h
        cases mem_append_iff.mpr h with
        | inl hcs => exact List.mem_append_front _ _ _ hcs
        | inr hcons =>
          apply List.mem_append_back
          cases hcons with
          | head _ =>
            apply List.Mem.tail
            apply List.mem_append_back
            apply (List.mem_singleton_iff y y).mpr rfl
          | tail _ hcons' =>
            rw [←cons_append]
            exact List.mem_append_front _ _ _ hcons'

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
-- End `counts` work

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

-- Lemmas for selectColumns1_spec2

theorem List.eq_or_mem_tail_of_mem {x x' : α} {xs : List α} :
  x ∈ x' :: xs → x = x' ∨ x ∈ xs
| .head _ => .inl rfl
| .tail _ h => .inr h

theorem List.neq_of_mem_not_mem {x y : α} {xs : List α} :
  x ∈ xs → y ∉ xs → x ≠ y :=
  λ hxs => mt (λ heq => heq ▸ hxs)

theorem List.get_mem_cons_of_head_not_mem_getee {y :α} {xs ys : List α} {i} :
  xs.get i ∈ y :: ys → y ∉ xs → xs.get i ∈ ys :=
  λ hget hnmem =>
  have hget_lem := get_mem xs i.val i.isLt
  have hneq_lem := neq_of_mem_not_mem hget_lem hnmem
  match eq_or_mem_tail_of_mem hget with
  | .inr htl => htl
  | .inl heq => absurd heq hneq_lem

theorem List.sieve_mem_iff_true_unique :
  ∀  {i} {xs : List α} {bs : List Bool} (pf1 pf2) (hu : List.Unique xs),
  xs.get ⟨i, pf1⟩ ∈ bs.sieve xs ↔ bs.get ⟨i, pf2⟩ = true
| 0, x :: xs, false :: bs, pf1, pf2, .cons hnmem hu' =>
  Iff.intro
    (λ hf =>
      have not_mem_sieve_of_not_mem :=
        mt (mem_of_mem_sublist (sieve_sublist bs xs))
      False.rec $ not_mem_sieve_of_not_mem hnmem hf)
    (λ hb => nomatch hb)
| 0, x :: xs, true :: bs, pf1, pf2, .cons hnmem hu' =>
  Iff.intro
    (λ _ => rfl)
    (λ _ => List.Mem.head _)
| .succ n, x :: xs, false :: bs, pf1, pf2, .cons hnmem hu' =>
  Iff.intro
    (λ hf =>
      (sieve_mem_iff_true_unique
        (Nat.lt_of_succ_lt_succ pf1)
        (Nat.lt_of_succ_lt_succ pf2)
        hu').mp hf)
    (λ hb => (sieve_mem_iff_true_unique pf1 pf2 (.cons hnmem hu')).mpr hb)
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

theorem List.mem_map_sieve_of_mem_map {f : α → β} {x : α}
  : ∀ {xs : List α} {bs : List Bool}, f x ∈ map f (sieve bs xs) → f x ∈ map f xs
| [], [], h => nomatch h
| x' :: xs, [], h => h
| x' :: xs, false :: bs, h => Mem.tail _ $ mem_map_sieve_of_mem_map h
| x' :: xs, true :: bs, h =>
  match eq_or_mem_tail_of_mem h with
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
      | false => simp only [get, map] at hget
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

/- Equality type for pattern-matching workaround in proof of
  `selectColumns2_spec3` -/

inductive EqT : α → α → Type where
  | refl (a : α) : EqT a a
infix:50 " ≡ " => EqT

def EqT.ofEq {a b : α} : a = b → a ≡ b := λ | .refl _ => .refl _
