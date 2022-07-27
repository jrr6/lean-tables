-- Variant on orElse that's useful for de-option-ifying cell values
def Option.orDefault {α} [Inhabited α] : Option α → α
| some x => x
| none => default

-- List utilities
inductive List.All {α} (p : α → Prop) : List α → Prop
| vac      : All p []
| cons {x xs} : p x → All p xs → All p (x::xs)

inductive List.Sublist {α} : List α → List α → Prop
| nil : Sublist [] []
| cons (x xs ys) : Sublist xs ys → Sublist xs (x :: ys)
| cons2 (x xs ys) : Sublist xs ys → Sublist (x :: xs) (x :: ys)

-- Nifty, but hard to write proofs over
-- def List.prod {α β} (xs : List α) (ys : List β) : List (α × β) :=
-- List.foldl List.append [] (List.map (λ x => List.map (λ y => (x, y)) ys) xs)

-- This goes the wrong way -- keep it around just in case...
theorem Nat.lt_of_add_lt_add : ∀ (a m n : Nat), m + a < n + a → m < n
| 0, m, n, h => h
| 1, m, n, h => Nat.lt_of_succ_lt_succ h
| succ (succ a'), m, n, h =>
  -- Copied from `one_lt_succ_succ` in Lean 3's `basic.lean`
  have term_help : 1 < succ (succ a') := succ_lt_succ $ succ_pos a'
  have ih1 := lt_of_add_lt_add 1 (m + succ a') (n + succ a') h
  have ih := lt_of_add_lt_add (succ a') m n ih1
  ih
termination_by Nat.lt_of_add_lt_add a m n h => a

theorem Nat.add_lt_add_of_lt : ∀ (a m n : Nat), m < n → m + a < n + a :=
by intros a m n h
   induction a with
   | zero => exact h
   | succ n' ih =>
    rw [←Nat.add_one, ←Nat.add_assoc, ←Nat.add_assoc, Nat.add_one, Nat.add_one]
    apply Nat.succ_lt_succ
    exact ih

def List.prod {α β} : List α → List β → List (α × β)
| [], _ => []
| _, [] => []
| [x], y :: ys => (x, y) :: prod [x] ys
| x :: x' :: xs, ys =>
  have h₁ : Nat.succ 0 + length ys <  
            Nat.succ (Nat.succ (length xs)) + length ys :=
    by apply Nat.add_lt_add_of_lt
       apply Nat.succ_lt_succ $ Nat.succ_pos (length xs)
  have h₂ : Nat.succ (length xs) + length ys <
            Nat.succ (Nat.succ (length xs)) + length ys :=
    by apply Nat.add_lt_add_of_lt
       apply Nat.succ_lt_succ
       apply Nat.lt.base
  prod [x] ys ++ prod (x' :: xs) ys
termination_by List.prod xs ys => xs.length + ys.length

-- TODO: So List.nth *does* still exist in the prelude -- they just changed
-- the name to `List.get`...
def List.nth {α} : (xs : List α) → (n : Nat) → (n < List.length xs) → α
| [], _, h => absurd h (by intro nh; cases nh)
| x::xs, 0, h => x
| x::xs, Nat.succ n, h => nth xs n (Nat.le_of_succ_le_succ h)

def List.nths {α}
              (xs : List α)
              (ns : List {n : Nat // n < List.length xs}) : List α :=
  List.map (λ n => List.nth xs n.val n.property) ns

def List.dropLastN {α} : Nat → List α → List α :=
  (λ n => reverse ∘ List.drop n ∘ reverse)

-- This is slick, but unfortunately, it breaks type inference
-- def List.sieve' {α} (bs : List Bool) (xs : List α) : List α :=
--   xs |> List.zip bs 
--      |> List.filter Prod.fst
--      |> List.map Prod.snd

def List.sieve {α} : List Bool → List α → List α
| [], xs => xs
| _, [] => []
| true :: bs, x :: xs => x :: sieve bs xs
| false :: bs, _ :: xs => sieve bs xs

-- TODO: Haven't actually done the big-O analysis, but it's probably more
-- efficient to make the recursive case x :: flatten (xs :: ys). Unfortunately,
-- the termination checker doesn't like that implementation.
-- Initial attempt was:
-- termination_by flatten xs => 
--   List.foldl (λ acc xs => acc + List.length xs + 1) 0 xs)
-- TODO: After all that, I don't think we even need this function after all...
def List.flatten {α} : List (List α) → List α
| [] => []
| [] :: ys => flatten ys
| (x :: xs) :: ys => (x :: xs) ++ flatten ys

def List.flatMap {α β} (f : α → List β) : List α → List β
| [] => []
| x :: xs => f x ++ flatMap f xs

-- def List.verifiedEnum' : (xs : List α) → List ({n : Nat // n < xs.length} × α)
-- | [] => []
-- | x :: xs =>
--   let zs := x :: xs
--   have hzs : zs = x :: xs := rfl
--   let rec vEnumFrom : (ys : {ys // ys.length < zs.length})
--                       → {n : Nat // n < zs.length - ys.val.length}
--                       → List ({n : Nat // n < zs.length} × α)
--   | ⟨[], _⟩, _ => []
--   | ⟨y :: ys, hys⟩, ⟨n, hn⟩ =>
--     ⟨⟨n,
--     by apply hn
--     ⟩, y⟩ :: vEnumFrom ⟨ys, sorry⟩ ⟨n + 1, sorry⟩

--   vEnumFrom ⟨zs, sorry⟩ ⟨0, sorry⟩
  -- ⟨⟨0, Nat.lt_of_succ_le (Nat.le_add_left 1 (length xs))⟩, x⟩
  --   :: vEnumFrom ⟨xs, _⟩ ⟨0, _⟩

-- TODO: I refuse to believe there isn't a simpler way to do this
-- TODO: using `reverse` makes the proofs easier, but could find a way to avoid?
def List.verifiedEnum : (xs : List α) → List ({n : Nat // n < xs.length} × α)
| [] => []
| z :: zs =>
  let xs := z :: zs  -- `xs@(z :: zs)` doesn't work
  let rec vEnumFrom : (ys : {ys : List α // ys.length ≤ xs.length})
                      → {n : Nat // n < ys.val.length}
                      → List ({n : Nat // n < xs.length} × α)
                      → List ({n : Nat // n < xs.length} × α)
    | ⟨[], h⟩, n, acc => acc
    | ⟨y :: ys, hys⟩, ⟨0, hn⟩, acc =>
      ((⟨0, @Nat.lt_of_lt_of_le 0 (length ys + 1) (length xs)
                                (Nat.zero_lt_succ (length ys)) hys⟩, y) :: acc)
    | ⟨y :: ys, hys⟩, ⟨Nat.succ n, hn⟩, acc =>
      vEnumFrom ⟨ys, @Nat.le_trans (length ys) (length ys + 1) (length xs)
                                   (Nat.le_succ (length ys)) hys⟩
                ⟨n, Nat.lt_of_succ_lt_succ hn⟩
                ((⟨Nat.succ n, Nat.lt_of_lt_of_le hn hys⟩, y) :: acc)
  vEnumFrom ⟨reverse xs, Nat.le_of_eq $ List.length_reverse xs⟩
            ⟨length xs - 1,
             by rw [List.length_reverse]; apply Nat.sub_succ_lt_self; apply Nat.zero_lt_succ⟩
            []
termination_by vEnumFrom ys n acc => ys.val.length
-- | [] => []
-- | x :: xs => verifiedEnumFrom x :: xs ⟨length xs - 1, by
--   simp [length]
--   calc length xs - 1 ≤ length xs := by apply Nat.sub_le
--                    _ < length xs + 1 := by constructor
--   ⟩

theorem List.filter_length_aux {α} (g : α → Bool) (xs : List α) :
    ∀ rs : List α, List.length (List.filterAux g xs rs)
                   <= List.length xs + List.length rs :=
by
  induction xs with
  | nil =>
    intro rs
    simp only [filter, filterAux]
    rw [List.length_reverse]
    simp only [length, Nat.zero_add]
    apply Nat.le.refl
  | cons x xs ih =>
    intro rs
    simp only [filter, filterAux]
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
  List.filter_length_aux g xs []

-- Temporary merge sort algorithm until the full sorting library gets ported

def List.split {α} : List α → List α × List α
| [] => ([], [])
| [x] => ([x], [])
| x₁ :: x₂ :: xs =>
  let (ys, zs) := split xs;
  (x₁ :: ys, x₂ :: zs)

theorem List.split_length_fst' {α} :
    ∀ (xs : List α), (split xs).fst.length ≤ xs.length
| [] => by simp only [length]
| [x] => by simp only [length]
| x₁ :: x₂ :: xs =>
  have ih := split_length_fst' xs;
  by simp only [split, length]
     apply Nat.le.step
     apply Nat.succ_le_succ
     apply ih

theorem List.split_length_fst {α} :
    ∀ (xs : List α), xs.length ≤ 1 ∨ (split xs).fst.length < xs.length
| [] => by simp only [length]
| [x] => by simp only [length]
| [x, y] => by simp only [length]
| [x, y, z] => by simp only [length]
| x₁ :: x₂ :: x :: x' :: xs =>
  have ih := split_length_fst (x :: x' :: xs);
  by simp only [split, length]
     apply Or.intro_right
     apply Nat.succ_lt_succ
     simp [length, Nat.add] at ih
     apply Nat.lt.step
     cases ih with
     | inl _ => contradiction
     | inr h => apply h

theorem List.split_length_snd {α} :
    ∀ (xs : List α), xs = [] ∨ (split xs).snd.length < xs.length
| [] => by simp only [length]
| [x] => by simp only [length]
| [x, y] => by simp only [length]
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
| [] => by simp only [length]
| [x] => by simp only [length]
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
  have _ : xs.length + ys.length.succ < xs.length.succ + ys.length.succ := by
    rw [←Nat.add_one,
        ←Nat.add_one,
        ←Nat.add_assoc (length xs) (length ys),
        Nat.add_assoc (length xs) 1,
        Nat.add_comm 1,
        Nat.add_assoc (length ys),
        ←Nat.add_assoc (length xs) (length ys) (1 + 1)
        ]
    apply Nat.lt.base
  match cmp x y with
  | Ordering.gt => y :: mergeWith cmp (ys, x :: xs)
  | _ => x :: mergeWith cmp (y :: ys, xs)
termination_by mergeWith cmp prd => prd.fst.length + prd.snd.length

def List.mergeSortWith {α} : (α → α → Ordering) → List α → List α
| _, [] => []
| _, [x] => [x]
| cmp, x₁ :: x₂ :: xs =>
  have _ : (split (x₁::x₂::xs)).fst.length < (x₁::x₂::xs).length :=
    match xs with
    | [] => by simp only [length]
    | [xs] => by simp only [length]
    | y :: y' :: ys =>
      by cases split_length_fst (y :: y' :: ys) with
      | inl _ => contradiction
      | inr h =>
        simp only [length] at *
        apply Nat.lt.step
        apply Nat.succ_lt_succ
        exact h

   have _ : (split (x₁::x₂::xs)).snd.length < (x₁::x₂::xs).length :=
    match xs with
    | [] => by simp only [length]
    | [xs] => by simp only [length]
    | y :: y' :: ys =>
      by cases split_length_snd (y :: y' :: ys) with
      | inl _ => contradiction
      | inr h =>
        simp only [length] at *
        apply Nat.lt.step
        apply Nat.succ_lt_succ
        exact h 
  
  let xs_split := split (x₁ :: x₂ :: xs)
  mergeWith cmp (mergeSortWith cmp (xs_split.fst),
                  mergeSortWith cmp (xs_split.snd))
termination_by mergeSortWith cmp xs => xs.length

-- theorem List.length_map : ∀ (xs : List α) (f : α → β),
--     List.length (List.map f xs) = List.length xs
-- | [], _ => rfl
-- | (x :: xs), f => congrArg _ (length_map xs f)

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
  by
  simp only [List.zip, List.zipWith]
  -- TODO: how do you "refold" a definition in Lean 4?
  have aux : List.zipWith Prod.mk xs ys = List.zip xs ys := rfl
  rw [aux]
  simp only [List.length]
  apply congrArg (λ x => x + 1)
  apply ih

theorem List.length_prod : ∀ (xs : List α) (ys : List β),
  List.length (List.prod xs ys) = xs.length * ys.length
| [], _ => by simp [prod, length]
| x :: xs, [] => by simp [prod, length]
| [x], y :: ys =>
  have ih := length_prod [x] ys
  by simp only [prod]
     unfold length  -- `simp only [length]` does bad things
     simp only
     rw [ih]
     simp only [length]
     rw [Nat.one_mul, Nat.one_mul]
| x :: x' :: xs, y :: ys =>
  -- TODO: could probably consolidate these with the List.prod helper lemmas
  -- (there are some slight discrepancies due to specifying `y :: ys`)
  have h_term₁ : Nat.succ 0 + Nat.succ (length ys) <
                 Nat.succ (Nat.succ (length xs)) + Nat.succ (length ys) :=
    by apply Nat.add_lt_add_of_lt
       apply Nat.succ_lt_succ $ Nat.succ_pos (length xs)
  have h_term₂ : Nat.succ (length xs) + Nat.succ (length ys) <
                 Nat.succ (Nat.succ (length xs)) + Nat.succ (length ys) :=
    by apply Nat.add_lt_add_of_lt
       apply Nat.succ_lt_succ
       apply Nat.lt.base
  have ih₁ := length_prod [x] (y :: ys)
  have ih₂ := length_prod (x' :: xs) (y :: ys)
  by unfold prod
     simp only
     rw [List.length_append, ih₁, ih₂]
     simp only [length]
     rw [←Nat.add_mul, Nat.zero_add, Nat.add_comm 1]
termination_by List.length_prod xs ys => xs.length + ys.length

theorem List.length_drop : ∀ (n : Nat) (xs : List α),
  n < xs.length → length (drop n xs) = length xs - n
| 0, _, _ => by simp only [drop, Nat.sub_zero]
| n + 1, x :: xs, h =>
  have ih := length_drop n xs (Nat.lt_of_succ_lt_succ h)
  by simp only [drop, Nat.add, length]
     rw [Nat.succ_sub_succ_eq_sub]
     exact ih

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

theorem List.sublist_self : ∀ (xs : List α), Sublist xs xs
| [] => Sublist.nil
| x :: xs => Sublist.cons2 x xs xs (sublist_self xs)

theorem List.empty_sublist : ∀ (xs : List α), Sublist [] xs
| [] => Sublist.nil
| x :: xs => Sublist.cons x [] xs $ empty_sublist xs

-- This shouldn't need to be this verbose -- is something up with the defeqs for
-- `sieve`?
theorem List.sieve_sublist : (bs : List Bool) → (xs : List α) →
  Sublist (List.sieve bs xs) xs
| [], [] => Sublist.nil
| [], x :: xs => List.sublist_self (x :: xs)
| true :: bs, [] => Sublist.nil
| false :: bs, [] => Sublist.nil
| true :: bs, x :: xs => Sublist.cons2 x (sieve bs xs) xs (sieve_sublist bs xs)
| false :: bs, x :: xs => Sublist.cons x (sieve bs xs) xs (sieve_sublist bs xs)

theorem List.sublist_of_map_sublist :
  (xs : List α) → (ys : List α) → (f : α → β) → Sublist xs ys →
    Sublist (xs.map f) (ys.map f)
| [], ys, f, h => empty_sublist (map f ys)
| xs, x :: ys, f, Sublist.cons _ _ _ h =>
  have ih := sublist_of_map_sublist xs ys f h
  Sublist.cons (f x) (map f xs) (map f ys) ih
| x :: xs, _ :: ys, f, Sublist.cons2 _ _ _ h =>
  have ih := sublist_of_map_sublist xs ys f h
  Sublist.cons2 (f x) (map f xs) (map f ys) ih

theorem List.removeAll_singleton_hd_eq [DecidableEq α] :
  ∀ (x: α) (xs : List α), removeAll (x :: xs) [x] = removeAll xs [x] :=
by intros x xs
   simp [removeAll, filter, filterAux, notElem, elem]

theorem List.filterAux_acc_eq_rev_append : ∀ (p : α → Bool) (xs as bs : List α),
  filterAux p xs (bs ++ as) = reverse as ++ filterAux p xs bs
| p, [], as, bs => by simp [filterAux]
| p, xs, [], bs => by simp [filterAux]
| p, x :: xs, a :: as, bs =>
  have ih_true := filterAux_acc_eq_rev_append p xs (a :: as) (x :: bs)
  have ih_false := filterAux_acc_eq_rev_append p xs (a :: as) bs
  by simp only [filterAux]
     cases p x with
     | true => simp only; apply ih_true
     | false => simp only; apply ih_false

theorem List.removeAll_singleton_hd_neq {α : Type _} [BEq α] :
  ∀ (x : α) (y : α) (xs : List α),
    ((x == y) = false) → removeAll (x :: xs) [y] = x :: removeAll xs [y] :=
by intros x y xs hneq
   simp only [removeAll, filter, filterAux, notElem, elem, hneq]
   exact filterAux_acc_eq_rev_append _ xs [x] []

theorem List.sieve_removeAll : (bs : List Bool) → (xs : List α) →
  length bs = length xs →
    length (sieve bs xs) = length (removeAll bs [false])
| [], [], h => rfl
| b :: bs, [], h => by cases h
| [], x :: xs, h => by cases h
| true :: bs, x :: xs, h =>
  have ih := sieve_removeAll bs xs (Nat.succ.inj h)
  by rw [removeAll_singleton_hd_neq]
     . simp only [length]
       apply congrArg (λ x => x + 1)
       exact ih
     . simp only
| false :: bs, x :: xs, h =>
  have ih := sieve_removeAll bs xs (Nat.succ.inj h)
  by rw [removeAll_singleton_hd_eq]
     . simp only [length, sieve]
       exact ih

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
termination_by length_mergeSortWith cmp xs => xs.length

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

-- I suspect this is probably built in somewhere, but I'm not finding it
-- def Int.abs (z : Int) := if z < 0 then -z else z

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
   simp only at h
   cases n with
   | ofNat n => contradiction
   | negSucc n =>
     simp only [abs]
     unfold HSub.hSub
     unfold instHSub
     unfold Sub.sub
     unfold Int.instSubInt
     unfold Int.sub
     simp only
     rw [neg_succ_eq_neg_ofNat_succ]
