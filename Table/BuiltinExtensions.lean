-- Variant on orElse that's useful for de-option-ifying cell values
def Option.orDefault {α} [Inhabited α] : Option α → α
| some x => x
| none => default

-- List utilities
inductive List.All {α} (p : α → Prop) : List α → Prop
| vac      : All p []
| cons {x xs} : p x → All p xs → All p (x::xs)

-- Nifty, but hard to write proofs over
-- def List.prod {α β} (xs : List α) (ys : List β) : List (α × β) :=
--   List.foldl List.append [] (List.map (λ x => List.map (λ y => (x, y)) ys) xs)

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
  have h₁ : Nat.succ 0 + length ys < Nat.succ (Nat.succ (length xs)) + length ys :=
    by apply Nat.add_lt_add_of_lt
       apply Nat.succ_lt_succ $ Nat.succ_pos (length xs)
  have h₂ : Nat.succ (length xs) + length ys < Nat.succ (Nat.succ (length xs)) + length ys :=
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

-- TODO: I refuse to believe there isn't a simpler way to do this
def List.verifiedEnum : (xs : List α) → List ({n : Nat // n < xs.length} × α)
| [] => []
| z :: zs =>
  let xs := z :: zs;
  let rec vEnumFrom : (ys : {ys : List α // ys.length ≤ xs.length})
                      → {n : Nat // n < ys.val.length}
                      → List ({n : Nat // n < xs.length} × α)
                      → List ({n : Nat // n < xs.length} × α)
    | ⟨[], h⟩, n, acc => acc
    | ⟨y :: ys, hys⟩, ⟨0, hn⟩, acc => ((⟨0, @Nat.lt_of_lt_of_le 0 (length ys + 1) (length xs) (Nat.zero_lt_succ (length ys)) hys⟩, y) :: acc)
    | ⟨y :: ys, hys⟩, ⟨Nat.succ n, hn⟩, acc => vEnumFrom ⟨ys, @Nat.le_trans (length ys) (length ys + 1) (length xs) (Nat.le_succ (length ys)) hys⟩
                                        ⟨n, Nat.lt_of_succ_lt_succ hn⟩
                                        ((⟨Nat.succ n, Nat.lt_of_lt_of_le hn hys⟩, y) :: acc)
    vEnumFrom ⟨xs, Nat.le_refl (length xs)⟩ ⟨length xs - 1, by apply Nat.sub_succ_lt_self; apply Nat.zero_lt_succ⟩ []
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

def List.merge_with {α} : (α → α → Ordering) → List α × List α → List α
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
  | Ordering.gt => y :: merge_with cmp (x :: xs, ys)
  | _ => x :: merge_with cmp (xs, y :: ys)
termination_by merge_with cmp prd => prd.fst.length + prd.snd.length

def List.merge_sort_with {α} : (α → α → Ordering) → List α → List α
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
  merge_with cmp (merge_sort_with cmp (xs_split.fst), merge_sort_with cmp (xs_split.snd))
termination_by merge_sort_with cmp xs => xs.length

theorem List.length_map : ∀ (xs : List α) (f : α → β),
    List.length (List.map f xs) = List.length xs
| [], _ => rfl
| (x :: xs), f => congrArg _ (length_map xs f)

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
  have h_term₁ : Nat.succ 0 + Nat.succ (length ys) < Nat.succ (Nat.succ (length xs)) + Nat.succ (length ys) :=
    by apply Nat.add_lt_add_of_lt
       apply Nat.succ_lt_succ $ Nat.succ_pos (length xs)
  have h_term₂ : Nat.succ (length xs) + Nat.succ (length ys) < Nat.succ (Nat.succ (length xs)) + Nat.succ (length ys) :=
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
  have ih : length (take n xs) = n := length_take n xs (Nat.lt_of_succ_lt_succ h)
  by simp only [take, length]
     apply congrArg Nat.succ ih

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
