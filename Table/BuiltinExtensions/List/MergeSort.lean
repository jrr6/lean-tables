/-!
Merge sort for lists. This implementation was written before merge-sort was
added to the library; we continue to use it because of proof dependencies.
-/

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

theorem List.length_mergeWith : ∀ (cmp : α → α → Ordering)
                                   (xs ys : List α),
  length (mergeWith cmp (xs, ys)) = length xs + length ys
| cmp, [], ys => by simp only [mergeWith, length, Nat.zero_add]
| cmp, x :: xs, [] => by simp only [mergeWith, length]
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
termination_by _ xs ys => xs.length + ys.length

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
| _, [] => by simp only [mergeSortWith]
| _, [x] => by simp only [mergeSortWith]
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
