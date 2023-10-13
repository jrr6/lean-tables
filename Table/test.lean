
def foldl : (α → β → β) → β → List α → β
| _, z, [] => z
| f, z, x :: xs => foldl f (f x z) xs

def foldr : (α → β → β) → β → List α → β
| _, z, [] => z
| f, z, x :: xs => f x (foldr f z xs)

def comm_assoc (f : α → β → β) := ∀ (a b : α) (c : β), f a (f b c) = f b (f a c)

theorem foldr_helper :
  ∀ (g : α → β → β) (hg : comm_assoc g) (z : β) (x : α) (xs : List α),
    foldr g (g x z) xs = g x (foldr g z xs) := by
  intros g hg z x xs
  induction xs generalizing z with
  | nil => simp only [foldl, foldr]
  | cons y xs ih => rw [foldr, ih, foldr, hg]

theorem kaz : ∀ (g : α → β → β) (hg : comm_assoc g) (z : β) (xs : List α),
    foldl g z xs = foldr g z xs := by
  intros g hg z xs
  induction xs generalizing z with
  | nil => simp [foldl, foldr]
  | cons x xs ih =>
    rw [foldl, ih, foldr]
    apply foldr_helper _ hg

theorem plus_comm_assoc : comm_assoc Nat.add := by
  intros a b c
  simp
  rw [←Nat.add_assoc, Nat.add_comm a, Nat.add_assoc]

-- #check Int.ofString
