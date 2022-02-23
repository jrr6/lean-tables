universe u
-- variable (header : Type) (sort : Type (u + 1))

inductive DepList : List (Sort u) → Sort (u + 1)
| nil : DepList []
| cons {α : Sort u} {βs : List (Sort u)} : α → DepList βs → DepList (α :: βs)

def DepList.append {αs βs} : DepList αs → DepList βs → DepList (List.append αs βs)
| DepList.nil, ys => ys
| (DepList.cons x xs), ys => DepList.cons x (append xs ys)

def DepList.singleton {α} (x : α) := DepList.cons x DepList.nil
