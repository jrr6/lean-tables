universe u v
-- variable (header : Type) (sort : Type (u + 1))

inductive DepList : List (Sort u) → Sort (u + 1)
| nil : DepList []
| cons {α : Sort u} {βs : List (Sort u)} : α → DepList βs → DepList (α :: βs)

def DepList.append {αs βs} : DepList αs → DepList βs → DepList (List.append αs βs)
| DepList.nil, ys => ys
| (DepList.cons x xs), ys => DepList.cons x (append xs ys)

def DepList.singleton {α} (x : α) := DepList.cons x DepList.nil

inductive Member : α → List α → Type _
| hd {a as} : Member a (a :: as)
| tl {a b bs} : Member a bs → Member a (b :: bs)

-- See here:
-- https://leanprover.github.io/lean4/doc/examples/deBruijn.lean.html
inductive HList {α : Type v} (β : α → Type u) : List α → Type (max u v)
| nil : HList β []
| cons {i is} : β i → HList β is → HList β (i::is)

def HList.get {α} {β : α → Type u} {i is} : HList β is → Member i is → β i
| HList.cons a as, Member.hd => a
| HList.cons a as, Member.tl h => as.get h

#reduce @HList.get _ _ "key" _ (@HList.cons String (λ x => Nat) "key" [] 63 HList.nil) (by apply Member.hd)

-- This is rather unhelpful b/c it just gets the first element of the specified
-- type, but it's a POC anyway
def DepList.get {αs : List (Sort u)} : DepList αs → Member α αs → α
| DepList.cons a as, Member.hd => a
| DepList.cons a as, Member.tl h => as.get h

#reduce @DepList.get Nat _ (DepList.cons "hi" (DepList.cons true (DepList.cons 31 (DepList.cons () DepList.nil)))) (by
  apply Member.tl
  apply Member.tl
  apply Member.hd
)
