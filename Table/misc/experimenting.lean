inductive UniqueList (α : Type _) [inst : DecidableEq α] : (h : α → Bool) → Type _
| nil : @UniqueList α inst (λ _ => true)
| cons {p'} : (c : α)
                → (h : p' c = true)
                → @UniqueList α inst p'
                → @UniqueList α inst (λ x => x ≠ c && p' x)

-- How is this possible?
#reduce UniqueList.cons 3 (by
  simp
) (UniqueList.cons 3 ( by
 simp
) UniqueList.nil)

#check UniqueList.cons 3 _ (UniqueList.cons 3 _ (UniqueList.cons 3 _ UniqueList.nil))
#reduce UniqueList.cons 3 _ (UniqueList.cons 3 _ (UniqueList.cons 3 _ UniqueList.nil))

#reduce UniqueList.cons 4 (UniqueList.cons 3 (UniqueList.cons 2 UniqueList.nil))
#reduce UniqueList.cons () (UniqueList.cons () UniqueList.nil)

#reduce List.get [2,4] ⟨1, _⟩

-- See if List.nodup exists in Lean 4

def List.distinct {α : Type _} [DecidableEq α] : List α → Bool
| [] => true
| (x::xs) => not (elem x xs) && distinct xs

def UniqueList2 (α : Type _) [DecidableEq α] := {xs : List α // List.distinct xs}
macro "unique" : tactic => `(simp [List.distinct] <;> trace "list contains duplicates")

def xs : UniqueList2 Nat := ⟨[3,4,5], by unique⟩
def xs2 : UniqueList2 Nat := ⟨[3,4,5,2, 3], by unique⟩
