inductive UniqueList (α : Type _) [inst : DecidableEq α] : {h : α → Bool} → Type _
| nil : @UniqueList α inst (λ _ => true)
| cons {p'} : (c : α)
                → {h : p' c = true}
                → @UniqueList α inst p'
                → @UniqueList α inst (λ x => x ≠ c && not (p' x))


-- How is this possible?
#check UniqueList.cons 3 (UniqueList.cons 3 (UniqueList.cons 3 UniqueList.nil))
#reduce UniqueList.cons 3 (UniqueList.cons 3 (UniqueList.cons 3 UniqueList.nil))
#reduce UniqueList.cons () (UniqueList.cons () UniqueList.nil)

def List.distinct {α : Type _} [DecidableEq α] : List α → Bool
| [] => true
| (x::xs) => not (elem x xs) && distinct xs

def UniqueList2 (α : Type _) [DecidableEq α] := {xs : List α // List.distinct xs}
macro "unique" : tactic => `(simp [List.distinct] <;> trace "failed")

def xs : UniqueList2 Nat := ⟨[3,4,5], by simp⟩
def xs2 : UniqueList2 Nat := ⟨[3,4,5,2], by simp⟩
