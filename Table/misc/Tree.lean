-- Use an RBT or something more effecient eventually...
universe u₁ u₂

inductive DTree {κ : Type u₁} : Sort (max (u₁ + 2) (u₂ + 1))
| node {α : Sort u₂} : κ → α → DTree → DTree → DTree
| empty

#check DTree.node "hi" 3 DTree.empty (DTree.node "hi" [2,3] DTree.empty DTree.empty)


