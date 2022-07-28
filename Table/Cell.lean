universe u u_η

inductive Cell {η : Type u_η}
               [DecidableEq η]
               (name : η)
               (τ : Type u)    : Type (max u u_η)
| emp : Cell name τ
| val : τ → Cell name τ

variable {η : Type u_η} [dec_η : DecidableEq η]

namespace Cell

def toOption {nm τ} : @Cell η dec_η nm τ → Option τ
| Cell.emp => Option.none
| Cell.val x => Option.some x

def fromOption {nm τ} : Option τ → @Cell η dec_η nm τ
| none => emp
| some x => val x

def name {nm τ} (_ : @Cell η dec_η nm τ) : η :=
  nm
def type {nm τ} (_ : @Cell η dec_η nm τ) := τ

def rename {nm τ} : Cell (η := η) nm τ → (nm' : η) → Cell nm' τ
| Cell.emp, nm => Cell.emp
| Cell.val x, nm => Cell.val x

end Cell

-- Decidable equality
instance {nm : η} {τ : Type u} [inst : DecidableEq τ] : DecidableEq (Cell nm τ)
| Cell.emp, Cell.emp => isTrue rfl
| Cell.emp, (Cell.val x) => isFalse (λ hneg => Cell.noConfusion hneg)
| (Cell.val x), Cell.emp => isFalse (λ hneg => Cell.noConfusion hneg)
| (Cell.val x), (Cell.val y) =>
  Eq.mpr (congrArg Decidable $ Cell.val.injEq x y) (inst x y)
