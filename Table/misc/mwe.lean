universe u_η u

-- Types
def Header {η} := (η × Type u)
def Schema {η} := List (@Header η)

inductive Cell {η : Type u_η} [DecidableEq η] (name : η) (τ : Type u) : Type (max u u_η)
| emp : Cell name τ
| val : τ → Cell name τ

inductive Row {η : Type u_η} [DecidableEq η] : Schema → Type (max u_η (u + 1))
| nil : Row []
| cons {name : η} {τ : Type u} {hs : Schema} :
    Cell name τ → Row hs → Row ((name, τ) :: hs)

structure Table {η : Type u_η} [DecidableEq η] (hs : @Schema η) where
  rows : List (Row hs)

-- Predicates
inductive Schema.HasCol {η : Type u_η} : @Header η → @Schema η → Prop
| hd {c : η} {τ : Type u} {rs : Schema} : HasCol (c, τ) ((c, τ) :: rs)
| tl {r c τ rs} : HasCol (c, τ) rs → HasCol (c, τ) (r::rs)

inductive Schema.HasName : η → @Schema η → Prop
| hd {c : η} {rs : Schema} {τ : Type u} : HasName c ((c, τ) :: rs)
| tl {r c rs} : HasName c rs → HasName c (r::rs)

def CertifiedName (schema : @Schema η) := {c : η // Schema.HasName c schema}

-- Utility functions
-- Converts a cell to an option
def Cell.toOption {η nm τ} [dec_η : DecidableEq η] : @Cell η dec_η nm τ → Option τ
| Cell.emp => Option.none
| Cell.val x => Option.some x

-- Returns the schema entry with the specified name
def Schema.lookup {η : Type u_η} [DecidableEq η] : (s : @Schema η) → CertifiedName s → @Header η
| [], ⟨c, hc⟩ => absurd hc (by cases hc)
| (nm, τ)::hs, ⟨c, hc⟩ => dite (nm = c)
                               (λ _ => (nm, τ))
                               (λ h => lookup hs ⟨c, by
                                  cases hc with
                                  | hd => contradiction
                                  | tl in_hs => exact in_hs
                                  ⟩)

variable {η : Type u_η} [dec_η : DecidableEq η] {schema : @Schema η}

def get_from_proof {schema : @Schema η} {c : η} {τ : Type u}
    : Schema.HasCol (c, τ) schema → Row schema → Option τ
| Schema.HasCol.hd, Row.cons cell cells => cell.toOption
| Schema.HasCol.tl h, Row.cons cell cells => get_from_proof h cells

/- Mapping to the get_with_lookup error message:
τ = x✝
xs = x✝¹
h = _
-/ 
theorem get_with_lookup_should_work {c : η}
                                    {τ : Type u}
                                    {xs : List (@Header η)}
                                    {h : Schema.HasName c ((c, τ) :: xs)}
      : (Schema.lookup ((c, τ) :: xs) ⟨c, h⟩).snd = τ :=
  by simp [Schema.lookup, Prod.snd]

def get_with_lookup {schema : @Schema η} {c : η}
    : (h : Schema.HasName c schema) → (r : Row schema) → Option (schema.lookup ⟨c, h⟩).snd
| Schema.HasName.hd, Row.cons cell cells => cell.toOption
| Schema.HasName.tl h, Row.cons cell cells => get_with_lookup h cells
