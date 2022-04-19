-- LATER SET ATTEMPT:
theorem get_with_lookup_should_work {c : η} {τ : Type u} {xs : List (@Header η)}
  {h : Schema.HasName c ((c, τ) :: xs)} : (Schema.lookup ((c, τ) :: xs) ⟨c, h⟩).snd = τ := by
  simp [Schema.lookup, Prod.snd]

def get_with_lookup {schema : @Schema η} {c : η}
    : (h : Schema.HasName c schema) → (r : Row schema) → Option (schema.lookup ⟨c, h⟩).snd
| Schema.HasName.hd, @Row.cons _ _ _ τ _ cell cells =>
    have _ : (Schema.lookup ((c, τ) :: _) ⟨c, _⟩).snd = τ := by apply get_with_lookup_should_work;
    (cell.toOption : Option τ)
| Schema.HasName.tl h, Row.cons cell cells => get_with_lookup h cells

-- inductive Schema.HasCol {η : Type u_η} : η → @Schema η → Prop
-- | hd {c : η} {τ : Type u} {rs : Schema} : HasCol c ((c, τ) :: rs)
-- | tl {r c rs} : HasCol c rs → HasCol c (r::rs)

-- inductive List.In {α} : α → List α → Prop
-- | hd {e xs} : In e (e::xs)
-- | tl {x y xs} : In y xs → In y (x::xs)

--------------------------------------------------------------------------------
-- MAYHEM HENCEFORTH ENSUES:

-- Given a schema, returns the type associated with a given header therein
-- TODO: I just want the match to work...see how Haskell does it...
def typeForHeader : (s : @Schema η) → (header : η) → s.HasCol header → Type u
| (nm, τ)::s₂, header, Schema.HasCol.hd => τ
| (nm, τ)::s₂, header, h => typeForHeader s₂ header (by cases h with
                                                         | hd => contradiction
                                                         | tl h => exact h)

-- def getValue_test3 {nm τ}: Row ((nm, τ) :: schema) → (c : η) → (h : Schema.HasCol c ((nm, τ) :: schema)) → Option (
--   match h with
--   | Schema.HasCol.hd => τ
--   | Schema.HasCol.tl hs => sorry
-- )
-- | @Row.cons _ _ nm _ _ cell cells, c => if nm = c then cell.toOption else getValue_test3 cells c

-- | (nm, τ)::s₂, header, h => dite (nm = header)
--                                  (λ _ => τ) 
--                                  (λ nh => typeForHeader s₂ header (by
--                                      cases h with
--                                      | hd => contradiction
--                                      | tl h => exact h
--                                  ))

-- TODO: this is a nightmare... -- uniqueness might help? --> Haskell example
-- seems to case on the proof itself (i.e., to determine if we're at the matching
-- element --- may also obviate the need for equality checking?)?...
-- TODO: eliminate sorry
def getValue_test : Row schema → (c : η) → Option (typeForHeader schema c sorry)
| Row.nil, _ => Option.none
| @Row.cons _ _ nm _ _ cell cells, c => if nm = c then cell.toOption else getValue_test cells c

def getValue_test2 : Row schema → (c : η) → schema.HasCol c → Option (typeForHeader schema c sorry)
| Row.nil, _, _ => Option.none
| @Row.cons _ _ nm _ _ cell cells, c, _ => if nm = c then cell.toOption else getValue_test2 cells c

#check @Row.cons

def getValue : {nm : η} → {τ : Type u} → {xs : @Schema η} → Row ((nm, τ)::xs) → η → Option (typeForHeader xs nm sorry)
| _, _, [], _, _ => Option.none
| _, _, (nm, τ)::xs, Row.cons cell cells, c => if nm = c
                                         then cell.toOption
                                         else match xs with
                                              | [] => Option.none
                                              | (nm₂, τ₂)::ys => @getValue nm₂ τ₂ ys cells c

-- This seems really promising! But no...
def getValue_test4 {schema₁ : @Schema η} {τ : Type u} : Row schema₁ → (c : η) → schema.HasCol (c, τ) → Option τ
| Row.cons cell _, _, Schema.HasCol.hd => cell.toOption
| Row.cons cell cells, c, Schema.HasCol.tl h => getValue_test4 cells c h

-- THIS WILL NEVER WORK! YOU CAN'T ASSUME IT'S THE FIRST THING IN THE SCHEMA!
def getValue_test5 {nm : η} {τ : Type u} {xs : @Schema η} : Row ((nm, τ)::xs) → (c : η) → schema.HasCol (c, τ) → Option τ
| Row.cons cell _, _, Schema.HasCol.hd => cell.toOption
| Row.cons cell cells, c, Schema.HasCol.tl h => match cells with
                                                | Row.nil => Option.none  -- TODO: this is an impossible case
                                                | @Row.cons _ _ nm₂ τ₂ s₂ _ ys => @getValue_test5 nm₂ τ₂ _ ys cells c

def getValue_class (r : Row schema) (c : η) {τ} (h : @Schema.HasCol η (c, τ) schema) :=
  match h with
  | Schema.HasCol.hd => Schema.HasCol.hd.getp r
  | Schema.HasCol.tl h => (Schema.HasCol.tl h).getp r

-- THIS SHOULD WORK!!! Right...?
def get_from_proof {schema} {c : η} {τ : Type u} : Schema.HasCol (c, τ) schema → Row schema → Option τ
| Schema.HasCol.hd, Row.cons cell cells => cell.toOption
| Schema.HasCol.tl h, Row.cons cell cells => get_from_proof h cells
