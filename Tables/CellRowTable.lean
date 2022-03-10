universe u_η
universe u

def Stringable (τ : Type u) [inst : ToString τ] : Type u × ToString τ := (τ, inst)

-- Row/Cell setup based on Stephanie Weirich, "Dependent Types in Haskell,"
-- https://www.youtube.com/watch?v=wNa3MMbhwS4
-- Code!:
-- https://github.com/sweirich/dth/blob/master/regexp/src/OccDict.hs

def Header {η} := (η × Type u)
def Schema {η} := List (@Header η)

def Schema.names {η : Type u_η} := List.map (@Prod.fst η (Type u))

inductive Cell {η : Type u_η} [DecidableEq η] (name : η) (τ : Type u) : Type (max u u_η)
| emp : Cell name τ
| val : τ → Cell name τ

def Cell.toOption {η nm τ} [dec_η : DecidableEq η] : @Cell η dec_η nm τ → Option τ
| Cell.emp => Option.none
| Cell.val x => Option.some x

-- Lingering question: should rows have a built-in indexing scheme? (Probably.)
-- Should tables contain their number of rows and columns at type level? (Also
-- probably.)

inductive Row {η : Type u_η} [DecidableEq η] : Schema → Type (max u_η (u + 1))
| nil : Row []
| cons {name : η} {τ : Type u} {hs : Schema} :
    Cell name τ → Row hs → Row ((name, τ) :: hs)

structure Table {η : Type u_η} [DecidableEq η] (hs : @Schema η) where
  rows : List (Row hs)

variable {η : Type u_η} [dec_η : DecidableEq η] {schema : @Schema η}

def Row.append {schema₁ schema₂} :
    @Row η _ schema₁ → Row schema₂ → Row (List.append schema₁ schema₂)
| Row.nil, rs₂ => rs₂
| Row.cons r₁ rs₁, rs₂ => Row.cons r₁ (append rs₁ rs₂)

def Row.singleCell {name τ} (x : τ) :=
  @Row.cons η dec_η name τ [] (Cell.val x) Row.nil

def List.prod {α β} (xs : List α) (ys : List β) : List (α × β) :=
  List.foldl List.append [] (List.map (λ x => List.map (λ y => (x, y)) ys) xs)

-- inductive Schema.HasCol {η : Type u_η} : η → @Schema η → Prop
-- | hd {c : η} {τ : Type u} {rs : Schema} : HasCol c ((c, τ) :: rs)
-- | tl {r c rs} : HasCol c rs → HasCol c (r::rs)

inductive Schema.HasCol {η : Type u_η} : @Header η → @Schema η → Prop
| hd {c : η} {τ : Type u} {rs : Schema} : HasCol (c, τ) ((c, τ) :: rs)
| tl {r c τ rs} : HasCol (c, τ) rs → HasCol (c, τ) (r::rs)

-- inductive List.In {α} : α → List α → Prop
-- | hd {e xs} : In e (e::xs)
-- | tl {x y xs} : In y xs → In y (x::xs)

-----------------------------------TESTING--------------------------------------
def Row.repr {η} [ToString η] [DecidableEq η]: {xs : @Schema η} → Row xs → String
| [], Row.nil => ""
| (nm, x) :: xs, Row.cons val d => (toString nm) ++ ": something, " ++ repr d

#check Cell "hi" Nat

def x : Cell "hi" Nat := Cell.val 42

#eval Row.repr (Row.cons x Row.nil)
--------------------------------------------------------------------------------

def emptyTable {α : Type u₁} [hα : DecidableEq α] : @Table α hα [] :=
  Table.mk []

def addRows (t : Table schema) (r : List (Row schema)) : Table schema :=
  {rows := List.append t.rows r}

def addColumn {τ} (t : Table schema) (c : η) (vs : List τ) :
    Table (List.append schema [(c, τ)]) :=
  {rows := (List.map (λ (olds, new) =>
                      Row.append olds (Row.singleCell new))
                      -- @DepList.append (List.map Prod.snd schema) [c.snd] olds (DepList.singleton new))
                      (List.zip t.rows vs))}

def buildColumn {τ} (t : Table schema) (c : η) (f : Row schema → τ) :=
  addColumn t c (List.map f t.rows)

def vcat (t1 : Table schema) (t2 : Table schema) : Table schema :=
  {rows := List.append t1.rows t2.rows}

def hcat {schema₁ schema₂}
               (t1 : @Table η dec_η schema₁) (t2 : @Table η dec_η schema₂) :
                  @Table η dec_η (List.append schema₁ schema₂) :=
  {rows := List.map (λ (r1, r2) => Row.append r1 r2) (List.zip t1.rows t2.rows)}

def values (rs : List (Row schema)) : Table schema := {rows := rs}

def crossJoin {schema₁ schema₂}
              (t1 : @Table η dec_η schema₁) (t2 : @Table η dec_η schema₂) :
                @Table η dec_η (List.append schema₁ schema₂) :=
  {rows := List.map (λ (c1, c2) => Row.append c1 c2)
                        (List.prod t1.rows t2.rows)}

def leftJoin : False := sorry -- TODO:

def nrows (t : Table schema) : Nat := List.length t.rows

def ncols (t : Table schema) : Nat := List.length schema

def header (t : Table schema) : List η := List.map Prod.fst schema

-- TODO: might be nicer to build the row/column indexing into the Table type
-- itself?
-- TODO: eliminate sorry
def getRow : (t : Table schema) → Nat → (n < nrows t) → Row schema
| {rows := []}, n, h => absurd h (by
      intro nh
      simp [nrows] at nh
      apply Nat.not_lt_zero _ nh
    )
| {rows := r::rs}, 0, h => r
| {rows := r::rs}, Nat.succ n, h => getRow {rows := rs} n (by sorry : n < nrows {rows := rs})

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

-- Emulating Stephanie Weirich's approach:
class Gettable {c τ} (h : Schema.HasCol (c, τ) schema) where
  getp : Row schema → Option τ

@[instance] def gettableHd {c τ}: @Gettable η dec_η ((c,τ)::schema) c τ (@Schema.HasCol.hd η c τ schema) :=
  {getp := λ (Row.cons c _) => c.toOption}

-- TODO: I hate typeclasses, but maybe this will work...
@[instance] def gettableTl {c τ h r} [cls : Gettable h] : @Gettable η dec_η (r::schema) c τ (Schema.HasCol.tl h) :=
  {getp := λ (Row.cons c cs) => cls.getp h cs}

def getValue_class_inst (r : Row schema) (c : η) {τ} (h : Schema.HasCol (c, τ) schema) [inst : Gettable h] : Option τ := inst.getp h r

def getValue_class (r : Row schema) (c : η) {τ} (h : @Schema.HasCol η (c, τ) schema) :=
  match h with
  | Schema.HasCol.hd => Schema.HasCol.hd.getp r
  | Schema.HasCol.tl h => (Schema.HasCol.tl h).getp r

-- THIS SHOULD WORK!!! Right...?
def get_from_proof {schema} {c : η} {τ : Type u} : Schema.HasCol (c, τ) schema → Row schema → Option τ
| Schema.HasCol.hd, Row.cons cell cells => cell.toOption
| Schema.HasCol.tl h, Row.cons cell cells => get_from_proof h cells

-------------------------------------------------------------------------------

-- Testing, etc.

#reduce addRows (addColumn emptyTable "name" []) [Row.singleCell "hello"]
#reduce getValue_class_inst (Row.append
        (@Row.singleCell String _ "pi" (List Nat) [3,1,4,1,5])
        (@Row.singleCell String _ "age" Nat 20))
        "age" (by
        apply Schema.HasCol.tl
        apply Schema.HasCol.hd
        )
