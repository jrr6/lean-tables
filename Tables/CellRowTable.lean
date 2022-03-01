universe u_η
universe u

def Stringable (τ : Type u) [inst : ToString τ] : Type u × ToString τ := (τ, inst)

-- Row/Cell setup based on Stephanie Weirich, "Dependent Types in Haskell,"
-- https://www.youtube.com/watch?v=wNa3MMbhwS4

def Header {η} := (η × Type u)
def Schema {η} := List (@Header η)

def Schema.names {η : Type u_η} := List.map (@Prod.fst η (Type u))

inductive Cell {η : Type u_η} [DecidableEq η] (name : η) (τ : Type u) : Type (max u u_η)
| emp : Cell name τ
| val : τ → Cell name τ

def Cell.toOption {η nm τ} [dec_η : DecidableEq η] : @Cell η dec_η nm τ → Option τ
| Cell.emp => Option.none
| Cell.val x => Option.some x

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

inductive Schema.HasCol {η : Type u_η} : η → @Schema η → Prop
| hd {c : η} {τ : Type u₁} {rs : Schema} : HasCol c ((c, τ) :: rs)
| tl {c r rs} : HasCol c rs → HasCol c (r::rs)

inductive List.In {α} : α → List α → Prop
| hd {e xs} : In e (e::xs)
| tl {x y xs} : In y xs → In y (x::xs)

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

def leftJoin : False := sorry -- TODO

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

-- Given a schema, returns the type associated with a given header therein
def typeForHeader : (s : @Schema η) → (header : η) → List.In header (Schema.names s) → Type u
| [], header, h => absurd h (λ nh => by cases h)
| (nm, τ)::s₂, header, h => dite (nm = header)
                                 (λ _ => τ) 
                                 (λ nh => typeForHeader s₂ header (by
                                     cases h with
                                     | hd => contradiction
                                     | tl h => exact h
                                 ))

-- TODO: this is a nightmare... -- uniqueness might help?
-- TODO: eliminate sorry
def getValue_test : Row schema → (c : η) → Option (typeForHeader schema c sorry)
| Row.nil, _ => Option.none
| @Row.cons _ _ nm _ _ cell cells, c => if nm = c then cell.toOption else getValue cells c

def getValue_test2 : Row schema → (c : η) → List.In c (Schema.names schema) → Option (typeForHeader schema c sorry)
| Row.nil, _ => Option.none
| @Row.cons _ _ nm _ _ cell cells, c => if nm = c then cell.toOption else getValue cells c

#check @Row.cons

def getValue : {nm : η} → {τ : Type u} → {xs : @Schema η} → Row ((nm, τ)::xs) → η → Option (typeForHeader xs nm sorry)
| _, _, [], _, _ => Option.none
| _, _, (nm, τ)::xs, Row.cons cell cells, c => if nm = c
                                         then cell.toOption
                                         else match xs with
                                              | [] => Option.none
                                              | (nm₂, τ₂)::ys => @getValue nm₂ τ₂ ys cells c

-- Testing, etc.

#reduce addRows (addColumn emptyTable "name" []) [Row.singleCell "hello"]
