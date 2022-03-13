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

inductive Schema.HasCol {η : Type u_η} : @Header η → @Schema η → Prop
| hd {c : η} {τ : Type u} {rs : Schema} : HasCol (c, τ) ((c, τ) :: rs)
| tl {r c τ rs} : HasCol (c, τ) rs → HasCol (c, τ) (r::rs)

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


-- Emulating Stephanie Weirich's approach:
class Gettable {c τ} (h : Schema.HasCol (c, τ) schema) where
  getp : Row schema → Option τ

@[instance] def gettableHd {c τ}: @Gettable η dec_η ((c,τ)::schema) c τ (@Schema.HasCol.hd η c τ schema) :=
  {getp := λ (Row.cons c _) => c.toOption}

@[instance] def gettableTl {c τ h r} [cls : Gettable h] : @Gettable η dec_η (r::schema) c τ (Schema.HasCol.tl h) :=
  {getp := λ (Row.cons c cs) => cls.getp h cs}

-- TODO: it would be nice not to have to provide a proof...
def getValue (r : Row schema) (c : η) {τ} (h : Schema.HasCol (c, τ) schema) [inst : Gettable h] : Option τ := inst.getp h r

-- ...but in the meantime, here's a tactic to make the proof trivial
macro "header" : tactic => `(repeat ((try apply Schema.HasCol.hd) <;> (apply Schema.HasCol.tl)))

-------------------------------------------------------------------------------

-- Testing, etc.
#reduce addRows (addColumn emptyTable "name" []) [Row.singleCell "hello"]
#reduce getValue (Row.append
        (@Row.singleCell String _ "pi" (List Nat) [3,1,4,1,5])
        (@Row.singleCell String _ "age" Nat 20))
        "age" (by header)
