universe u_η
universe u

def Stringable (τ : Type u) [inst : ToString τ] : Type u × ToString τ := (τ, inst)

-- Row/Cell setup based on Stephanie Weirich, "Dependent Types in Haskell,"
-- https://www.youtube.com/watch?v=wNa3MMbhwS4
-- Code!:
-- https://github.com/sweirich/dth/blob/master/regexp/src/OccDict.hs

def Header {η} := (η × Type u)
def Schema {η} := List (@Header η)

inductive Cell {η : Type u_η} [DecidableEq η] (name : η) (τ : Type u) : Type (max u u_η)
| emp : Cell name τ
| val : τ → Cell name τ

def Cell.toOption {η nm τ} [dec_η : DecidableEq η] : @Cell η dec_η nm τ → Option τ
| Cell.emp => Option.none
| Cell.val x => Option.some x

def Cell.name {η nm τ} [dec_η : DecidableEq η] (_ : @Cell η dec_η nm τ) : η := nm

-- Lingering question: should rows have a built-in indexing scheme? (Probably.)
-- Should tables contain their number of rows and columns at type level? (Also
-- probably.)
-- Also, we still need to enforce distinct column names somehow...
--  --> we could quotient over lists to restrict to lists that don't contain
--      duplicates, but I could imagine that causing a lot of headaches

inductive Row {η : Type u_η} [DecidableEq η] : Schema → Type (max u_η (u + 1))
| nil : Row []
| cons {name : η} {τ : Type u} {hs : Schema} :
    Cell name τ → Row hs → Row ((name, τ) :: hs)

structure Table {η : Type u_η} [DecidableEq η] (hs : @Schema η) where
  rows : List (Row hs)

variable {η : Type u_η} [dec_η : DecidableEq η] {schema : @Schema η}

-- Schema column predicates
inductive Schema.HasCol {η : Type u_η} : @Header η → @Schema η → Prop
| hd {c : η} {τ : Type u} {rs : Schema} : HasCol (c, τ) ((c, τ) :: rs)
| tl {r c τ rs} : HasCol (c, τ) rs → HasCol (c, τ) (r::rs)

inductive Schema.HasName : η → @Schema η → Prop
| hd {c : η} {rs : Schema} {τ : Type u} : HasName c ((c, τ) :: rs)
| tl {r c rs} : HasName c rs → HasName c (r::rs)

-- Schema functions
def Schema.names {η : Type u_η} := List.map (@Prod.fst η (Type u))

def Schema.pick {η : Type u_η} [DecidableEq η]: (s : Schema) → List {c : η // Schema.HasName c s} → @Schema η
| [], _ => []
| _, [] => []
| (nm, τ)::hs, [⟨c, hc⟩] => dite (nm = c) (λ _ => [(nm, τ)]) (λ h => pick hs [⟨c, by
  cases hc with
  | hd => contradiction
  | tl in_hs => exact in_hs
  ⟩])
| hs, c1::c2::cs =>
  -- Help out the termination checker
  have _ : List.length hs + Nat.succ 0 < List.length hs + Nat.succ (Nat.succ (List.length cs)) := by
    apply Nat.add_lt_add_left
    exact @Nat.succ_lt_succ 0 (Nat.succ (List.length cs)) (Nat.zero_lt_succ (List.length cs));
  List.append (pick hs [c1]) (pick hs (c2::cs))
termination_by pick s cs => List.length s + List.length cs

-- List utilities
inductive List.All {α} (p : α → Prop) : List α → Prop
| vac      : All p []
| sing {x} : p x → All p [x]
| cons {x xs} : p x → All p xs → All p (x::xs)

def List.prod {α β} (xs : List α) (ys : List β) : List (α × β) :=
  List.foldl List.append [] (List.map (λ x => List.map (λ y => (x, y)) ys) xs)

-- TODO: So List.nth *does* still exist in the prelude -- they just changed
-- the name to `List.get`...
def List.nth {α} : (xs : List α) → (n : Nat) → (n < List.length xs) → α
| [], _, h => absurd h (by intro nh; cases nh)
| x::xs, 0, h => x
| x::xs, Nat.succ n, h => nth xs n (Nat.le_of_succ_le_succ h)

def List.nths {α} (xs : List α) (ns : List {n : Nat // n < List.length xs}): List α :=
  List.map (λ n => List.nth xs n.val n.property) ns

-- This is slick, but unfortunately, it breaks type inference
-- def List.sieve {α} (bs : List Bool) (xs : List α) : List α :=
--   List.zip bs xs |> List.filter Prod.fst
--                  |> List.map Prod.snd

def List.sieve {α} : List Bool → List α → List α
| [], xs => xs
| _, [] => []
| true :: bs, x :: xs => x :: sieve bs xs
| false :: bs, _ :: xs => sieve bs xs

-- Row utilities
def Row.singleCell {name τ} (x : τ) :=
  @Row.cons η dec_η name τ [] (Cell.val x) Row.nil

def Row.append {schema₁ schema₂} :
    @Row η _ schema₁ → Row schema₂ → Row (List.append schema₁ schema₂)
| Row.nil, rs₂ => rs₂
| Row.cons r₁ rs₁, rs₂ => Row.cons r₁ (append rs₁ rs₂)

def Row.map {schema} (f : ∀ n α, Cell n α → @Cell η dec_η n α) : Row schema → @Row η dec_η schema
| Row.nil => Row.nil
| @Row.cons _ _ n τ _ r₁ rs₁ => Row.cons (f n τ r₁) (map f rs₁)

-- TODO: probably makes more sense to move this to some general "collection"
-- interface rather than reimplementing for every type -- wonder if this is
-- something James is working on
-- It would also be nice if we could make this function less verbose.
-- Unfortunately, Lean's type-checker needs some help...
def Row.sieve {schema} : (bs : List Bool) → Row schema → @Row η dec_η (List.sieve bs schema)
| [], Row.nil => Row.nil
| [], Row.cons r rs => Row.cons r rs
| true :: bs, Row.nil => Row.nil
| false :: bs, Row.nil => Row.nil
| true :: bs, Row.cons r rs => Row.cons r (sieve bs rs)
| false :: bs, Row.cons r rs => sieve bs rs

def Row.nth {schema} : (rs : @Row η dec_η schema) → (n : Nat) → (h : n < List.length schema) →
    let (nm, τ) := List.nth schema n h;
    @Cell η dec_η nm τ
| Row.nil, _, h => absurd h (by intro nh; cases nh)
| Row.cons r rs, 0, h => r
| Row.cons r rs, Nat.succ n, h => nth rs n (Nat.le_of_succ_le_succ h)

-- It would be nice if Lean could figure out that we're structurally recursing,
-- but in the meantime, we have to provide a manual termination relation
def Row.nths {schema} :
    (ns : List {n : Nat // n < List.length schema})
      → Row schema
      → @Row η dec_η (List.nths schema ns)
| [], Row.nil => Row.nil
| [], Row.cons x xs => Row.nil
| n::ns, Row.nil => absurd n.property
                          (by intro nh; simp [List.length] at nh; contradiction)
| n::ns, r => Row.cons (Row.nth r n.val n.property) (nths ns r)
  termination_by nths ns r => List.length ns

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
def getRow : (t : Table schema) → (n : Nat) → (n < nrows t) → Row schema
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
def getValue {τ} (r : Row schema) (c : η) (h : Schema.HasCol (c, τ) schema) [inst : Gettable h] : Option τ := inst.getp h r

-- ...but in the meantime, here's a tactic to make the proof trivial
macro "header" : tactic => `(repeat ((try apply Schema.HasCol.hd) <;> (apply Schema.HasCol.tl)))

def getColumnIndex (t : Table schema) (n : Nat) (h : n < ncols t) := List.map (λr => List.nth _ n h) t.rows

def getColumn {τ} (t : Table schema) (c : η) (h : Schema.HasCol (c, τ) schema) [inst : Gettable h] : List (Option τ) := List.map (λ r => inst.getp h r) t.rows

-- TODO: get rid of sorry!
def selectRowsIndices (t : Table schema) (ns : List {n : Nat // n < nrows t}) : Table schema :=
  {rows := List.map (λ n => getRow t n.val n.property) ns}

-- We don't strictly *need* the proof here, but if we want to be consistent about
-- enforcing preconditions through proof terms, we should probably leave it...
def selectRows (t : Table schema) (bs : List Bool) (h : List.length bs = nrows t) : Table schema :=
  {rows := List.sieve bs t.rows}

def selectColumns (t : Table schema) (bs : List Bool) (h : List.length bs = ncols t) :
    Table (List.sieve bs schema) :=
  {rows := t.rows.map (λ r => Row.sieve bs r)}

def selectColumnsN (t : Table schema) (ns : List {n : Nat // n < ncols t}) : Table (List.nths schema ns) :=
  {rows := t.rows.map (Row.nths ns)}

-- TODO: pivotLonger and pivotWider

-------------------------------------------------------------------------------

section table_testing

#check Cell "hi" Nat

def x : Cell "hi" Nat := Cell.val 42

-- Implementation of a table string-representation function (provided all τs in
-- the schema have ToString instances):
instance : ToString (@Row η dec_η []) where
  toString := λ_ => ""

instance {η nm τ} {xs : @Schema η} [ToString τ] [DecidableEq η] [ToString (Row xs)] : ToString (Row ((nm, τ) :: xs)) where
  toString := λ(Row.cons cell d) =>
                let s := match cell.toOption with
                         | some v => toString v
                         | none   => "[empty]";
                let s_d := toString d; 
                s ++ (if s_d = "" then "" else "\t|\t" ++ s_d)

def Row.repr [ToString (Row schema)] (r : Row schema) := toString r

instance {η} {schema : @Schema η} [ToString η] [DecidableEq η] [inst : ToString (Row schema)] : ToString (Table schema) where
  toString := λ t =>
  List.foldr (λ (nm, _) acc => ToString.toString nm ++ (if acc = "" then "" else "\t|\t") ++ acc) "" schema
    ++ "\n"
    ++ List.foldr (λ r acc => inst.toString r ++ "\n" ++ acc) "" t.rows

def Table.repr [ToString (Table schema)] (t : Table schema) := toString t

#eval Row.repr (Row.cons x (Row.cons x Row.nil))

-- This could probably use some syntactic sugar...
def t1 : Table [("prof", String), ("course", Nat), ("taught", Bool)] :=
  -- Can simplify this by just using Table.mk
  addRows
    (emptyTable |> (λ t => addColumn t "prof" [])
                |> (λ t => addColumn t "course" [])
                |> (λ t => addColumn t "taught" []))
    [Row.cons (Cell.val "Kaynar") (Row.cons (Cell.val 15122) (Row.cons (Cell.val true) Row.nil)),
      Row.cons (Cell.val "Crary") (Row.cons (Cell.val 15150) (Row.cons (Cell.val true) Row.nil)),
      Row.cons (Cell.val "Erdmann") (Row.cons (Cell.val 15150) (Row.cons (Cell.val false) Row.nil)),
      Row.cons (Cell.val "Cervesato") (Row.cons (Cell.val 15122) (Row.cons (Cell.val false) Row.nil))]

#eval Table.repr t1
#reduce t1

infixr:50 "|" => Row.cons
notation "**|" => Row.nil
notation "/[" elem "]/" => Cell.val elem
notation "/[_]/" => Cell.emp

def t2 : Table [("prof", String), ("course", Nat), ("taught", Bool)] :=
  Table.mk
    [
      /[ "Lewis" ]/         | /[_]/      | /[ true ]/  | **|,
      /[ "Krishnamurthi" ]/ | /[ 1730 ]/ | /[ false ]/ | **|
      ]

def joined := vcat t1 t2
#eval Table.repr joined
#reduce joined

def schoolIded := addColumn joined "school" ["CMU", "CMU", "CMU", "CMU", "Brown", "Brown"]
#check schoolIded

#reduce selectRowsIndices schoolIded [⟨3, _⟩, ⟨4, _⟩]
#reduce schoolIded |> (λ t => selectRowsIndices t [⟨1, _⟩, ⟨4, _⟩])
                   |> (λ t => selectColumns t [true, false, false, true])

-- Testing, etc.
#reduce addRows (addColumn emptyTable "name" []) [Row.singleCell "hello"]
#reduce getValue (Row.append
        (@Row.singleCell String _ "pi" (List Nat) [3,1,4,1,5])
        (@Row.singleCell String _ "age" Nat 20))
        "age" (by header)

def departments : Table [("Department ID", Nat),
                         ("Department Name", String)] :=
Table.mk [
  /[31]/ | /["Sales"]/       | **|,
  /[33]/ | /["Engineering"]/ | **|,
  /[34]/ | /["Clerical"]/    | **|,
  /[35]/ | /["Marketing"]/   | **|
]

def gradebookTable : Table [("name", ULift String),
                            ("age", ULift Nat),
                            ("quizzes", Table [("quiz#", {n : Nat // 1 ≤ n ∧ n ≤ 4}),
                                               ("grade", Nat)]),
                            ("midterm", ULift Nat),
                            ("final", ULift Nat)] :=
Table.mk [
  /[ULift.up "Bob"]/ |
  /[ULift.up 12]/ |
  /[Table.mk [/[⟨1, by simp⟩]/ | /[8]/ | **|,
              /[⟨2, by simp⟩]/ | /[9]/ | **|,
              /[⟨3, by simp⟩]/ | /[7]/ | **|,
              /[⟨4, by simp⟩]/ | /[9]/ | **|]]/ |
  /[ULift.up 77]/ |
  /[ULift.up 87]/ | **|,

  /[ULift.up "Alice"]/ |
  /[ULift.up 17]/ |
  /[Table.mk [/[⟨1, by simp⟩]/ | /[6]/ | **|,
              /[⟨2, by simp⟩]/ | /[8]/ | **|,
              /[⟨3, by simp⟩]/ | /[8]/ | **|,
              /[⟨4, by simp⟩]/ | /[7]/ | **|]]/ |
  /[ULift.up 88]/ |
  /[ULift.up 85]/ | **|,

  /[ULift.up "Eve"]/ |
  /[ULift.up 13]/ |
  /[Table.mk [/[⟨1, by simp⟩]/ | /[7]/ | **|,
              /[⟨2, by simp⟩]/ | /[9]/ | **|,
              /[⟨3, by simp⟩]/ | /[8]/ | **|,
              /[⟨4, by simp⟩]/ | /[8]/ | **|]]/ |
  /[ULift.up 84]/ |
  /[ULift.up 77]/ | **|
  
]

#eval Table.repr gradebookTable

end table_testing
