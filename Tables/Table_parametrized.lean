universe u
-- variable (header : Type) (sort : Type (u + 1))

inductive DepList : List (Sort u) → Sort (u + 1)
| nil : DepList []
| cons {α : Sort u} {βs : List (Sort u)} : α → DepList βs → DepList (α :: βs)

def DepList.append {αs βs} : DepList αs → DepList βs → DepList (List.append αs βs)
| DepList.nil, ys => ys
| (DepList.cons x xs), ys => DepList.cons x (append xs ys)

def DepList.singleton {α} (x : α) := DepList.cons x DepList.nil

def List.prod {α β} (xs : List α) (ys : List β) : List (α × β) :=
  List.foldl List.append [] (List.map (λ x => List.map (λ y => (x, y)) ys) xs)

def Sublist {α} [DecidableEq α] (xs : List α) := {ys : List α // ys.all (λy => xs.elem y) }

-- | [], ys => []
-- | xs, [] => []
-- | [x], y::ys => (x,y) :: (prod [x] ys)
-- | (x::xs), ys => List.append (prod [x] ys) (prod xs ys)

universe u₁ u₂

def Table.ColumnHeader {η : Type u₁} := (η × Type u₂)

def Table.Schema {η : Type u₁} := List (@ColumnHeader η)
def Table.Schema.names {η : Type u₁} := List.map (@Prod.fst η (Type u₂))

structure Table {η : Type u₁} [DecidableEq η]
                (schema : @Table.Schema η ) where
  cells : List (DepList (List.map Prod.snd schema))
-- TODO: figure out what to do about empty cells (it seems like this should
-- really be a non-issue on the library side -- if the user wants a cell to be
-- able to be empty, just make it optionally-typed, no?)
-- TODO: enforce that headers be distinct

-- inductive Table
-- | mk : (η : Type u₁) → (schema : List (η × Type u₂)) → List (DepList (List.map Prod.snd schema)) → Table

-- Projection maps
-- def Table.η : Table → Type u₁
-- | Table.mk η _ _ => η

-- def Table.schema : (t : Table) → List (t.η × Type u₂)
-- | Table.mk _ schema _ => schema

-- def Table.cells : (t : Table) → List (DepList (List.map Prod.snd t.schema))
-- | Table.mk _ _ cells => cells

variable {η : Type u₁} [dec_η : DecidableEq η] {schema : List (η × Type u₂)}

-- Convenience types
def Table.Row {η : Type u₁} (schema : List (η × Type u₂)) := DepList (List.map Prod.snd schema)

-- Begin B2T2

def Table.emptyTable {α : Type u₁} [hα : DecidableEq α] : @Table α hα [] :=
  Table.mk []

def Table.addRows (t : Table schema) (r : List (Table.Row schema)) : Table schema :=
  {cells := List.append t.cells r}

def Table.addColumn (t : Table schema) (c : ColumnHeader) (vs : List (Prod.snd c)) :
    Table (List.append schema [c]) :=
  {cells := (List.map (λ (olds, new) =>
                      DepList.append olds (DepList.singleton new))
                      -- @DepList.append (List.map Prod.snd schema) [c.snd] olds (DepList.singleton new))
                      (List.zip t.cells vs))}

def Table.buildColumn (t : Table schema) (c : ColumnHeader) (f : Row schema → Prod.snd c) :=
  addColumn t c (List.map f t.cells)

def Table.vcat (t1 : Table schema) (t2 : Table schema) : Table schema :=
  {cells := List.append t1.cells t2.cells}

def Table.hcat {schema₁ schema₂}
               (t1 : @Table η dec_η schema₁) (t2 : @Table η dec_η schema₂) :
                  @Table η (List.append schema₁ schema₂) :=
  {cells := List.map (λ (r1, r2) => DepList.append r1 r2)
                     (List.zip t1.cells t2.cells)}

def Table.values (rs : List (Table.Row schema)) : Table schema := {cells := rs}

def Table.crossJoin {schema₁ schema₂}
                    (t1 : @Table η dec_η schema₁) (t2 : @Table η dec_η schema₂) :
                      @Table η dec_η (List.append schema₁ schema₂) :=
  {cells := List.map (λ (c1, c2) => DepList.append c1 c2)
                        (List.prod t1.cells t2.cells)}


#reduce List.enum ["a", "b"]

def colIndices {α} [DecidableEq α] {ys : List α} (xs : Sublist ys) :=
  (List.enum ys) |> List.filter (λ (i, e) => xs.val.elem e)
                 |> List.map Prod.fst

def getCol : (schema : @Table.Schema η) → Table.Row schema → @Table.ColumnHeader η → _ -- What do we even return???
| [], DepList.nil, (name, τ) => sorry
| h :: hs, DepList.cons y ys, c => if h = c then y else getCol hs ys c

-- TODO: fill this in
-- TODO: need to enforce that all entries in the schemata for elements of cs
-- specify the same type
-- TODO: need to be able to add "empty cells" -- I guess we're enforcing
-- optionality at the table type level...
def Table.leftJoin {schema₁ schema₂}
                   (t1 : @Table η dec_η schema₁)
                   (t2 : @Table η dec_η schema₂)
                   -- TODO: why can't we just do schemaᵢ.name?
                   (cs : @Sublist η dec_η (List.append (List.map Prod.fst schema₁) (List.map Prod.fst schema₂))) :
    -- TODO: make this WAY more readable
    Table (List.append schema₁ (schema₂.filter (λ x => cs.val.notElem (Prod.fst x)))) := sorry
    -- t1.cells.map (λ r1 =>
    --   let rs2 := t2.cells.filter (λ r2 => cs.all (λ c => r1[c] = r2[c]) ) in
    --   match rs2 with
    --   | [] => []
    --   | _ => rs2.map (r2 => _)
    --   )

-- Want some sort of easy way to specify that an η is a valid column name to
-- index into a given schema
-- Is there an easy way to have type-validatable "is-in" relations on lists?
-- Or should we try to do some sort of dependently-typed dictionary?

-- TODO: Ask Rob if there's any way to maintain invariants through abstraction
-- besides `private`

-- Maybe we can embed the column header in the DepList somehow? We're already
-- extending base types to accommodate empty cells -- maybe we can somehow
-- enforce that every element of the deplist is somehow "tagged" with the
-- corresponding header at the type level? (That way it's not an invariant we
-- have to manually enforce.)

structure W where
  cells : Nat
  thing : String

structure X where
  cells : Nat
  other : String

-- def funfunction : 

#check List.removeAll
