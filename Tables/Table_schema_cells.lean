universe u
-- variable (header : Type) (sort : Type (u + 1))

inductive DepList : List (Sort u) → Sort (u + 1)
| nil : DepList []
| cons {α : Sort u} {βs : List (Sort u)} : α → DepList βs → DepList (α :: βs)

def DepList.append {αs βs} : DepList αs → DepList βs → DepList (List.append αs βs)
| DepList.nil, ys => ys
| (DepList.cons x xs), ys => DepList.cons x (append xs ys)

def DepList.singleton {α} (x : α) := DepList.cons x DepList.nil

universe u₁
universe u₂

-- def Table_manual := (η : Type (u₁ + 1)) × (schema : List (η × Type u₂)) × List (DepList (List.map Prod.snd schema))

-- def Table_manual.η : Table_manual → Type (u₁ + 1) := λ self => self.1
-- def Table_manual.schema : (t : Table_manual) → List (t.η × Type u₂) := λ self => self.2.1
-- def Table_manual.cells : (t : Table_manual) → List (DepList (List.map Prod.snd t.schema)) := λ self => self.2.2

structure Table where
  η : Type (u₁ + 1)
  schema : List (η × Type u₂)
  cells : List (DepList (List.map Prod.snd schema))

def Table.Row (t : Table) := DepList (List.map Prod.snd t.schema)

def Table.ColumnHeader (t : Table) := (t.η × Type u₂)
-- TODO: create named projection maps for name & type

def Table.emptyTable {α : Type (u₁ + 1)} := Table.mk α [] []

-- FIXME: r should actually be a SEQUENCE (list) of rows
def Table.addRows (t : Table) (r : Table.Row t) : Table :=
  {t with cells := List.append t.cells [r]}

-- TODO: these are equal, but only extensionally so
def Table.addColumn (t : Table) (c : Table.ColumnHeader t) (vs : List (Prod.snd c)) :=
  {t with schema := List.append t.schema [c],
          cells  := List.map (λ (olds, new) =>
                      @DepList.append (List.map Prod.snd t.schema) [c.snd] olds (DepList.singleton new))
                      (List.zip t.cells vs)}

def Table.buildColumn (t : Table) (c : Table.ColumnHeader t) (f : Row t → Prod.snd c) :=
  addColumn t c (List.map f t.cells)

-- TODO: how to enforce same η and schema?
def Table.vcat (t1 : Table) (t2 : Table)
               {h1 : t1.η = t2.η} {h2 : t1.schema = t2.schema} : Table :=
  {t1 with cells := List.append t1.cells t2.cells}

-- TODO: there should be some clever way to use addColumn/buildColumn with some
-- sort of list zip/fold deal...
def Table.hcat (t1 : Table) (t2 : Table) {h1 : t1.η = t2.η} : Table := _


