universe u_η
universe u

def Header {η} := (η × Type u)
def Schema {η} := List (@Header η)

-- Cell, row, table
-- Row/Cell setup based on Stephanie Weirich, "Dependent Types in Haskell,"
-- https://www.youtube.com/watch?v=wNa3MMbhwS4
-- Code!:
-- https://github.com/sweirich/dth/blob/master/regexp/src/OccDict.hs

inductive Cell {η : Type u_η}
               [DecidableEq η]
               (name : η)
               (τ : Type u)    : Type (max u u_η)
| emp : Cell name τ
| val : τ → Cell name τ

inductive Row {η : Type u_η} [DecidableEq η] : @Schema η → Type (max u_η (u + 1))
| nil : Row []
| cons {name : η} {τ : Type u} {hs : Schema} :
    Cell name τ → Row hs → Row ((name, τ) :: hs)

-- Lingering question: should rows have a built-in indexing scheme? (Probably.)
-- Should tables contain their number of rows and columns at type level? (Also
-- probably.)
-- Also, we still need to enforce distinct column names somehow...
--  --> we could subtype over lists to restrict to lists that don't contain
--      duplicates, but I could imagine that causing a lot of headaches

structure Table {η : Type u_η} [DecidableEq η] (hs : @Schema η) where
  rows : List (Row hs)

-- Schema column predicates
inductive Schema.HasCol {η : Type u_η} : @Header η → @Schema η → Type (max (u + 1) u_η)
| hd {c : η} {τ : Type u} {rs : Schema} : HasCol (c, τ) ((c, τ) :: rs)
| tl {r c τ rs} : HasCol (c, τ) rs → HasCol (c, τ) (r::rs)

inductive Schema.HasName {η : Type u_η} : η → @Schema η → Type (max (u + 1) u_η)
| hd {c : η} {rs : Schema} {τ : Type u} : HasName c ((c, τ) :: rs)
| tl {r c rs} : HasName c rs → HasName c (r::rs)

-- Schema-related convenience types
def Subschema {η : Type u_η} (schm : @Schema η) :=
  List ((h : Header) × schm.HasCol (h.fst, h.snd))

def CertifiedName (schema : @Schema η) := ((c : η) × Schema.HasName c schema)
def CertifiedHeader (schema : @Schema η) :=
  ((h : Header) × Schema.HasCol h schema)

/-
Action lists represent a collection of items to apply to a schema with a
guarantee that the validity of each proof of containment is preserved after each
action item is applied. It generalizes the following instances:
    inductive SchemaRemoveList {η : Type u_η} [DecidableEq η] :
      @Schema.{u_η, u} η → Type (max u_η (u + 1))
    | nil {schema} : SchemaRemoveList schema
    | cons {schema} : (cn : CertifiedName schema) →
                      SchemaRemoveList (schema.removeName cn.2) →
                      SchemaRemoveList schema

    inductive SchemaFlattenList {η : Type u_η} [DecidableEq η] :
      @Schema η → Type _
    | nil {schema} : SchemaFlattenList schema
    | cons {schema} : (cn : ((c : η) × (τ: Type u) × schema.HasCol (c, List τ))) →
                      SchemaFlattenList (schema.flattenList cn) →
                      SchemaFlattenList schema

    inductive SchemaRenameList {η : Type u_η} [DecidableEq η] :
      @Schema η → Type _
    | nil {schema} : SchemaRenameList schema
    | cons {schema} : (cnc : (CertifiedName schema × η))→
                      SchemaRenameList (schema.renameColumn cnc.1.2 cnc.2) →
                      SchemaRenameList schema
-/
inductive Schema.ActionList {η : Type u_η} [DecidableEq η]
                            {κ : @Schema η → Type u}
                            (f : ∀ (s : @Schema η), κ s → @Schema η)
    : @Schema η → Type _
| nil {schema}  : ActionList f schema
| cons {schema} : (entry : κ schema) →
                  ActionList f (f schema entry) →
                  ActionList f schema
