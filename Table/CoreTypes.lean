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

inductive Row {η : Type u_η} [DecidableEq η] : Schema → Type (max u_η (u + 1))
| nil : Row []
| cons {name : η} {τ : Type u} {hs : Schema} :
    Cell name τ → Row hs → Row ((name, τ) :: hs)

-- Lingering question: should rows have a built-in indexing scheme? (Probably.)
-- Should tables contain their number of rows and columns at type level? (Also
-- probably.)
-- Also, we still need to enforce distinct column names somehow...
--  --> we could quotient over lists to restrict to lists that don't contain
--      duplicates, but I could imagine that causing a lot of headaches

structure Table {η : Type u_η} [DecidableEq η] (hs : @Schema η) where
  rows : List (Row hs)

-- Schema column predicates
inductive Schema.HasCol {η : Type u_η} : @Header η → @Schema η → Prop
| hd {c : η} {τ : Type u} {rs : Schema} : HasCol (c, τ) ((c, τ) :: rs)
| tl {r c τ rs} : HasCol (c, τ) rs → HasCol (c, τ) (r::rs)

inductive Schema.HasName {η : Type u_η} : η → @Schema η → Prop
| hd {c : η} {rs : Schema} {τ : Type u} : HasName c ((c, τ) :: rs)
| tl {r c rs} : HasName c rs → HasName c (r::rs)

-- Schema-related convenience types
def Subschema {η : Type u_η} (schm : @Schema η) :=
  List {h : Header // schm.HasCol (h.fst, h.snd)}

def CertifiedName (schema : @Schema η) := {c : η // Schema.HasName c schema}
def CertifiedHeader (schema : @Schema η) :=
  {h : Header // Schema.HasCol h schema}
