import Table.Schema
import Table.Row

universe u_η
universe u
-- Cell, row, table
-- Row/Cell setup based on Stephanie Weirich, "Dependent Types in Haskell":
-- https://github.com/sweirich/dth/blob/master/regexp/src

-- We don't enforce uniqueness of column names as part of `Table`. Instead, a
-- uniquely named table can be represented as a `Table` together with a
-- `Schema.Unique` proof

structure Table {η : Type u_η} [DecidableEq η] (hs : @Schema η) where
  rows : List (Row hs)

-- Decidable equality
-- TODO: simplify a la case 4 of Cell instance?
instance {η : Type u_η} [dec_η : DecidableEq η]
         {sch : @Schema η} [inst : DecidableEq (Row sch)]
    : DecidableEq (Table sch) :=
λ {rows := r₁} {rows := r₂} =>
dite (r₁ = r₂)
     (λ htrue => isTrue $ congrArg Table.mk htrue)
     (λ hfalse => isFalse (λ hneg => absurd (Table.mk.inj hneg) hfalse))
