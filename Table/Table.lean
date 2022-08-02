import Table.Schema
import Table.Row

universe u_η
universe u
-- Cell, row, table
-- Row/Cell setup based on Stephanie Weirich, "Dependent Types in Haskell,"
-- https://www.youtube.com/watch?v=wNa3MMbhwS4
-- Code!:
-- https://github.com/sweirich/dth/blob/master/regexp/src

-- We may still want to enforce distinct column names somehow...
--  --> we could subtype over lists to restrict to lists that don't contain
--      duplicates, but I could imagine that causing a lot of headaches

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
