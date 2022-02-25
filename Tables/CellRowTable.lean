universe u_η
universe u

def Stringable (τ : Type u) [inst : ToString τ] : Type u × ToString τ := (τ, inst)

-- Based on Stephanie Weirich, "Dependent Types in Haskell,"
-- https://www.youtube.com/watch?v=wNa3MMbhwS4

inductive Cell {η : Type u_η} (name : η) (τ : Sort u) : Sort _
| mk : τ → Cell name τ

inductive Row {η : Type u_η} : List (η × Type u) → Sort _
| nil : Row []
| cons {name : η} {τ : Type u} {hs : List (η × Type u)} :
    Cell name τ → Row hs → Row ((name, τ) :: hs)

structure Table {η : Type u_η} (hs : List (η × Type u)) where
  rows : List (Row hs)

def Row.repr {η} [ToString η] : {xs : List (η × Type u)} → Row xs → String
| [], Row.nil => ""
| (nm, x) :: xs, Row.cons val d => (toString nm) ++ ": something, " ++ repr d

#check Cell "hi" Nat

def x : Cell "hi" Nat := Cell.mk 42

#eval Row.repr (Row.cons x Row.nil)
