-- Lean 3!
import algebra
import data.real.basic
import data.vector
import tactic.explode
import tactic.find
import tactic.induction
import tactic.linarith
import tactic.rcases
import tactic.rewrite
import tactic.ring_exp
import tactic.tidy
import tactic.where

lemma two_a (G : Type) [comm_group G] : ∀ (g h : G) (m n : ℕ),
  nat.gcd m n = 1 → g^n = 1 ∧ h^m = 1 → false := sorry

def table {label_t : Type} (col_ts : list (label_t × list Type)) : Type := sorry

