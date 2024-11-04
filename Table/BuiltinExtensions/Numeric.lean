/-!
Lemmas about numeric types: `Nat` and `Int`.
-/

-- Based on `buffer.lt_aux_1` in Lean 3's `lib/lean/library/data/buffer.lean`
theorem Nat.lt_of_lt_add_left {a b c : Nat} (h : a + c < b) : a < b :=
Nat.lt_of_le_of_lt (Nat.le_add_right a c) h

-- Reproducing `algebra/order/sub.lean` for Nats

-- Based on `le_add_tsub` from Mathlib
theorem Nat.le_add_sub {a b : Nat} : a ≤ b + (a - b) :=
  Nat.sub_le_iff_le_add'.mp $ Nat.le_refl (a - b)

theorem Nat.lt_of_sub_add {m k n : Nat} (hkm : k < m) (hn : n > 0) :
    m - (k + n) < m - k :=
  Nat.sub_lt_sub_left hkm (Nat.lt_add_of_pos_right hn)

theorem Int.natAbs_of_nonneg_eq_toNat : ∀ z : Int, z ≥ 0 → z.natAbs = z.toNat
  | ofNat n, h => rfl

theorem Int.add_neg_eq_sub (m : Int) : ∀ n, n < 0 → m + n = m - n.natAbs
  | negSucc n, h => rfl


-- -- TODO: decide whether to use this or `Fin.instOfNat`
-- instance (k : Nat) : OfNat (Fin k.succ) n :=
--   if h : n < k.succ
--   then ⟨n, h⟩
--   else ⟨0, Nat.zero_lt_succ k⟩
