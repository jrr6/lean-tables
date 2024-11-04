/-!
Contains lemmas about existing logical operators and functions; also contains
definitions for type-level logical operators.
-/

theorem not_or_distrib : ¬ (a ∨ b) ↔ ¬a ∧ ¬b :=
Iff.intro
(λ h => And.intro (λ ha => h (Or.intro_left _ ha))
                  (λ hb => h (Or.intro_right _ hb)))
(λ h => λ hneg =>
  match hneg with
  | Or.inl ha => h.left ha
  | Or.inr hb => h.right hb)

theorem not_not (p : Prop) : p → ¬¬p := λ hp hneg => hneg hp

theorem Or.assoc : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R :=
  Iff.intro (λ h => h.elim (λ hpq => hpq.elim Or.inl (Or.inr ∘ Or.inl))
                           (Or.inr ∘ Or.inr))
            (λ h => h.elim (Or.inl ∘ Or.inl)
                           (λ hqr => hqr.elim (Or.inl ∘ Or.inr) Or.inr))

theorem Iff.not_iff_not_of_iff : (p ↔ q) → (¬ p ↔ ¬ q) := λ hpq =>
  Iff.intro (λ hnp hq => hnp $ hpq.mpr hq) (λ hnq hp => hnq $ hpq.mp hp)

-- Basic fact about equality used in `removeHeaderHasCol'`
theorem Eq.cast_distrib_fun {α} {x y : α} {σ τ : α → Type _}
    (h : x = y) (f : ∀ {z}, τ z → σ z) (t : τ x) :
    h ▸ (f t) = f (h ▸ t) :=
  h.rec (Eq.refl (f t))

def Injective (f : α → β) := ∀ a a', f a = f a' → a = a'

def Function.swap (f : α → β → γ) : β → α → γ :=
  λ b a => f a b

-- Type-level negation for use with type-valued predicates
def NotT (α : Type _) := α → Empty

/- Equality type for pattern-matching workaround in proof of
  `selectColumns2_spec3` -/
inductive EqT : α → α → Type where
  | refl (a : α) : EqT a a
infix:50 " ≡ " => EqT

def EqT.ofEq {a b : α} : a = b → a ≡ b := λ | .refl _ => .refl _
