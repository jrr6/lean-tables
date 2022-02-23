import tactic.induction

set_option pp.generalized_field_notation false

-- Statics
inductive exp : Type
| tt : exp
| ff : exp
| nor1 : exp → exp → exp
| nor2 : exp → exp → exp

inductive circ : exp → Prop
| tt : circ exp.tt
| ff : circ exp.ff
| nor1 : ∀ e₁ e₂ : exp, circ e₁ → circ e₂ → circ (exp.nor1 e₁ e₂)
| nor2 : ∀ e₁ e₂ : exp, circ e₁ → circ e₂ → circ (exp.nor2 e₁ e₂)

-- Dynamics
inductive big_step : exp → exp → Prop
| tt : big_step exp.tt exp.tt
| ff : big_step exp.ff exp.ff
| nor1_tt_any : ∀e₁ e₂ : exp, big_step e₁ exp.tt →
                  big_step (exp.nor1 e₁ e₂) exp.ff
| nor1_ff_tt : ∀e₁ e₂ : exp, big_step e₁ exp.ff → big_step e₂ exp.tt →
                  big_step (exp.nor1 e₁ e₂) exp.ff
| nor1_ff_ff : ∀e₁ e₂ : exp, big_step e₁ exp.ff → big_step e₂ exp.ff →
                  big_step (exp.nor1 e₁ e₂) exp.tt
| nor2_any_tt : ∀e₁ e₂ : exp, big_step e₂ exp.tt →
                  big_step (exp.nor2 e₁ e₂) exp.ff
| nor2_tt_ff : ∀e₁ e₂ : exp, big_step e₁ exp.tt → big_step e₂ exp.ff →
                  big_step (exp.nor2 e₁ e₂) exp.ff
| nor2_ff_ff : ∀e₁ e₂ : exp, big_step e₁ exp.ff → big_step e₂ exp.ff →
                  big_step (exp.nor2 e₁ e₂) exp.tt

-- 25:52
lemma termination :  -- i.e., "always valuable"
  ∀e : exp, circ e → (big_step e exp.tt) ∨ (big_step e exp.ff)
| exp.tt := (λ_, or.intro_left (big_step exp.tt exp.ff) big_step.tt)
| exp.ff := (λ_, or.intro_right (big_step exp.ff exp.tt) big_step.ff)
| (exp.nor1 e₁ e₂) :=
  have pre_h_val₁ : circ e₁ → (big_step e₁ exp.tt) ∨ (big_step e₁ exp.ff) :=
    termination e₁,
  have pre_h_val₂ : circ e₂ → (big_step e₂ exp.tt) ∨ (big_step e₂ exp.ff) :=
    termination e₂,
  begin
    intro h,
    cases' h with e₁ e₂ h₁ h₂,
    have h_val₁ := pre_h_val₁ h₁,
    have h_val₂ := pre_h_val₂ h₂,
    cases' h_val₁ with h_val₁,
    {
      apply or.intro_right,
      apply big_step.nor1_tt_any e₁ e₂ h_val₁,
    },
    {
      rename h h_val₁,
      cases' h_val₂ with h_val₂,
      {
        apply or.intro_right,
        apply big_step.nor1_ff_tt e₁ e₂ h_val₁ h_val₂,
      },
      {
        rename h h_val₂,
        apply or.intro_left,
        apply big_step.nor1_ff_ff e₁ e₂ h_val₁ h_val₂,
      }
    }
  end
| (exp.nor2 e₁ e₂) :=
  have pre_h_val₁ : circ e₁ → (big_step e₁ exp.tt) ∨ (big_step e₁ exp.ff) :=
    termination e₁,
  have pre_h_val₂ : circ e₂ → (big_step e₂ exp.tt) ∨ (big_step e₂ exp.ff) :=
    termination e₂,
  begin
    intro h,
    cases' h,
    rename h h₁,
    rename h_1 h₂,
    have h_val₁ := pre_h_val₁ h₁,
    have h_val₂ := pre_h_val₂ h₂,
    cases' h_val₂ with h_val₂,
    {
      apply or.intro_right,
      apply big_step.nor2_any_tt e₁ e₂ h_val₂,
    },
    {
      rename h h_val₂,
      cases' h_val₁ with h_val₁,
      {
        apply or.intro_right,
        apply big_step.nor2_tt_ff e₁ e₂ h_val₁ h_val₂,
      },
      {
        rename h h_val₁,
        apply or.intro_left,
        apply big_step.nor2_ff_ff e₁ e₂ h_val₁ h_val₂,
      }
    }
  end

-- Alternative formulation (40:00)
inductive exp2 : Type
| tt : exp2
| ff : exp2
| ite : exp2 → exp2 → exp2 → exp2

inductive circ2 : exp2 → Prop
| tt  : circ2 exp2.tt
| ff  : circ2 exp2.ff
| ite : ∀(e₁ e₂ e₃ : exp2), circ2 e₁ → circ2 e₂ → circ2 e₃ →
        circ2 (exp2.ite e₁ e₂ e₃)

inductive big_step2 : exp2 → exp2 → Prop
| tt : big_step2 exp2.tt exp2.tt
| ff : big_step2 exp2.ff exp2.ff
| ite_tt : ∀(e₁ e₂ e₂' e₃ : exp2), big_step2 e₁ exp2.tt → big_step2 e₂ e₂' →
           big_step2 (exp2.ite e₁ e₂ e₃) e₂'
| ite_ff : ∀(e₁ e₂ e₃ e₃' : exp2), big_step2 e₁ exp2.ff → big_step2 e₃ e₃' →
           big_step2 (exp2.ite e₁ e₂ e₃) e₃'

lemma termination2 : ∀e : exp2, circ2 e →
                        (big_step2 e exp2.tt) ∨ (big_step2 e exp2.ff)
| exp2.tt := (λ_, or.intro_left (big_step2 exp2.tt exp2.ff) big_step2.tt)
| exp2.ff := (λ_, or.intro_right (big_step2 exp2.ff exp2.tt) big_step2.ff)
| (exp2.ite e₁ e₂ e₃) :=
  have pre_he₁ : circ2 e₁ → (big_step2 e₁ exp2.tt) ∨ (big_step2 e₁ exp2.ff) :=
    termination2 e₁,
  have pre_he₂ : circ2 e₂ → (big_step2 e₂ exp2.tt) ∨ (big_step2 e₂ exp2.ff) :=
    termination2 e₂,
  have pre_he₃ : circ2 e₃ → (big_step2 e₃ exp2.tt) ∨ (big_step2 e₃ exp2.ff) :=
    termination2 e₃,
  begin
    intro hcirc,
    cases' hcirc with e₁ e₂ e₃ hcirc₁ hcirc₂ hcirc₃,
    have he₁ := pre_he₁ hcirc₁,
    have he₂ := pre_he₂ hcirc₂,
    have he₃ := pre_he₃ hcirc₃,
    cases' he₁,
    {
      cases' he₂,
      {
        apply or.intro_left,
        exact big_step2.ite_tt e₁ e₂ exp2.tt e₃ h h_1,
      },
      {
        apply or.intro_right,
        exact big_step2.ite_tt e₁ e₂ exp2.ff e₃ h h_1,
      }
    },
    {
      cases' he₃,
      {
        apply or.intro_left,
        exact big_step2.ite_ff e₁ e₂ e₃ exp2.tt h h_1,
      },
      {
        apply or.intro_right,
        exact big_step2.ite_ff e₁ e₂ e₃ exp2.ff h h_1,
      }
    }
  end

-- Small-step (structural operational) semantics
inductive val : exp → Prop
| tt : val exp.tt
| ff : val exp.ff

inductive small_step : exp → exp → Prop
| nor1_fst_step : ∀ e₁ e₁' e₂ : exp,
    small_step e₁ e₁' → small_step (exp.nor1 e₁ e₂) (exp.nor1 e₁' e₂)
| nor1_tt_any : ∀e : exp, small_step (exp.nor1 exp.tt e) exp.ff
| nor1_ff_step : ∀e e' : exp,
    small_step e e' → small_step (exp.nor1 exp.ff e) (exp.nor1 exp.ff e')
| nor1_ff_tt : small_step (exp.nor1 exp.ff exp.tt) exp.ff
| nor1_ff_ff : small_step (exp.nor1 exp.ff exp.ff) exp.tt
| nor2_snd_step : ∀ e₁ e₂ e₂' : exp,
    small_step e₂ e₂' → small_step (exp.nor2 e₁ e₂) (exp.nor2 e₁ e₂')
| nor2_any_tt : ∀e : exp, small_step (exp.nor2 e exp.tt) exp.ff
| nor2_ff_step : ∀e e' : exp,
    small_step e e' → small_step (exp.nor2 e exp.ff) (exp.nor2 e' exp.ff)
| nor2_tt_ff : small_step (exp.nor2 exp.tt exp.ff) exp.ff
| nor2_ff_ff : small_step (exp.nor2 exp.ff exp.ff) exp.tt

lemma small_step_coherence :
  ∀e e': exp, ((circ e ∧ small_step e e') → circ e')
                ∧ (circ e → (val e ∨ (∃e'' : exp, small_step e e''))) :=
begin
  intros e e',
  -- Might've been simpler just to induct on e out here?
  apply and.intro,
  -- LHS
  {
    intros h,
    cases' h,
    induction' left,
    { cases' right },
    { cases' right },
    {
      cases' right,
      {
        apply circ.nor1,
        apply ih_left _ right,
        apply left_1,
      },
      { exact circ.ff },
      {
        apply circ.nor1,
        apply circ.ff,
        exact ih_left_1 _ right,
      },
      { exact circ.ff },
      { exact circ.tt },
    },
    {
      cases' right,
      { exact circ.nor2 e₁ e' left (ih_left_1 e' right) },
      { exact circ.ff },
      { exact circ.nor2 e' exp.ff (ih_left e' right) circ.ff },
      { exact circ.ff },
      { exact circ.tt },
    }
  },
  -- RHS
  {
    intro h,
    clear e', -- just for the first half
    induction' e,
    { exact or.intro_left _ val.tt },
    { exact or.intro_left _ val.ff },
    {
      apply or.intro_right,
      cases' h,
      cases' ih_e h,
      {
        cases' h_2,
        { exact exists.intro exp.ff (small_step.nor1_tt_any e₂) },
        {
          cases' ih_e_1 h_1,
          {
            cases' h_2,
            { exact exists.intro exp.ff small_step.nor1_ff_tt },
            { exact exists.intro exp.tt small_step.nor1_ff_ff },
          },
          {
            cases' h_2,
            exact exists.intro (exp.nor1 exp.ff w)
                               (small_step.nor1_ff_step e₂ w h_2),
          }
        }
      },
      {
        cases' h_2,
        exact exists.intro (exp.nor1 w e₂)
                           (small_step.nor1_fst_step e₁ w e₂ h_2),
      }
    },
    {
      apply or.intro_right,
      cases' h,
      cases' ih_e_1 h_1,
      {
        cases' h_2,
        { exact exists.intro exp.ff (small_step.nor2_any_tt e₁) },
        {
          cases' ih_e h,
          {
            cases' h_2,
            { exact exists.intro exp.ff small_step.nor2_tt_ff },
            { exact exists.intro exp.tt small_step.nor2_ff_ff },
          },
          {
            cases' h_2,
            exact exists.intro (exp.nor2 w exp.ff)
                               (small_step.nor2_ff_step e₁ w h_2),
          }
        }
      },
      {
        cases' h_2,
        exact exists.intro (exp.nor2 e₁ w)
                           (small_step.nor2_snd_step e₁ e₂ w h_2),
      }
    }
  }
end

inductive star {α : Sort _} (r : α → α → Prop) (a : α) : α → Prop
| refl {}    : star a
| tail {b c} : star b → r b c → star c

def multistep := star small_step

lemma big_small_step_equiv :
  ∀ (e v : exp) (hv : val v), big_step e v ↔ multistep e v :=
begin
  intros e v hv,
  apply iff.intro,
  {
    intro hbigstep,
    unfold multistep,
    -- TODO: induction or cases?
    induction' hbigstep,
    { exact star.refl },
    { exact star.refl },
    {
      -- TODO: this seems to suggest that we should've used induction earlier--
      -- seems unlikely we'd need another case split?
      
      -- FILL IN HERE
      apply small_step.nor1_tt_any,
      cases' hbigstep,
      {
        apply star.tail,
        apply star.refl,
        apply small_step.nor1_tt_any,
      },
      {
        
      }
    }
  }
end
