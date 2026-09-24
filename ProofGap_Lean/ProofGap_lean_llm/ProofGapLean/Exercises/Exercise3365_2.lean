import ProofGapLean.Prelude.Core
import Mathlib.Data.Set.Card
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise3365_2

noncomputable section

def identityFunction (x : ℝ) : ℝ :=
  x

def negIdentityFunction (x : ℝ) : ℝ :=
  -x

def absoluteValueFunction (x : ℝ) : ℝ :=
  |x|

def negAbsoluteValueFunction (x : ℝ) : ℝ :=
  -|x|

def IsContinuousSquareRootChoice (y : ℝ → ℝ) : Prop :=
  Continuous y ∧ ∀ x, x ^ 2 = y x ^ 2

def continuousSquareRootChoices : Set (ℝ → ℝ) :=
  {y | IsContinuousSquareRootChoice y}

private theorem eq_or_eq_neg_of_sq_eq_sq {a b : ℝ} (h : a ^ 2 = b ^ 2) :
    b = a ∨ b = -a := by
  have hfactor : (b - a) * (b + a) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hba | hba
  · left
    linarith
  · right
    linarith

private theorem identity_choice_on_component
    {y : ℝ → ℝ} (hy : Continuous y)
    (hsq : ∀ t, t ^ 2 = y t ^ 2)
    {a x : ℝ}
    (hside : (0 < a ∧ 0 < x) ∨ (a < 0 ∧ x < 0))
    (ha : y a = a) :
    y x = x := by
  rcases eq_or_eq_neg_of_sq_eq_sq (hsq x) with hx | hx
  · exact hx
  · exfalso
    have hneg_cont : Continuous (fun t : ℝ => -y t) := hy.neg
    rcases hside with hpos | hneg
    · rcases hpos with ⟨ha0, hx0⟩
      by_cases hax : a ≤ x
      · obtain ⟨c, hc, hc0⟩ :=
          intermediate_value_Icc hax hneg_cont.continuousOn
            (show (0 : ℝ) ∈ Set.Icc (-y a) (-y x) by
              constructor <;> simp only [ha, hx] <;> linarith)
        have hc_sq := hsq c
        nlinarith [hc.1, hc_sq]
      · have hxa : x ≤ a := (lt_of_not_ge hax).le
        obtain ⟨c, hc, hc0⟩ :=
          intermediate_value_Icc hxa hy.continuousOn
            (show (0 : ℝ) ∈ Set.Icc (y x) (y a) by
              constructor <;> simp only [ha, hx] <;> linarith)
        have hc_sq := hsq c
        nlinarith [hc.1, hc_sq]
    · rcases hneg with ⟨ha0, hx0⟩
      by_cases hax : a ≤ x
      · obtain ⟨c, hc, hc0⟩ :=
          intermediate_value_Icc hax hy.continuousOn
            (show (0 : ℝ) ∈ Set.Icc (y a) (y x) by
              constructor <;> simp only [ha, hx] <;> linarith)
        have hc_sq := hsq c
        nlinarith [hc.2, hc_sq]
      · have hxa : x ≤ a := (lt_of_not_ge hax).le
        obtain ⟨c, hc, hc0⟩ :=
          intermediate_value_Icc hxa hneg_cont.continuousOn
            (show (0 : ℝ) ∈ Set.Icc (-y x) (-y a) by
              constructor <;> simp only [ha, hx] <;> linarith)
        have hc_sq := hsq c
        nlinarith [hc.2, hc_sq]

theorem gap1 :
    continuousSquareRootChoices =
      {negIdentityFunction, identityFunction,
        absoluteValueFunction, negAbsoluteValueFunction} := by
  ext y
  simp only [continuousSquareRootChoices, Set.mem_setOf_eq,
    IsContinuousSquareRootChoice, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hy, hsq⟩
    have hy0 : y 0 = 0 := by
      nlinarith [hsq 0]
    have hsame : ∀ {a x : ℝ},
        ((0 < a ∧ 0 < x) ∨ (a < 0 ∧ x < 0)) →
          y a = a → y x = x := by
      intro a x hside ha
      exact identity_choice_on_component hy hsq hside ha
    have hopp : ∀ {a x : ℝ},
        ((0 < a ∧ 0 < x) ∨ (a < 0 ∧ x < 0)) →
          y a = -a → y x = -x := by
      intro a x hside ha
      have hneg_cont : Continuous (fun t : ℝ => -y t) := hy.neg
      have hneg_sq : ∀ t : ℝ, t ^ 2 = (-y t) ^ 2 := by
        intro t
        calc
          t ^ 2 = y t ^ 2 := hsq t
          _ = (-y t) ^ 2 := by ring
      have hneg_a : -y a = a := by linarith
      have hout := identity_choice_on_component hneg_cont hneg_sq hside hneg_a
      linarith
    rcases eq_or_eq_neg_of_sq_eq_sq (hsq 1) with h1 | h1
    · rcases eq_or_eq_neg_of_sq_eq_sq (hsq (-1)) with hm1 | hm1
      · have hfun : y = identityFunction := by
          funext x
          rcases lt_trichotomy x 0 with hx | hx | hx
          · simpa [identityFunction] using
              hsame (a := (-1 : ℝ)) (x := x)
                (Or.inr ⟨by norm_num, hx⟩) hm1
          · subst x
            simp [identityFunction, hy0]
          · simpa [identityFunction] using
              hsame (a := (1 : ℝ)) (x := x)
                (Or.inl ⟨by norm_num, hx⟩) h1
        exact Or.inr (Or.inl hfun)
      · have hfun : y = absoluteValueFunction := by
          funext x
          rcases lt_trichotomy x 0 with hx | hx | hx
          · simpa [absoluteValueFunction, abs_of_neg hx] using
              hopp (a := (-1 : ℝ)) (x := x)
                (Or.inr ⟨by norm_num, hx⟩) hm1
          · subst x
            simp [absoluteValueFunction, hy0]
          · simpa [absoluteValueFunction, abs_of_pos hx] using
              hsame (a := (1 : ℝ)) (x := x)
                (Or.inl ⟨by norm_num, hx⟩) h1
        exact Or.inr (Or.inr (Or.inl hfun))
    · rcases eq_or_eq_neg_of_sq_eq_sq (hsq (-1)) with hm1 | hm1
      · have hfun : y = negAbsoluteValueFunction := by
          funext x
          rcases lt_trichotomy x 0 with hx | hx | hx
          · simpa [negAbsoluteValueFunction, abs_of_neg hx] using
              hsame (a := (-1 : ℝ)) (x := x)
                (Or.inr ⟨by norm_num, hx⟩) hm1
          · subst x
            simp [negAbsoluteValueFunction, hy0]
          · simpa [negAbsoluteValueFunction, abs_of_pos hx] using
              hopp (a := (1 : ℝ)) (x := x)
                (Or.inl ⟨by norm_num, hx⟩) h1
        exact Or.inr (Or.inr (Or.inr hfun))
      · have hfun : y = negIdentityFunction := by
          funext x
          rcases lt_trichotomy x 0 with hx | hx | hx
          · simpa [negIdentityFunction] using
              hopp (a := (-1 : ℝ)) (x := x)
                (Or.inr ⟨by norm_num, hx⟩) hm1
          · subst x
            simp [negIdentityFunction, hy0]
          · simpa [negIdentityFunction] using
              hopp (a := (1 : ℝ)) (x := x)
                (Or.inl ⟨by norm_num, hx⟩) h1
        exact Or.inl hfun
  · rintro (rfl | rfl | rfl | rfl)
    · constructor
      · simpa [negIdentityFunction] using
          (continuous_id.neg : Continuous (fun x : ℝ => -x))
      · intro x
        simp [negIdentityFunction]
    · constructor
      · simpa [identityFunction] using
          (continuous_id : Continuous (fun x : ℝ => x))
      · intro x
        simp [identityFunction]
    · constructor
      · simpa [absoluteValueFunction] using
          (continuous_id.abs : Continuous (fun x : ℝ => |x|))
      · intro x
        by_cases hx : 0 ≤ x
        · rw [absoluteValueFunction, abs_of_nonneg hx]
        · rw [absoluteValueFunction, abs_of_neg (lt_of_not_ge hx)]
          ring
    · constructor
      · simpa [negAbsoluteValueFunction] using
          (continuous_id.abs.neg : Continuous (fun x : ℝ => -|x|))
      · intro x
        by_cases hx : 0 ≤ x
        · rw [negAbsoluteValueFunction, abs_of_nonneg hx]
          ring
        · rw [negAbsoluteValueFunction, abs_of_neg (lt_of_not_ge hx)]
          ring

theorem gap2 :
    continuousSquareRootChoices.ncard = 4 := by
  have hni_i : negIdentityFunction ≠ identityFunction := by
    intro h
    have h' := congrFun h (1 : ℝ)
    norm_num [negIdentityFunction, identityFunction] at h'
  have hni_abs : negIdentityFunction ≠ absoluteValueFunction := by
    intro h
    have h' := congrFun h (1 : ℝ)
    norm_num [negIdentityFunction, absoluteValueFunction] at h'
  have hni_nabs : negIdentityFunction ≠ negAbsoluteValueFunction := by
    intro h
    have h' := congrFun h (-1 : ℝ)
    norm_num [negIdentityFunction, negAbsoluteValueFunction] at h'
  have hi_abs : identityFunction ≠ absoluteValueFunction := by
    intro h
    have h' := congrFun h (-1 : ℝ)
    norm_num [identityFunction, absoluteValueFunction] at h'
  have hi_nabs : identityFunction ≠ negAbsoluteValueFunction := by
    intro h
    have h' := congrFun h (1 : ℝ)
    norm_num [identityFunction, negAbsoluteValueFunction] at h'
  have habs_nabs : absoluteValueFunction ≠ negAbsoluteValueFunction := by
    intro h
    have h' := congrFun h (1 : ℝ)
    norm_num [absoluteValueFunction, negAbsoluteValueFunction] at h'
  rw [gap1]
  simp [hni_i, hni_abs, hni_nabs, hi_abs, hi_nabs, habs_nabs]

end

end ProofGap.Exercise3365_2
