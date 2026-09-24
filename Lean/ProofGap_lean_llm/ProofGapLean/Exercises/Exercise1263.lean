import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

namespace ProofGap.Exercise1263

noncomputable section

def f (a x : ℝ) : ℝ := Real.arctan ((x + a) / (1 - a * x))
def g (x : ℝ) : ℝ := Real.arctan x

def rawDerivative (a x : ℝ) : ℝ :=
  1 / (1 + ((x + a) / (1 - a * x)) ^ 2) *
    (1 - a * x + a * (x + a)) / (1 - a * x) ^ 2

private lemma deriv_f_eq_rawDerivative (a x : ℝ)
    (hden : 1 - a * x ≠ 0) :
    deriv (f a) x = rawDerivative a x := by
  have hnum : HasDerivAt (fun y : ℝ => y + a) 1 x :=
    (hasDerivAt_id x).add_const a
  have hden' : HasDerivAt (fun y : ℝ => 1 - a * y) (-a) x := by
    convert (hasDerivAt_const (x := x) (1 : ℝ)).sub
      ((hasDerivAt_id x).const_mul a) using 1 <;> ring
  have hquot := hnum.div hden' hden
  have harctan := hquot.arctan
  unfold f rawDerivative
  have h := harctan.deriv
  simp only [Pi.div_apply, one_mul, mul_neg, sub_neg_eq_add,
    mul_comm] at h
  convert h using 1 <;> ring

private lemma rawDerivative_eq (a x : ℝ) (hden : 1 - a * x ≠ 0) :
    rawDerivative a x = 1 / (1 + x ^ 2) := by
  have hnum :
      1 - a * x + a * (x + a) = 1 + a ^ 2 := by ring
  have hfrac :
      1 + ((x + a) / (1 - a * x)) ^ 2 =
        ((1 + a ^ 2) * (1 + x ^ 2)) / (1 - a * x) ^ 2 := by
    have hd2 : (1 - a * x) ^ 2 ≠ 0 := pow_ne_zero 2 hden
    rw [div_pow]
    apply (eq_div_iff hd2).2
    rw [add_mul, one_mul, div_mul_cancel₀ _ hd2]
    ring
  have ha2 : 1 + a ^ 2 ≠ 0 := by positivity
  have hx2 : 1 + x ^ 2 ≠ 0 := by positivity
  unfold rawDerivative
  rw [hnum, hfrac]
  field_simp [hden, ha2, hx2]

theorem gap1 (a x : ℝ) (hax : a * x < 1) :
    deriv (f a) x = rawDerivative a x := by
  exact deriv_f_eq_rawDerivative a x (by linarith)

theorem gap2 (a x : ℝ) (hax : a * x < 1) :
    rawDerivative a x = 1 / (1 + x ^ 2) := by
  exact rawDerivative_eq a x (by linarith)

theorem gap3 (a x : ℝ) (hax : a * x < 1) :
    deriv (f a) x = 1 / (1 + x ^ 2) := by
  rw [gap1 a x hax, gap2 a x hax]

theorem gap4 (a x : ℝ) (hax : a * x < 1) :
    deriv g x = 1 / (1 + x ^ 2) := by
  unfold g
  exact (Real.hasDerivAt_arctan x).deriv

theorem gap5 (a x : ℝ) (hax : a * x < 1) :
    deriv (f a) x = deriv g x := by
  rw [gap3 a x hax, gap4 a x hax]

theorem gap6 (a : ℝ) :
    ∃ C₁, ∀ x, a * x < 1 → f a x - g x = C₁ := by
  refine ⟨Real.arctan a, ?_⟩
  intro x hax
  have hadd := Real.arctan_add hax
  unfold f g
  rw [add_comm x a]
  linarith

theorem gap7 (a x : ℝ) (hax : 1 < a * x) :
    deriv (f a) x = rawDerivative a x := by
  exact deriv_f_eq_rawDerivative a x (by linarith)

theorem gap8 (a x : ℝ) (hax : 1 < a * x) :
    rawDerivative a x = 1 / (1 + x ^ 2) := by
  exact rawDerivative_eq a x (by linarith)

theorem gap9 (a x : ℝ) (hax : 1 < a * x) :
    deriv (f a) x = 1 / (1 + x ^ 2) := by
  rw [gap7 a x hax, gap8 a x hax]

theorem gap10 (a x : ℝ) (hax : 1 < a * x) :
    deriv g x = 1 / (1 + x ^ 2) := by
  unfold g
  exact (Real.hasDerivAt_arctan x).deriv

theorem gap11 (a x : ℝ) (hax : 1 < a * x) :
    deriv (f a) x = deriv g x := by
  rw [gap9 a x hax, gap10 a x hax]

theorem gap12 (a : ℝ) :
    ∃ C₂, ∀ x, 1 < a * x → f a x - g x = C₂ := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · refine ⟨Real.arctan a + Real.pi, ?_⟩
    intro x hax
    have hadd := Real.arctan_add_eq_sub_pi hax ha
    unfold f g
    rw [add_comm x a]
    linarith
  · refine ⟨0, ?_⟩
    intro x hax
    norm_num at hax
  · refine ⟨Real.arctan a - Real.pi, ?_⟩
    intro x hax
    have hadd := Real.arctan_add_eq_add_pi hax ha
    unfold f g
    rw [add_comm x a]
    linarith

theorem gap13 (a : ℝ) (ha : 0 < a) :
    ∃ C₁, -Real.arctan (1 / a) + Real.pi / 2 = C₁ := by
  exact ⟨-Real.arctan (1 / a) + Real.pi / 2, rfl⟩

theorem gap14 (a : ℝ) (ha : 0 < a) :
    -Real.arctan (1 / a) + Real.pi / 2 = Real.arctan a := by
  rw [show 1 / a = a⁻¹ by simp, Real.arctan_inv_of_pos ha]
  ring

theorem gap15 (a x : ℝ) (ha : 0 < a) (hax : a * x < 1) :
    f a x - g x = Real.arctan a := by
  have hadd := Real.arctan_add hax
  unfold f g
  rw [add_comm x a]
  linarith

theorem gap16 (a : ℝ) (ha : 0 < a) :
    ∃ C₂, -Real.arctan (1 / a) - Real.pi / 2 = C₂ := by
  exact ⟨-Real.arctan (1 / a) - Real.pi / 2, rfl⟩

theorem gap17 (a : ℝ) (ha : 0 < a) :
    -Real.arctan (1 / a) - Real.pi / 2 = Real.arctan a - Real.pi := by
  rw [show 1 / a = a⁻¹ by simp, Real.arctan_inv_of_pos ha]
  ring

theorem gap18 (a x : ℝ) (ha : 0 < a) (hax : 1 < a * x) :
    f a x - g x = Real.arctan a - Real.pi := by
  have hadd := Real.arctan_add_eq_add_pi hax ha
  unfold f g
  rw [add_comm x a]
  linarith

end

end ProofGap.Exercise1263
