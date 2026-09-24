import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace ProofGap.Exercise1245

noncomputable section

def f (x : ℝ) : ℝ := 1 / x

def mvtPoint (a b ξ : ℝ) : Prop :=
  ξ ∈ Set.Ioo (min a b) (max a b) ∧
    f b - f a = deriv f ξ * (b - a)

theorem gap1 (a b ξ : ℝ) (hab : a * b < 0) (hξ : mvtPoint a b ξ) :
    f b - f a = deriv f ξ * (b - a) := by
  exact hξ.2

theorem gap2 (a b ξ : ℝ) (hab : a * b < 0) (hξ : mvtPoint a b ξ) :
    1 / b - 1 / a = -(1 / ξ ^ 2) * (b - a) := by
  have h := hξ.2
  have hf : f = fun x : ℝ => x⁻¹ := by
    funext x
    simp [f, one_div]
  rw [hf] at h
  rw [deriv_inv] at h
  simpa [one_div] using h

theorem gap3 (a b ξ : ℝ) (hab : a * b < 0) (hξ : mvtPoint a b ξ) :
    -(1 / ξ ^ 2) * (b - a) = (a - b) / ξ ^ 2 := by
  ring

theorem gap4 (a b ξ : ℝ) (hab : a * b < 0) (hξ : mvtPoint a b ξ) :
    1 / b - 1 / a = (a - b) / ξ ^ 2 := by
  rw [gap2 a b ξ hab hξ, gap3 a b ξ hab hξ]

theorem gap5 (a b : ℝ) (hab : a * b < 0) :
    1 / b - 1 / a = (a - b) / (a * b) := by
  have hab0 : a * b ≠ 0 := ne_of_lt hab
  have ha : a ≠ 0 := fun ha => hab0 (by simp [ha])
  have hb : b ≠ 0 := fun hb => hab0 (by simp [hb])
  field_simp [ha, hb]

theorem gap6 (a b ξ : ℝ) (hab : a * b < 0) (hξ : mvtPoint a b ξ) :
    (a - b) / ξ ^ 2 = (a - b) / (a * b) := by
  calc
    (a - b) / ξ ^ 2 = 1 / b - 1 / a :=
      (gap4 a b ξ hab hξ).symm
    _ = (a - b) / (a * b) := gap5 a b hab

theorem gap7 (a b ξ : ℝ) (hab : a * b < 0) (hξ : mvtPoint a b ξ) :
    ξ ^ 2 = a * b := by
  have hab0 : a * b ≠ 0 := ne_of_lt hab
  have hnum : a - b ≠ 0 := by
    intro heq
    have habEq : a = b := sub_eq_zero.mp heq
    rw [habEq] at hab
    nlinarith [sq_nonneg b]
  have hfrac := gap6 a b ξ hab hξ
  have hξ2 : ξ ^ 2 ≠ 0 := by
    intro hz
    rw [hz, div_zero] at hfrac
    exact (div_ne_zero hnum hab0) hfrac.symm
  have hcross := (div_eq_div_iff hξ2 hab0).mp hfrac
  exact (mul_left_cancel₀ hnum hcross).symm

theorem gap8 (a b ξ : ℝ) (hab : a * b < 0) (hξ : mvtPoint a b ξ) :
    a * b < 0 := by
  exact hab

theorem gap9 (a b ξ : ℝ) (hab : a * b < 0) (hξ : mvtPoint a b ξ) :
    ξ ^ 2 < 0 := by
  rw [gap7 a b ξ hab hξ]
  exact hab

theorem gap10 (a b ξ : ℝ) (hab : a * b < 0) (hξ : mvtPoint a b ξ) :
    False := by
  nlinarith [sq_nonneg ξ, gap9 a b ξ hab hξ]

theorem gap11 (a b : ℝ) (hab : a * b < 0) :
    ¬∃ ξ, mvtPoint a b ξ := by
  rintro ⟨ξ, hξ⟩
  exact gap10 a b ξ hab hξ

theorem gap12 (a b : ℝ) (hab : a * b < 0) :
    ¬∃ ξ, ξ ∈ Set.Ioo (min a b) (max a b) ∧
      f b - f a = deriv f ξ * (b - a) := by
  simpa [mvtPoint] using gap11 a b hab

end

end ProofGap.Exercise1245
