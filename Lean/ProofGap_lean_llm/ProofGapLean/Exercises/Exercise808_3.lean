import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise808_3

noncomputable section

def f (x : ℝ) : ℝ := Real.sin x + Real.cos x
def oscSet (δ : ℝ) : Set ℝ :=
  {|f x - f y| | (x ∈ Set.Icc (0 : ℝ) (2 * Real.pi))
    (y ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) (h : |x - y| ≤ δ)}
def ω (δ : ℝ) : ℝ := sSup (oscSet δ)

theorem gap1 (x : ℝ) :
    f x = Real.sqrt 2 * Real.sin (x + Real.pi / 4) := by
  rw [f, Real.sin_add, Real.sin_pi_div_four, Real.cos_pi_div_four]
  have hs : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) :=
    Real.mul_self_sqrt (by norm_num)
  calc
    Real.sin x + Real.cos x =
        (Real.sqrt 2 * Real.sqrt 2) / 2 *
          (Real.sin x + Real.cos x) := by
      rw [hs]
      ring
    _ = Real.sqrt 2 *
        (Real.sin x * (Real.sqrt 2 / 2) +
          Real.cos x * (Real.sqrt 2 / 2)) := by
      ring
theorem gap2 (x₁ x₂ : ℝ) :
    |Real.sqrt 2 * Real.sin (x₁ + Real.pi / 4) -
      Real.sqrt 2 * Real.sin (x₂ + Real.pi / 4)| =
    Real.sqrt 2 * 2 *
      |Real.cos ((x₁ + x₂ + Real.pi / 2) / 2) *
        Real.sin ((x₁ - x₂) / 2)| := by
  have hsum :
      ((x₁ + Real.pi / 4) + (x₂ + Real.pi / 4)) / 2 =
        (x₁ + x₂ + Real.pi / 2) / 2 := by
    ring
  have hdiff :
      ((x₁ + Real.pi / 4) - (x₂ + Real.pi / 4)) / 2 =
        (x₁ - x₂) / 2 := by
    ring
  rw [← mul_sub, Real.sin_sub_sin, hsum, hdiff]
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have htwo : (0 : ℝ) ≤ 2 := by norm_num
  simp only [abs_mul, abs_of_nonneg hs, abs_of_nonneg htwo]
  ring
theorem gap3 (x₁ x₂ : ℝ) :
    |Real.sqrt 2 * Real.sin (x₁ + Real.pi / 4) -
      Real.sqrt 2 * Real.sin (x₂ + Real.pi / 4)| ≤
    Real.sqrt 2 * 2 * (|x₁ - x₂| / 2) := by
  have hc :
      |Real.cos ((x₁ + x₂ + Real.pi / 2) / 2)| ≤ 1 :=
    Real.abs_cos_le_one _
  have hs :
      |Real.sin ((x₁ - x₂) / 2)| ≤ |(x₁ - x₂) / 2| :=
    Real.abs_sin_le_abs
  have hK : 0 ≤ Real.sqrt 2 * 2 :=
    mul_nonneg (Real.sqrt_nonneg _) (by norm_num)
  have hc_mul :
      |Real.cos ((x₁ + x₂ + Real.pi / 2) / 2)| *
          |Real.sin ((x₁ - x₂) / 2)| ≤
        1 * |Real.sin ((x₁ - x₂) / 2)| :=
    mul_le_mul_of_nonneg_right hc (abs_nonneg _)
  have hs_mul :
      1 * |Real.sin ((x₁ - x₂) / 2)| ≤
        1 * |(x₁ - x₂) / 2| :=
    mul_le_mul_of_nonneg_left hs (by norm_num)
  calc
    |Real.sqrt 2 * Real.sin (x₁ + Real.pi / 4) -
        Real.sqrt 2 * Real.sin (x₂ + Real.pi / 4)| =
        Real.sqrt 2 * 2 *
          (|Real.cos ((x₁ + x₂ + Real.pi / 2) / 2)| *
            |Real.sin ((x₁ - x₂) / 2)|) := by
      rw [gap2, abs_mul]
    _ ≤ Real.sqrt 2 * 2 *
        (1 * |Real.sin ((x₁ - x₂) / 2)|) :=
      mul_le_mul_of_nonneg_left hc_mul hK
    _ ≤ Real.sqrt 2 * 2 * (1 * |(x₁ - x₂) / 2|) :=
      mul_le_mul_of_nonneg_left hs_mul hK
    _ = Real.sqrt 2 * 2 * (|x₁ - x₂| / 2) := by
      norm_num [abs_div]
theorem gap4 (δ x₁ x₂ : ℝ) (hδ : |x₁ - x₂| ≤ δ) :
    Real.sqrt 2 * 2 * (|x₁ - x₂| / 2) ≤ Real.sqrt 2 * δ := by
  calc
    Real.sqrt 2 * 2 * (|x₁ - x₂| / 2) =
        Real.sqrt 2 * |x₁ - x₂| := by
      ring
    _ ≤ Real.sqrt 2 * δ :=
      mul_le_mul_of_nonneg_left hδ (Real.sqrt_nonneg _)
theorem gap5 (δ x₁ x₂ : ℝ) (hδ : |x₁ - x₂| ≤ δ) :
    |Real.sqrt 2 * Real.sin (x₁ + Real.pi / 4) -
      Real.sqrt 2 * Real.sin (x₂ + Real.pi / 4)| ≤ Real.sqrt 2 * δ := by
  exact (gap3 x₁ x₂).trans (gap4 δ x₁ x₂ hδ)
theorem gap6 (δ : ℝ) (hδ : 0 ≤ δ) : ω δ ≤ Real.sqrt 2 * δ := by
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (2 * Real.pi) :=
    ⟨le_rfl, mul_nonneg (by norm_num) (le_of_lt Real.pi_pos)⟩
  have hdist : |(0 : ℝ) - 0| ≤ δ := by
    simpa using hδ
  have hne : (oscSet δ).Nonempty := by
    refine ⟨|f 0 - f 0|, ?_⟩
    exact ⟨0, hzero, 0, hzero, hdist, rfl⟩
  refine csSup_le hne ?_
  intro z hz
  rcases hz with ⟨x, hx, y, hy, hxy, rfl⟩
  simpa only [gap1] using gap5 δ x y hxy
theorem gap7 (δ : ℝ) (hδ : 0 ≤ δ) :
    let C := Real.sqrt 2
    let α : ℕ := 1
    ω δ ≤ C * δ ^ α := by
  simpa only [pow_one] using gap6 δ hδ

end

end ProofGap.Exercise808_3
