import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise1069

noncomputable section

def y (a x : ℝ) : ℝ := a * Real.cosh (x / a)

def normalLength (a x : ℝ) : ℝ :=
  |y a x| * Real.sqrt (1 + deriv (y a) x ^ 2)

theorem gap1 (a x : ℝ) (ha : a ≠ 0) :
    normalLength a x =
      |y a x| * Real.sqrt (1 + deriv (y a) x ^ 2) := by
  rfl

theorem gap2 (a x : ℝ) (ha : a ≠ 0) :
    deriv (y a) x = a * (1 / a) * Real.sinh (x / a) := by
  change deriv (fun t => a * Real.cosh (t / a)) x = _
  have hinner : HasDerivAt (fun t : ℝ => t / a) (1 / a) x := by
    simpa using (hasDerivAt_id x).div_const a
  have hcoshRaw := (Real.hasDerivAt_cosh (x / a)).comp x hinner
  have hcosh : HasDerivAt (fun t : ℝ => Real.cosh (t / a))
      ((1 / a) * Real.sinh (x / a)) x := by
    simpa [Function.comp_def, mul_comm] using hcoshRaw
  simpa [mul_assoc] using (hcosh.const_mul a).deriv

theorem gap3 (a x : ℝ) (ha : a ≠ 0) :
    a * (1 / a) * Real.sinh (x / a) = Real.sinh (x / a) := by
  simp [ha]

theorem gap4 (a x : ℝ) (ha : a ≠ 0) :
    deriv (y a) x = Real.sinh (x / a) := by
  rw [gap2 a x ha, gap3 a x ha]

theorem gap5 (a x : ℝ) (ha : a ≠ 0) :
    Real.sqrt (1 + deriv (y a) x ^ 2) =
      Real.sqrt (1 + Real.sinh (x / a) ^ 2) := by
  rw [gap4 a x ha]

theorem gap6 (a x : ℝ) (ha : a ≠ 0) :
    Real.sqrt (1 + Real.sinh (x / a) ^ 2) =
      |Real.cosh (x / a)| := by
  have h : 1 + Real.sinh (x / a) ^ 2 = Real.cosh (x / a) ^ 2 := by
    linarith [Real.cosh_sq_sub_sinh_sq (x / a)]
  rw [h, Real.sqrt_sq_eq_abs]

theorem gap7 (a x : ℝ) (ha : a ≠ 0) :
    |Real.cosh (x / a)| = |y a x / a| := by
  simp [y, ha]

theorem gap8 (a x : ℝ) (ha : a ≠ 0) :
    Real.sqrt (1 + deriv (y a) x ^ 2) = |y a x / a| := by
  rw [gap5 a x ha, gap6 a x ha, gap7 a x ha]

theorem gap9 (a x₀ y₀ : ℝ) (ha : a ≠ 0) (hpoint : y a x₀ = y₀) :
    normalLength a x₀ = |y₀| * |y₀ / a| := by
  rw [gap1 a x₀ ha, gap8 a x₀ ha, hpoint]

theorem gap10 (a y₀ : ℝ) (ha : a ≠ 0) :
    |y₀| * |y₀ / a| = y₀ ^ 2 / |a| := by
  calc
    |y₀| * |y₀ / a| = |y₀| * (|y₀| / |a|) := by rw [abs_div]
    _ = (|y₀| * |y₀|) / |a| := by rw [mul_div_assoc]
    _ = y₀ ^ 2 / |a| := by
      rw [← abs_mul, abs_of_nonneg (mul_self_nonneg y₀)]
      simp [pow_two]

theorem gap11 (a x₀ y₀ : ℝ) (ha : a ≠ 0) (hpoint : y a x₀ = y₀) :
    normalLength a x₀ = y₀ ^ 2 / |a| := by
  rw [gap9 a x₀ y₀ ha hpoint, gap10 a y₀ ha]

theorem gap12 (a x₀ y₀ : ℝ) (ha : a ≠ 0) (hpoint : y a x₀ = y₀) :
    normalLength a x₀ = y₀ ^ 2 / |a| := by
  exact gap11 a x₀ y₀ ha hpoint

end

end ProofGap.Exercise1069
