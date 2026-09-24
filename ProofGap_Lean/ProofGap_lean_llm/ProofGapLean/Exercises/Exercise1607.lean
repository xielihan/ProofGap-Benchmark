import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise1607

noncomputable section

def radius (a φ : ℝ) := a * (1 + Real.cos φ)
def powThreeHalves (u : ℝ) := u * Real.sqrt u
def curvatureRadius (a φ : ℝ) :=
  powThreeHalves ((radius a φ) ^ 2 + (deriv (radius a) φ) ^ 2) /
    ((radius a φ) ^ 2 + 2 * (deriv (radius a) φ) ^ 2 -
      radius a φ * deriv (deriv (radius a)) φ)

private theorem sqrt_two_sq_mul (a u : ℝ) (ha : 0 ≤ a) :
    Real.sqrt (2 * a ^ 2 * u) = Real.sqrt 2 * a * Real.sqrt u := by
  calc
    Real.sqrt (2 * a ^ 2 * u) =
        Real.sqrt 2 * Real.sqrt (a ^ 2 * u) := by
      rw [show 2 * a ^ 2 * u = 2 * (a ^ 2 * u) by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ = Real.sqrt 2 * (Real.sqrt (a ^ 2) * Real.sqrt u) := by
      rw [Real.sqrt_mul (sq_nonneg a)]
    _ = Real.sqrt 2 * a * Real.sqrt u := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ha] <;> ring

theorem gap1 (a φ : ℝ) :
    deriv (radius a) φ = -a * Real.sin φ := by
  unfold radius
  simpa [neg_mul, mul_neg] using
    (((hasDerivAt_const (x := φ) (c := a)).mul
      ((hasDerivAt_const (x := φ) (c := (1 : ℝ))).add
        (Real.hasDerivAt_cos φ))).deriv)
theorem gap2 (a φ : ℝ) :
    deriv (deriv (radius a)) φ = -a * Real.cos φ := by
  have hfun : deriv (radius a) = fun x : ℝ => -a * Real.sin x := by
    funext x
    exact gap1 a x
  rw [hfun]
  simpa using
    (((hasDerivAt_const (x := φ) (c := -a)).mul
      (Real.hasDerivAt_sin φ)).deriv)
theorem gap3 (a φ : ℝ) (ha : 0 < a) (hφ : 0 < 1 + Real.cos φ) :
    curvatureRadius a φ =
      powThreeHalves
          (a ^ 2 * (1 + Real.cos φ) ^ 2 + a ^ 2 * (Real.sin φ) ^ 2) /
        (a ^ 2 * (1 + Real.cos φ) ^ 2 + 2 * a ^ 2 * (Real.sin φ) ^ 2 +
          a ^ 2 * Real.cos φ * (1 + Real.cos φ)) := by
  unfold curvatureRadius
  rw [gap1 a φ, gap2 a φ]
  unfold radius
  have hn :
      (a * (1 + Real.cos φ)) ^ 2 + (-a * Real.sin φ) ^ 2 =
        a ^ 2 * (1 + Real.cos φ) ^ 2 + a ^ 2 * (Real.sin φ) ^ 2 := by
    ring
  have hd :
      (a * (1 + Real.cos φ)) ^ 2 + 2 * (-a * Real.sin φ) ^ 2 -
          a * (1 + Real.cos φ) * (-a * Real.cos φ) =
        a ^ 2 * (1 + Real.cos φ) ^ 2 +
          2 * a ^ 2 * (Real.sin φ) ^ 2 +
          a ^ 2 * Real.cos φ * (1 + Real.cos φ) := by
    ring
  rw [hn, hd]
theorem gap4 (a φ : ℝ) (ha : 0 < a) (hφ : 0 < 1 + Real.cos φ) :
    curvatureRadius a φ =
      2 * Real.sqrt 2 * a ^ 3 * powThreeHalves (1 + Real.cos φ) /
        (3 * a ^ 2 * (1 + Real.cos φ)) := by
  rw [gap3 a φ ha hφ]
  have hsum :
      (1 + Real.cos φ) ^ 2 + (Real.sin φ) ^ 2 =
        2 * (1 + Real.cos φ) := by
    nlinarith [Real.sin_sq_add_cos_sq φ]
  have hdenCore :
      (1 + Real.cos φ) ^ 2 + 2 * (Real.sin φ) ^ 2 +
          Real.cos φ * (1 + Real.cos φ) =
        3 * (1 + Real.cos φ) := by
    nlinarith [Real.sin_sq_add_cos_sq φ]
  have hnumArg :
      a ^ 2 * (1 + Real.cos φ) ^ 2 + a ^ 2 * (Real.sin φ) ^ 2 =
        2 * a ^ 2 * (1 + Real.cos φ) := by
    calc
      a ^ 2 * (1 + Real.cos φ) ^ 2 + a ^ 2 * (Real.sin φ) ^ 2 =
          a ^ 2 * ((1 + Real.cos φ) ^ 2 + (Real.sin φ) ^ 2) := by ring
      _ = a ^ 2 * (2 * (1 + Real.cos φ)) := by rw [hsum]
      _ = 2 * a ^ 2 * (1 + Real.cos φ) := by ring
  have hden :
      a ^ 2 * (1 + Real.cos φ) ^ 2 +
          2 * a ^ 2 * (Real.sin φ) ^ 2 +
          a ^ 2 * Real.cos φ * (1 + Real.cos φ) =
        3 * a ^ 2 * (1 + Real.cos φ) := by
    calc
      a ^ 2 * (1 + Real.cos φ) ^ 2 +
            2 * a ^ 2 * (Real.sin φ) ^ 2 +
            a ^ 2 * Real.cos φ * (1 + Real.cos φ) =
          a ^ 2 * ((1 + Real.cos φ) ^ 2 +
            2 * (Real.sin φ) ^ 2 + Real.cos φ * (1 + Real.cos φ)) := by ring
      _ = a ^ 2 * (3 * (1 + Real.cos φ)) := by rw [hdenCore]
      _ = 3 * a ^ 2 * (1 + Real.cos φ) := by ring
  rw [hnumArg, hden]
  unfold powThreeHalves
  rw [sqrt_two_sq_mul a (1 + Real.cos φ) (le_of_lt ha)]
  ring
theorem gap5 (a φ : ℝ) (ha : 0 < a) (hφ : 0 < 1 + Real.cos φ) :
    curvatureRadius a φ =
      (2 : ℝ) / 3 * Real.sqrt (2 * a * radius a φ) := by
  rw [gap4 a φ ha hφ]
  have hsqrt :
      Real.sqrt (2 * a * radius a φ) =
        Real.sqrt 2 * a * Real.sqrt (1 + Real.cos φ) := by
    rw [radius]
    have hinside :
        2 * a * (a * (1 + Real.cos φ)) =
          2 * a ^ 2 * (1 + Real.cos φ) := by
      ring
    rw [hinside, sqrt_two_sq_mul a (1 + Real.cos φ) (le_of_lt ha)]
  rw [hsqrt]
  unfold powThreeHalves
  field_simp [ne_of_gt ha, ne_of_gt hφ] <;> ring

end
end ProofGap.Exercise1607
