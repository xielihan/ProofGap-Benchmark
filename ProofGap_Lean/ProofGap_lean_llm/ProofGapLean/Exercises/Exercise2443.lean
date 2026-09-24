import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace ProofGap.Exercise2443
noncomputable section

open scoped Interval

def speed (a t : ℝ) : ℝ :=
  Real.sqrt (a ^ 2 * (1 - Real.cos t) ^ 2 + a ^ 2 * Real.sin t ^ 2)
def s (a : ℝ) : ℝ := ∫ t in (0 : ℝ)..2 * Real.pi, speed a t

theorem gap1 (a : ℝ) :
    s a =
      ∫ t in (0 : ℝ)..2 * Real.pi,
        Real.sqrt (a ^ 2 * (1 - Real.cos t) ^ 2 + a ^ 2 * Real.sin t ^ 2) := by
  rfl

theorem gap2 (a : ℝ) (ha : 0 ≤ a) :
    (∫ t in (0 : ℝ)..2 * Real.pi, speed a t) =
      2 * a * ∫ t in (0 : ℝ)..2 * Real.pi, Real.sin (t / 2) := by
  have htwo_pi : (0 : ℝ) ≤ 2 * Real.pi :=
    mul_nonneg (by linarith) Real.pi_pos.le
  have hpoint : ∀ t ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
      speed a t = 2 * a * Real.sin (t / 2) := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
      simpa only [Set.uIcc_of_le htwo_pi] using ht
    have hhalf_nonneg : 0 ≤ t / 2 := by
      linarith [ht'.1]
    have hhalf_le : t / 2 ≤ Real.pi := by
      linarith [ht'.2]
    have hsin_nonneg : 0 ≤ Real.sin (t / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hhalf_nonneg hhalf_le
    have hcos_two :
        Real.cos t = 2 * Real.cos (t / 2) ^ 2 - 1 := by
      convert Real.cos_two_mul (t / 2) using 1 <;> ring
    have hsin_two :
        Real.sin t = 2 * Real.sin (t / 2) * Real.cos (t / 2) := by
      convert Real.sin_two_mul (t / 2) using 1 <;> ring
    have hcosdiff :
        1 - Real.cos t = 2 * Real.sin (t / 2) ^ 2 := by
      rw [hcos_two]
      nlinarith [Real.sin_sq_add_cos_sq (t / 2)]
    have htrig :
        (1 - Real.cos t) ^ 2 + Real.sin t ^ 2 =
          4 * Real.sin (t / 2) ^ 2 := by
      rw [hcosdiff, hsin_two]
      calc
        (2 * Real.sin (t / 2) ^ 2) ^ 2 +
              (2 * Real.sin (t / 2) * Real.cos (t / 2)) ^ 2 =
            4 * Real.sin (t / 2) ^ 2 *
              (Real.sin (t / 2) ^ 2 + Real.cos (t / 2) ^ 2) := by ring
        _ = 4 * Real.sin (t / 2) ^ 2 := by
          rw [Real.sin_sq_add_cos_sq]
          ring
    have hinside :
        a ^ 2 * (1 - Real.cos t) ^ 2 + a ^ 2 * Real.sin t ^ 2 =
          (2 * a * Real.sin (t / 2)) ^ 2 := by
      calc
        a ^ 2 * (1 - Real.cos t) ^ 2 + a ^ 2 * Real.sin t ^ 2 =
            a ^ 2 * ((1 - Real.cos t) ^ 2 + Real.sin t ^ 2) := by ring
        _ = a ^ 2 * (4 * Real.sin (t / 2) ^ 2) := by rw [htrig]
        _ = (2 * a * Real.sin (t / 2)) ^ 2 := by ring
    have hnonneg : 0 ≤ 2 * a * Real.sin (t / 2) :=
      mul_nonneg (mul_nonneg (by linarith) ha) hsin_nonneg
    unfold speed
    rw [hinside, Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg]
  calc
    (∫ t in (0 : ℝ)..2 * Real.pi, speed a t) =
        ∫ t in (0 : ℝ)..2 * Real.pi, 2 * a * Real.sin (t / 2) :=
      intervalIntegral.integral_congr hpoint
    _ = 2 * a * ∫ t in (0 : ℝ)..2 * Real.pi, Real.sin (t / 2) := by
      rw [intervalIntegral.integral_const_mul]

theorem gap3 (a : ℝ) :
    2 * a * (∫ t in (0 : ℝ)..2 * Real.pi, Real.sin (t / 2)) =
      8 * a := by
  let F : ℝ → ℝ := fun t => -2 * Real.cos (t / 2)
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
      HasDerivAt F (Real.sin (t / 2)) t := by
    intro t ht
    dsimp [F]
    convert ((Real.hasDerivAt_cos (t / 2)).comp t
      ((hasDerivAt_id t).div_const 2)).const_mul (-2) using 1 <;> ring
  have hint : IntervalIntegrable (fun t : ℝ => Real.sin (t / 2))
      MeasureTheory.volume (0 : ℝ) (2 * Real.pi) :=
    (Real.continuous_sin.comp (continuous_id.div_const 2)).intervalIntegrable _ _
  have hi :
      (∫ t in (0 : ℝ)..2 * Real.pi, Real.sin (t / 2)) =
        F (2 * Real.pi) - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have harg : (2 * Real.pi) / 2 = Real.pi := by ring
  rw [hi]
  dsimp [F]
  rw [harg, Real.cos_pi]
  simp
  ring

theorem gap4 (a : ℝ) (ha : 0 ≤ a) :
    s a = 8 * a := by
  calc
    s a = ∫ t in (0 : ℝ)..2 * Real.pi, speed a t := rfl
    _ = 2 * a * ∫ t in (0 : ℝ)..2 * Real.pi, Real.sin (t / 2) := gap2 a ha
    _ = 8 * a := gap3 a

end
end ProofGap.Exercise2443
