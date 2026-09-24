import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open scoped Interval

namespace ProofGap.Exercise2320

noncomputable section

def meanVelocity (v : ℝ → ℝ) (T : ℝ) : ℝ :=
  1 / T * ∫ t in 0..T, v t

theorem gap1 (v : ℝ → ℝ) (g T : ℝ)
    (hv : ∀ t, v t = v 0 + g * t) :
    meanVelocity v T =
      1 / T * ∫ t in 0..T, (v 0 + g * t) := by
  unfold meanVelocity
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  exact hv t

theorem gap2 (v : ℝ → ℝ) (g T : ℝ) (hT : T ≠ 0) :
    1 / T * (∫ t in 0..T, (v 0 + g * t)) =
      (1 / 2 : ℝ) * g * T + v 0 := by
  have hc : IntervalIntegrable (fun _ : ℝ => v 0) MeasureTheory.volume 0 T :=
    continuous_const.intervalIntegrable 0 T
  have hl : IntervalIntegrable (fun t : ℝ => g * t) MeasureTheory.volume 0 T :=
    (((by fun_prop) : Continuous fun t : ℝ => g * t).intervalIntegrable 0 T)
  rw [intervalIntegral.integral_add hc hl]
  rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_id]
  simp only [sub_zero, smul_eq_mul]
  field_simp [hT]
  ring

theorem gap3 (v : ℝ → ℝ) (g T : ℝ)
    (hvT : v T = v 0 + g * T) :
    (1 / 2 : ℝ) * g * T + v 0 =
      (1 / 2 : ℝ) * (v 0 + v T) := by
  rw [hvT]
  ring

theorem gap4 (v : ℝ → ℝ) (g T : ℝ) (hT : T ≠ 0)
    (hv : ∀ t, v t = v 0 + g * t) :
    meanVelocity v T =
      (1 / 2 : ℝ) * (v 0 + v T) := by
  rw [gap1 v g T hv, gap2 v g T hT]
  exact gap3 v g T (hv T)

end

end ProofGap.Exercise2320
