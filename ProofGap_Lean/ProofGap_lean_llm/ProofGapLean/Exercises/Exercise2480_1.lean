import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped Interval

namespace ProofGap.Exercise2480_1

noncomputable section

def volume (a : ℝ) : ℝ :=
  Real.pi * ∫ t in 0..(2 * Real.pi),
    a ^ 3 * (1 - Real.cos t) ^ 3

theorem gap1 (a Vₓ : ℝ) (hV : Vₓ = volume a) :
    Vₓ = Real.pi * ∫ t in 0..(2 * Real.pi),
      a ^ 3 * (1 - Real.cos t) ^ 3 := by
  simpa [volume] using hV

theorem gap2 (a : ℝ) :
    Real.pi * (∫ t in 0..(2 * Real.pi),
      a ^ 3 * (1 - Real.cos t) ^ 3) =
        5 * Real.pi ^ 2 * a ^ 3 := by
  let F : ℝ → ℝ := fun t =>
    a ^ 3 * ((5 / 2 : ℝ) * t - 4 * Real.sin t
      + (3 / 2 : ℝ) * (Real.sin t * Real.cos t)
      + (1 / 3 : ℝ) * (Real.sin t) ^ 3)
  have hderiv (t : ℝ) :
      HasDerivAt F (a ^ 3 * (1 - Real.cos t) ^ 3) t := by
    have hraw : HasDerivAt F
        (a ^ 3 * ((5 / 2 : ℝ) - 4 * Real.cos t
          + (3 / 2 : ℝ) * ((Real.cos t) ^ 2 - (Real.sin t) ^ 2)
          + (Real.sin t) ^ 2 * Real.cos t)) t := by
      dsimp [F]
      convert
        (((((hasDerivAt_id t).const_mul (5 / 2 : ℝ)).sub
            ((Real.hasDerivAt_sin t).const_mul 4)).add
          (((Real.hasDerivAt_sin t).mul (Real.hasDerivAt_cos t)).const_mul
            (3 / 2 : ℝ))).add
          (((Real.hasDerivAt_sin t).pow 3).const_mul (1 / 3 : ℝ))).const_mul
            (a ^ 3) using 1 <;> ring
    have hcoeff :
        (5 / 2 : ℝ) - 4 * Real.cos t
            + (3 / 2 : ℝ) * ((Real.cos t) ^ 2 - (Real.sin t) ^ 2)
            + (Real.sin t) ^ 2 * Real.cos t =
          (1 - Real.cos t) ^ 3 := by
      calc
        (5 / 2 : ℝ) - 4 * Real.cos t
              + (3 / 2 : ℝ) * ((Real.cos t) ^ 2 - (Real.sin t) ^ 2)
              + (Real.sin t) ^ 2 * Real.cos t =
            (1 - Real.cos t) ^ 3
              + (Real.cos t - (3 / 2 : ℝ)) *
                ((Real.sin t) ^ 2 + (Real.cos t) ^ 2 - 1) := by ring
        _ = (1 - Real.cos t) ^ 3 := by
          rw [Real.sin_sq_add_cos_sq]
          ring
    rw [hcoeff] at hraw
    exact hraw
  have hcont : Continuous (fun t : ℝ => a ^ 3 * (1 - Real.cos t) ^ 3) :=
    continuous_const.mul ((continuous_const.sub Real.continuous_cos).pow 3)
  have hint :
      (∫ t in 0..(2 * Real.pi), a ^ 3 * (1 - Real.cos t) ^ 3) =
        F (2 * Real.pi) - F 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      exact hderiv t
    · exact hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 (2 * Real.pi)
  have hF : F (2 * Real.pi) - F 0 = 5 * Real.pi * a ^ 3 := by
    dsimp [F]
    rw [Real.sin_two_pi, Real.sin_zero]
    ring
  rw [hint, hF]
  ring

theorem gap3 (a Vₓ : ℝ) (hV : Vₓ = volume a) :
    Vₓ = 5 * Real.pi ^ 2 * a ^ 3 := by
  rw [hV]
  simpa [volume] using gap2 a

end

end ProofGap.Exercise2480_1
