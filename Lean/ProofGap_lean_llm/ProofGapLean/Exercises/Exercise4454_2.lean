import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise4454_2

noncomputable section

open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def dot (p q : Vec3) : ℝ :=
  p.1 * q.1 + p.2.1 * q.2.1 + p.2.2 * q.2.2

def shiftedCircle (t : ℝ) : Vec3 :=
  (2 + Real.cos t, Real.sin t, 0)

def shiftedCircleVelocity (t : ℝ) : Vec3 :=
  (-Real.sin t, Real.cos t, 0)

def swirlField (c : ℝ) (p : Vec3) : Vec3 :=
  (-p.2.1, p.1, c)

def workPullback (c t : ℝ) : ℝ :=
  dot (swirlField c (shiftedCircle t)) (shiftedCircleVelocity t)

def lineIntegral (c : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..2 * Real.pi, workPullback c t

theorem gap1 (t : ℝ) :
    shiftedCircle t = (2 + Real.cos t, Real.sin t, 0) := by
  rfl

theorem gap2 (c t : ℝ) :
    workPullback c t = 2 * Real.cos t + 1 := by
  dsimp [workPullback, dot, swirlField, shiftedCircle, shiftedCircleVelocity]
  nlinarith [Real.sin_sq_add_cos_sq t]

theorem gap3 (c : ℝ) :
    lineIntegral c =
      ∫ t in (0 : ℝ)..2 * Real.pi, (2 * Real.cos t + 1) := by
  simp [lineIntegral, gap2]

theorem gap4 :
    (∫ t in (0 : ℝ)..2 * Real.pi, (2 * Real.cos t + 1)) =
      2 * Real.pi := by
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const_mul]
    have hcos :
        (∫ x in (0 : ℝ)..2 * Real.pi, Real.cos x) =
          Real.sin (2 * Real.pi) - Real.sin 0 := by
      apply intervalIntegral.integral_deriv_eq_sub'
      · funext x
        exact (Real.hasDerivAt_sin x).deriv
      · intro x hx
        exact (Real.hasDerivAt_sin x).differentiableAt
      · exact Real.continuous_cos.continuousOn
    rw [hcos]
    simp
  · exact (continuous_const.mul Real.continuous_cos).intervalIntegrable _ _
  · exact continuous_const.intervalIntegrable _ _

theorem gap5 (c : ℝ) :
    lineIntegral c = 2 * Real.pi := by
  calc
    lineIntegral c = ∫ t in (0 : ℝ)..2 * Real.pi, (2 * Real.cos t + 1) := gap3 c
    _ = 2 * Real.pi := gap4

end

end ProofGap.Exercise4454_2
