import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped Interval

namespace ProofGap.Exercise2507

noncomputable section

def arcLength (a α : ℝ) : ℝ := 2 * a * α
def xMoment (a α : ℝ) : ℝ := ∫ φ in -α..α, a ^ 2 * Real.cos φ

theorem gap1 (η : ℝ) (hη : η = 0) : η = 0 := by
  exact hη

theorem gap2 (a α s : ℝ) (hs : s = arcLength a α) :
    s = 2 * a * α := by
  simpa [arcLength] using hs

theorem gap3 (a α My : ℝ) (hMy : My = xMoment a α) :
    My = ∫ φ in -α..α, a ^ 2 * Real.cos φ := by
  simpa [xMoment] using hMy

theorem gap4 (a α My : ℝ) (hMy : My = xMoment a α) :
    My = ∫ φ in -α..α, a ^ 2 * Real.cos φ := by
  exact gap3 a α My hMy

theorem gap5 (a α : ℝ) :
    (∫ φ in -α..α, a ^ 2 * Real.cos φ) =
      2 * a ^ 2 * Real.sin α := by
  rw [intervalIntegral.integral_const_mul]
  have hderiv : deriv Real.sin = Real.cos := by
    funext x
    exact (Real.hasDerivAt_sin x).deriv
  have hcos :
      (∫ x in -α..α, Real.cos x) =
        Real.sin α - Real.sin (-α) := by
    apply intervalIntegral.integral_deriv_eq_sub' Real.sin hderiv <;>
      first
      | exact fun x _ => (Real.hasDerivAt_sin x).differentiableAt
      | exact Real.continuous_cos
      | exact Real.continuous_cos.continuousOn
      | exact Real.continuous_cos.intervalIntegrable _ _
  rw [hcos, Real.sin_neg]
  ring

theorem gap6 (a α My : ℝ) (hMy : My = xMoment a α) :
    My = 2 * a ^ 2 * Real.sin α := by
  calc
    My = ∫ φ in -α..α, a ^ 2 * Real.cos φ := gap3 a α My hMy
    _ = 2 * a ^ 2 * Real.sin α := gap5 a α

theorem gap7 (a α ξ My s : ℝ) (hs : s = arcLength a α)
    (hMy : My = 2 * a ^ 2 * Real.sin α) (hξ : ξ = My / s) :
    ξ = (2 * a ^ 2 * Real.sin α) / (2 * a * α) := by
  calc
    ξ = My / s := hξ
    _ = (2 * a ^ 2 * Real.sin α) / (2 * a * α) := by
      rw [hMy, hs, arcLength]

theorem gap8 (a α : ℝ) (ha : a ≠ 0) (hα : α ≠ 0) :
    (2 * a ^ 2 * Real.sin α) / (2 * a * α) =
      a * Real.sin α / α := by
  field_simp [ha, hα] <;> ring

theorem gap9 (a α ξ : ℝ) (ha : a ≠ 0) (hα : α ≠ 0)
    (hξ : ξ = (2 * a ^ 2 * Real.sin α) / (2 * a * α)) :
    ξ = a * Real.sin α / α := by
  calc
    ξ = (2 * a ^ 2 * Real.sin α) / (2 * a * α) := hξ
    _ = a * Real.sin α / α := gap8 a α ha hα

theorem gap10 (a α ξ η : ℝ) (ha : a ≠ 0) (hα : α ≠ 0)
    (hξ : ξ = a * Real.sin α / α) (hη : η = 0) :
    (ξ, η) = (a * Real.sin α / α, 0) := by
  rw [hξ, hη]

end

end ProofGap.Exercise2507
