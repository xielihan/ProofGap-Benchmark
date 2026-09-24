import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace ProofGap.Exercise2444
noncomputable section

open Set
open scoped Interval

def curveX (a t : ℝ) : ℝ := a * (Real.cos t + t * Real.sin t)
def curveY (a t : ℝ) : ℝ := a * (Real.sin t - t * Real.cos t)
def s (a : ℝ) : ℝ := ∫ t in (0 : ℝ)..2 * Real.pi, a * t

theorem gap1 (a t : ℝ) :
    HasDerivAt (curveX a) (a * t * Real.cos t) t := by
  unfold curveX
  convert
    (((Real.hasDerivAt_cos t).add
      ((hasDerivAt_id t).mul (Real.hasDerivAt_sin t))).const_mul a) using 1 <;>
    simp only [id_eq] <;>
    ring

theorem gap2 (a t : ℝ) :
    HasDerivAt (curveY a) (a * t * Real.sin t) t := by
  unfold curveY
  convert
    (((Real.hasDerivAt_sin t).sub
      ((hasDerivAt_id t).mul (Real.hasDerivAt_cos t))).const_mul a) using 1 <;>
    simp only [id_eq] <;>
    ring

theorem gap3 (a t : ℝ) (ha : 0 ≤ a) (ht : t ∈ Icc 0 (2 * Real.pi)) :
    Real.sqrt ((a * t * Real.cos t) ^ 2 + (a * t * Real.sin t) ^ 2) =
      a * t := by
  have hat : 0 ≤ a * t := mul_nonneg ha ht.1
  have hsq :
      (a * t * Real.cos t) ^ 2 + (a * t * Real.sin t) ^ 2 =
        (a * t) ^ 2 := by
    calc
      (a * t * Real.cos t) ^ 2 + (a * t * Real.sin t) ^ 2 =
          (a * t) ^ 2 * (Real.sin t ^ 2 + Real.cos t ^ 2) := by ring
      _ = (a * t) ^ 2 := by rw [Real.sin_sq_add_cos_sq]; ring
  rw [hsq, Real.sqrt_sq hat]

theorem gap4 (a : ℝ) (ha : 0 ≤ a) :
    s a = ∫ t in (0 : ℝ)..2 * Real.pi, a * t := by
  rfl

theorem gap5 (a : ℝ) :
    (∫ t in (0 : ℝ)..2 * Real.pi, a * t) =
      2 * Real.pi ^ 2 * a := by
  have hderiv (x : ℝ) :
      HasDerivAt (fun y : ℝ => a / 2 * y ^ 2) (a * x) x := by
    convert (((hasDerivAt_id x).pow 2).const_mul (a / 2)) using 1 <;>
      simp only [id_eq] <;>
      ring
  have hcont : Continuous (fun x : ℝ => a * x) :=
    continuous_const.mul continuous_id
  have hint : IntervalIntegrable (fun x : ℝ => a * x)
      MeasureTheory.volume (0 : ℝ) (2 * Real.pi) :=
    hcont.intervalIntegrable _ _
  have hFTC :
      (∫ x in (0 : ℝ)..2 * Real.pi, a * x) =
        a / 2 * (2 * Real.pi) ^ 2 - a / 2 * (0 : ℝ) ^ 2 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hderiv x) hint
  rw [hFTC]
  ring

theorem gap6 (a : ℝ) (ha : 0 ≤ a) :
    s a = 2 * Real.pi ^ 2 * a := by
  calc
    s a = ∫ t in (0 : ℝ)..2 * Real.pi, a * t := gap4 a ha
    _ = 2 * Real.pi ^ 2 * a := gap5 a

end
end ProofGap.Exercise2444
