import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4223

noncomputable section

open MeasureTheory
open scoped Interval

def involute (a t : ℝ) : ℝ × ℝ :=
  (a * (Real.cos t + t * Real.sin t),
    a * (Real.sin t - t * Real.cos t))

def involuteSpeed (a t : ℝ) : ℝ :=
  Real.sqrt
    ((deriv (fun s => (involute a s).1) t) ^ 2 +
      (deriv (fun s => (involute a s).2) t) ^ 2)

def weightedCurveIntegral (a : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..2 * Real.pi,
    (((involute a t).1) ^ 2 + ((involute a t).2) ^ 2) *
      involuteSpeed a t

theorem gap1 (a t : ℝ) :
    involuteSpeed a t =
      Real.sqrt
        (a ^ 2 * t ^ 2 * (Real.cos t) ^ 2 +
          a ^ 2 * t ^ 2 * (Real.sin t) ^ 2) := by
  have hid : HasDerivAt (fun s : ℝ => s) 1 t := by
    simpa only [id_eq] using (hasDerivAt_id t)
  have h₁ :
      HasDerivAt
        (fun s : ℝ => a * (Real.cos s + s * Real.sin s))
        (a * t * Real.cos t) t := by
    convert
      (hasDerivAt_const t a).mul
        ((Real.hasDerivAt_cos t).add
          (hid.mul (Real.hasDerivAt_sin t))) using 1 <;> ring
  have h₂ :
      HasDerivAt
        (fun s : ℝ => a * (Real.sin s - s * Real.cos s))
        (a * t * Real.sin t) t := by
    convert
      (hasDerivAt_const t a).mul
        ((Real.hasDerivAt_sin t).sub
          (hid.mul (Real.hasDerivAt_cos t))) using 1 <;> ring
  unfold involuteSpeed
  simp only [involute, Prod.fst, Prod.snd]
  rw [h₁.deriv, h₂.deriv]
  congr 1
  ring

theorem gap2
    (a t : ℝ) (ha : 0 < a)
    (ht : t ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    Real.sqrt
        (a ^ 2 * t ^ 2 * (Real.cos t) ^ 2 +
          a ^ 2 * t ^ 2 * (Real.sin t) ^ 2) =
      a * t := by
  have htrig : (Real.cos t) ^ 2 + (Real.sin t) ^ 2 = 1 := by
    simpa [add_comm] using Real.sin_sq_add_cos_sq t
  calc
    Real.sqrt
        (a ^ 2 * t ^ 2 * (Real.cos t) ^ 2 +
          a ^ 2 * t ^ 2 * (Real.sin t) ^ 2) =
        Real.sqrt ((a * t) ^ 2) := by
          congr 1
          rw [← mul_add, htrig]
          ring
    _ = |a * t| := Real.sqrt_sq_eq_abs (a * t)
    _ = a * t := by
      rw [abs_of_nonneg]
      exact mul_nonneg (le_of_lt ha) ht.1

theorem gap3
    (a t : ℝ) (ha : 0 < a)
    (ht : t ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    involuteSpeed a t = a * t := by
  rw [gap1 a t, gap2 a t ha ht]

theorem gap4 (a : ℝ) (ha : 0 < a) :
    weightedCurveIntegral a =
      ∫ t in (0 : ℝ)..2 * Real.pi,
        (a ^ 2 * (Real.cos t + t * Real.sin t) ^ 2 +
          a ^ 2 * (Real.sin t - t * Real.cos t) ^ 2) *
          (a * t) := by
  unfold weightedCurveIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  have hnonneg : (0 : ℝ) ≤ 2 * Real.pi := by
    exact mul_nonneg (by norm_num) Real.pi_nonneg
  rw [Set.uIcc_of_le hnonneg] at ht
  simp only [involute, Prod.fst, Prod.snd]
  rw [gap3 a t ha ht]
  ring

theorem gap5 (a : ℝ) :
    (∫ t in (0 : ℝ)..2 * Real.pi,
        (a ^ 2 * (Real.cos t + t * Real.sin t) ^ 2 +
          a ^ 2 * (Real.sin t - t * Real.cos t) ^ 2) *
          (a * t)) =
      ∫ t in (0 : ℝ)..2 * Real.pi,
        a ^ 3 * t * (1 + t ^ 2) := by
  apply intervalIntegral.integral_congr
  intro t _
  have htrig : (Real.cos t) ^ 2 + (Real.sin t) ^ 2 = 1 := by
    simpa [add_comm] using Real.sin_sq_add_cos_sq t
  calc
    (a ^ 2 * (Real.cos t + t * Real.sin t) ^ 2 +
        a ^ 2 * (Real.sin t - t * Real.cos t) ^ 2) *
        (a * t) =
      a ^ 3 * t * (1 + t ^ 2) *
        ((Real.cos t) ^ 2 + (Real.sin t) ^ 2) := by ring
    _ = a ^ 3 * t * (1 + t ^ 2) := by rw [htrig, mul_one]

theorem gap6 (a : ℝ) :
    (∫ t in (0 : ℝ)..2 * Real.pi,
        a ^ 3 * t * (1 + t ^ 2)) =
      2 * Real.pi ^ 2 * a ^ 3 * (1 + 2 * Real.pi ^ 2) := by
  let F : ℝ → ℝ :=
    fun t => a ^ 3 / 2 * t ^ 2 + a ^ 3 / 4 * t ^ 4
  have hF (t : ℝ) :
      HasDerivAt F (a ^ 3 * t * (1 + t ^ 2)) t := by
    have hid : HasDerivAt (fun s : ℝ => s) 1 t := by
      simpa only [id_eq] using (hasDerivAt_id t)
    dsimp [F]
    convert
      ((hasDerivAt_const t (a ^ 3 / 2)).mul (hid.pow 2)).add
        ((hasDerivAt_const t (a ^ 3 / 4)).mul (hid.pow 4))
      using 1 <;> ring
  have hcont :
      Continuous (fun t : ℝ => a ^ 3 * t * (1 + t ^ 2)) :=
    (continuous_const.mul continuous_id).mul
      (continuous_const.add (continuous_id.pow 2))
  calc
    (∫ t in (0 : ℝ)..2 * Real.pi,
        a ^ 3 * t * (1 + t ^ 2)) =
      F (2 * Real.pi) - F 0 := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        all_goals
          first
          | exact hcont.continuousOn
          | exact hcont.intervalIntegrable _ _
          | intro t _
            exact hF t
          | intro t
            exact hF t
    _ = 2 * Real.pi ^ 2 * a ^ 3 * (1 + 2 * Real.pi ^ 2) := by
      dsimp [F]
      ring

theorem gap7 (a : ℝ) (ha : 0 < a) :
    weightedCurveIntegral a =
      2 * Real.pi ^ 2 * a ^ 3 * (1 + 2 * Real.pi ^ 2) := by
  calc
    weightedCurveIntegral a =
        ∫ t in (0 : ℝ)..2 * Real.pi,
          (a ^ 2 * (Real.cos t + t * Real.sin t) ^ 2 +
            a ^ 2 * (Real.sin t - t * Real.cos t) ^ 2) *
            (a * t) := gap4 a ha
    _ = ∫ t in (0 : ℝ)..2 * Real.pi,
          a ^ 3 * t * (1 + t ^ 2) := gap5 a
    _ = 2 * Real.pi ^ 2 * a ^ 3 * (1 + 2 * Real.pi ^ 2) := gap6 a

end

end ProofGap.Exercise4223
