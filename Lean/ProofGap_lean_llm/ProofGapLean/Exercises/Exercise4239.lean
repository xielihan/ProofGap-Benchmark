import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace ProofGap.Exercise4239

noncomputable section

open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def curveMap (t : ℝ) : Vec3 :=
  (t * Real.cos t, t * Real.sin t, t)

def rawSpeed (t : ℝ) : ℝ :=
  Real.sqrt
    ((Real.cos t - t * Real.sin t) ^ 2 +
      (Real.sin t + t * Real.cos t) ^ 2 + 1)

def speed (t : ℝ) : ℝ :=
  Real.sqrt (2 + t ^ 2)

def weightedLength (t₀ : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..t₀, t * rawSpeed t

theorem gap1 (t : ℝ) :
    rawSpeed t =
      Real.sqrt
        ((Real.cos t - t * Real.sin t) ^ 2 +
          (Real.sin t + t * Real.cos t) ^ 2 + 1) := by
  rfl

theorem gap2 (t : ℝ) :
    rawSpeed t = speed t := by
  unfold rawSpeed speed
  congr 1
  calc
    (Real.cos t - t * Real.sin t) ^ 2 +
          (Real.sin t + t * Real.cos t) ^ 2 + 1 =
        (Real.sin t ^ 2 + Real.cos t ^ 2) * (1 + t ^ 2) + 1 := by
          ring
    _ = 2 + t ^ 2 := by
      rw [Real.sin_sq_add_cos_sq]
      ring

theorem gap3 (t : ℝ) :
    rawSpeed t = Real.sqrt (2 + t ^ 2) := by
  simpa [speed] using gap2 t

theorem gap4 (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    weightedLength t₀ =
      ∫ t in (0 : ℝ)..t₀, t * Real.sqrt (2 + t ^ 2) := by
  unfold weightedLength
  simp_rw [gap3]

theorem gap5 (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    (∫ t in (0 : ℝ)..t₀, t * Real.sqrt (2 + t ^ 2)) =
      1 / 3 *
        (Real.rpow (2 + t₀ ^ 2) (3 / 2 : ℝ) -
          Real.rpow 2 (3 / 2 : ℝ)) := by
  let F : ℝ → ℝ := fun x =>
    (1 / 3 : ℝ) * Real.rpow (2 + x ^ 2) (3 / 2 : ℝ)
  have hcont : Continuous (fun x : ℝ => x * Real.sqrt (2 + x ^ 2)) :=
    continuous_id.mul ((continuous_const.add (continuous_id.pow 2)).sqrt)
  have hderiv : ∀ x : ℝ,
      HasDerivAt F (x * Real.sqrt (2 + x ^ 2)) x := by
    intro x
    have hx : 2 + x ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg x]
    have hinner :
        HasDerivAt (fun y : ℝ => 2 + y ^ 2) (2 * x) x := by
      convert (hasDerivAt_const x (2 : ℝ)).add ((hasDerivAt_id x).pow 2) using 1 <;>
        norm_num <;> ring
    dsimp [F]
    convert (((Real.hasDerivAt_rpow_const
      (p := (3 / 2 : ℝ)) (Or.inl hx)).comp x hinner).const_mul
        (1 / 3 : ℝ)) using 1 <;>
      norm_num [Real.sqrt_eq_rpow] <;> ring
  have hderiv_eq :
      deriv F = fun x : ℝ => x * Real.sqrt (2 + x ^ 2) := by
    funext x
    exact (hderiv x).deriv
  have hFTC :
      (∫ x in (0 : ℝ)..t₀, x * Real.sqrt (2 + x ^ 2)) =
        F t₀ - F 0 :=
    intervalIntegral.integral_deriv_eq_sub' F hderiv_eq
      (fun x _ => (hderiv x).differentiableAt)
      hcont.continuousOn
  simpa [F, mul_sub] using hFTC

theorem gap6 (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    weightedLength t₀ =
      1 / 3 *
        (Real.rpow (2 + t₀ ^ 2) (3 / 2 : ℝ) -
          Real.rpow 2 (3 / 2 : ℝ)) := by
  calc
    weightedLength t₀ =
        ∫ t in (0 : ℝ)..t₀, t * Real.sqrt (2 + t ^ 2) := gap4 t₀ ht₀
    _ = 1 / 3 *
        (Real.rpow (2 + t₀ ^ 2) (3 / 2 : ℝ) -
          Real.rpow 2 (3 / 2 : ℝ)) := gap5 t₀ ht₀

end

end ProofGap.Exercise4239
