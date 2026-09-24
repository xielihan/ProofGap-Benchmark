import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped Interval

namespace ProofGap.Exercise2278

noncomputable section

def originalIntegral : ℝ :=
  ∫ x in 0..Real.pi, (x * Real.sin x) ^ 2

def firstBoundary (x : ℝ) : ℝ := x ^ 2 / 4 * Real.sin (2 * x)
def secondBoundary (x : ℝ) : ℝ := -x / 4 * Real.cos (2 * x)

private theorem square_sine_integrand (x : ℝ) :
    (x * Real.sin x) ^ 2 =
      (1 / 2 : ℝ) * (x ^ 2 * (1 - Real.cos (2 * x))) := by
  have htrig : 1 - Real.cos (2 * x) = 2 * Real.sin x ^ 2 := by
    rw [show (2 : ℝ) * x = x + x by ring, Real.cos_add]
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [htrig]
  ring

private theorem integral_of_global_derivative
    (f F : ℝ → ℝ) (a b : ℝ)
    (hd : ∀ x, HasDerivAt F (f x) x)
    (hc : Continuous f) :
    (∫ x in a..b, f x) = F b - F a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hd x) (hc.intervalIntegrable a b)

private theorem hasDerivAt_sin_two (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sin (2 * y))
      (2 * Real.cos (2 * x)) x := by
  convert (Real.hasDerivAt_sin (2 * x)).comp x
    ((hasDerivAt_id x).const_mul 2) using 1 <;> ring

private theorem hasDerivAt_cos_two (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.cos (2 * y))
      (-2 * Real.sin (2 * x)) x := by
  convert (Real.hasDerivAt_cos (2 * x)).comp x
    ((hasDerivAt_id x).const_mul 2) using 1 <;> ring

private theorem continuous_sin_two :
    Continuous (fun x : ℝ => Real.sin (2 * x)) := by
  exact Real.continuous_sin.comp (continuous_const.mul continuous_id)

private theorem continuous_cos_two :
    Continuous (fun x : ℝ => Real.cos (2 * x)) := by
  exact Real.continuous_cos.comp (continuous_const.mul continuous_id)

private theorem original_integral_value :
    originalIntegral = Real.pi ^ 3 / 6 - Real.pi / 4 := by
  let F : ℝ → ℝ := fun x =>
    x ^ 3 / 6 -
      (x ^ 2 * Real.sin (2 * x) / 4 +
        x * Real.cos (2 * x) / 4 - Real.sin (2 * x) / 8)
  have hd : ∀ x : ℝ,
      HasDerivAt F
        ((1 / 2 : ℝ) * (x ^ 2 * (1 - Real.cos (2 * x)))) x := by
    intro x
    dsimp [F]
    convert (((hasDerivAt_id x).pow 3).div_const 6).sub
      ((((((hasDerivAt_id x).pow 2).mul (hasDerivAt_sin_two x)).div_const 4).add
        (((hasDerivAt_id x).mul (hasDerivAt_cos_two x)).div_const 4)).sub
        ((hasDerivAt_sin_two x).div_const 8)) using 1 <;>
      simp [id_eq] <;> ring
  have hc : Continuous
      (fun x : ℝ => (1 / 2 : ℝ) * (x ^ 2 * (1 - Real.cos (2 * x)))) := by
    exact continuous_const.mul
      ((continuous_id.pow 2).mul (continuous_const.sub continuous_cos_two))
  calc
    originalIntegral =
        ∫ x in 0..Real.pi,
          (1 / 2 : ℝ) * (x ^ 2 * (1 - Real.cos (2 * x))) := by
      unfold originalIntegral
      apply intervalIntegral.integral_congr
      intro x _
      exact square_sine_integrand x
    _ = F Real.pi - F 0 :=
      integral_of_global_derivative _ _ _ _ hd hc
    _ = Real.pi ^ 3 / 6 - Real.pi / 4 := by
      dsimp [F]
      simp [Real.sin_two_pi, Real.cos_two_pi]

private theorem integral_square_cos_two_value :
    (∫ x in 0..Real.pi, x ^ 2 * Real.cos (2 * x)) = Real.pi / 2 := by
  let F : ℝ → ℝ := fun x =>
    x ^ 2 * Real.sin (2 * x) / 2 +
      x * Real.cos (2 * x) / 2 - Real.sin (2 * x) / 4
  have hd : ∀ x : ℝ,
      HasDerivAt F (x ^ 2 * Real.cos (2 * x)) x := by
    intro x
    dsimp [F]
    convert (((((hasDerivAt_id x).pow 2).mul
      (hasDerivAt_sin_two x)).div_const 2).add
      (((hasDerivAt_id x).mul
        (hasDerivAt_cos_two x)).div_const 2)).sub
      ((hasDerivAt_sin_two x).div_const 4) using 1 <;>
      simp [id_eq] <;> ring
  have hc : Continuous (fun x : ℝ => x ^ 2 * Real.cos (2 * x)) :=
    (continuous_id.pow 2).mul continuous_cos_two
  calc
    (∫ x in 0..Real.pi, x ^ 2 * Real.cos (2 * x)) =
        F Real.pi - F 0 :=
      integral_of_global_derivative _ _ _ _ hd hc
    _ = Real.pi / 2 := by
      dsimp [F]
      simp [Real.sin_two_pi, Real.cos_two_pi]

private theorem integral_mul_sin_two_value :
    (∫ x in 0..Real.pi, x * Real.sin (2 * x)) = -Real.pi / 2 := by
  let F : ℝ → ℝ := fun x =>
    -x * Real.cos (2 * x) / 2 + Real.sin (2 * x) / 4
  have hd : ∀ x : ℝ,
      HasDerivAt F (x * Real.sin (2 * x)) x := by
    intro x
    dsimp [F]
    convert (((((hasDerivAt_id x).neg.mul
      (hasDerivAt_cos_two x)).div_const 2).add
      ((hasDerivAt_sin_two x).div_const 4))) using 1 <;>
      simp [id_eq] <;> ring
  have hc : Continuous (fun x : ℝ => x * Real.sin (2 * x)) :=
    continuous_id.mul continuous_sin_two
  calc
    (∫ x in 0..Real.pi, x * Real.sin (2 * x)) =
        F Real.pi - F 0 :=
      integral_of_global_derivative _ _ _ _ hd hc
    _ = -Real.pi / 2 := by
      dsimp [F]
      simp [Real.sin_two_pi, Real.cos_two_pi]

private theorem integral_cos_two_value :
    (∫ x in 0..Real.pi, Real.cos (2 * x)) = 0 := by
  let F : ℝ → ℝ := fun x => Real.sin (2 * x) / 2
  have hd : ∀ x : ℝ,
      HasDerivAt F (Real.cos (2 * x)) x := by
    intro x
    dsimp [F]
    convert (hasDerivAt_sin_two x).div_const 2 using 1 <;> ring
  calc
    (∫ x in 0..Real.pi, Real.cos (2 * x)) = F Real.pi - F 0 :=
      integral_of_global_derivative _ _ _ _ hd continuous_cos_two
    _ = 0 := by
      dsimp [F]
      simp [Real.sin_two_pi]

theorem gap1 :
    originalIntegral =
      (1 / 2 : ℝ) * ∫ x in 0..Real.pi, x ^ 2 * (1 - Real.cos (2 * x)) := by
  unfold originalIntegral
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  exact square_sine_integrand x

theorem gap2 :
    originalIntegral =
      Real.pi ^ 3 / 6 -
        (1 / 2 : ℝ) * ∫ x in 0..Real.pi, x ^ 2 * Real.cos (2 * x) := by
  rw [original_integral_value, integral_square_cos_two_value]
  ring

theorem gap3 :
    originalIntegral =
      Real.pi ^ 3 / 6 -
        (firstBoundary Real.pi - firstBoundary 0) +
        (1 / 2 : ℝ) * ∫ x in 0..Real.pi, x * Real.sin (2 * x) := by
  rw [original_integral_value, integral_mul_sin_two_value]
  unfold firstBoundary
  simp [Real.sin_two_pi]
  ring

theorem gap4 :
    originalIntegral =
      Real.pi ^ 3 / 6 +
        (secondBoundary Real.pi - secondBoundary 0) +
        (1 / 4 : ℝ) * ∫ x in 0..Real.pi, Real.cos (2 * x) := by
  rw [original_integral_value, integral_cos_two_value]
  unfold secondBoundary
  simp [Real.cos_two_pi]
  ring

theorem gap5 :
    Real.pi ^ 3 / 6 +
        (secondBoundary Real.pi - secondBoundary 0) +
        (1 / 4 : ℝ) * (∫ x in 0..Real.pi, Real.cos (2 * x)) =
      Real.pi ^ 3 / 6 - Real.pi / 4 := by
  rw [integral_cos_two_value]
  unfold secondBoundary
  simp [Real.cos_two_pi]
  ring

theorem gap6 :
    originalIntegral = Real.pi ^ 3 / 6 - Real.pi / 4 := by
  exact original_integral_value

end

end ProofGap.Exercise2278
