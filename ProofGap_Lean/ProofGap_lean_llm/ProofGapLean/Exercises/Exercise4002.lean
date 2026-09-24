import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise4002

noncomputable section

open scoped Interval

def ellipticMap (c u v : ℝ) : ℝ × ℝ :=
  (c * Real.cosh u * Real.cos v, c * Real.sinh u * Real.sin v)

def jacobianAbs (c u v : ℝ) : ℝ :=
  |c ^ 2 * Real.cosh u ^ 2 - c ^ 2 * Real.cos v ^ 2|

def parameterArea (c u₁ u₂ v₁ v₂ : ℝ) : ℝ :=
  ∫ u in u₁..u₂, ∫ v in v₁..v₂, jacobianAbs c u v

private theorem _exercise4002_integral_cosh_two_form (a b : ℝ) :
    (∫ x in a..b, (1 + Real.cosh (2 * x)) / 2) =
      (b - a) / 2 + (Real.sinh (2 * b) - Real.sinh (2 * a)) / 4 := by
  calc
    (∫ x in a..b, (1 + Real.cosh (2 * x)) / 2) =
        (fun x : ℝ => x / 2 + Real.sinh (2 * x) / 4) b -
          (fun x : ℝ => x / 2 + Real.sinh (2 * x) / 4) a := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x _
        have htwo : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
          convert (hasDerivAt_id x).const_mul 2 using 1 <;> ring
        have hsinh :
            HasDerivAt (fun y : ℝ => Real.sinh (2 * y))
              (Real.cosh (2 * x) * 2) x :=
          (Real.hasDerivAt_sinh (2 * x)).comp x htwo
        convert ((hasDerivAt_id x).div_const 2).add (hsinh.div_const 4) using 1 <;> ring
      · have htwo : Continuous (fun x : ℝ => 2 * x) :=
          continuous_const.mul continuous_id
        exact ((continuous_const.add (Real.continuous_cosh.comp htwo)).div_const 2).intervalIntegrable a b
    _ = (b - a) / 2 +
        (Real.sinh (2 * b) - Real.sinh (2 * a)) / 4 := by
      ring

private theorem _exercise4002_integral_cos_sq (a b : ℝ) :
    (∫ x in a..b, Real.cos x ^ 2) =
      (b - a) / 2 + (Real.sin (2 * b) - Real.sin (2 * a)) / 4 := by
  calc
    (∫ x in a..b, Real.cos x ^ 2) =
        ∫ x in a..b, (1 + Real.cos (2 * x)) / 2 := by
      apply intervalIntegral.integral_congr
      intro x _
      change Real.cos x ^ 2 = (1 + Real.cos (2 * x)) / 2
      rw [Real.cos_two_mul]
      ring
    _ = (fun x : ℝ => x / 2 + Real.sin (2 * x) / 4) b -
          (fun x : ℝ => x / 2 + Real.sin (2 * x) / 4) a := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x _
        have htwo : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
          convert (hasDerivAt_id x).const_mul 2 using 1 <;> ring
        have hsin :
            HasDerivAt (fun y : ℝ => Real.sin (2 * y))
              (Real.cos (2 * x) * 2) x :=
          (Real.hasDerivAt_sin (2 * x)).comp x htwo
        convert ((hasDerivAt_id x).div_const 2).add (hsin.div_const 4) using 1 <;> ring
      · have htwo : Continuous (fun x : ℝ => 2 * x) :=
          continuous_const.mul continuous_id
        exact ((continuous_const.add (Real.continuous_cos.comp htwo)).div_const 2).intervalIntegrable a b
    _ = (b - a) / 2 +
        (Real.sin (2 * b) - Real.sin (2 * a)) / 4 := by
      ring

theorem gap1 (c u v : ℝ) :
    jacobianAbs c u v =
      |c ^ 2 * Real.cosh u ^ 2 - c ^ 2 * Real.cos v ^ 2| := by
  rfl

theorem gap2 (u : ℝ) :
    1 ≤ Real.cosh u ^ 2 := by
  nlinarith [Real.one_le_cosh u]

theorem gap3 (v : ℝ) :
    Real.cos v ^ 2 ≤ 1 := by
  nlinarith [Real.neg_one_le_cos v, Real.cos_le_one v]

theorem gap4 (u v : ℝ) :
    Real.cos v ^ 2 ≤ Real.cosh u ^ 2 := by
  exact le_trans (gap3 v) (gap2 u)

theorem gap5 (c u₁ u₂ v₁ v₂ : ℝ)
    (hu : u₁ ≤ u₂) (hv : v₁ ≤ v₂) :
    parameterArea c u₁ u₂ v₁ v₂ =
      c ^ 2 *
        ∫ u in u₁..u₂,
          ∫ v in v₁..v₂, Real.cosh u ^ 2 - Real.cos v ^ 2 := by
  unfold parameterArea
  have hpoint (u v : ℝ) :
      jacobianAbs c u v =
        c ^ 2 * (Real.cosh u ^ 2 - Real.cos v ^ 2) := by
    unfold jacobianAbs
    have hn :
        0 ≤ c ^ 2 * Real.cosh u ^ 2 - c ^ 2 * Real.cos v ^ 2 := by
      rw [← mul_sub]
      exact mul_nonneg (sq_nonneg c) (sub_nonneg.mpr (gap4 u v))
    rw [abs_of_nonneg hn]
    ring
  simp_rw [hpoint, intervalIntegral.integral_const_mul]

theorem gap6 (c u₁ u₂ v₁ v₂ : ℝ)
    (hu : u₁ ≤ u₂) (hv : v₁ ≤ v₂) :
    parameterArea c u₁ u₂ v₁ v₂ =
      c ^ 2 *
        ((v₂ - v₁) *
            (∫ u in u₁..u₂, (1 + Real.cosh (2 * u)) / 2) -
          (u₂ - u₁) *
            ∫ v in v₁..v₂, Real.cos v ^ 2) := by
  rw [gap5 c u₁ u₂ v₁ v₂ hu hv]
  congr 1
  have hcos :
      IntervalIntegrable (fun v : ℝ => Real.cos v ^ 2)
        MeasureTheory.volume v₁ v₂ :=
    (Real.continuous_cos.pow 2).intervalIntegrable v₁ v₂
  have hinner (u : ℝ) :
      (∫ v in v₁..v₂, Real.cosh u ^ 2 - Real.cos v ^ 2) =
        (v₂ - v₁) * Real.cosh u ^ 2 -
          ∫ v in v₁..v₂, Real.cos v ^ 2 := by
    have hconst :
        IntervalIntegrable (fun _ : ℝ => Real.cosh u ^ 2)
          MeasureTheory.volume v₁ v₂ :=
      (continuous_const : Continuous (fun _ : ℝ => Real.cosh u ^ 2)).intervalIntegrable v₁ v₂
    rw [intervalIntegral.integral_sub hconst hcos]
    simp [intervalIntegral.integral_const]
  simp_rw [hinner]
  have hfirst :
      IntervalIntegrable
        (fun u : ℝ => (v₂ - v₁) * Real.cosh u ^ 2)
        MeasureTheory.volume u₁ u₂ :=
    ((continuous_const : Continuous (fun _ : ℝ => v₂ - v₁)).mul
      (Real.continuous_cosh.pow 2)).intervalIntegrable u₁ u₂
  have hsecond :
      IntervalIntegrable
        (fun _ : ℝ => ∫ v in v₁..v₂, Real.cos v ^ 2)
        MeasureTheory.volume u₁ u₂ :=
    (continuous_const : Continuous
      (fun _ : ℝ => ∫ v in v₁..v₂, Real.cos v ^ 2)).intervalIntegrable u₁ u₂
  rw [intervalIntegral.integral_sub hfirst hsecond]
  rw [intervalIntegral.integral_const_mul]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  have hcoshInt :
      (∫ u in u₁..u₂, Real.cosh u ^ 2) =
        ∫ u in u₁..u₂, (1 + Real.cosh (2 * u)) / 2 := by
    apply intervalIntegral.integral_congr
    intro u _
    change Real.cosh u ^ 2 = (1 + Real.cosh (2 * u)) / 2
    rw [Real.cosh_two_mul]
    nlinarith [Real.cosh_sq_sub_sinh_sq u]
  rw [hcoshInt]

theorem gap7 (c u₁ u₂ v₁ v₂ : ℝ)
    (hu : u₁ ≤ u₂) (hv : v₁ ≤ v₂) :
    parameterArea c u₁ u₂ v₁ v₂ =
      c ^ 2 / 4 *
        ((v₂ - v₁) * (Real.sinh (2 * u₂) - Real.sinh (2 * u₁)) -
          (u₂ - u₁) * (Real.sin (2 * v₂) - Real.sin (2 * v₁))) := by
  rw [gap6 c u₁ u₂ v₁ v₂ hu hv]
  rw [_exercise4002_integral_cosh_two_form]
  rw [_exercise4002_integral_cos_sq]
  ring

end

end ProofGap.Exercise4002
