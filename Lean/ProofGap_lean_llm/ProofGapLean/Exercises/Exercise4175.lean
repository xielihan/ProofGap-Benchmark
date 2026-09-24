import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4175

noncomputable section

open MeasureTheory
open scoped Interval

def gaussian (x y : ℝ) : ℝ :=
  Real.exp (-(x ^ 2 + y ^ 2))

def cartesianIntegral : ℝ :=
  ∫ y : ℝ, ∫ x : ℝ, gaussian x y

def polarIntegral : ℝ :=
  ∫ theta in (0 : ℝ)..2 * Real.pi,
    ∫ r in Set.Ici (0 : ℝ), r * Real.exp (-r ^ 2)

def radialPrimitive (r : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * Real.exp (-r ^ 2)

private theorem gaussian_factor (x y : ℝ) :
    gaussian x y = Real.exp (-x ^ 2) * Real.exp (-y ^ 2) := by
  unfold gaussian
  rw [← Real.exp_add]
  congr 1
  ring

private theorem cartesianIntegral_value :
    cartesianIntegral = Real.pi := by
  unfold cartesianIntegral
  simp_rw [gaussian_factor]
  have hgauss :
      (∫ x : ℝ, Real.exp (-x ^ 2)) = Real.sqrt Real.pi := by
    simpa using (integral_gaussian (b := (1 : ℝ)))
  have hinner (y : ℝ) :
      (∫ x : ℝ, Real.exp (-x ^ 2) * Real.exp (-y ^ 2)) =
        Real.sqrt Real.pi * Real.exp (-y ^ 2) := by
    rw [integral_mul_const, hgauss]
  simp_rw [hinner]
  rw [integral_const_mul, hgauss]
  simpa [pow_two] using Real.sq_sqrt (le_of_lt Real.pi_pos)

private theorem radialIntegral_value :
    (∫ r in Set.Ici (0 : ℝ), r * Real.exp (-r ^ 2)) = (1 / 2 : ℝ) := by
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  have hderiv (x : ℝ) :
      HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    simpa [id, mul_comm] using (hasDerivAt_id x).pow 2
  have hcont : Continuous (fun x : ℝ => x ^ 2) :=
    continuous_id.pow 2
  have hderivCont : Continuous (fun x : ℝ => 2 * x) :=
    continuous_const.mul continuous_id
  have hexpCont : Continuous (fun x : ℝ => Real.exp (-x)) :=
    Real.continuous_exp.comp continuous_id.neg
  have htendsto :
      Filter.Tendsto (fun x : ℝ => x ^ 2) Filter.atTop Filter.atTop := by
    simpa using
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ)))
  have hgIci :
      IntegrableOn (fun u : ℝ => Real.exp (-u)) (Set.Ici (0 : ℝ)) := by
    by_contra hInt
    have hzero :
        (∫ u in Set.Ici (0 : ℝ), Real.exp (-u)) = 0 :=
      MeasureTheory.integral_undef hInt
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi,
      integral_exp_neg_Ioi] at hzero
    norm_num at hzero
  have hdomInt :
      IntegrableOn
        (fun x : ℝ => (2 * Real.exp 1) * Real.exp (-x))
        (Set.Ici (0 : ℝ)) := by
    simpa using hgIci.const_mul (2 * Real.exp 1)
  have htargetCont : Continuous
      (fun x : ℝ =>
        (((fun u : ℝ => Real.exp (-u)) ∘
          (fun t : ℝ => t ^ 2)) x) * (2 * x)) :=
    (hexpCont.comp hcont).mul hderivCont
  have hcomp :
      IntegrableOn
        (fun x : ℝ =>
          (((fun u : ℝ => Real.exp (-u)) ∘
            (fun t : ℝ => t ^ 2)) x) * (2 * x))
        (Set.Ici (0 : ℝ)) := by
    refine hdomInt.mono' htargetCont.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    have hx0 : 0 ≤ x := hx
    have hexponent : -(x ^ 2) ≤ 1 - 2 * x := by
      nlinarith [sq_nonneg (x - 1)]
    have hexp_le :
        Real.exp (-(x ^ 2)) ≤ Real.exp (1 - 2 * x) :=
      Real.exp_le_exp.mpr hexponent
    have hxexp : x ≤ Real.exp x := by
      calc
        x ≤ x + 1 := by linarith
        _ ≤ Real.exp x := Real.add_one_le_exp x
    have hmul :
        x * Real.exp (-(x ^ 2)) ≤
          Real.exp x * Real.exp (1 - 2 * x) := by
      exact mul_le_mul hxexp hexp_le (Real.exp_nonneg _)
        (Real.exp_nonneg _)
    have hbound :
        Real.exp (-(x ^ 2)) * (2 * x) ≤
          (2 * Real.exp 1) * Real.exp (-x) := by
      calc
        Real.exp (-(x ^ 2)) * (2 * x) =
            2 * (x * Real.exp (-(x ^ 2))) := by ring
        _ ≤ 2 * (Real.exp x * Real.exp (1 - 2 * x)) :=
          mul_le_mul_of_nonneg_left hmul (by norm_num)
        _ = 2 * Real.exp (x + (1 - 2 * x)) := by
          rw [Real.exp_add]
        _ = 2 * Real.exp (1 - x) := by
          rw [show x + (1 - 2 * x) = 1 - x by ring]
        _ = 2 * (Real.exp 1 * Real.exp (-x)) := by
          rw [show 1 - x = 1 + (-x) by ring, Real.exp_add]
        _ = (2 * Real.exp 1) * Real.exp (-x) := by ring
    have hleft :
        0 ≤ Real.exp (-(x ^ 2)) * (2 * x) :=
      mul_nonneg (Real.exp_nonneg _)
        (mul_nonneg (by norm_num) hx0)
    simpa only [Function.comp_apply, Real.norm_eq_abs,
      abs_of_nonneg hleft] using hbound
  have hsubRaw :
      (∫ x in Set.Ioi (0 : ℝ),
        (((fun u : ℝ => Real.exp (-u)) ∘
          (fun t : ℝ => t ^ 2)) x) * (2 * x)) =
        ∫ u in Set.Ioi ((fun t : ℝ => t ^ 2) 0), Real.exp (-u) := by
    apply integral_comp_mul_deriv_Ioi
    · exact hcont.continuousOn
    · exact htendsto
    · intro x hx
      exact (hderiv x).hasDerivWithinAt
    · exact hexpCont.continuousOn
    · refine hgIci.mono_set ?_
      rintro u ⟨x, hx, rfl⟩
      exact sq_nonneg x
    · exact hcomp
  have hsub :
      (∫ x in Set.Ioi (0 : ℝ),
        Real.exp (-(x ^ 2)) * (2 * x)) =
        ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) := by
    simpa [Function.comp_apply] using hsubRaw
  calc
    (∫ r in Set.Ioi (0 : ℝ), r * Real.exp (-r ^ 2)) =
        ∫ r in Set.Ioi (0 : ℝ),
          (Real.exp (-(r ^ 2)) * (2 * r)) / 2 := by
      apply integral_congr_ae
      filter_upwards with r
      ring
    _ = (∫ r in Set.Ioi (0 : ℝ),
          Real.exp (-(r ^ 2)) * (2 * r)) / 2 := by
      rw [integral_div]
    _ = (∫ u in Set.Ioi (0 : ℝ), Real.exp (-u)) / 2 := by
      rw [hsub]
    _ = (1 / 2 : ℝ) := by
      rw [integral_exp_neg_Ioi]
      norm_num

private theorem polarIntegral_value :
    polarIntegral = Real.pi := by
  simp [polarIntegral, radialIntegral_value] <;> ring

theorem gap1 :
    cartesianIntegral = polarIntegral := by
  exact cartesianIntegral_value.trans polarIntegral_value.symm

theorem gap2 :
    polarIntegral =
      2 * Real.pi * (0 - radialPrimitive 0) := by
  calc
    polarIntegral = Real.pi := polarIntegral_value
    _ = 2 * Real.pi * (0 - radialPrimitive 0) := by
      norm_num [radialPrimitive] <;> ring

theorem gap3 :
    2 * Real.pi * (0 - radialPrimitive 0) =
      Real.pi := by
  norm_num [radialPrimitive] <;> ring

theorem gap4 :
    cartesianIntegral = Real.pi := by
  calc
    cartesianIntegral = polarIntegral := gap1
    _ = 2 * Real.pi * (0 - radialPrimitive 0) := gap2
    _ = Real.pi := gap3

end

end ProofGap.Exercise4175
