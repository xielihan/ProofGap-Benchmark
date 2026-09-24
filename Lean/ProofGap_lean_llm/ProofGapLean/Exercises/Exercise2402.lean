import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise2402
noncomputable section

open Filter MeasureTheory
open scoped Interval

def baseIntegrand (a x : ℝ) : ℝ := 1 / (a ^ 2 + x ^ 2)
def fullIntegrand (a x : ℝ) : ℝ := a ^ 3 / (a ^ 2 + x ^ 2)
def halfTrunc (a b : ℝ) : ℝ := ∫ x in (0 : ℝ)..b, baseIntegrand a x

private theorem halfTrunc_formula (a b : ℝ) (ha : a ≠ 0) :
    halfTrunc a b = a⁻¹ * Real.arctan (b / a) := by
  unfold halfTrunc baseIntegrand
  simp only [one_div]
  rw [integral_inv_sq_add_sq ha]
  simp

private theorem halfTrunc_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto (halfTrunc a) atTop (nhds (Real.pi / (2 * a))) := by
  have hscale : Tendsto (fun b : ℝ => b / a) atTop atTop :=
    tendsto_id.atTop_div_const ha
  have hatan :
      Tendsto (fun b : ℝ => Real.arctan (b / a))
        atTop (nhds (Real.pi / 2)) :=
    tendsto_nhds_of_tendsto_nhdsWithin
      (Real.tendsto_arctan_atTop.comp hscale)
  have hmul :
      Tendsto (fun b : ℝ => a⁻¹ * Real.arctan (b / a))
        atTop (nhds (a⁻¹ * (Real.pi / 2))) :=
    tendsto_const_nhds.mul hatan
  have hlimit : a⁻¹ * (Real.pi / 2) = Real.pi / (2 * a) := by
    field_simp [ha.ne']
  rw [← hlimit]
  apply hmul.congr'
  filter_upwards [] with b
  rw [halfTrunc_formula a b ha.ne']

private theorem integral_baseIntegrand (a : ℝ) (ha : 0 < a) :
    (∫ x : ℝ, baseIntegrand a x) = Real.pi / a := by
  have heq : ∀ x : ℝ,
      baseIntegrand a x =
        a⁻¹ ^ 2 * (1 + (x / a) ^ 2)⁻¹ := by
    intro x
    unfold baseIntegrand
    field_simp [ha.ne']
  have hchange :
      (∫ x : ℝ, (1 + (x / a) ^ 2)⁻¹) =
        |a| * ∫ y : ℝ, (1 + y ^ 2)⁻¹ := by
    simpa only [smul_eq_mul] using
      (Measure.integral_comp_div (fun y : ℝ => (1 + y ^ 2)⁻¹) a)
  calc
    (∫ x : ℝ, baseIntegrand a x) =
        ∫ x : ℝ, a⁻¹ ^ 2 * (1 + (x / a) ^ 2)⁻¹ := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact heq x
    _ = a⁻¹ ^ 2 * ∫ x : ℝ, (1 + (x / a) ^ 2)⁻¹ :=
      by rw [integral_const_mul]
    _ = a⁻¹ ^ 2 * (|a| * ∫ y : ℝ, (1 + y ^ 2)⁻¹) := by
      rw [hchange]
    _ = Real.pi / a := by
      rw [integral_univ_inv_one_add_sq, abs_of_pos ha]
      field_simp [ha.ne']

private theorem integral_fullIntegrand (a : ℝ) (ha : 0 < a) :
    (∫ x : ℝ, fullIntegrand a x) = Real.pi * a ^ 2 := by
  calc
    (∫ x : ℝ, fullIntegrand a x) =
        ∫ x : ℝ, a ^ 3 * baseIntegrand a x := by
          apply integral_congr_ae
          filter_upwards [] with x
          simp only [fullIntegrand, baseIntegrand]
          ring
    _ = a ^ 3 * ∫ x : ℝ, baseIntegrand a x := by
      rw [integral_const_mul]
    _ = Real.pi * a ^ 2 := by
      rw [integral_baseIntegrand a ha]
      field_simp [ha.ne']

theorem gap1 (a L : ℝ) (ha : 0 < a)
    (hL : Tendsto (halfTrunc a) atTop (nhds L)) :
    (∫ x : ℝ, fullIntegrand a x) = 2 * a ^ 3 * L := by
  have hLeq : L = Real.pi / (2 * a) :=
    tendsto_nhds_unique hL (halfTrunc_tendsto a ha)
  rw [integral_fullIntegrand a ha, hLeq]
  field_simp [ha.ne']

theorem gap2 (a : ℝ) (ha : 0 < a) :
    Tendsto (halfTrunc a) atTop (nhds (Real.pi / (2 * a))) := by
  exact halfTrunc_tendsto a ha

theorem gap3 (a : ℝ) (ha : 0 < a) :
    2 * a ^ 3 * (Real.pi / (2 * a)) = Real.pi * a ^ 2 := by
  field_simp [ha.ne']

theorem gap4 (a : ℝ) (ha : 0 < a) :
    (∫ x : ℝ, fullIntegrand a x) = Real.pi * a ^ 2 := by
  exact integral_fullIntegrand a ha

end
end ProofGap.Exercise2402
