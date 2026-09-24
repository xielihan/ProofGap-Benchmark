import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped Interval

namespace ProofGap.Exercise2260

noncomputable section

def transform (x : ℝ) : ℝ := x + 1 / x
def discriminant (t : ℝ) : ℝ := Real.sqrt (t ^ 2 - 4)
def upperBranch (t : ℝ) : ℝ := (t + discriminant t) / 2
def lowerBranch (t : ℝ) : ℝ := (t - discriminant t) / 2
def upperJacobian (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (1 + t / discriminant t)
def lowerJacobian (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (1 - t / discriminant t)

def originalIntegrand (x : ℝ) : ℝ :=
  (1 + x - 1 / x) * Real.exp (transform x)

def upperPullback (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (1 + discriminant t) * Real.exp t *
    (1 + t / discriminant t)

def lowerPullback (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (1 - discriminant t) * Real.exp t *
    (1 - t / discriminant t)

def combinedPullback (t : ℝ) : ℝ :=
  Real.exp t * (discriminant t + t / discriminant t)

def productRuleIntegrand (t : ℝ) : ℝ :=
  discriminant t * deriv Real.exp t +
    Real.exp t * deriv discriminant t

def primitive (t : ℝ) : ℝ := discriminant t * Real.exp t

private def originalPrimitive (x : ℝ) : ℝ := x * Real.exp (transform x)

private theorem hasDerivAt_originalPrimitive {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt originalPrimitive (originalIntegrand x) x := by
  have htransform :
      HasDerivAt transform (1 - 1 / x ^ 2) x := by
    unfold transform
    convert (hasDerivAt_id x).add ((hasDerivAt_const x (1 : ℝ)).div
      (hasDerivAt_id x) hx) using 1
    simp only [id_eq]
    field_simp [hx]
    ring
  have hexp := (Real.hasDerivAt_exp (transform x)).comp x htransform
  have hd := (hasDerivAt_id x).mul hexp
  convert hd using 1
  unfold originalIntegrand
  simp only [id_eq, Function.comp_apply]
  field_simp [hx]
  ring

private theorem originalIntegrand_continuousAt {x : ℝ} (hx : x ≠ 0) :
    ContinuousAt originalIntegrand x := by
  have hinv : ContinuousAt (fun y : ℝ => 1 / y) x :=
    continuousAt_const.div continuousAt_id hx
  have htransform : ContinuousAt transform x := by
    simpa only [transform] using continuousAt_id.add hinv
  unfold originalIntegrand
  exact ((continuousAt_const.add continuousAt_id).sub hinv).mul
    (Real.continuous_exp.continuousAt.comp htransform)

private theorem originalIntegrand_continuousOn :
    ContinuousOn originalIntegrand (Set.uIcc (1 / 2 : ℝ) 2) := by
  rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)]
  intro x hx
  exact (originalIntegrand_continuousAt (by linarith [hx.1])).continuousWithinAt

private theorem originalIntegral_eq_value :
    (∫ x in (1 / 2 : ℝ)..2, originalIntegrand x) =
      (3 / 2 : ℝ) * Real.exp (5 / 2) := by
  have hderiv : ∀ x ∈ Set.uIcc (1 / 2 : ℝ) 2,
      HasDerivAt originalPrimitive (originalIntegrand x) x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hx
    exact hasDerivAt_originalPrimitive (by linarith [hx.1])
  have hint : IntervalIntegrable originalIntegrand MeasureTheory.volume
      (1 / 2 : ℝ) 2 := by
    exact originalIntegrand_continuousOn.intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hftc]
  norm_num [originalPrimitive, transform]
  ring

private theorem radicand_pos {t : ℝ} (ht : 2 < t) : 0 < t ^ 2 - 4 := by
  nlinarith

private theorem discriminant_pos {t : ℝ} (ht : 2 < t) :
    0 < discriminant t := by
  exact Real.sqrt_pos.2 (radicand_pos ht)

private theorem discriminant_sq {t : ℝ} (ht : 2 ≤ t) :
    discriminant t ^ 2 = t ^ 2 - 4 := by
  unfold discriminant
  exact Real.sq_sqrt (by nlinarith)

private theorem hasDerivAt_discriminant {t : ℝ} (ht : 2 < t) :
    HasDerivAt discriminant (t / discriminant t) t := by
  have hinner : HasDerivAt (fun y : ℝ => y ^ 2 - 4) (2 * t) t := by
    convert ((hasDerivAt_id t).pow 2).sub_const 4 using 1 <;>
      simp <;> ring
  have hd0 : discriminant t ≠ 0 := (discriminant_pos ht).ne'
  unfold discriminant
  convert (Real.hasDerivAt_sqrt (ne_of_gt (radicand_pos ht))).comp t hinner using 1
  field_simp [hd0]

private theorem hasDerivAt_upperProduct {t : ℝ} (ht : 2 < t) :
    HasDerivAt (fun y => upperBranch y * Real.exp y) (upperPullback t) t := by
  have hd := hasDerivAt_discriminant ht
  have hb : HasDerivAt upperBranch
      ((1 / 2 : ℝ) * (1 + t / discriminant t)) t := by
    unfold upperBranch
    convert ((hasDerivAt_id t).add hd).div_const 2 using 1 <;> ring
  have hp := hb.mul (Real.hasDerivAt_exp t)
  convert hp using 1
  unfold upperPullback upperBranch
  have hd0 : discriminant t ≠ 0 := (discriminant_pos ht).ne'
  have hd2 := discriminant_sq ht.le
  field_simp [hd0]
  ring_nf at hd2 ⊢

private theorem hasDerivAt_lowerProduct {t : ℝ} (ht : 2 < t) :
    HasDerivAt (fun y => lowerBranch y * Real.exp y) (lowerPullback t) t := by
  have hd := hasDerivAt_discriminant ht
  have hb : HasDerivAt lowerBranch
      ((1 / 2 : ℝ) * (1 - t / discriminant t)) t := by
    unfold lowerBranch
    convert ((hasDerivAt_id t).sub hd).div_const 2 using 1 <;> ring
  have hp := hb.mul (Real.hasDerivAt_exp t)
  convert hp using 1
  unfold lowerPullback lowerBranch
  have hd0 : discriminant t ≠ 0 := (discriminant_pos ht).ne'
  have hd2 := discriminant_sq ht.le
  field_simp [hd0]
  ring_nf at hd2 ⊢

private theorem hasDerivAt_primitive {t : ℝ} (ht : 2 < t) :
    HasDerivAt primitive (combinedPullback t) t := by
  have hp := (hasDerivAt_discriminant ht).mul (Real.hasDerivAt_exp t)
  convert hp using 1
  unfold combinedPullback
  ring

private theorem primitive_continuous : Continuous primitive := by
  unfold primitive discriminant
  exact (Real.continuous_sqrt.comp
    ((continuous_id.pow 2).sub continuous_const)).mul Real.continuous_exp

private theorem productRule_eq_combined_of_gt {t : ℝ} (ht : 2 < t) :
    productRuleIntegrand t = combinedPullback t := by
  unfold productRuleIntegrand combinedPullback
  rw [(Real.hasDerivAt_exp t).deriv, (hasDerivAt_discriminant ht).deriv]
  ring

private theorem one_div_sqrt_eq_rpow_neg_half {x : ℝ} (hx : 0 ≤ x) :
    1 / Real.sqrt x = x ^ (-1 / 2 : ℝ) := by
  calc
    1 / Real.sqrt x = (x ^ (1 / 2 : ℝ))⁻¹ := by
      rw [Real.sqrt_eq_rpow]
      simp
    _ = x ^ (-(1 / 2 : ℝ)) := (Real.rpow_neg hx (1 / 2 : ℝ)).symm
    _ = x ^ (-1 / 2 : ℝ) := by norm_num

private def endpointSingular (t : ℝ) : ℝ :=
  (t - 2) ^ (-1 / 2 : ℝ)

private theorem endpointSingular_intervalIntegrable :
    IntervalIntegrable endpointSingular MeasureTheory.volume 2 (5 / 2) := by
  have hbase :
      IntervalIntegrable (fun u : ℝ => u ^ (-1 / 2 : ℝ))
        MeasureTheory.volume 0 (1 / 2) :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hshift := hbase.comp_sub_right 2
  convert hshift using 1 <;> norm_num [endpointSingular]

private theorem smoothFactor_continuousOn :
    ContinuousOn (fun t : ℝ => 1 / Real.sqrt (t + 2))
      (Set.uIcc (2 : ℝ) (5 / 2)) := by
  rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 5 / 2)]
  intro t ht
  have hpos : 0 < t + 2 := by linarith [ht.1]
  exact (continuousAt_const.div
    (Real.continuous_sqrt.continuousAt.comp
      (continuousAt_id.add continuousAt_const))
    (ne_of_gt (Real.sqrt_pos.2 hpos))).continuousWithinAt

private theorem invDiscriminant_intervalIntegrable :
    IntervalIntegrable (fun t : ℝ => 1 / discriminant t)
      MeasureTheory.volume 2 (5 / 2) := by
  have hprod := endpointSingular_intervalIntegrable.mul_continuousOn
    smoothFactor_continuousOn
  apply hprod.congr
  intro t ht
  rw [Set.uIoc_of_le (by norm_num : (2 : ℝ) ≤ 5 / 2)] at ht
  have ht2 : 2 < t := ht.1
  have hm : 0 ≤ t - 2 := by linarith
  have hp : 0 ≤ t + 2 := by linarith
  have hm0 : Real.sqrt (t - 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by linarith))
  have hp0 : Real.sqrt (t + 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by linarith))
  unfold endpointSingular discriminant
  change (t - 2) ^ (-1 / 2 : ℝ) * (1 / Real.sqrt (t + 2)) =
    1 / Real.sqrt (t ^ 2 - 4)
  rw [← one_div_sqrt_eq_rpow_neg_half hm]
  rw [show t ^ 2 - 4 = (t - 2) * (t + 2) by ring]
  rw [Real.sqrt_mul hm]
  field_simp [hm0, hp0]

private theorem discriminant_continuous : Continuous discriminant := by
  unfold discriminant
  exact Real.continuous_sqrt.comp
    ((continuous_id.pow 2).sub continuous_const)

private theorem combinedPullback_intervalIntegrable :
    IntervalIntegrable combinedPullback MeasureTheory.volume 2 (5 / 2) := by
  have hregular :
      IntervalIntegrable (fun t : ℝ => Real.exp t * discriminant t)
        MeasureTheory.volume 2 (5 / 2) :=
    (Real.continuous_exp.mul discriminant_continuous).intervalIntegrable _ _
  have hfactor : ContinuousOn (fun t : ℝ => Real.exp t * t)
      (Set.uIcc (2 : ℝ) (5 / 2)) :=
    (Real.continuous_exp.mul continuous_id).continuousOn
  have hsingular :=
    invDiscriminant_intervalIntegrable.continuousOn_mul hfactor
  have hsum := hregular.add hsingular
  apply hsum.congr
  intro t ht
  unfold combinedPullback
  ring

private theorem upperPullback_intervalIntegrable :
    IntervalIntegrable upperPullback MeasureTheory.volume 2 (5 / 2) := by
  have hregular :
      IntervalIntegrable (fun t : ℝ => Real.exp t * (1 + t))
        MeasureTheory.volume 2 (5 / 2) :=
    (Real.continuous_exp.mul
      (continuous_const.add continuous_id)).intervalIntegrable _ _
  have hrep := (combinedPullback_intervalIntegrable.add hregular).const_mul
    (1 / 2 : ℝ)
  apply hrep.congr
  intro t ht
  rw [Set.uIoc_of_le (by norm_num : (2 : ℝ) ≤ 5 / 2)] at ht
  have hd0 : discriminant t ≠ 0 := (discriminant_pos ht.1).ne'
  change (1 / 2 : ℝ) *
      (combinedPullback t + Real.exp t * (1 + t)) = upperPullback t
  unfold combinedPullback upperPullback
  field_simp [hd0]
  ring

private theorem lowerPullback_intervalIntegrable :
    IntervalIntegrable lowerPullback MeasureTheory.volume 2 (5 / 2) := by
  have hregular :
      IntervalIntegrable (fun t : ℝ => Real.exp t * (1 + t))
        MeasureTheory.volume 2 (5 / 2) :=
    (Real.continuous_exp.mul
      (continuous_const.add continuous_id)).intervalIntegrable _ _
  have hrep := (hregular.sub combinedPullback_intervalIntegrable).const_mul
    (1 / 2 : ℝ)
  apply hrep.congr
  intro t ht
  rw [Set.uIoc_of_le (by norm_num : (2 : ℝ) ≤ 5 / 2)] at ht
  have hd0 : discriminant t ≠ 0 := (discriminant_pos ht.1).ne'
  change (1 / 2 : ℝ) *
      (Real.exp t * (1 + t) - combinedPullback t) = lowerPullback t
  unfold combinedPullback lowerPullback
  field_simp [hd0]
  ring

private theorem productRuleIntegrand_intervalIntegrable :
    IntervalIntegrable productRuleIntegrand MeasureTheory.volume 2 (5 / 2) := by
  apply combinedPullback_intervalIntegrable.congr
  intro t ht
  rw [Set.uIoc_of_le (by norm_num : (2 : ℝ) ≤ 5 / 2)] at ht
  exact (productRule_eq_combined_of_gt ht.1).symm

private theorem upper_sub_lower_integrals_eq_combined :
    (∫ t in (2 : ℝ)..5 / 2, upperPullback t) -
        (∫ t in (2 : ℝ)..5 / 2, lowerPullback t) =
      ∫ t in (2 : ℝ)..5 / 2, combinedPullback t := by
  rw [← intervalIntegral.integral_sub upperPullback_intervalIntegrable
    lowerPullback_intervalIntegrable]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with t
  intro ht
  rw [Set.uIoc_of_le (by norm_num : (2 : ℝ) ≤ 5 / 2)] at ht
  have hd0 : discriminant t ≠ 0 := (discriminant_pos ht.1).ne'
  unfold upperPullback lowerPullback combinedPullback
  field_simp [hd0]
  ring

private theorem combinedIntegral_eq_primitive :
    (∫ t in (2 : ℝ)..5 / 2, combinedPullback t) =
      primitive (5 / 2) - primitive 2 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (2 : ℝ) ≤ 5 / 2) primitive_continuous.continuousOn
  · intro t ht
    exact hasDerivAt_primitive ht.1
  · exact combinedPullback_intervalIntegrable

private theorem productRuleIntegral_eq_combined :
    (∫ t in (2 : ℝ)..5 / 2, productRuleIntegrand t) =
      ∫ t in (2 : ℝ)..5 / 2, combinedPullback t := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with t
  intro ht
  rw [Set.uIoc_of_le (by norm_num : (2 : ℝ) ≤ 5 / 2)] at ht
  exact productRule_eq_combined_of_gt ht.1

private theorem primitive_endpoint_value :
    primitive (5 / 2) - primitive 2 =
      (3 / 2 : ℝ) * Real.exp (5 / 2) := by
  norm_num [primitive, discriminant]
  rw [show Real.sqrt 9 = 3 by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
        norm_num,
    show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
        norm_num]

private theorem combinedIntegral_eq_value :
    (∫ t in (2 : ℝ)..5 / 2, combinedPullback t) =
      (3 / 2 : ℝ) * Real.exp (5 / 2) :=
  combinedIntegral_eq_primitive.trans primitive_endpoint_value

theorem gap1 (x : ℝ) (hx : x ≠ 0) :
    transform x ^ 2 - 4 = (x - 1 / x) ^ 2 := by
  unfold transform
  field_simp [hx]
  ring

theorem gap2 (t : ℝ) (ht : 2 ≤ t) :
    transform (upperBranch t) = t ∧
      transform (lowerBranch t) = t := by
  have hd2 := discriminant_sq ht
  have hdnonneg : 0 ≤ discriminant t := Real.sqrt_nonneg _
  have htpos : 0 < t := by linarith
  have hdlt : discriminant t < t := by nlinarith
  have hp : t + discriminant t ≠ 0 := by positivity
  have hm : t - discriminant t ≠ 0 := by linarith
  constructor
  · unfold transform upperBranch
    field_simp [hp]
    nlinarith
  · unfold transform lowerBranch
    field_simp [hm]
    nlinarith

theorem gap3 :
    (∫ x in (1 / 2 : ℝ)..2, originalIntegrand x) =
      (∫ x in (1 : ℝ)..2, originalIntegrand x) +
        ∫ x in (1 / 2 : ℝ)..1, originalIntegrand x := by
  have hleft : IntervalIntegrable originalIntegrand MeasureTheory.volume
      (1 / 2 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at hx
    exact (originalIntegrand_continuousAt (by linarith [hx.1])).continuousWithinAt
  have hright : IntervalIntegrable originalIntegrand MeasureTheory.volume
      1 2 := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hx
    exact (originalIntegrand_continuousAt (by linarith [hx.1])).continuousWithinAt
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft hright
  linarith

theorem gap4 :
    (∫ x in (1 / 2 : ℝ)..2, originalIntegrand x) =
      (∫ t in (2 : ℝ)..5 / 2, upperPullback t) -
        ∫ t in (2 : ℝ)..5 / 2, lowerPullback t := by
  calc
    (∫ x in (1 / 2 : ℝ)..2, originalIntegrand x) =
        (3 / 2 : ℝ) * Real.exp (5 / 2) := originalIntegral_eq_value
    _ = ∫ t in (2 : ℝ)..5 / 2, combinedPullback t :=
      combinedIntegral_eq_value.symm
    _ = (∫ t in (2 : ℝ)..5 / 2, upperPullback t) -
        ∫ t in (2 : ℝ)..5 / 2, lowerPullback t :=
      upper_sub_lower_integrals_eq_combined.symm

theorem gap5 :
    (∫ x in (1 / 2 : ℝ)..2, originalIntegrand x) =
      ∫ t in (2 : ℝ)..5 / 2, combinedPullback t := by
  exact originalIntegral_eq_value.trans combinedIntegral_eq_value.symm

theorem gap6 :
    (∫ x in (1 / 2 : ℝ)..2, originalIntegrand x) =
      ∫ t in (2 : ℝ)..5 / 2, productRuleIntegrand t := by
  exact (gap5.trans productRuleIntegral_eq_combined.symm)

theorem gap7 :
    (∫ t in (2 : ℝ)..5 / 2, productRuleIntegrand t) =
      primitive (5 / 2) - primitive 2 := by
  exact productRuleIntegral_eq_combined.trans combinedIntegral_eq_primitive

theorem gap8 :
    primitive (5 / 2) - primitive 2 =
      (3 / 2 : ℝ) * Real.exp (5 / 2) := by
  exact primitive_endpoint_value

theorem gap9 :
    (∫ x in (1 / 2 : ℝ)..2, originalIntegrand x) =
      (3 / 2 : ℝ) * Real.exp (5 / 2) := by
  exact originalIntegral_eq_value

end

end ProofGap.Exercise2260
