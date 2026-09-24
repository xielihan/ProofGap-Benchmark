import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace ProofGap.Exercise2436
noncomputable section

open Set
open scoped Interval

def y (a x : ℝ) : ℝ := a * Real.log (a ^ 2 / (a ^ 2 - x ^ 2))
def arcIntegrand (a x : ℝ) : ℝ := (a ^ 2 + x ^ 2) / (a ^ 2 - x ^ 2)
def s (a b : ℝ) : ℝ := ∫ x in (0 : ℝ)..b, arcIntegrand a x

private lemma denom_pos_on_Icc (a b x : ℝ) (ha : 0 < a) (hba : b < a)
    (hx : x ∈ Icc 0 b) : 0 < a ^ 2 - x ^ 2 := by
  have hxa : x < a := lt_of_le_of_lt hx.2 hba
  calc
    a ^ 2 - x ^ 2 = (a - x) * (a + x) := by ring
    _ > 0 := mul_pos (sub_pos.mpr hxa)
      (add_pos_of_pos_of_nonneg ha hx.1)

theorem gap1 (a b x : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hba : b < a)
    (hx : x ∈ Icc 0 b) :
    HasDerivAt (y a) (2 * a * x / (a ^ 2 - x ^ 2)) x := by
  have hden : 0 < a ^ 2 - x ^ 2 :=
    denom_pos_on_Icc a b x ha hba hx
  have hdenDeriv :
      HasDerivAt (fun t : ℝ => a ^ 2 - t ^ 2) (-2 * x) x := by
    convert
      (hasDerivAt_const (x : ℝ) (a ^ 2)).sub
        ((hasDerivAt_id x).pow 2) using 1 <;>
      simp only [id_eq] <;> ring
  have hquot :=
    (hasDerivAt_const (x : ℝ) (a ^ 2)).div hdenDeriv hden.ne'
  have hq : a ^ 2 / (a ^ 2 - x ^ 2) ≠ 0 :=
    (div_pos (pow_pos ha 2) hden).ne'
  have hlog := (Real.hasDerivAt_log hq).comp x hquot
  unfold y
  convert hlog.const_mul a using 1 <;>
    field_simp [ha.ne', hden.ne', hq] <;> ring

theorem gap2 (a b x : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hba : b < a)
    (hx : x ∈ Icc 0 b) :
    Real.sqrt (1 + (2 * a * x / (a ^ 2 - x ^ 2)) ^ 2) =
      arcIntegrand a x := by
  have hden : 0 < a ^ 2 - x ^ 2 :=
    denom_pos_on_Icc a b x ha hba hx
  have harc : 0 ≤ arcIntegrand a x := by
    unfold arcIntegrand
    exact div_nonneg
      (add_nonneg (sq_nonneg a) (sq_nonneg x)) hden.le
  have hsq :
      1 + (2 * a * x / (a ^ 2 - x ^ 2)) ^ 2 =
        (arcIntegrand a x) ^ 2 := by
    unfold arcIntegrand
    field_simp [hden.ne']
    ring
  calc
    Real.sqrt (1 + (2 * a * x / (a ^ 2 - x ^ 2)) ^ 2) =
        Real.sqrt ((arcIntegrand a x) ^ 2) := by rw [hsq]
    _ = arcIntegrand a x := Real.sqrt_sq harc

theorem gap3 (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hba : b < a) :
    s a b = ∫ x in (0 : ℝ)..b, arcIntegrand a x := by
  rfl

theorem gap4 (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hba : b < a) :
    (∫ x in (0 : ℝ)..b, arcIntegrand a x) =
      a * Real.log ((a + b) / (a - b)) - b := by
  let F : ℝ → ℝ := fun t =>
    a * Real.log (a + t) - a * Real.log (a - t) - t
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) b,
      HasDerivAt F (arcIntegrand a x) x := by
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) b := by
      simpa [uIcc_of_le hb] using hx
    have hden : 0 < a ^ 2 - x ^ 2 :=
      denom_pos_on_Icc a b x ha hba hx'
    have hp : 0 < a + x := add_pos_of_pos_of_nonneg ha hx'.1
    have hm : 0 < a - x :=
      sub_pos.mpr (lt_of_le_of_lt hx'.2 hba)
    have hplus :
        HasDerivAt (fun t : ℝ => Real.log (a + t)) (a + x)⁻¹ x := by
      convert
        (Real.hasDerivAt_log hp.ne').comp x
          ((hasDerivAt_const x a).add (hasDerivAt_id x)) using 1 <;> ring
    have hminus :
        HasDerivAt (fun t : ℝ => Real.log (a - t)) (-(a - x)⁻¹) x := by
      convert
        (Real.hasDerivAt_log hm.ne').comp x
          ((hasDerivAt_const x a).sub (hasDerivAt_id x)) using 1 <;> ring
    have hraw : HasDerivAt F
        (a * (a + x)⁻¹ - a * (-(a - x)⁻¹) - 1) x := by
      simpa [F] using
        (((hplus.const_mul a).sub (hminus.const_mul a)).sub
          (hasDerivAt_id x))
    have heq :
        a * (a + x)⁻¹ - a * (-(a - x)⁻¹) - 1 =
          arcIntegrand a x := by
      unfold arcIntegrand
      field_simp [hp.ne', hm.ne', hden.ne']
      ring
    simpa only [heq] using hraw
  have hconst : Continuous (fun _ : ℝ => a ^ 2) := continuous_const
  have hsquare : Continuous (fun x : ℝ => x ^ 2) := continuous_id.pow 2
  have hne : ∀ x ∈ uIcc (0 : ℝ) b, a ^ 2 - x ^ 2 ≠ 0 := by
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) b := by
      simpa [uIcc_of_le hb] using hx
    exact (denom_pos_on_Icc a b x ha hba hx').ne'
  have hcont : ContinuousOn (arcIntegrand a) (uIcc (0 : ℝ) b) := by
    simpa only [arcIntegrand] using
      (hconst.add hsquare).continuousOn.div
        (hconst.sub hsquare).continuousOn hne
  have hfund :
      (∫ x in (0 : ℝ)..b, arcIntegrand a x) = F b - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      hderiv hcont.intervalIntegrable
  calc
    (∫ x in (0 : ℝ)..b, arcIntegrand a x) = F b - F 0 := hfund
    _ = a * Real.log ((a + b) / (a - b)) - b := by
      have hp : 0 < a + b := add_pos_of_pos_of_nonneg ha hb
      have hm : 0 < a - b := sub_pos.mpr hba
      dsimp [F]
      rw [Real.log_div hp.ne' hm.ne']
      ring

theorem gap5 (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hba : b < a) :
    s a b = a * Real.log ((a + b) / (a - b)) - b := by
  calc
    s a b = ∫ x in (0 : ℝ)..b, arcIntegrand a x :=
      gap3 a b ha hb hba
    _ = a * Real.log ((a + b) / (a - b)) - b :=
      gap4 a b ha hb hba

end
end ProofGap.Exercise2436
