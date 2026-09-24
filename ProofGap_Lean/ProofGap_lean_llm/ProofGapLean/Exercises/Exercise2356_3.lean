import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue

namespace ProofGap.Exercise2356_3
noncomputable section

open Filter MeasureTheory
open scoped Interval

def f (x : ℝ) : ℝ := Real.sqrt x * Real.sin x
def accumulated (x : ℝ) : ℝ := ∫ ξ in (0 : ℝ)..x, f ξ
def average (x : ℝ) : ℝ := accumulated x / x
def HasMean (L : ℝ) : Prop := Tendsto average atTop (nhds L)

theorem gap1 (x : ℝ) (hx : 0 ≤ x) :
    ∃ c ∈ Set.Icc (0 : ℝ) x,
      accumulated x = Real.sqrt x * ∫ ξ in c..x, Real.sin ξ := by
  let s := Real.sqrt x
  have hs0 : 0 ≤ s := Real.sqrt_nonneg x
  have hs2 : s ^ 2 = x := by simpa [s] using Real.sq_sqrt hx
  have hsub : accumulated x =
      ∫ u in (0 : ℝ)..s, 2 * u ^ 2 * Real.sin (u ^ 2) := by
    have hcv := intervalIntegral.integral_comp_mul_deriv
      (a := (0 : ℝ)) (b := s) (f := fun u : ℝ => u ^ 2)
      (f' := fun u : ℝ => 2 * u) (g := f)
      (fun u _ => by
        convert (hasDerivAt_id u).pow 2 using 1 <;> simp [id] <;> ring)
      (by fun_prop) (by unfold f; fun_prop)
    simp only [Function.comp_apply] at hcv
    rw [hs2] at hcv
    norm_num at hcv
    unfold accumulated
    rw [← hcv]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hs0] at hu
    unfold f
    change Real.sqrt (u ^ 2) * Real.sin (u ^ 2) * (2 * u) =
      2 * u ^ 2 * Real.sin (u ^ 2)
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hu.1]
    ring
  have hcosDeriv : ∀ u ∈ Set.uIcc (0 : ℝ) s,
      HasDerivAt (fun y : ℝ => Real.cos (y ^ 2))
        (-2 * u * Real.sin (u ^ 2)) u := by
    intro u _
    convert ((hasDerivAt_id u).pow 2).cos using 1 <;> simp [id] <;> ring
  have hvint : IntervalIntegrable
      (fun y : ℝ => -2 * y * Real.sin (y ^ 2)) volume 0 s :=
    (by fun_prop : Continuous (fun y : ℝ => -2 * y * Real.sin (y ^ 2))).intervalIntegrable 0 s
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := s)
    (u := fun y : ℝ => y) (v := fun y : ℝ => Real.cos (y ^ 2))
    (u' := fun _ : ℝ => 1) (v' := fun y : ℝ => -2 * y * Real.sin (y ^ 2))
    (fun u _ => hasDerivAt_id u) hcosDeriv intervalIntegrable_const hvint
  have hibp' : (∫ u in (0 : ℝ)..s, 2 * u ^ 2 * Real.sin (u ^ 2)) =
      -s * Real.cos x + ∫ u in (0 : ℝ)..s, Real.cos (u ^ 2) := by
    calc
      (∫ u in (0 : ℝ)..s, 2 * u ^ 2 * Real.sin (u ^ 2)) =
          ∫ u in (0 : ℝ)..s, -(u * (-2 * u * Real.sin (u ^ 2))) := by
        apply intervalIntegral.integral_congr
        intro u _
        ring
      _ = -(∫ u in (0 : ℝ)..s, u * (-2 * u * Real.sin (u ^ 2))) := by
        rw [intervalIntegral.integral_neg]
      _ = -s * Real.cos x + ∫ u in (0 : ℝ)..s, Real.cos (u ^ 2) := by
        rw [hibp]
        simp only [one_mul, zero_mul, sub_zero]
        rw [hs2]
        ring
  obtain ⟨d, hd, hmean⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg
    (μ := volume) (a := (0 : ℝ)) (b := s)
    (f := fun u : ℝ => Real.cos (u ^ 2)) (g := fun _ : ℝ => 1)
    (by fun_prop) intervalIntegrable_const (by intro u hu; norm_num)
  rw [Set.uIcc_of_le hs0] at hd
  have hdSq : d * d ≤ s * s := mul_self_le_mul_self hd.1 hd.2
  have hd2 : d ^ 2 ∈ Set.Icc (0 : ℝ) x := by
    constructor
    · positivity
    · nlinarith
  refine ⟨d ^ 2, hd2, ?_⟩
  rw [hsub, hibp']
  have hmean' : (∫ u in (0 : ℝ)..s, Real.cos (u ^ 2)) =
      Real.cos (d ^ 2) * s := by
    simpa using hmean
  rw [hmean']
  have hsin : (∫ ξ in d ^ 2..x, Real.sin ξ) =
      Real.cos (d ^ 2) - Real.cos x := by
    rw [integral_sin]
  rw [hsin]
  ring

theorem gap2 (x c : ℝ) :
    Real.sqrt x * (∫ ξ in c..x, Real.sin ξ) =
      Real.sqrt x * (Real.cos c - Real.cos x) := by
  rw [integral_sin]

theorem gap3 (x : ℝ) (hx : 0 ≤ x) :
    ∃ c ∈ Set.Icc (0 : ℝ) x,
      accumulated x = Real.sqrt x * (Real.cos c - Real.cos x) := by
  obtain ⟨c, hc, hacc⟩ := gap1 x hx
  exact ⟨c, hc, hacc.trans (gap2 x c)⟩

theorem gap4 :
    HasMean 0 ↔ Tendsto average atTop (nhds 0) := by
  rfl

theorem gap5 (x : ℝ) (hx : 0 < x) :
    |average x| ≤ 2 / Real.sqrt x := by
  obtain ⟨c, hc, hacc⟩ := gap3 x hx.le
  have hspos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have havg : average x = (Real.cos c - Real.cos x) / Real.sqrt x := by
    unfold average
    rw [hacc]
    field_simp [hx.ne', hspos.ne']
    rw [hs2]
    ring
  have hcos : |Real.cos c - Real.cos x| ≤ 2 := by
    calc
      |Real.cos c - Real.cos x| ≤ |Real.cos c| + |Real.cos x| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (Real.abs_cos_le_one c) (Real.abs_cos_le_one x)
      _ = 2 := by norm_num
  rw [havg, abs_div, abs_of_pos hspos]
  exact div_le_div_of_nonneg_right hcos hspos.le

theorem gap6 :
    Tendsto (fun x : ℝ => 2 / Real.sqrt x) atTop (nhds 0) := by
  have hinv : Tendsto (fun x : ℝ => (Real.sqrt x)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  simpa [div_eq_mul_inv] using
    (tendsto_const_nhds.mul hinv :
      Tendsto (fun x : ℝ => (2 : ℝ) * (Real.sqrt x)⁻¹) atTop (nhds (2 * 0)))

theorem gap7 : HasMean 0 := by
  unfold HasMean
  apply (tendsto_zero_iff_abs_tendsto_zero average).2
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun x => abs_nonneg (average x)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact gap5 x hx
  · exact gap6

end
end ProofGap.Exercise2356_3
