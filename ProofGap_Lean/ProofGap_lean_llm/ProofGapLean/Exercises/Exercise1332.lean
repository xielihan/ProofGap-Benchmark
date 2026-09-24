import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise1332

noncomputable section
open Filter
open scoped Topology

def punctured (x₀ : ℝ) := nhdsWithin x₀ ({x₀} : Set ℝ)ᶜ
def sec (x : ℝ) := 1 / Real.cos x
def original (a b x : ℝ) :=
  Real.log (Real.cos (a * x)) / Real.log (Real.cos (b * x))
def firstStage (a b x : ℝ) :=
  (a * Real.tan (a * x)) / (b * Real.tan (b * x))
def secondStage (a b x : ℝ) :=
  (a / b) * ((a * sec (a * x) ^ 2) / (b * sec (b * x) ^ 2))

private theorem tendsto_id_punctured :
    Tendsto (fun x : ℝ => x) (punctured 0) (𝓝 0) := by
  unfold punctured
  exact tendsto_id.mono_left inf_le_left

private theorem eventually_ne_zero_punctured :
    ∀ᶠ x : ℝ in punctured 0, x ≠ 0 := by
  unfold punctured
  filter_upwards [self_mem_nhdsWithin] with x hx
  simpa using hx

private theorem tendsto_log_cos_div_sq (c : ℝ) :
    Tendsto (fun x => Real.log (Real.cos (c * x)) / x ^ 2)
      (punctured 0) (𝓝 (-(c ^ 2 / 2))) := by
  by_cases hc : c = 0
  · subst c
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (punctured 0) (𝓝 0))
  have hcx : Tendsto (fun x : ℝ => c * x) (punctured 0) (𝓝 0) := by
    simpa using
      (tendsto_const_nhds.mul tendsto_id_punctured :
        Tendsto (fun x : ℝ => c * x) (punctured 0) (𝓝 (c * 0)))
  have hhalf : Tendsto (fun x : ℝ => c * x / 2) (punctured 0) (𝓝 0) := by
    simpa using hcx.div_const 2
  have hcos : Tendsto (fun x : ℝ => Real.cos (c * x))
      (punctured 0) (𝓝 1) := by
    simpa using Real.continuous_cos.continuousAt.tendsto.comp hcx
  have hy : Tendsto (fun x : ℝ => Real.cos (c * x) - 1)
      (punctured 0) (𝓝 0) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) (punctured 0) (𝓝 1) :=
      tendsto_const_nhds
    simpa using hcos.sub hone
  have hsinc : Tendsto (fun x : ℝ => Real.sinc (c * x / 2))
      (punctured 0) (𝓝 1) := by
    simpa using Real.continuous_sinc.continuousAt.tendsto.comp hhalf
  have hsinc_pos : ∀ᶠ x in punctured 0, 0 < Real.sinc (c * x / 2) :=
    (tendsto_order.1 hsinc).1 0 zero_lt_one
  have hy_ne : ∀ᶠ x in punctured 0, Real.cos (c * x) - 1 ≠ 0 := by
    filter_upwards [eventually_ne_zero_punctured, hsinc_pos] with x hx hs
    have hu : c * x / 2 ≠ 0 := div_ne_zero (mul_ne_zero hc hx) (by norm_num)
    have hsne : Real.sinc (c * x / 2) ≠ 0 := ne_of_gt hs
    have hsine : Real.sin (c * x / 2) ≠ 0 := by
      intro hzero
      apply hsne
      simp [Real.sinc, hu, hzero]
    have htrig := Real.sin_sq_add_cos_sq (c * x / 2)
    have hcos2 : Real.cos (c * x) =
        2 * Real.cos (c * x / 2) ^ 2 - 1 := by
      convert Real.cos_two_mul (c * x / 2) using 1 <;> ring
    have hone : 1 - Real.cos (c * x) =
        2 * Real.sin (c * x / 2) ^ 2 := by
      nlinarith [htrig, hcos2]
    have hone_ne : 1 - Real.cos (c * x) ≠ 0 := by
      rw [hone]
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hsine)
    intro hzero
    apply hone_ne
    linarith
  have hydiv_eq :
      (fun x : ℝ => (Real.cos (c * x) - 1) / x ^ 2) =ᶠ[punctured 0]
        fun x => -(c ^ 2 / 2) * Real.sinc (c * x / 2) ^ 2 := by
    filter_upwards [eventually_ne_zero_punctured] with x hx
    have hu : c * x / 2 ≠ 0 := div_ne_zero (mul_ne_zero hc hx) (by norm_num)
    have hsine : Real.sin (c * x / 2) =
        (c * x / 2) * Real.sinc (c * x / 2) := by
      rw [show Real.sinc (c * x / 2) =
        Real.sin (c * x / 2) / (c * x / 2) by simp [Real.sinc, hu]]
      field_simp [hu]
    have htrig := Real.sin_sq_add_cos_sq (c * x / 2)
    have hcos2 : Real.cos (c * x) =
        2 * Real.cos (c * x / 2) ^ 2 - 1 := by
      convert Real.cos_two_mul (c * x / 2) using 1 <;> ring
    have hone : 1 - Real.cos (c * x) =
        2 * Real.sin (c * x / 2) ^ 2 := by
      nlinarith [htrig, hcos2]
    rw [show Real.cos (c * x) - 1 = -(1 - Real.cos (c * x)) by ring,
      hone, hsine]
    field_simp [hx, hc]
  have hydiv : Tendsto (fun x : ℝ => (Real.cos (c * x) - 1) / x ^ 2)
      (punctured 0) (𝓝 (-(c ^ 2 / 2))) := by
    rw [tendsto_congr' hydiv_eq]
    simpa using tendsto_const_nhds.mul (hsinc.pow 2)
  have hinner_raw :
      HasDerivAt ((fun _ : ℝ => (1 : ℝ)) + id) (0 + 1) 0 :=
    (hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).add (hasDerivAt_id 0)
  change HasDerivAt (fun u : ℝ => 1 + u) (0 + 1) 0 at hinner_raw
  have hinner : HasDerivAt (fun u : ℝ => 1 + u) 1 0 := by
    simpa only [zero_add] using hinner_raw
  have hlog_at_one : HasDerivAt Real.log 1 1 := by
    simpa using Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)
  have hlog_at_inner : HasDerivAt Real.log 1 ((1 : ℝ) + 0) := by
    simpa using hlog_at_one
  have hlog_one_plus : HasDerivAt (fun u : ℝ => Real.log (1 + u)) 1 0 := by
    have hcomp := hlog_at_inner.comp 0 hinner
    change HasDerivAt (fun u : ℝ => Real.log (1 + u)) (1 * 1) 0 at hcomp
    simpa only [one_mul] using hcomp
  have hbase : Tendsto (fun u : ℝ => Real.log (1 + u) / u)
      (punctured 0) (𝓝 1) := by
    simpa [punctured, div_eq_mul_inv, mul_comm] using
      hlog_one_plus.tendsto_slope_zero
  have hy_punctured : Tendsto (fun x : ℝ => Real.cos (c * x) - 1)
      (punctured 0) (punctured 0) := by
    unfold punctured
    refine tendsto_nhdsWithin_iff.2 ⟨hy, ?_⟩
    filter_upwards [hy_ne] with x hx
    simpa using hx
  have hlog_ratio : Tendsto
      (fun x : ℝ => Real.log (Real.cos (c * x)) /
        (Real.cos (c * x) - 1)) (punctured 0) (𝓝 1) := by
    have hcomp := hbase.comp hy_punctured
    change Tendsto
      (fun x : ℝ => Real.log (1 + (Real.cos (c * x) - 1)) /
        (Real.cos (c * x) - 1)) (punctured 0) (𝓝 1) at hcomp
    refine hcomp.congr' ?_
    filter_upwards with x
    rw [show 1 + (Real.cos (c * x) - 1) = Real.cos (c * x) by ring]
  have hfinal_eq :
      (fun x : ℝ => Real.log (Real.cos (c * x)) / x ^ 2) =ᶠ[punctured 0]
        fun x =>
          (Real.log (Real.cos (c * x)) / (Real.cos (c * x) - 1)) *
            ((Real.cos (c * x) - 1) / x ^ 2) := by
    filter_upwards [eventually_ne_zero_punctured, hy_ne] with x hx hyx
    field_simp [hx, hyx]
  rw [tendsto_congr' hfinal_eq]
  simpa using hlog_ratio.mul hydiv

private theorem tendsto_scaled_tan_div (c : ℝ) :
    Tendsto (fun x => c * Real.tan (c * x) / x)
      (punctured 0) (𝓝 (c ^ 2)) := by
  by_cases hc : c = 0
  · subst c
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (punctured 0) (𝓝 0))
  have hcx : Tendsto (fun x : ℝ => c * x) (punctured 0) (𝓝 0) := by
    simpa using
      (tendsto_const_nhds.mul tendsto_id_punctured :
        Tendsto (fun x : ℝ => c * x) (punctured 0) (𝓝 (c * 0)))
  have hsinc : Tendsto (fun x : ℝ => Real.sinc (c * x))
      (punctured 0) (𝓝 1) := by
    simpa using Real.continuous_sinc.continuousAt.tendsto.comp hcx
  have hcos : Tendsto (fun x : ℝ => Real.cos (c * x))
      (punctured 0) (𝓝 1) := by
    simpa using Real.continuous_cos.continuousAt.tendsto.comp hcx
  have hcos_pos : ∀ᶠ x in punctured 0, 0 < Real.cos (c * x) :=
    (tendsto_order.1 hcos).1 0 zero_lt_one
  have heq : (fun x : ℝ => c * Real.tan (c * x) / x) =ᶠ[punctured 0]
      fun x => c ^ 2 * Real.sinc (c * x) / Real.cos (c * x) := by
    filter_upwards [eventually_ne_zero_punctured, hcos_pos] with x hx hcosx
    have hcxne : c * x ≠ 0 := mul_ne_zero hc hx
    have hsine : Real.sin (c * x) = (c * x) * Real.sinc (c * x) := by
      rw [show Real.sinc (c * x) = Real.sin (c * x) / (c * x) by
        simp [Real.sinc, hcxne]]
      field_simp [hcxne]
    rw [Real.tan_eq_sin_div_cos, hsine]
    field_simp [hx, hc, ne_of_gt hcosx]
  rw [tendsto_congr' heq]
  have hnum : Tendsto (fun x : ℝ => c ^ 2 * Real.sinc (c * x))
      (punctured 0) (𝓝 (c ^ 2)) := by
    simpa using tendsto_const_nhds.mul hsinc
  simpa using hnum.div hcos (by norm_num)

private theorem tendsto_sec_sq (c : ℝ) :
    Tendsto (fun x => sec (c * x) ^ 2) (punctured 0) (𝓝 1) := by
  have hcx : Tendsto (fun x : ℝ => c * x) (punctured 0) (𝓝 0) := by
    simpa using
      (tendsto_const_nhds.mul tendsto_id_punctured :
        Tendsto (fun x : ℝ => c * x) (punctured 0) (𝓝 (c * 0)))
  have hcos : Tendsto (fun x : ℝ => Real.cos (c * x))
      (punctured 0) (𝓝 1) := by
    simpa using Real.continuous_cos.continuousAt.tendsto.comp hcx
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) (punctured 0) (𝓝 1) :=
    tendsto_const_nhds
  have hsec : Tendsto (fun x : ℝ => sec (c * x))
      (punctured 0) (𝓝 1) := by
    change Tendsto (fun x : ℝ => (1 : ℝ) / Real.cos (c * x))
      (punctured 0) (𝓝 1)
    simpa only [div_one] using hone.div hcos (by norm_num)
  simpa using hsec.pow 2

theorem gap1 (a b : ℝ) (hb : b ≠ 0) :
    Tendsto (original a b) (punctured 0) (nhds ((a / b) ^ 2)) := by
  have ha := tendsto_log_cos_div_sq a
  have hb' := tendsto_log_cos_div_sq b
  have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb
  have hblim : -(b ^ 2 / 2) < 0 := by nlinarith
  have hbnorm_neg : ∀ᶠ x in punctured 0,
      Real.log (Real.cos (b * x)) / x ^ 2 < 0 :=
    (tendsto_order.1 hb').2 0 hblim
  have heq : (fun x => original a b x) =ᶠ[punctured 0]
      fun x => (Real.log (Real.cos (a * x)) / x ^ 2) /
        (Real.log (Real.cos (b * x)) / x ^ 2) := by
    filter_upwards [eventually_ne_zero_punctured, hbnorm_neg] with x hx hneg
    have hlogb : Real.log (Real.cos (b * x)) ≠ 0 := by
      intro h
      apply ne_of_lt hneg
      simp [h]
    unfold original
    field_simp [hx, hlogb]
  rw [tendsto_congr' heq]
  have hquot := ha.div hb' (by nlinarith : -(b ^ 2 / 2) ≠ 0)
  convert hquot using 1
  field_simp [hb]
theorem gap2 (a b : ℝ) (hb : b ≠ 0) :
    Tendsto (firstStage a b) (punctured 0) (nhds ((a / b) ^ 2)) := by
  have ha := tendsto_scaled_tan_div a
  have hb' := tendsto_scaled_tan_div b
  have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb
  have hbnorm_pos : ∀ᶠ x in punctured 0,
      0 < b * Real.tan (b * x) / x :=
    (tendsto_order.1 hb').1 0 hb2
  have heq : (fun x => firstStage a b x) =ᶠ[punctured 0]
      fun x => (a * Real.tan (a * x) / x) /
        (b * Real.tan (b * x) / x) := by
    filter_upwards [eventually_ne_zero_punctured, hbnorm_pos] with x hx hpos
    have htanb : b * Real.tan (b * x) ≠ 0 := by
      intro h
      apply ne_of_gt hpos
      simp [h]
    unfold firstStage
    field_simp [hx, htanb]
  rw [tendsto_congr' heq]
  have hquot := ha.div hb' (ne_of_gt hb2)
  convert hquot using 1
  field_simp [hb]
theorem gap3 (a b : ℝ) (hb : b ≠ 0) :
    Tendsto (secondStage a b) (punctured 0) (nhds ((a / b) ^ 2)) := by
  have ha := tendsto_sec_sq a
  have hb' := tendsto_sec_sq b
  have hnum : Tendsto (fun x => a * sec (a * x) ^ 2) (punctured 0) (𝓝 a) := by
    simpa using (tendsto_const_nhds.mul ha)
  have hden : Tendsto (fun x => b * sec (b * x) ^ 2) (punctured 0) (𝓝 b) := by
    simpa using (tendsto_const_nhds.mul hb')
  have hfrac := hnum.div hden hb
  have hall : Tendsto
      (fun x : ℝ => (a / b) *
        ((a * sec (a * x) ^ 2) / (b * sec (b * x) ^ 2)))
      (punctured 0) (𝓝 ((a / b) * (a / b))) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => a / b)
      (punctured 0) (𝓝 (a / b))).mul hfrac
  change Tendsto
    (fun x : ℝ => (a / b) *
      ((a * sec (a * x) ^ 2) / (b * sec (b * x) ^ 2)))
    (punctured 0) (𝓝 ((a / b) ^ 2))
  convert hall using 1 <;> ring
theorem gap4 (a b : ℝ) (hb : b ≠ 0) :
    Tendsto (original a b) (punctured 0) (nhds ((a / b) ^ 2)) := by
  exact gap1 a b hb

end
end ProofGap.Exercise1332
