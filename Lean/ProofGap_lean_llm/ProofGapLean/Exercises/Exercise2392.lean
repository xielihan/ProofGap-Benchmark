import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2392
noncomputable section

open Filter Set
open scoped Interval

def integrand (x : ℝ) : ℝ := 1 / (x ^ 2 - 3 * x + 2)

def trunc (ε η b : ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..(1 - ε), integrand x) +
    (∫ x in (1 + ε)..(2 - η), integrand x) +
      ∫ x in (2 + η)..b, integrand x

def expanded (ε η b : ℝ) : ℝ :=
  Real.log ((ε + 1) / ε) - Real.log 2 +
    Real.log (η / (1 - η)) - Real.log ((1 - ε) / ε) +
      Real.log |(b - 2) / (b - 1)| - Real.log (η / (1 + η))

def reduced (ε η : ℝ) : ℝ :=
  Real.log ((1 + ε) / (1 - ε)) - Real.log 2 +
    Real.log ((1 + η) / (1 - η))

private theorem integral_integrand_eq (a b : ℝ)
    (h1 : ∀ x ∈ uIcc a b, x ≠ 1)
    (h2 : ∀ x ∈ uIcc a b, x ≠ 2) :
    (∫ x in a..b, integrand x) =
      (Real.log |b - 2| - Real.log |b - 1|) -
        (Real.log |a - 2| - Real.log |a - 1|) := by
  have hderiv : ∀ x ∈ uIcc a b,
      HasDerivAt (fun y : ℝ => Real.log |y - 2| - Real.log |y - 1|)
        (integrand x) x := by
    intro x hx
    have hx1 : x ≠ 1 := h1 x hx
    have hx2 : x ≠ 2 := h2 x hx
    have hd2raw :=
      (Real.hasDerivAt_log (sub_ne_zero.mpr hx2)).comp x
        ((hasDerivAt_id x).sub_const 2)
    have hd1raw :=
      (Real.hasDerivAt_log (sub_ne_zero.mpr hx1)).comp x
        ((hasDerivAt_id x).sub_const 1)
    have hd2 : HasDerivAt (fun y : ℝ => Real.log (y - 2)) (x - 2)⁻¹ x := by
      convert hd2raw using 1 <;> simp
    have hd1 : HasDerivAt (fun y : ℝ => Real.log (y - 1)) (x - 1)⁻¹ x := by
      convert hd1raw using 1 <;> simp
    have heq : (x - 2)⁻¹ - (x - 1)⁻¹ = integrand x := by
      unfold integrand
      rw [show x ^ 2 - 3 * x + 2 = (x - 1) * (x - 2) by ring]
      field_simp [sub_ne_zero.mpr hx1, sub_ne_zero.mpr hx2]
      <;> ring
    rw [← heq]
    simpa only [Real.log_abs] using hd2.sub hd1
  have hcont : ContinuousOn integrand (uIcc a b) := by
    intro x hx
    have hx1 : x ≠ 1 := h1 x hx
    have hx2 : x ≠ 2 := h2 x hx
    have hden : x ^ 2 - 3 * x + 2 ≠ 0 := by
      rw [show x ^ 2 - 3 * x + 2 = (x - 1) * (x - 2) by ring]
      exact mul_ne_zero (sub_ne_zero.mpr hx1) (sub_ne_zero.mpr hx2)
    have hsq : ContinuousAt (fun y : ℝ => y ^ 2) x :=
      continuousAt_id.pow 2
    have hlin : ContinuousAt (fun y : ℝ => 3 * y) x :=
      continuousAt_const.mul continuousAt_id
    have hpoly : ContinuousAt (fun y : ℝ => y ^ 2 - 3 * y + 2) x :=
      (hsq.sub hlin).add continuousAt_const
    have hone : ContinuousAt (fun _ : ℝ => (1 : ℝ)) x :=
      continuousAt_const
    unfold integrand
    exact (hone.div hpoly hden).continuousWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hcont.intervalIntegrable

theorem gap1 (ε η b : ℝ)
    (hε : ε ∈ Ioo 0 1) (hη : η ∈ Ioo 0 1) (hb : 2 < b) :
    trunc ε η b = expanded ε η b := by
  rcases hε with ⟨hε0, hε1⟩
  rcases hη with ⟨hη0, hη1⟩
  have hεne : ε ≠ 0 := ne_of_gt hε0
  have hηne : η ≠ 0 := ne_of_gt hη0
  have hεpne : ε + 1 ≠ 0 := ne_of_gt (by linarith)
  have hηpne : 1 + η ≠ 0 := ne_of_gt (by linarith)
  have hεmne : 1 - ε ≠ 0 := ne_of_gt (by linarith)
  have hηmne : 1 - η ≠ 0 := ne_of_gt (by linarith)
  have hb2ne : b - 2 ≠ 0 := ne_of_gt (by linarith)
  have hb1ne : b - 1 ≠ 0 := ne_of_gt (by linarith)
  have hI1 := integral_integrand_eq (a := (0 : ℝ)) (b := 1 - ε)
    (by
      intro x hx hx'
      rw [mem_uIcc] at hx
      rcases hx with hx | hx <;> rcases hx with ⟨hxl, hxr⟩ <;> linarith)
    (by
      intro x hx hx'
      rw [mem_uIcc] at hx
      rcases hx with hx | hx <;> rcases hx with ⟨hxl, hxr⟩ <;> linarith)
  have hI2 := integral_integrand_eq (a := 1 + ε) (b := 2 - η)
    (by
      intro x hx hx'
      rw [mem_uIcc] at hx
      rcases hx with hx | hx <;> rcases hx with ⟨hxl, hxr⟩ <;> linarith)
    (by
      intro x hx hx'
      rw [mem_uIcc] at hx
      rcases hx with hx | hx <;> rcases hx with ⟨hxl, hxr⟩ <;> linarith)
  have hI3 := integral_integrand_eq (a := 2 + η) (b := b)
    (by
      intro x hx hx'
      rw [mem_uIcc] at hx
      rcases hx with hx | hx <;> rcases hx with ⟨hxl, hxr⟩ <;> linarith)
    (by
      intro x hx hx'
      rw [mem_uIcc] at hx
      rcases hx with hx | hx <;> rcases hx with ⟨hxl, hxr⟩ <;> linarith)
  have ha11 : |1 - ε - 2| = 1 + ε := by
    rw [abs_of_neg] <;> linarith
  have ha12 : |1 - ε - 1| = ε := by
    rw [abs_of_neg] <;> linarith
  have ha01 : |(0 : ℝ) - 2| = 2 := by norm_num
  have ha02 : |(0 : ℝ) - 1| = 1 := by norm_num
  have ha21 : |2 - η - 2| = η := by
    rw [abs_of_neg] <;> linarith
  have ha22 : |2 - η - 1| = 1 - η := by
    rw [abs_of_pos] <;> linarith
  have ha31 : |1 + ε - 2| = 1 - ε := by
    rw [abs_of_neg] <;> linarith
  have ha32 : |1 + ε - 1| = ε := by
    rw [abs_of_pos] <;> linarith
  have hab1 : |b - 2| = b - 2 := by
    rw [abs_of_pos] <;> linarith
  have hab2 : |b - 1| = b - 1 := by
    rw [abs_of_pos] <;> linarith
  have ha41 : |2 + η - 2| = η := by
    rw [abs_of_pos] <;> linarith
  have ha42 : |2 + η - 1| = 1 + η := by
    rw [abs_of_pos] <;> linarith
  unfold trunc expanded
  rw [hI1, hI2, hI3, abs_div]
  rw [ha11, ha12, ha01, ha02, ha21, ha22, ha31, ha32,
    hab1, hab2, ha41, ha42]
  rw [Real.log_div hεpne hεne, Real.log_div hηne hηmne,
    Real.log_div hεmne hεne, Real.log_div hb2ne hb1ne,
    Real.log_div hηne hηpne]
  rw [add_comm ε 1]
  simp only [Real.log_one]
  ring

theorem gap2 (ε η b : ℝ)
    (hε : ε ∈ Ioo 0 1) (hη : η ∈ Ioo 0 1) (hb : 2 < b) :
    expanded ε η b =
      reduced ε η + Real.log |(b - 2) / (b - 1)| := by
  rcases hε with ⟨hε0, hε1⟩
  rcases hη with ⟨hη0, hη1⟩
  have hεne : ε ≠ 0 := ne_of_gt hε0
  have hηne : η ≠ 0 := ne_of_gt hη0
  have hεpne : 1 + ε ≠ 0 := ne_of_gt (by linarith)
  have hηpne : 1 + η ≠ 0 := ne_of_gt (by linarith)
  have hεmne : 1 - ε ≠ 0 := ne_of_gt (by linarith)
  have hηmne : 1 - η ≠ 0 := ne_of_gt (by linarith)
  unfold expanded reduced
  rw [add_comm ε 1]
  rw [Real.log_div hεpne hεne, Real.log_div hηne hηmne,
    Real.log_div hεmne hεne, Real.log_div hηne hηpne,
    Real.log_div hεpne hεmne, Real.log_div hηpne hηmne]
  ring

theorem gap3 :
    Tendsto
      (fun p : ℝ × ℝ => reduced p.1 p.2)
      (nhdsWithin 0 (Ioi 0) ×ˢ nhdsWithin 0 (Ioi 0))
      (nhds (-Real.log 2)) := by
  let L := nhdsWithin (0 : ℝ) (Ioi 0) ×ˢ nhdsWithin (0 : ℝ) (Ioi 0)
  have h0 : Tendsto (fun x : ℝ => x) (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have hp1 : Tendsto (fun p : ℝ × ℝ => p.1) L (nhds 0) :=
    h0.comp tendsto_fst
  have hp2 : Tendsto (fun p : ℝ × ℝ => p.2) L (nhds 0) :=
    h0.comp tendsto_snd
  have hr1 :
      Tendsto (fun p : ℝ × ℝ => (1 + p.1) / (1 - p.1)) L (nhds 1) := by
    simpa using
      ((tendsto_const_nhds.add hp1).div
        (tendsto_const_nhds.sub hp1) (by norm_num : (1 - 0 : ℝ) ≠ 0))
  have hr2 :
      Tendsto (fun p : ℝ × ℝ => (1 + p.2) / (1 - p.2)) L (nhds 1) := by
    simpa using
      ((tendsto_const_nhds.add hp2).div
        (tendsto_const_nhds.sub hp2) (by norm_num : (1 - 0 : ℝ) ≠ 0))
  have hl1 :
      Tendsto (fun p : ℝ × ℝ => Real.log ((1 + p.1) / (1 - p.1))) L
        (nhds 0) := by
    simpa using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hr1
  have hl2 :
      Tendsto (fun p : ℝ × ℝ => Real.log ((1 + p.2) / (1 - p.2))) L
        (nhds 0) := by
    simpa using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hr2
  simpa [L, reduced] using (hl1.sub tendsto_const_nhds).add hl2

theorem gap4 :
    -Real.log 2 = Real.log (1 / 2 : ℝ) := by
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
    (by norm_num : (2 : ℝ) ≠ 0)]
  rw [Real.log_one]
  ring

theorem gap5 :
    Tendsto
      (fun p : ℝ × (ℝ × ℝ) => trunc p.1 p.2.1 p.2.2)
      (nhdsWithin 0 (Ioi 0) ×ˢ
        (nhdsWithin 0 (Ioi 0) ×ˢ atTop))
      (nhds (Real.log (1 / 2 : ℝ))) := by
  let Fε : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0)
  let Fη : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0)
  let L : Filter (ℝ × (ℝ × ℝ)) :=
    Fε ×ˢ (Fη ×ˢ (atTop : Filter ℝ))
  have hεw : Tendsto (fun p : ℝ × (ℝ × ℝ) => p.1) L Fε :=
    tendsto_fst
  have hsnd :
      Tendsto (fun p : ℝ × (ℝ × ℝ) => p.2) L
        (Fη ×ˢ (atTop : Filter ℝ)) :=
    tendsto_snd
  have hηw : Tendsto (fun p : ℝ × (ℝ × ℝ) => p.2.1) L Fη :=
    (tendsto_fst : Tendsto (fun p : ℝ × ℝ => p.1)
      (Fη ×ˢ (atTop : Filter ℝ)) Fη).comp hsnd
  have hbw : Tendsto (fun p : ℝ × (ℝ × ℝ) => p.2.2) L atTop :=
    (tendsto_snd : Tendsto (fun p : ℝ × ℝ => p.2)
      (Fη ×ˢ (atTop : Filter ℝ)) atTop).comp hsnd
  have hpairs :
      Tendsto (fun p : ℝ × (ℝ × ℝ) => (p.1, p.2.1)) L (Fε ×ˢ Fη) :=
    hεw.prodMk hηw
  have hred :
      Tendsto (fun p : ℝ × (ℝ × ℝ) => reduced p.1 p.2.1) L
        (nhds (-Real.log 2)) := by
    simpa [Fε, Fη] using gap3.comp hpairs
  have hsub : Tendsto (fun b : ℝ => b - 1) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro c
    filter_upwards [eventually_ge_atTop (c + 1)] with b hb
    linarith
  have hinv : Tendsto (fun b : ℝ => (b - 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hsub
  have hratio' :
      Tendsto (fun b : ℝ => 1 - (b - 1)⁻¹) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hinv
  have heqratio :
      (fun b : ℝ => (b - 2) / (b - 1)) =ᶠ[atTop]
        (fun b : ℝ => 1 - (b - 1)⁻¹) := by
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with b hb
    have hb1 : b - 1 ≠ 0 := by linarith
    field_simp [hb1]
    <;> ring
  have hratio :
      Tendsto (fun b : ℝ => (b - 2) / (b - 1)) atTop (nhds 1) :=
    hratio'.congr' heqratio.symm
  have hlograw :
      Tendsto (fun b : ℝ => Real.log ((b - 2) / (b - 1))) atTop
        (nhds 0) := by
    simpa only [Function.comp_apply, Real.log_one] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
  have heqlog :
      (fun b : ℝ => Real.log ((b - 2) / (b - 1))) =ᶠ[atTop]
        (fun b : ℝ => Real.log |(b - 2) / (b - 1)|) := by
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with b hb
    have hpos : 0 < (b - 2) / (b - 1) :=
      div_pos (by linarith) (by linarith)
    rw [abs_of_pos hpos]
  have hlog :
      Tendsto (fun b : ℝ => Real.log |(b - 2) / (b - 1)|) atTop
        (nhds 0) :=
    hlograw.congr' heqlog
  have hlogp :
      Tendsto
        (fun p : ℝ × (ℝ × ℝ) => Real.log |(p.2.2 - 2) / (p.2.2 - 1)|)
        L (nhds 0) :=
    hlog.comp hbw
  have hsum :
      Tendsto
        (fun p : ℝ × (ℝ × ℝ) =>
          reduced p.1 p.2.1 + Real.log |(p.2.2 - 2) / (p.2.2 - 1)|)
        L (nhds (Real.log (1 / 2 : ℝ))) := by
    simpa only [add_zero, gap4] using hred.add hlogp
  have hepspos : ∀ᶠ p in L, 0 < p.1 :=
    hεw.eventually self_mem_nhdsWithin
  have hepslt : ∀ᶠ p in L, p.1 < 1 :=
    hεw.eventually
      (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  have hetapos : ∀ᶠ p in L, 0 < p.2.1 :=
    hηw.eventually self_mem_nhdsWithin
  have hetalt : ∀ᶠ p in L, p.2.1 < 1 :=
    hηw.eventually
      (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  have hbgt : ∀ᶠ p in L, 2 < p.2.2 :=
    hbw.eventually (eventually_gt_atTop (2 : ℝ))
  have heq :
      (fun p : ℝ × (ℝ × ℝ) => trunc p.1 p.2.1 p.2.2) =ᶠ[L]
        (fun p : ℝ × (ℝ × ℝ) =>
          reduced p.1 p.2.1 + Real.log |(p.2.2 - 2) / (p.2.2 - 1)|) := by
    filter_upwards [hepspos, hepslt, hetapos, hetalt, hbgt] with p hε0 hε1 hη0 hη1 hb
    rw [gap1 p.1 p.2.1 p.2.2 ⟨hε0, hε1⟩ ⟨hη0, hη1⟩ hb,
      gap2 p.1 p.2.1 p.2.2 ⟨hε0, hε1⟩ ⟨hη0, hη1⟩ hb]
  simpa [L, Fε, Fη] using hsum.congr' heq.symm

end
end ProofGap.Exercise2392
