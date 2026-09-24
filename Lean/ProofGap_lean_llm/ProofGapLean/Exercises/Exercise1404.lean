import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1404

noncomputable section
open Filter
open scoped Topology

def original (x : ℝ) := x - x ^ 2 * Real.log (1 + 1 / x)
def expansionStage (x : ℝ) :=
  x - x ^ 2 * (1 / x - 1 / (2 * x ^ 2) + 1 / (3 * x ^ 3))
def leadingStage (x : ℝ) := (1 / 2 : ℝ) + 1 / x

private theorem log_second_order_limit :
    Tendsto (fun x : ℝ => (x - Real.log (1 + x)) / x ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
  have hdf_point : ∀ x : ℝ, 0 < x →
      HasDerivAt (fun y : ℝ => y - Real.log (1 + y)) (x / (1 + x)) x := by
    intro x hx
    have hinner : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
      convert (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x) using 1
      <;> ring
    have hlog_raw :=
      (Real.hasDerivAt_log (show 1 + x ≠ 0 by linarith)).comp x hinner
    have hlog :
        HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + x)) x := by
      convert hlog_raw using 1 <;> simp [one_div]
    convert (hasDerivAt_id x).sub hlog using 1
    · field_simp [show 1 + x ≠ 0 by linarith]
      ring
  have hdf : ∀ᶠ x in 𝓝[>] (0 : ℝ),
      HasDerivAt (fun y : ℝ => y - Real.log (1 + y)) (x / (1 + x)) x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    change 0 < x at hx
    exact hdf_point x hx
  have hdg_point : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    intro x
    convert (hasDerivAt_id x).pow 2 using 1 <;> simp <;> ring
  have hdg : ∀ᶠ x in 𝓝[>] (0 : ℝ),
      HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x :=
    Filter.Eventually.of_forall hdg_point
  have hgne : ∀ᶠ x in 𝓝[>] (0 : ℝ), (2 * x : ℝ) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    change 0 < x at hx
    exact mul_ne_zero (by norm_num) (ne_of_gt hx)
  have hfder0 :
      HasDerivAt (fun y : ℝ => y - Real.log (1 + y)) 0 0 := by
    have hinner : HasDerivAt (fun y : ℝ => 1 + y) 1 0 := by
      convert (hasDerivAt_const 0 (1 : ℝ)).add (hasDerivAt_id 0) using 1
      <;> norm_num
    have hlog_outer : HasDerivAt Real.log 1 (1 + (0 : ℝ)) := by
      simpa using
        (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0))
    have hlog_raw := hlog_outer.comp 0 hinner
    have hlog : HasDerivAt (fun y : ℝ => Real.log (1 + y)) 1 0 := by
      simpa [Function.comp_def] using hlog_raw
    convert (hasDerivAt_id 0).sub hlog using 1 <;> norm_num
  have hf0 :
      Tendsto (fun y : ℝ => y - Real.log (1 + y))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := hfder0.continuousAt.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from inf_le_left)
    simpa using h
  have hg0 : Tendsto (fun y : ℝ => y ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (hdg_point 0).continuousAt.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from inf_le_left)
    simpa using h
  have hone : Tendsto (fun x : ℝ => 1 + x) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using
      ((tendsto_const_nhds.add tendsto_id).mono_left inf_le_left :
        Tendsto (fun x : ℝ => 1 + x) (𝓝[>] (0 : ℝ)) (𝓝 (1 + 0)))
  have hquot :
      Tendsto (fun x : ℝ => (x / (1 + x)) / (2 * x))
        (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
    have hbase :
        Tendsto (fun x : ℝ => 1 / (2 * (1 + x)))
          (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
      convert tendsto_const_nhds.div (tendsto_const_nhds.mul hone)
        (by norm_num : (2 : ℝ) * 1 ≠ 0) using 1 <;> norm_num
    apply hbase.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    change 0 < x at hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hx1 : 1 + x ≠ 0 := by linarith
    field_simp [hx0, hx1]
  apply HasDerivAt.lhopital_zero_nhdsGT
    (f' := fun x : ℝ => x / (1 + x)) (g' := fun x : ℝ => 2 * x)
  · exact hdf
  · exact hdg
  · exact hgne
  · exact hf0
  · exact hg0
  · exact hquot

theorem gap1 : Tendsto original atTop (nhds (1 / 2 : ℝ)) := by
  have hinv_right :
      Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_inv_atTop_zero, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact inv_pos.mpr hx
  have hlim := log_second_order_limit.comp hinv_right
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  dsimp [original]
  field_simp [ne_of_gt hx]
theorem gap2 : Tendsto expansionStage atTop (nhds (1 / 2 : ℝ)) := by
  have hinv : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
    simpa [one_div] using
      (tendsto_inv_atTop_zero :
        Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))
  have hsmall :
      Tendsto (fun x : ℝ => (1 / 3 : ℝ) * (1 / x)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hinv)
  have hsimple :
      Tendsto (fun x : ℝ => (1 / 2 : ℝ) - (1 / 3 : ℝ) * (1 / x))
        atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa using (tendsto_const_nhds.sub hsmall)
  apply hsimple.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  dsimp [expansionStage]
  field_simp [ne_of_gt hx]
  ring
theorem gap3 : Tendsto leadingStage atTop (nhds (1 / 2 : ℝ)) := by
  have hinv : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
    simpa [one_div] using
      (tendsto_inv_atTop_zero :
        Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))
  change Tendsto (fun x : ℝ => (1 / 2 : ℝ) + 1 / x)
    atTop (𝓝 (1 / 2 : ℝ))
  simpa using
    (tendsto_const_nhds.add hinv :
      Tendsto (fun x : ℝ => (1 / 2 : ℝ) + 1 / x)
        atTop (𝓝 ((1 / 2 : ℝ) + 0)))
theorem gap4 : Tendsto original atTop (nhds (1 / 2 : ℝ)) := by
  exact gap1

end
end ProofGap.Exercise1404
