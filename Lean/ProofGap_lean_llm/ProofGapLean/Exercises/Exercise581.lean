import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise581

noncomputable section

def f (x : ℝ) : ℝ := Real.arcsin ((1 - x) / (1 + x))

/-- Source: `proof_gap/exercise_581/1.txt`. -/
theorem gap1 : Filter.Tendsto f Filter.atTop (nhds (Real.arcsin (-1))) := by
  unfold f
  have h_inv : Filter.Tendsto (fun x : ℝ => 1 / x) Filter.atTop (nhds 0) := by
    simpa only [one_div] using
      (tendsto_inv_atTop_zero :
        Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0))
  have h_num : Filter.Tendsto (fun x : ℝ => 1 / x - 1) Filter.atTop
      (nhds (0 - 1)) :=
    h_inv.sub tendsto_const_nhds
  have h_den : Filter.Tendsto (fun x : ℝ => 1 / x + 1) Filter.atTop
      (nhds (0 + 1)) :=
    h_inv.add tendsto_const_nhds
  have h_ratio : Filter.Tendsto
      (fun x : ℝ => (1 / x - 1) / (1 / x + 1)) Filter.atTop (nhds (-1)) := by
    simpa using
      (h_num.div h_den (by norm_num : (0 : ℝ) + 1 ≠ 0))
  have h_eq :
      (fun x : ℝ => (1 / x - 1) / (1 / x + 1)) =ᶠ[Filter.atTop]
        (fun x : ℝ => (1 - x) / (1 + x)) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have hx0 : x ≠ 0 := ne_of_gt hxpos
    have hx1 : 1 + x ≠ 0 :=
      ne_of_gt (add_pos zero_lt_one hxpos)
    have hfrac0 : 1 / x + 1 ≠ 0 :=
      ne_of_gt (add_pos (one_div_pos.mpr hxpos) zero_lt_one)
    field_simp [hx0, hx1, hfrac0] <;> ring
  have h_arg : Filter.Tendsto (fun x : ℝ => (1 - x) / (1 + x))
      Filter.atTop (nhds (-1)) :=
    h_ratio.congr' h_eq
  exact Real.continuous_arcsin.continuousAt.tendsto.comp h_arg

/-- Source: `proof_gap/exercise_581/2.txt`. -/
theorem gap2 : Real.arcsin (-1) = -Real.pi / 2 := by
  rw [Real.arcsin_neg, Real.arcsin_one]
  ring

/-- Source: `proof_gap/exercise_581/3.txt`. -/
theorem gap3 : Filter.Tendsto f Filter.atTop (nhds (-Real.pi / 2)) := by
  simpa only [gap2] using gap1

end

end ProofGap.Exercise581
