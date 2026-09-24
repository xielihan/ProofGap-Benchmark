import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1325

noncomputable section
open Filter
open scoped Topology

def punctured (x₀ : ℝ) := nhdsWithin x₀ ({x₀} : Set ℝ)ᶜ
def original (x : ℝ) :=
  (x * (Real.exp x + 1) - 2 * (Real.exp x - 1)) / x ^ 3
def firstStage (x : ℝ) :=
  (Real.exp x + 1 + x * Real.exp x - 2 * Real.exp x) / (3 * x ^ 2)
def secondStage (x : ℝ) := (1 - Real.exp x + x * Real.exp x) / (3 * x ^ 2)
def thirdStage (x : ℝ) := x * Real.exp x / (6 * x)
def finalStage (x : ℝ) := Real.exp x / 6

private theorem secondStage_limit :
    Tendsto secondStage (punctured 0) (nhds (1 / 6 : ℝ)) := by
  have hp_le : punctured 0 ≤ nhds 0 := by
    unfold punctured nhdsWithin
    exact inf_le_left
  have hrem :
      (fun x : ℝ ↦ Real.exp x - (1 + x + x ^ 2 / 2)) =o[nhds 0]
        (fun x : ℝ ↦ x ^ 2) := by
    simpa [Finset.sum_range_succ] using
      Real.exp_sub_sum_range_succ_isLittleO_pow 2
  have hquot : Tendsto
      (fun x : ℝ ↦ (Real.exp x - (1 + x + x ^ 2 / 2)) / x ^ 2)
      (punctured 0) (nhds 0) :=
    hrem.tendsto_div_nhds_zero.mono_left hp_le
  have hid : Tendsto (fun x : ℝ ↦ x) (punctured 0) (nhds 0) :=
    tendsto_id.mono_left hp_le
  have hfactor : Tendsto (fun x : ℝ ↦ (x - 1) / 3)
      (punctured 0) (nhds (-(1 : ℝ) / 3)) := by
    simpa using (hid.sub_const 1).div_const 3
  have hlim : Tendsto
      (fun x : ℝ ↦ (1 / 6 : ℝ) + x / 6 +
        ((x - 1) / 3) *
          ((Real.exp x - (1 + x + x ^ 2 / 2)) / x ^ 2))
      (punctured 0) (nhds (1 / 6 : ℝ)) := by
    convert tendsto_const_nhds.add (hid.div_const 6) |>.add (hfactor.mul hquot) using 1 <;>
      norm_num
  have hne : ∀ᶠ x in punctured 0, x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  apply hlim.congr'
  filter_upwards [hne] with x hx
  unfold secondStage
  field_simp [hx]
  ring

private theorem finalStage_limit :
    Tendsto finalStage (punctured 0) (nhds (1 / 6 : ℝ)) := by
  have hp_le : punctured 0 ≤ nhds 0 := by
    unfold punctured nhdsWithin
    exact inf_le_left
  simpa [finalStage] using
    (Real.tendsto_exp_nhds_zero_nhds_one.div_const 6).mono_left hp_le

theorem gap1 : Tendsto original (punctured 0) (nhds (1 / 6 : ℝ)) := by
  have hp_le : punctured 0 ≤ nhds 0 := by
    unfold punctured nhdsWithin
    exact inf_le_left
  have hrem :
      (fun x : ℝ ↦ Real.exp x - (1 + x + x ^ 2 / 2 + x ^ 3 / 6)) =o[nhds 0]
        (fun x : ℝ ↦ x ^ 3) := by
    simpa [Finset.sum_range_succ] using
      Real.exp_sub_sum_range_succ_isLittleO_pow 3
  have hquot : Tendsto
      (fun x : ℝ ↦
        (Real.exp x - (1 + x + x ^ 2 / 2 + x ^ 3 / 6)) / x ^ 3)
      (punctured 0) (nhds 0) :=
    hrem.tendsto_div_nhds_zero.mono_left hp_le
  have hid : Tendsto (fun x : ℝ ↦ x) (punctured 0) (nhds 0) :=
    tendsto_id.mono_left hp_le
  have hfactor : Tendsto (fun x : ℝ ↦ x - 2) (punctured 0) (nhds (-2)) := by
    simpa using hid.sub_const 2
  have hlim : Tendsto
      (fun x : ℝ ↦ (1 / 6 : ℝ) + x / 6 +
        (x - 2) *
          ((Real.exp x - (1 + x + x ^ 2 / 2 + x ^ 3 / 6)) / x ^ 3))
      (punctured 0) (nhds (1 / 6 : ℝ)) := by
    convert tendsto_const_nhds.add (hid.div_const 6) |>.add (hfactor.mul hquot) using 1 <;>
      norm_num
  have hne : ∀ᶠ x in punctured 0, x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  apply hlim.congr'
  filter_upwards [hne] with x hx
  unfold original
  field_simp [hx]
  ring
theorem gap2 : Tendsto firstStage (punctured 0) (nhds (1 / 6 : ℝ)) := by
  have heq : firstStage = secondStage := by
    funext x
    unfold firstStage secondStage
    congr 1
    ring
  rw [heq]
  exact secondStage_limit
theorem gap3 : Tendsto secondStage (punctured 0) (nhds (1 / 6 : ℝ)) := by
  have hp_le : punctured 0 ≤ nhds 0 := by
    unfold punctured nhdsWithin
    exact inf_le_left
  have hrem :
      (fun x : ℝ ↦ Real.exp x - (1 + x + x ^ 2 / 2)) =o[nhds 0]
        (fun x : ℝ ↦ x ^ 2) := by
    simpa [Finset.sum_range_succ] using
      Real.exp_sub_sum_range_succ_isLittleO_pow 2
  have hquot : Tendsto
      (fun x : ℝ ↦ (Real.exp x - (1 + x + x ^ 2 / 2)) / x ^ 2)
      (punctured 0) (nhds 0) :=
    hrem.tendsto_div_nhds_zero.mono_left hp_le
  have hid : Tendsto (fun x : ℝ ↦ x) (punctured 0) (nhds 0) :=
    tendsto_id.mono_left hp_le
  have hfactor : Tendsto (fun x : ℝ ↦ (x - 1) / 3)
      (punctured 0) (nhds (-(1 : ℝ) / 3)) := by
    simpa using (hid.sub_const 1).div_const 3
  have hlim : Tendsto
      (fun x : ℝ ↦ (1 / 6 : ℝ) + x / 6 +
        ((x - 1) / 3) *
          ((Real.exp x - (1 + x + x ^ 2 / 2)) / x ^ 2))
      (punctured 0) (nhds (1 / 6 : ℝ)) := by
    convert tendsto_const_nhds.add (hid.div_const 6) |>.add (hfactor.mul hquot) using 1 <;>
      norm_num
  have hne : ∀ᶠ x in punctured 0, x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  apply hlim.congr'
  filter_upwards [hne] with x hx
  unfold secondStage
  field_simp [hx]
  ring
theorem gap4 : Tendsto thirdStage (punctured 0) (nhds (1 / 6 : ℝ)) := by
  apply finalStage_limit.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  unfold thirdStage finalStage
  field_simp [hx0]
theorem gap5 : Tendsto finalStage (punctured 0) (nhds (1 / 6 : ℝ)) := by
  exact finalStage_limit
theorem gap6 : Tendsto finalStage (punctured 0) (nhds (1 / 6 : ℝ)) := by
  exact gap5
theorem gap7 : Tendsto original (punctured 0) (nhds (1 / 6 : ℝ)) := by
  exact gap1

end
end ProofGap.Exercise1325
