import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1321

noncomputable section
open Filter
open scoped Topology

def punctured (x₀ : ℝ) := nhdsWithin x₀ ({x₀} : Set ℝ)ᶜ
def sec (x : ℝ) := 1 / Real.cos x
def original (x : ℝ) :=
  (3 * Real.tan (4 * x) - 12 * Real.tan x) /
    (3 * Real.sin (4 * x) - 12 * Real.sin x)
def firstStage (x : ℝ) :=
  (12 * sec (4 * x) ^ 2 - 12 * sec x ^ 2) /
    (12 * Real.cos (4 * x) - 12 * Real.cos x)
def secondStage (x : ℝ) :=
  -(Real.cos (4 * x) + Real.cos x) /
    (Real.cos x ^ 2 * Real.cos (4 * x) ^ 2)

private def reduced (x : ℝ) :=
  -((1 + Real.cos x) * (6 * Real.cos x ^ 2 - 1)) /
    (Real.cos x * Real.cos (4 * x) *
      (2 * Real.cos x ^ 2 + 2 * Real.cos x + 1))

private theorem punctured_le_nhds (x₀ : ℝ) :
    punctured x₀ ≤ 𝓝 x₀ := by
  change (𝓝 x₀ ⊓ principal ({x₀} : Set ℝ)ᶜ) ≤ 𝓝 x₀
  exact inf_le_left

private theorem eventually_ne_small :
    ∀ᶠ x in punctured 0, x ≠ 0 ∧ |x| < (1 / 4 : ℝ) := by
  have hne : ∀ᶠ x in punctured 0, x ≠ 0 := by
    simpa [punctured] using
      (self_mem_nhdsWithin :
        ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ, x ∈ ({0} : Set ℝ)ᶜ)
  have hball : Metric.ball (0 : ℝ) (1 / 4 : ℝ) ∈ 𝓝 0 :=
    Metric.ball_mem_nhds 0 (by norm_num)
  have hball' : Metric.ball (0 : ℝ) (1 / 4 : ℝ) ∈ punctured 0 :=
    punctured_le_nhds 0 hball
  have hsmall : ∀ᶠ x in punctured 0, |x| < (1 / 4 : ℝ) := by
    filter_upwards [hball'] with x hx
    simpa [Metric.mem_ball, Real.dist_eq] using hx
  filter_upwards [hne, hsmall] with x hx hxs
  exact ⟨hx, hxs⟩

private theorem reduced_tendsto :
    Tendsto reduced (punctured 0) (nhds (-2)) := by
  have hc : ContinuousAt (fun x : ℝ => Real.cos x) 0 :=
    Real.continuous_cos.continuousAt
  have hc4 : ContinuousAt (fun x : ℝ => Real.cos (4 * x)) 0 :=
    (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).continuousAt
  have hn : ContinuousAt
      (fun x : ℝ => -((1 + Real.cos x) * (6 * Real.cos x ^ 2 - 1))) 0 :=
    ((continuousAt_const.add hc).mul
      ((continuousAt_const.mul (hc.pow 2)).sub continuousAt_const)).neg
  have hp : ContinuousAt
      (fun x : ℝ => 2 * Real.cos x ^ 2 + 2 * Real.cos x + 1) 0 :=
    ((continuousAt_const.mul (hc.pow 2)).add
      (continuousAt_const.mul hc)).add continuousAt_const
  have hd : ContinuousAt
      (fun x : ℝ => Real.cos x * Real.cos (4 * x) *
        (2 * Real.cos x ^ 2 + 2 * Real.cos x + 1)) 0 :=
    (hc.mul hc4).mul hp
  have hcont : ContinuousAt reduced 0 := by
    unfold reduced
    exact hn.div hd (by norm_num)
  have ht : Tendsto reduced (𝓝 0) (𝓝 (reduced 0)) := hcont
  have hv : reduced 0 = -2 := by
    norm_num [reduced]
  rw [hv] at ht
  exact ht.mono_left (punctured_le_nhds 0)

private theorem secondStage_tendsto :
    Tendsto secondStage (punctured 0) (nhds (-2)) := by
  have hc : ContinuousAt (fun x : ℝ => Real.cos x) 0 :=
    Real.continuous_cos.continuousAt
  have hc4 : ContinuousAt (fun x : ℝ => Real.cos (4 * x)) 0 :=
    (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).continuousAt
  have hn : ContinuousAt
      (fun x : ℝ => -(Real.cos (4 * x) + Real.cos x)) 0 :=
    (hc4.add hc).neg
  have hd : ContinuousAt
      (fun x : ℝ => Real.cos x ^ 2 * Real.cos (4 * x) ^ 2) 0 :=
    (hc.pow 2).mul (hc4.pow 2)
  have hcont : ContinuousAt secondStage 0 := by
    unfold secondStage
    exact hn.div hd (by norm_num)
  have ht : Tendsto secondStage (𝓝 0) (𝓝 (secondStage 0)) := hcont
  have hv : secondStage 0 = -2 := by
    norm_num [secondStage]
  rw [hv] at ht
  exact ht.mono_left (punctured_le_nhds 0)

private theorem original_eq_reduced_of_ne_small
    {x : ℝ} (hx : x ≠ 0) (hsmall : |x| < (1 / 4 : ℝ)) :
    original x = reduced x := by
  have hpi := Real.pi_gt_three
  have hxlower : -(Real.pi / 2) < x := by
    have := neg_lt_of_abs_lt hsmall
    nlinarith
  have hxupper : x < Real.pi / 2 := by
    have := lt_of_le_of_lt (le_abs_self x) hsmall
    nlinarith
  have h4lower : -(Real.pi / 2) < 4 * x := by
    have := neg_lt_of_abs_lt hsmall
    nlinarith
  have h4upper : 4 * x < Real.pi / 2 := by
    have := lt_of_le_of_lt (le_abs_self x) hsmall
    nlinarith
  have hcospos : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo ⟨hxlower, hxupper⟩
  have hcos4pos : 0 < Real.cos (4 * x) :=
    Real.cos_pos_of_mem_Ioo ⟨h4lower, h4upper⟩
  have hsin : Real.sin x ≠ 0 := by
    rcases lt_or_gt_of_ne hx with hxneg | hxpos
    · have hs : 0 < Real.sin (-x) :=
        Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr hxneg) (by
          have := neg_lt_of_abs_lt hsmall
          nlinarith)
      simpa using (ne_of_gt hs)
    · exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hxpos (by
        have := lt_of_le_of_lt (le_abs_self x) hsmall
        nlinarith))
  have htrig := Real.sin_sq_add_cos_sq x
  have hspos : 0 < Real.sin x ^ 2 := sq_pos_of_ne_zero hsin
  have hcoslt : Real.cos x < 1 := by
    nlinarith
  have hsq : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
    nlinarith
  have hsin4 :
      Real.sin (4 * x) =
        4 * Real.sin x * Real.cos x * (2 * Real.cos x ^ 2 - 1) := by
    rw [show 4 * x = 2 * (2 * x) by ring, Real.sin_two_mul,
      Real.sin_two_mul, Real.cos_two_mul]
    ring
  have hcos4 :
      Real.cos (4 * x) = 2 * (2 * Real.cos x ^ 2 - 1) ^ 2 - 1 := by
    rw [show 4 * x = 2 * (2 * x) by ring, Real.cos_two_mul,
      Real.cos_two_mul]
  have hPpos : 0 < 2 * Real.cos x ^ 2 + 2 * Real.cos x + 1 := by
    nlinarith [sq_nonneg (Real.cos x)]
  have hB :
      Real.cos x * (2 * Real.cos x ^ 2 - 1) - 1 =
        (Real.cos x - 1) *
          (2 * Real.cos x ^ 2 + 2 * Real.cos x + 1) := by
    ring
  have hBne : Real.cos x * (2 * Real.cos x ^ 2 - 1) - 1 ≠ 0 := by
    rw [hB]
    exact mul_ne_zero (sub_ne_zero.mpr (ne_of_lt hcoslt)) (ne_of_gt hPpos)
  have hdenbase : Real.sin (4 * x) - 4 * Real.sin x ≠ 0 := by
    rw [hsin4]
    have hfactor :
        4 * Real.sin x * Real.cos x * (2 * Real.cos x ^ 2 - 1) -
            4 * Real.sin x =
          4 * Real.sin x *
            (Real.cos x * (2 * Real.cos x ^ 2 - 1) - 1) := by
      ring
    rw [hfactor]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hsin) hBne
  have hdenorig : 3 * Real.sin (4 * x) - 12 * Real.sin x ≠ 0 := by
    intro h
    apply hdenbase
    nlinarith
  have hN :
      Real.cos x ^ 2 * (2 * Real.cos x ^ 2 - 1) - Real.cos (4 * x) =
        Real.sin x ^ 2 * (6 * Real.cos x ^ 2 - 1) := by
    rw [hcos4, hsq]
    ring
  calc
    original x =
        ((Real.sin (4 * x) / Real.cos (4 * x)) -
            4 * (Real.sin x / Real.cos x)) /
          (Real.sin (4 * x) - 4 * Real.sin x) := by
      unfold original
      rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
      field_simp [hdenorig, hdenbase, ne_of_gt hcospos, ne_of_gt hcos4pos]
      <;> ring
    _ =
        (Real.cos x ^ 2 * (2 * Real.cos x ^ 2 - 1) - Real.cos (4 * x)) /
          (Real.cos x * Real.cos (4 * x) *
            (Real.cos x * (2 * Real.cos x ^ 2 - 1) - 1)) := by
      rw [hsin4]
      field_simp [hsin, ne_of_gt hcospos, ne_of_gt hcos4pos, hBne]
      <;> ring
    _ = reduced x := by
      rw [hN, hB, hsq]
      unfold reduced
      field_simp [ne_of_gt hcospos, ne_of_gt hcos4pos,
        ne_of_gt hPpos, sub_ne_zero.mpr (ne_of_lt hcoslt)]
      <;> ring

private theorem eventually_original_eq_reduced :
    original =ᶠ[punctured 0] reduced := by
  filter_upwards [eventually_ne_small] with x hx
  exact original_eq_reduced_of_ne_small hx.1 hx.2

private theorem firstStage_eq_secondStage_of_ne_small
    {x : ℝ} (hx : x ≠ 0) (hsmall : |x| < (1 / 4 : ℝ)) :
    firstStage x = secondStage x := by
  have hpi := Real.pi_gt_three
  have hxlower : -(Real.pi / 2) < x := by
    have := neg_lt_of_abs_lt hsmall
    nlinarith
  have hxupper : x < Real.pi / 2 := by
    have := lt_of_le_of_lt (le_abs_self x) hsmall
    nlinarith
  have h4lower : -(Real.pi / 2) < 4 * x := by
    have := neg_lt_of_abs_lt hsmall
    nlinarith
  have h4upper : 4 * x < Real.pi / 2 := by
    have := lt_of_le_of_lt (le_abs_self x) hsmall
    nlinarith
  have hcospos : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo ⟨hxlower, hxupper⟩
  have hcos4pos : 0 < Real.cos (4 * x) :=
    Real.cos_pos_of_mem_Ioo ⟨h4lower, h4upper⟩
  have hsin : Real.sin x ≠ 0 := by
    rcases lt_or_gt_of_ne hx with hxneg | hxpos
    · have hs : 0 < Real.sin (-x) :=
        Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr hxneg) (by
          have := neg_lt_of_abs_lt hsmall
          nlinarith)
      simpa using (ne_of_gt hs)
    · exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hxpos (by
        have := lt_of_le_of_lt (le_abs_self x) hsmall
        nlinarith))
  have htrig := Real.sin_sq_add_cos_sq x
  have hsabs : |Real.sin x| < (1 / 4 : ℝ) :=
    lt_of_le_of_lt
      (show |Real.sin x| ≤ |x| from Real.abs_sin_le_abs) hsmall
  have hp :
      0 < ((1 / 4 : ℝ) - |Real.sin x|) *
        (|Real.sin x| + (1 / 4 : ℝ)) :=
    mul_pos (sub_pos.mpr hsabs)
      (add_pos_of_nonneg_of_pos (abs_nonneg (Real.sin x)) (by norm_num))
  have hs_sq : Real.sin x ^ 2 < (1 / 4 : ℝ) ^ 2 := by
    nlinarith [sq_abs (Real.sin x)]
  have hcoshalf : (1 / 2 : ℝ) < Real.cos x := by
    nlinarith
  have hcos4 :
      Real.cos (4 * x) = 2 * (2 * Real.cos x ^ 2 - 1) ^ 2 - 1 := by
    rw [show 4 * x = 2 * (2 * x) by ring, Real.cos_two_mul,
      Real.cos_two_mul]
  have hcoslt : Real.cos x < 1 := by
    have hspos : 0 < Real.sin x ^ 2 := sq_pos_of_ne_zero hsin
    nlinarith
  have hc2 : (1 / 4 : ℝ) < Real.cos x ^ 2 := by
    nlinarith [sq_nonneg (Real.cos x - 1 / 2)]
  have hc3 : 0 < Real.cos x ^ 3 := pow_pos hcospos 3
  have hQpos : 0 < 8 * Real.cos x ^ 3 + 8 * Real.cos x ^ 2 - 1 := by
    nlinarith
  have hdiffid :
      Real.cos (4 * x) - Real.cos x =
        (Real.cos x - 1) *
          (8 * Real.cos x ^ 3 + 8 * Real.cos x ^ 2 - 1) := by
    rw [hcos4]
    ring
  have hdiff : Real.cos (4 * x) ≠ Real.cos x := by
    rw [← sub_ne_zero, hdiffid]
    exact mul_ne_zero (sub_ne_zero.mpr (ne_of_lt hcoslt)) (ne_of_gt hQpos)
  have hdiff0 : Real.cos (4 * x) - Real.cos x ≠ 0 :=
    sub_ne_zero.mpr hdiff
  have hden : 12 * Real.cos (4 * x) - 12 * Real.cos x ≠ 0 := by
    intro h
    apply hdiff
    nlinarith
  unfold firstStage secondStage sec
  field_simp [ne_of_gt hcospos, ne_of_gt hcos4pos, hdiff0, hden]
  <;> ring

private theorem eventually_firstStage_eq_secondStage :
    firstStage =ᶠ[punctured 0] secondStage := by
  filter_upwards [eventually_ne_small] with x hx
  exact firstStage_eq_secondStage_of_ne_small hx.1 hx.2

theorem gap1 : Tendsto original (punctured 0) (nhds (-2)) := by
  exact reduced_tendsto.congr' eventually_original_eq_reduced.symm
theorem gap2 : Tendsto firstStage (punctured 0) (nhds (-2)) := by
  exact secondStage_tendsto.congr' eventually_firstStage_eq_secondStage.symm
theorem gap3 : Tendsto secondStage (punctured 0) (nhds (-2)) := by
  exact secondStage_tendsto
theorem gap4 : Tendsto original (punctured 0) (nhds (-2)) := by
  exact gap1

end
end ProofGap.Exercise1321
