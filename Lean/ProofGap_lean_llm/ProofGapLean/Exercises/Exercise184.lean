import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Filter Topology

namespace ProofGap.Exercise184

noncomputable section

def y (x : ℝ) : ℝ := 1 / (1 - x)
def domain : Set ℝ := Set.Ioo 0 1
def valueSet : Set ℝ := {t | ∃ x ∈ domain, t = y x}

/-- Exercise 184, gap 1. -/
theorem gap1 : Tendsto y (𝓝[Set.Ioi 0] 0) (𝓝 1) := by
  have hc : ContinuousAt y 0 := by
    unfold y
    exact continuousAt_const.div
      (continuousAt_const.sub continuousAt_id) (by norm_num)
  have htend :
      Tendsto y (𝓝[Set.Ioi 0] 0) (𝓝 (y 0)) :=
    hc.continuousWithinAt
  simpa [y] using htend

/-- Exercise 184, gap 2. -/
theorem gap2 : Tendsto y (𝓝[Set.Iio 1] 1) atTop := by
  have hsub :
      Tendsto (fun x : ℝ => 1 - x) (𝓝[Set.Iio 1] 1) (𝓝[Set.Ioi 0] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hc : ContinuousAt (fun x : ℝ => 1 - x) 1 :=
        continuousAt_const.sub continuousAt_id
      simpa using hc.tendsto.mono_left
        (show 𝓝[Set.Iio 1] (1 : ℝ) ≤ 𝓝 1 from inf_le_left)
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact sub_pos.mpr (show x < 1 from hx)
  unfold y
  simpa only [one_div, Function.comp_apply] using
    tendsto_inv_nhdsGT_zero.comp hsub

/-- Exercise 184, gap 3; replace the free family `E_x`. -/
theorem gap3 : valueSet = Set.Ioi 1 := by
  ext t
  constructor
  · rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩
    unfold y
    have hden : 0 < 1 - x := sub_pos.mpr hx1
    apply (lt_div_iff₀ hden).2
    linarith
  · intro ht
    let x : ℝ := 1 - 1 / t
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    have honepos : 0 < 1 / t := by positivity
    have honelt : 1 / t < 1 := by
      apply (div_lt_iff₀ ht0).2
      simpa only [one_mul] using ht
    have hx0 : 0 < x := by
      dsimp [x]
      linarith
    have hx1 : x < 1 := by
      dsimp [x]
      linarith
    refine ⟨x, ⟨hx0, hx1⟩, ?_⟩
    unfold y
    dsimp [x]
    field_simp [ne_of_gt ht0]
    ring

end

end ProofGap.Exercise184
