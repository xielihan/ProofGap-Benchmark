import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Filter Topology

namespace ProofGap.Exercise185

noncomputable section

def y (x : ℝ) : ℝ := x / (2 * x - 1)
def domain : Set ℝ := Set.Ioo 0 1 \ {1 / 2}
def valueSet : Set ℝ := {t | ∃ x ∈ domain, t = y x}

/-- Exercise 185, gap 1; exclude the pole x=1/2. -/
theorem gap1 : ∀ x : ℝ, x ≠ 1 / 2 →
    y x = 1 / 2 + (1 / 2) * (1 / (2 * x - 1)) := by
  intro x hx
  unfold y
  have hden : 2 * x - 1 ≠ 0 := by
    intro h
    apply hx
    linarith
  have hcalc : x * (2 * x - 1)⁻¹ =
      1 / 2 + 1 / 2 * (2 * x - 1)⁻¹ := by
    calc
      x * (2 * x - 1)⁻¹ =
          (((2 * x - 1) + 1) / 2) * (2 * x - 1)⁻¹ := by
            congr 2
            ring
      _ = 1 / 2 + 1 / 2 * (2 * x - 1)⁻¹ := by
        field_simp [hden]
  simpa only [div_eq_mul_inv, one_mul] using hcalc

/-- Exercise 185, gap 2; the source incorrectly quantifies x around a limit statement. -/
theorem gap2 : Tendsto y (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
  have hc : ContinuousAt y 0 := by
    unfold y
    exact continuousAt_id.div
      ((continuousAt_const.mul continuousAt_id).sub continuousAt_const) (by norm_num)
  have ht : Tendsto y (𝓝[Set.Ioi 0] 0) (𝓝 (y 0)) :=
    hc.continuousWithinAt
  simpa [y] using ht

/-- Exercise 185, gap 3. -/
theorem gap3 : Tendsto y (𝓝[Set.Iio (1 / 2)] (1 / 2)) atBot := by
  let l : Filter ℝ := 𝓝[Set.Iio (1 / 2)] (1 / 2)
  have hden : Tendsto (fun x : ℝ => 2 * x - 1) l (𝓝[Set.Iio 0] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hc : ContinuousAt (fun x : ℝ => 2 * x - 1) (1 / 2) := by fun_prop
      simpa [l] using hc.tendsto.mono_left
        (show l ≤ 𝓝 (1 / 2) from inf_le_left)
    · dsimp [l]
      filter_upwards [self_mem_nhdsWithin] with x hx
      change x < 1 / 2 at hx
      change 2 * x - 1 < 0
      linarith
  have hinv : Tendsto (fun x : ℝ => (2 * x - 1)⁻¹) l atBot :=
    tendsto_inv_nhdsLT_zero.comp hden
  have hscaled : Tendsto (fun x : ℝ => (1 / 2) * (2 * x - 1)⁻¹) l atBot :=
    tendsto_const_nhds.pos_mul_atBot (by norm_num) hinv
  have hsum : Tendsto (fun x : ℝ => 1 / 2 + (1 / 2) * (2 * x - 1)⁻¹) l atBot :=
    tendsto_atBot_add_const_left l (1 / 2) hscaled
  apply hsum.congr'
  dsimp [l]
  filter_upwards [self_mem_nhdsWithin] with x hx
  change x < 1 / 2 at hx
  simpa only [one_div] using (gap1 x (ne_of_lt hx)).symm

/-- Exercise 185, gap 4. -/
theorem gap4 : Tendsto y (𝓝[Set.Ioi (1 / 2)] (1 / 2)) atTop := by
  let l : Filter ℝ := 𝓝[Set.Ioi (1 / 2)] (1 / 2)
  have hden : Tendsto (fun x : ℝ => 2 * x - 1) l (𝓝[Set.Ioi 0] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hc : ContinuousAt (fun x : ℝ => 2 * x - 1) (1 / 2) := by fun_prop
      simpa [l] using hc.tendsto.mono_left
        (show l ≤ 𝓝 (1 / 2) from inf_le_left)
    · dsimp [l]
      filter_upwards [self_mem_nhdsWithin] with x hx
      change 1 / 2 < x at hx
      change 0 < 2 * x - 1
      linarith
  have hinv : Tendsto (fun x : ℝ => (2 * x - 1)⁻¹) l atTop :=
    tendsto_inv_nhdsGT_zero.comp hden
  have hscaled : Tendsto (fun x : ℝ => (1 / 2) * (2 * x - 1)⁻¹) l atTop :=
    tendsto_const_nhds.pos_mul_atTop (by norm_num) hinv
  have hsum : Tendsto (fun x : ℝ => 1 / 2 + (1 / 2) * (2 * x - 1)⁻¹) l atTop :=
    tendsto_atTop_add_const_left l (1 / 2) hscaled
  apply hsum.congr'
  dsimp [l]
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 1 / 2 < x at hx
  simpa only [one_div] using (gap1 x (ne_of_gt hx)).symm

/-- Exercise 185, gap 5. -/
theorem gap5 : Tendsto y (𝓝[Set.Iio 1] 1) (𝓝 1) := by
  have hc : ContinuousAt y 1 := by
    unfold y
    exact continuousAt_id.div
      ((continuousAt_const.mul continuousAt_id).sub continuousAt_const) (by norm_num)
  have ht : Tendsto y (𝓝[Set.Iio 1] 1) (𝓝 (y 1)) :=
    hc.continuousWithinAt
  convert ht using 1 <;> norm_num [y]

/-- Exercise 185, gap 6; replace the free family `E_x`. -/
theorem gap6 : valueSet = Set.Iio 0 ∪ Set.Ioi 1 := by
  ext t
  constructor
  · rintro ⟨x, ⟨⟨hx0, hx1⟩, hxne⟩, rfl⟩
    by_cases hx : x < 1 / 2
    · left
      unfold y
      exact div_neg_of_pos_of_neg hx0 (by linarith)
    · right
      have hxhalf : 1 / 2 < x :=
        lt_of_le_of_ne (not_lt.mp hx) (Ne.symm hxne)
      have hden : 0 < 2 * x - 1 := by linarith
      unfold y
      apply (one_lt_div₀ hden).2
      linarith
  · intro ht
    rcases ht with ht | ht
    · change t < 0 at ht
      let x := t / (2 * t - 1)
      have hden : 2 * t - 1 < 0 := by linarith
      have hx0 : 0 < x := div_pos_of_neg_of_neg ht hden
      have hxhalf : x < 1 / 2 := by
        dsimp [x]
        apply (div_lt_iff_of_neg hden).2
        linarith
      have hy : y x = t := by
        have hyden : 2 * (t / (2 * t - 1)) - 1 = 1 / (2 * t - 1) := by
          field_simp [ne_of_lt hden]
          ring
        unfold y
        dsimp [x]
        rw [hyden]
        have hden' : t * 2 - 1 ≠ 0 := by
          simpa [mul_comm] using ne_of_lt hden
        field_simp [ne_of_lt hden, hden']
      exact ⟨x, ⟨⟨hx0, lt_trans hxhalf (by norm_num)⟩, ne_of_lt hxhalf⟩, hy.symm⟩
    · change 1 < t at ht
      let x := t / (2 * t - 1)
      have hden : 0 < 2 * t - 1 := by linarith
      have hxhalf : 1 / 2 < x := by
        dsimp [x]
        apply (lt_div_iff₀ hden).2
        linarith
      have hx1 : x < 1 := by
        dsimp [x]
        apply (div_lt_iff₀ hden).2
        linarith
      have hy : y x = t := by
        have hyden : 2 * (t / (2 * t - 1)) - 1 = 1 / (2 * t - 1) := by
          field_simp [ne_of_gt hden]
          ring
        unfold y
        dsimp [x]
        rw [hyden]
        have hden' : t * 2 - 1 ≠ 0 := by
          simpa [mul_comm] using ne_of_gt hden
        field_simp [ne_of_gt hden, hden']
      exact ⟨x, ⟨⟨lt_trans (by norm_num) hxhalf, hx1⟩, ne_of_gt hxhalf⟩, hy.symm⟩

end

end ProofGap.Exercise185
