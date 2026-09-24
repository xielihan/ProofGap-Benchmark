import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise598_1

noncomputable section

def f (x : ℝ) : ℝ := 2 * x / (1 + x)

/-- Exercise 598_1, gap 1; replace `BigEnough` by an explicit left-tail bound. -/
theorem gap1 (x : ℝ) (hx : x < -1) : 2 < f x := by
  unfold f
  have hden : 1 + x < 0 := by linarith
  have hden_ne : 1 + x ≠ 0 := ne_of_lt hden
  have hpos : 0 < (-2 : ℝ) / (1 + x) :=
    div_pos_of_neg_of_neg (by norm_num) hden
  have hid : 2 * x / (1 + x) = 2 + (-2 : ℝ) / (1 + x) := by
    field_simp [hden_ne]
    ring
  rw [hid]
  linarith

/-- Exercise 598_1, gap 2. -/
theorem gap2 : Filter.Tendsto f Filter.atBot (nhds 2) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Filter.eventually_le_atBot (-1 - 3 / ε)] with x hx
  have hquot : 0 < 3 / ε := div_pos (by norm_num) hε
  have hden : 1 + x < 0 := by linarith
  have hden_ne : 1 + x ≠ 0 := ne_of_lt hden
  have hnegden : 0 < -(1 + x) := neg_pos.mpr hden
  have hnegden_ne : -(1 + x) ≠ 0 := ne_of_gt hnegden
  have hbound : 3 / ε ≤ -(1 + x) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hbound (le_of_lt hε)
  have heps : ε * (3 / ε) = 3 := by
    field_simp [ne_of_gt hε]
  rw [heps] at hmul
  have hratio : 2 / (-(1 + x)) < ε := by
    apply (div_lt_iff₀ hnegden).2
    linarith
  have hdiff : f x - 2 = 2 / (-(1 + x)) := by
    unfold f
    field_simp [hden_ne, hnegden_ne]
    ring
  rw [Real.dist_eq, hdiff, abs_of_pos (div_pos (by norm_num) hnegden)]
  exact hratio

/-- Exercise 598_1, gap 3. -/
theorem gap3 : Filter.Tendsto f Filter.atBot (nhds 2) := by
  exact gap2

end

end ProofGap.Exercise598_1
