import ProofGapLean.Prelude.Core
import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise415

noncomputable section

def f (x : ℝ) : ℝ :=
  ((x - 1) * (x - 2) * (x - 3) * (x - 4) * (x - 5)) /
    (5 * x - 1) ^ 5

def HasLimitAtInfinity (g : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N > 0, ∀ x, N < |x| → |g x - L| < ε

/-- Exercise 415, gap 1. -/
theorem gap1 : ∃ degreeNumerator : ℕ, degreeNumerator = 5 := by
  exact ⟨5, rfl⟩

/-- Exercise 415, gap 2. -/
theorem gap2 : ∃ degreeDenominator : ℕ, degreeDenominator = 5 := by
  exact ⟨5, rfl⟩

/-- Exercise 415, gap 3. -/
theorem gap3 : HasLimitAtInfinity f (1 / (5 : ℝ) ^ 5) := by
  let h : ℝ → ℝ := fun y =>
    ((1 - y) * (1 - 2 * y) * (1 - 3 * y) *
      (1 - 4 * y) * (1 - 5 * y)) / (5 - y) ^ 5
  have hc1 : ContinuousAt (fun y : ℝ => 1 - y) 0 :=
    continuousAt_const.sub continuousAt_id
  have hc2 : ContinuousAt (fun y : ℝ => 1 - 2 * y) 0 :=
    continuousAt_const.sub (continuousAt_const.mul continuousAt_id)
  have hc3 : ContinuousAt (fun y : ℝ => 1 - 3 * y) 0 :=
    continuousAt_const.sub (continuousAt_const.mul continuousAt_id)
  have hc4 : ContinuousAt (fun y : ℝ => 1 - 4 * y) 0 :=
    continuousAt_const.sub (continuousAt_const.mul continuousAt_id)
  have hc5 : ContinuousAt (fun y : ℝ => 1 - 5 * y) 0 :=
    continuousAt_const.sub (continuousAt_const.mul continuousAt_id)
  have hcd : ContinuousAt (fun y : ℝ => 5 - y) 0 :=
    continuousAt_const.sub continuousAt_id
  have hcont : ContinuousAt h 0 := by
    dsimp [h]
    exact ((((hc1.mul hc2).mul hc3).mul hc4).mul hc5).div
      (hcd.pow 5) (by norm_num)
  have h0 : h 0 = 1 / (5 : ℝ) ^ 5 := by
    norm_num [h]
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ :=
    (Metric.continuousAt_iff.mp hcont) ε hε
  refine ⟨1 / δ, one_div_pos.mpr hδ, ?_⟩
  intro x hx
  have hxabs : 0 < |x| := lt_trans (one_div_pos.mpr hδ) hx
  have hx0 : x ≠ 0 := abs_pos.mp hxabs
  have hscale : 1 < |x| * δ := (div_lt_iff₀ hδ).mp hx
  have hrecip : 1 / |x| < δ := by
    apply (div_lt_iff₀ hxabs).mpr
    simpa [mul_comm] using hscale
  have hy : dist (1 / x) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_div, abs_one]
    exact hrecip
  have hfx : h (1 / x) = f x := by
    dsimp [h]
    unfold f
    by_cases hc : 5 * x - 1 = 0
    · have hxval : x = (1 : ℝ) / 5 := by
        linarith
      rw [hxval]
      norm_num
    · field_simp [hx0, hc] <;> ring_nf
  have hnear : dist (h (1 / x)) (h 0) < ε := hclose hy
  rw [hfx, h0] at hnear
  simpa [Real.dist_eq] using hnear

end

end ProofGap.Exercise415
