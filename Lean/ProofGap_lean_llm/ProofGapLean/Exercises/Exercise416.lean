import ProofGapLean.Prelude.Core
import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise416

noncomputable section

def f (x : ℝ) : ℝ :=
  ((2 * x - 3) ^ 20 * (3 * x + 2) ^ 30) / (2 * x + 1) ^ 50

def HasLimitAtInfinity (g : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N > 0, ∀ x, N < |x| → |g x - L| < ε

/-- Exercise 416, gap 1. -/
theorem gap1 : ∃ degreeNumerator degreeDenominator : ℕ,
    degreeNumerator = degreeDenominator := by
  exact ⟨0, 0, rfl⟩

/-- Exercise 416, gap 2. -/
theorem gap2 :
    HasLimitAtInfinity f (((2 : ℝ) ^ 20 * 3 ^ 30) / 2 ^ 50) := by
  let h : ℝ → ℝ := fun y =>
    ((2 - 3 * y) ^ 20 * (3 + 2 * y) ^ 30) / (2 + y) ^ 50
  have hc1 : ContinuousAt (fun y : ℝ => 2 - 3 * y) 0 :=
    continuousAt_const.sub (continuousAt_const.mul continuousAt_id)
  have hc2 : ContinuousAt (fun y : ℝ => 3 + 2 * y) 0 :=
    continuousAt_const.add (continuousAt_const.mul continuousAt_id)
  have hc3 : ContinuousAt (fun y : ℝ => 2 + y) 0 :=
    continuousAt_const.add continuousAt_id
  have hcont : ContinuousAt h 0 := by
    dsimp [h]
    exact ((hc1.pow 20).mul (hc2.pow 30)).div (hc3.pow 50) (by norm_num)
  have h0 : h 0 = (((2 : ℝ) ^ 20 * 3 ^ 30) / 2 ^ 50) := by
    simp [h]
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := (Metric.continuousAt_iff.mp hcont) ε hε
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
    by_cases hc : 2 * x + 1 = 0
    · have hxval : x = -(1 : ℝ) / 2 := by
        linarith
      rw [hxval]
      norm_num
    · field_simp [hx0, hc] <;> ring_nf
  have hnear : dist (h (1 / x)) (h 0) < ε := hclose hy
  rw [hfx, h0] at hnear
  simpa [Real.dist_eq] using hnear

/-- Exercise 416, gap 3. -/
theorem gap3 :
    ((2 : ℝ) ^ 20 * 3 ^ 30) / 2 ^ 50 = ((3 : ℝ) / 2) ^ 30 := by
  norm_num [div_pow]

/-- Exercise 416, gap 4. -/
theorem gap4 : HasLimitAtInfinity f (((3 : ℝ) / 2) ^ 30) := by
  simpa only [gap3] using gap2

end

end ProofGap.Exercise416
