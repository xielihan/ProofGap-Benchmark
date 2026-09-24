import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise534

noncomputable section

def f (x : ℝ) : ℝ := Real.logb 10 ((100 + x ^ 2) / (1 + 100 * x ^ 2))
def HasLimitAtInfinity (g : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ R > 0, ∀ x : ℝ, R < |x| → |g x - L| < ε

/-- Exercise 534, gap 1; retain the unsigned two-sided infinity through `|x|→∞`. -/
theorem gap1 : HasLimitAtInfinity f (Real.logb 10 (1 / 100)) := by
  intro ε hε
  have hcont :
      ContinuousAt (fun y : ℝ => Real.logb 10 y) (1 / 100) := by
    simpa only [Real.logb] using
      ((Real.continuousAt_log
        (show (1 / 100 : ℝ) ≠ 0 by norm_num)).div_const (Real.log 10))
  obtain ⟨δ, hδ, hδlog⟩ :=
    (Metric.continuousAt_iff.mp hcont) ε hε
  refine ⟨max 1 (1 / δ),
    lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro x hx
  have hxone : 1 < |x| :=
    lt_of_le_of_lt (le_max_left (1 : ℝ) (1 / δ)) hx
  have hxdelta : 1 / δ < |x| :=
    lt_of_le_of_lt (le_max_right (1 : ℝ) (1 / δ)) hx
  have hδne : δ ≠ 0 := ne_of_gt hδ
  have hone : 1 < δ * |x| := by
    calc
      (1 : ℝ) = δ * (1 / δ) := by field_simp
      _ < δ * |x| := mul_lt_mul_of_pos_left hxdelta hδ
  have habs_sq : |x| < x ^ 2 := by
    calc
      |x| < |x| ^ 2 := by nlinarith [abs_nonneg x]
      _ = x ^ 2 := sq_abs x
  have hsquared : 1 < δ * x ^ 2 :=
    lt_trans hone (mul_lt_mul_of_pos_left habs_sq hδ)
  have hx2 : 0 < x ^ 2 := by
    nlinarith [abs_nonneg x]
  have hden : 0 < 1 + 100 * x ^ 2 := by
    nlinarith
  have hdenne : 1 + 100 * x ^ 2 ≠ 0 := ne_of_gt hden
  have hbigden : 0 < 100 * (1 + 100 * x ^ 2) :=
    mul_pos (by norm_num) hden
  have hident :
      (100 + x ^ 2) / (1 + 100 * x ^ 2) - (1 / 100 : ℝ) =
        9999 / (100 * (1 + 100 * x ^ 2)) := by
    field_simp [hdenne]
    <;> ring
  have hfrac :
      9999 / (100 * (1 + 100 * x ^ 2)) < 1 / x ^ 2 := by
    apply (div_lt_div_iff₀ hbigden hx2).2
    nlinarith
  have hinv : 1 / x ^ 2 < δ := by
    apply (div_lt_iff₀ hx2).2
    nlinarith
  have harg :
      dist ((100 + x ^ 2) / (1 + 100 * x ^ 2)) (1 / 100 : ℝ) < δ := by
    rw [Real.dist_eq, hident,
      abs_of_pos (div_pos (by norm_num) hbigden)]
    exact lt_trans hfrac hinv
  have hout := hδlog harg
  simpa [f, Real.dist_eq] using hout

/-- Exercise 534, gap 2. -/
theorem gap2 : Real.logb 10 (1 / 100) = -2 := by
  have h100 : (100 : ℝ) = 10 ^ 2 := by norm_num
  have hlog10 : Real.log (10 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  rw [Real.logb, h100, one_div, Real.log_inv, Real.log_pow]
  field_simp [hlog10]
  <;> ring

/-- Exercise 534, gap 3. -/
theorem gap3 : HasLimitAtInfinity f (-2) := by
  rw [← gap2]
  exact gap1

end

end ProofGap.Exercise534
