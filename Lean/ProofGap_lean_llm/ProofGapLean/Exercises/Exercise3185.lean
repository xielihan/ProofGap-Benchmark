import ProofGapLean.Prelude.Analysis
import Mathlib.Order.Filter.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3185

noncomputable section

open Filter
open scoped Topology

def atTop₂ : Filter (ℝ × ℝ) :=
  (atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)

def target (p : ℝ × ℝ) : ℝ :=
  (p.1 + p.2) / (p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2)

def upperBound (p : ℝ × ℝ) : ℝ :=
  1 / |p.1| + 1 / |p.2|

/-- Exercise 3185, gap 1; exclude the zero denominator. -/
private theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  exact abs_add_le x y

theorem gap1 :
    ∀ x y : ℝ, (x, y) ≠ (0, 0) →
      0 ≤ |(x + y) / (x ^ 2 - x * y + y ^ 2)| := by
  intro x y hxy
  exact abs_nonneg _

/-- Exercise 3185, gap 2; both denominators are positive off the origin. -/
theorem gap2 :
    ∀ x y : ℝ, (x, y) ≠ (0, 0) →
      |(x + y) / (x ^ 2 - x * y + y ^ 2)| ≤
        |x + y| / (x ^ 2 + y ^ 2 - |x * y|) := by
  intro x y hxy
  have hsum : 0 < x ^ 2 + y ^ 2 := by
    by_contra h
    have hx0 : x = 0 := by
      nlinarith [sq_nonneg x, sq_nonneg y]
    have hy0 : y = 0 := by
      nlinarith [sq_nonneg x, sq_nonneg y]
    exact hxy (by simp [hx0, hy0])
  have hcomp : 0 < x ^ 2 + y ^ 2 - |x * y| := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y]
  have hcomp_le :
      x ^ 2 + y ^ 2 - |x * y| ≤ x ^ 2 - x * y + y ^ 2 := by
    nlinarith [le_abs_self (x * y)]
  have hden : 0 < x ^ 2 - x * y + y ^ 2 :=
    lt_of_lt_of_le hcomp hcomp_le
  rw [abs_div, abs_of_pos hden]
  apply (div_le_div_iff₀ hden hcomp).2
  exact mul_le_mul_of_nonneg_left hcomp_le (abs_nonneg (x + y))

/-- Exercise 3185, gap 3; the comparison denominator `|xy|` is nonzero. -/
theorem gap3 :
    ∀ x y : ℝ, x ≠ 0 → y ≠ 0 →
      |x + y| / (x ^ 2 + y ^ 2 - |x * y|) ≤
        |x + y| / |x * y| := by
  intro x y hx hy
  have hprod : 0 < |x * y| :=
    abs_pos.mpr (mul_ne_zero hx hy)
  have hprod_le :
      |x * y| ≤ x ^ 2 + y ^ 2 - |x * y| := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y]
  have hden : 0 < x ^ 2 + y ^ 2 - |x * y| :=
    lt_of_lt_of_le hprod hprod_le
  apply (div_le_div_iff₀ hden hprod).2
  exact mul_le_mul_of_nonneg_left hprod_le (abs_nonneg (x + y))

/-- Exercise 3185, gap 4; split the nonzero product. -/
theorem gap4 :
    ∀ x y : ℝ, x ≠ 0 → y ≠ 0 →
      |x + y| / |x * y| ≤ 1 / |x| + 1 / |y| := by
  intro x y hx hy
  rw [abs_mul]
  have hden : 0 ≤ |x| * |y| :=
    mul_nonneg (abs_nonneg x) (abs_nonneg y)
  calc
    |x + y| / (|x| * |y|) ≤
        (|x| + |y|) / (|x| * |y|) :=
      div_le_div_of_nonneg_right (abs_add x y) hden
    _ = 1 / |x| + 1 / |y| := by
      field_simp [abs_ne_zero.mpr hx, abs_ne_zero.mpr hy]
      <;> ring

/-- Exercise 3185, gap 5; reciprocal bounds use nonzero coordinates. -/
theorem gap5 :
    ∀ x y : ℝ, x ≠ 0 → y ≠ 0 →
      0 ≤ 1 / |x| + 1 / |y| := by
  intro x y hx hy
  exact add_nonneg
    (div_nonneg zero_le_one (abs_nonneg x))
    (div_nonneg zero_le_one (abs_nonneg y))

/-- Exercise 3185, gap 6; product-filter limit. -/
theorem gap6 :
    Tendsto upperBound atTop₂ (𝓝 0) := by
  have hinv : Tendsto (fun x : ℝ => 1 / |x|) atTop (𝓝 0) := by
    have hinv0 : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
      simpa [one_div] using
        (tendsto_inv_atTop_zero :
          Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))
    refine hinv0.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    simp [abs_of_nonneg hx]
  have hfst :
      Tendsto (fun p : ℝ × ℝ => p.1) atTop₂ atTop := by
    unfold atTop₂
    apply tendsto_fst
  have hsnd :
      Tendsto (fun p : ℝ × ℝ => p.2) atTop₂ atTop := by
    unfold atTop₂
    apply tendsto_snd
  have hfirst :
      Tendsto (fun p : ℝ × ℝ => 1 / |p.1|) atTop₂ (𝓝 0) := by
    simpa only [Function.comp_apply] using hinv.comp hfst
  have hsecond :
      Tendsto (fun p : ℝ × ℝ => 1 / |p.2|) atTop₂ (𝓝 0) := by
    simpa only [Function.comp_apply] using hinv.comp hsnd
  change Tendsto
    (fun p : ℝ × ℝ => 1 / |p.1| + 1 / |p.2|) atTop₂ (𝓝 0)
  simpa only [zero_add] using hfirst.add hsecond

/-- Exercise 3185, gap 7; squeeze at `(∞,∞)`. -/
theorem gap7 :
    Tendsto target atTop₂ (𝓝 0) := by
  have hfst :
      Tendsto (fun p : ℝ × ℝ => p.1) atTop₂ atTop := by
    unfold atTop₂
    apply tendsto_fst
  have hsnd :
      Tendsto (fun p : ℝ × ℝ => p.2) atTop₂ atTop := by
    unfold atTop₂
    apply tendsto_snd
  have hbounds :
      ∀ᶠ p in atTop₂,
        -upperBound p ≤ target p ∧ target p ≤ upperBound p := by
    filter_upwards
      [hfst.eventually (eventually_gt_atTop (0 : ℝ)),
       hsnd.eventually (eventually_gt_atTop (0 : ℝ))] with p hx hy
    have hx0 : p.1 ≠ 0 := ne_of_gt hx
    have hy0 : p.2 ≠ 0 := ne_of_gt hy
    have horigin : (p.1, p.2) ≠ (0, 0) := by
      intro hp
      apply hx0
      exact congrArg Prod.fst hp
    have h2 := gap2 p.1 p.2 horigin
    have h3 := gap3 p.1 p.2 hx0 hy0
    have h4 := gap4 p.1 p.2 hx0 hy0
    have habs : |target p| ≤ upperBound p := by
      dsimp [target, upperBound]
      exact h2.trans (h3.trans h4)
    constructor
    · calc
        -upperBound p ≤ -|target p| := neg_le_neg habs
        _ ≤ target p := neg_abs_le (target p)
    · exact (le_abs_self (target p)).trans habs
  have hneg :
      Tendsto (fun p : ℝ × ℝ => -upperBound p) atTop₂ (𝓝 0) := by
    simpa using gap6.neg
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hneg gap6
    (hbounds.mono fun p hp => hp.1)
    (hbounds.mono fun p hp => hp.2)

end

end ProofGap.Exercise3185
