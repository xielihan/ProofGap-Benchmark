import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise2733_1

noncomputable section

def term (x y : ℝ) (n : ℕ) : ℝ :=
  x ^ n / (n + y ^ n)

theorem gap1 (x y : ℝ) (hx : |x| < 1) (hy : 0 ≤ y) :
    ∀ n : ℕ, 1 ≤ n → |term x y n| ≤ |x| ^ n := by
  intro n hn
  unfold term
  rw [abs_div, abs_pow]
  have hyn : 0 ≤ y ^ n := pow_nonneg hy n
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hden : (1 : ℝ) ≤ (n : ℝ) + y ^ n :=
    le_trans hnreal (le_add_of_nonneg_right hyn)
  have hdenpos : 0 < (n : ℝ) + y ^ n :=
    lt_of_lt_of_le zero_lt_one hden
  rw [abs_of_pos hdenpos]
  apply (div_le_iff₀ hdenpos).2
  simpa only [mul_one] using
    (mul_le_mul_of_nonneg_left hden (pow_nonneg (abs_nonneg x) n))

theorem gap2 (x : ℝ) (hx : |x| < 1) :
    Summable (fun n : ℕ => |x| ^ (n + 1)) := by
  have habs : ‖|x|‖ < (1 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_abs] using hx
  have hgeom : Summable (fun n : ℕ => |x| ^ n) :=
    summable_geometric_of_norm_lt_one habs
  simpa only [pow_succ] using hgeom.mul_right |x|

theorem gap3 (x y : ℝ) (hx : |x| < 1) (hy : 0 ≤ y) :
    Summable (fun n : ℕ => |term x y (n + 1)|) := by
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) ?_ (gap2 x hx)
  intro n
  apply gap1 x y hx hy
  exact Nat.succ_le_succ (Nat.zero_le n)

theorem gap4 :
    {q : ℝ × ℝ | |q.1| < 1 ∧ 0 ≤ q.2} ⊆
      {q : ℝ × ℝ | Summable (fun n : ℕ => |term q.1 q.2 (n + 1)|)} := by
  intro q hq
  exact gap3 q.1 q.2 hq.1 hq.2

end

end ProofGap.Exercise2733_1
