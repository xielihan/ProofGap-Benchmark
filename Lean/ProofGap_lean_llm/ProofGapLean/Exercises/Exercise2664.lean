import ProofGapLean.Prelude.Discrete
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecificLimits.Normed

namespace ProofGap.Exercise2664

noncomputable section

def term (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n * (n - 1) / 2) / (2 : ℝ) ^ n

theorem gap1 :
    ∀ n : ℕ, |term n| = 1 / (2 : ℝ) ^ n := by
  intro n
  rw [term, abs_div, abs_pow, abs_pow]
  norm_num

theorem gap2 :
    Summable (fun n : ℕ => 1 / (2 : ℝ) ^ (n + 1)) := by
  have h : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num [Real.norm_eq_abs])
  refine (h.mul_right (1 / 2 : ℝ)).congr ?_
  intro n
  rw [one_div_pow, pow_succ]
  field_simp

theorem gap3 :
    Summable (fun n : ℕ => |term (n + 1)|) := by
  simpa only [gap1] using gap2

theorem gap4 :
    Summable (fun n : ℕ => term (n + 1)) := by
  have hnorm : Summable (fun n : ℕ => ‖term (n + 1)‖) := by
    simpa only [Real.norm_eq_abs] using gap3
  exact hnorm.of_norm

end

end ProofGap.Exercise2664
