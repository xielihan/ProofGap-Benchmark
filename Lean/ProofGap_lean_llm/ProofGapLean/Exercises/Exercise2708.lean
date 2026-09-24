import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise2708

noncomputable section

def positiveGeometric (n : ℕ) : ℝ :=
  1 / (2 : ℝ) ^ (n + 1)

def alternatingGeometric (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) / (3 : ℝ) ^ (n + 1)

private theorem hasSum_shifted_geometric (r : ℝ) (hr : ‖r‖ < 1) :
    HasSum (fun n : ℕ => r ^ (n + 1)) (r * (1 / (1 - r))) := by
  simpa [pow_succ, mul_comm, one_div] using
    (hasSum_geometric_of_norm_lt_one hr).mul_left r

private theorem tsum_add {f g : ℕ → ℝ} (hf : Summable f) (hg : Summable g) :
    (∑' n : ℕ, (f n + g n)) = (∑' n : ℕ, f n) + ∑' n : ℕ, g n := by
  exact (hf.hasSum.add hg.hasSum).tsum_eq

theorem gap1 :
    Summable positiveGeometric := by
  have hpositive :
      positiveGeometric =
        (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) := by
    funext n
    simp only [positiveGeometric, one_div, inv_pow]
  rw [hpositive]
  exact
    (hasSum_shifted_geometric (1 / 2 : ℝ) (by norm_num)).summable

theorem gap2 :
    Summable alternatingGeometric := by
  simpa [alternatingGeometric, div_pow] using
    (hasSum_shifted_geometric (-1 / 3 : ℝ) (by norm_num)).summable

theorem gap3 :
    ∑' n : ℕ, (positiveGeometric n + alternatingGeometric n) =
      (∑' n : ℕ, positiveGeometric n) +
        ∑' n : ℕ, alternatingGeometric n := by
  exact tsum_add gap1 gap2

theorem gap4 :
    (∑' n : ℕ, positiveGeometric n) +
        ∑' n : ℕ, alternatingGeometric n =
      (1 / 2 : ℝ) * (1 / (1 - 1 / 2)) +
        (-1 / 3 : ℝ) * (1 / (1 - (-1 / 3))) := by
  have hpositive :
      positiveGeometric =
        (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) := by
    funext n
    simp only [positiveGeometric, one_div, inv_pow]
  rw [hpositive]
  have hp :
      HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1))
        ((1 / 2 : ℝ) * (1 / (1 - 1 / 2))) := by
    exact hasSum_shifted_geometric (1 / 2 : ℝ) (by norm_num)
  have ha :
      HasSum alternatingGeometric
        ((-1 / 3 : ℝ) * (1 / (1 - (-1 / 3)))) := by
    simpa [alternatingGeometric, div_pow] using
      hasSum_shifted_geometric (-1 / 3 : ℝ) (by norm_num)
  rw [hp.tsum_eq, ha.tsum_eq]

theorem gap5 :
    (1 / 2 : ℝ) * (1 / (1 - 1 / 2)) +
      (-1 / 3 : ℝ) * (1 / (1 - (-1 / 3))) = 3 / 4 := by
  norm_num

theorem gap6 :
    ∑' n : ℕ, (positiveGeometric n + alternatingGeometric n) =
      3 / 4 := by
  calc
    ∑' n : ℕ, (positiveGeometric n + alternatingGeometric n) =
        (∑' n : ℕ, positiveGeometric n) +
          ∑' n : ℕ, alternatingGeometric n := gap3
    _ = (1 / 2 : ℝ) * (1 / (1 - 1 / 2)) +
          (-1 / 3 : ℝ) * (1 / (1 - (-1 / 3))) := gap4
    _ = 3 / 4 := gap5

end

end ProofGap.Exercise2708
