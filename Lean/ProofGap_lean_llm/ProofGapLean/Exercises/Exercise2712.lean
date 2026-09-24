import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise2712

noncomputable section

open scoped BigOperators

def convolution (q : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), q ^ i * q ^ (n - i)

theorem gap1 (q : ℝ) (hq : |q| < 1) :
    Summable (fun n : ℕ => |q ^ n|) := by
  have hs : Summable (fun n : ℕ => (|q| : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by
      simpa [Real.norm_eq_abs] using hq)
  simpa [abs_pow] using hs

theorem gap2 (q : ℝ) (hq : |q| < 1) :
    (∑' n : ℕ, q ^ n) ^ 2 = ∑' n : ℕ, convolution q n := by
  have hs : Summable (fun n : ℕ => ‖q ^ n‖) := by
    simpa [Real.norm_eq_abs] using gap1 q hq
  calc
    (∑' n : ℕ, q ^ n) ^ 2 = (∑' n : ℕ, q ^ n) * ∑' n : ℕ, q ^ n := by
      rw [pow_two]
    _ = ∑' n : ℕ, ∑ kl ∈ Finset.antidiagonal n, q ^ kl.1 * q ^ kl.2 :=
      tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hs hs
    _ = ∑' n : ℕ, convolution q n := by
      apply tsum_congr
      intro n
      unfold convolution
      symm
      refine Finset.sum_bij (fun i _ => (i, n - i)) ?_ ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_antidiagonal]
        have hi' := Finset.mem_range.mp hi
        omega
      · intro i₁ hi₁ i₂ hi₂ h
        exact congrArg Prod.fst h
      · intro kl hkl
        have hsum := Finset.mem_antidiagonal.mp hkl
        refine ⟨kl.1, ?_, ?_⟩
        · apply Finset.mem_range.mpr
          omega
        · apply Prod.ext
          · rfl
          · dsimp
            omega
      · intro i hi
        rfl

theorem gap3 (q : ℝ) :
    ∀ n : ℕ,
      convolution q n = ∑ i ∈ Finset.range (n + 1), q ^ i * q ^ (n - i) := by
  intro n
  rfl

theorem gap4 (q : ℝ) :
    ∀ n : ℕ,
      ∑ i ∈ Finset.range (n + 1), q ^ i * q ^ (n - i) =
        q ^ n * ∑ _i ∈ Finset.range (n + 1), (1 : ℝ) := by
  intro n
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  calc
    q ^ i * q ^ (n - i) = q ^ (i + (n - i)) := (pow_add q i (n - i)).symm
    _ = q ^ n := by rw [Nat.add_sub_of_le hin]
    _ = q ^ n * 1 := by simp

theorem gap5 (q : ℝ) :
    ∀ n : ℕ,
      q ^ n * ∑ _i ∈ Finset.range (n + 1), (1 : ℝ) =
        (n + 1 : ℕ) * q ^ n := by
  intro n
  simp [mul_comm]

theorem gap6 (q : ℝ) :
    ∀ n : ℕ, convolution q n = (n + 1 : ℕ) * q ^ n := by
  intro n
  rw [gap3 q n, gap4 q n, gap5 q n]

theorem gap7 (q : ℝ) (hq : |q| < 1) :
    (∑' n : ℕ, q ^ n) ^ 2 =
      ∑' n : ℕ, (n + 1 : ℕ) * q ^ n := by
  calc
    (∑' n : ℕ, q ^ n) ^ 2 = ∑' n : ℕ, convolution q n := gap2 q hq
    _ = ∑' n : ℕ, (n + 1 : ℕ) * q ^ n :=
      tsum_congr (fun n => gap6 q n)

theorem gap8 (q : ℝ) (hq : |q| < 1) :
    (∑' n : ℕ, q ^ n) ^ 2 =
      ∑' n : ℕ, (n + 1 : ℕ) * q ^ n := by
  exact gap7 q hq

end

end ProofGap.Exercise2712
