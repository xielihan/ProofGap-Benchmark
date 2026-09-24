import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2853

noncomputable section

def sineTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * x ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ)

def tripleSineTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * (3 : ℝ) ^ (2 * n + 1) * x ^ (2 * n + 1) /
    (Nat.factorial (2 * n + 1) : ℝ)

def sineCubeTerm (x : ℝ) (n : ℕ) : ℝ :=
  (3 / 4 : ℝ) * (-1 : ℝ) ^ (n + 1) *
    ((3 : ℝ) ^ (2 * n) - 1) * x ^ (2 * n + 1) /
      (Nat.factorial (2 * n + 1) : ℝ)

theorem gap1 :
    ∀ x : ℝ, Real.sin x ^ 3 =
      (3 / 4 : ℝ) * Real.sin x - (1 / 4 : ℝ) * Real.sin (3 * x) := by
  intro x
  linarith [Real.sin_three_mul x]

theorem gap2
    (hidentity :
      ∀ x : ℝ, Real.sin x ^ 3 =
        (3 / 4 : ℝ) * Real.sin x - (1 / 4 : ℝ) * Real.sin (3 * x)) :
    ∀ x : ℝ, Real.sin x ^ 3 =
      (3 / 4 : ℝ) * (∑' n, sineTerm x n) -
        (1 / 4 : ℝ) * (∑' n, tripleSineTerm x n) := by
  intro x
  have hs : HasSum (sineTerm x) (Real.sin x) := by
    simpa [sineTerm] using Real.hasSum_sin x
  have ht : HasSum (tripleSineTerm x) (Real.sin (3 * x)) := by
    apply (Real.hasSum_sin (3 * x)).congr
    intro n
    simp only [tripleSineTerm, mul_pow]
    ring
  rw [hs.tsum_eq, ht.tsum_eq]
  exact hidentity x

theorem gap3
    (hidentity :
      ∀ x : ℝ, Real.sin x ^ 3 =
        (3 / 4 : ℝ) * Real.sin x - (1 / 4 : ℝ) * Real.sin (3 * x))
    (hexpand :
      ∀ x : ℝ, Real.sin x ^ 3 =
        (3 / 4 : ℝ) * (∑' n, sineTerm x n) -
          (1 / 4 : ℝ) * (∑' n, tripleSineTerm x n)) :
    ∀ x : ℝ, Real.sin x ^ 3 = ∑' n, sineCubeTerm x n := by
  intro x
  have hs : HasSum (sineTerm x) (Real.sin x) := by
    simpa [sineTerm] using Real.hasSum_sin x
  have ht : HasSum (tripleSineTerm x) (Real.sin (3 * x)) := by
    apply (Real.hasSum_sin (3 * x)).congr
    intro n
    simp only [tripleSineTerm, mul_pow]
    ring
  have hseq :
      (fun n : ℕ => (3 / 4 : ℝ) * sineTerm x n -
        (1 / 4 : ℝ) * tripleSineTerm x n) = sineCubeTerm x := by
    funext n
    have hneg : (-1 : ℝ) ^ (n + 1) = -((-1 : ℝ) ^ n) := by
      rw [pow_succ]
      ring
    have hthree : (3 : ℝ) ^ (2 * n + 1) =
        3 * (3 : ℝ) ^ (2 * n) := by
      rw [pow_succ]
      ring
    simp only [sineTerm, tripleSineTerm, sineCubeTerm]
    rw [hneg, hthree]
    ring
  have hcomb :
      HasSum
        (fun n : ℕ => (3 / 4 : ℝ) * sineTerm x n -
          (1 / 4 : ℝ) * tripleSineTerm x n)
        ((3 / 4 : ℝ) * Real.sin x -
          (1 / 4 : ℝ) * Real.sin (3 * x)) :=
    (hs.mul_left (3 / 4 : ℝ)).sub (ht.mul_left (1 / 4 : ℝ))
  have hcube :
      HasSum (sineCubeTerm x)
        ((3 / 4 : ℝ) * Real.sin x -
          (1 / 4 : ℝ) * Real.sin (3 * x)) := by
    rw [← hseq]
    exact hcomb
  calc
    Real.sin x ^ 3 =
        (3 / 4 : ℝ) * (∑' n, sineTerm x n) -
          (1 / 4 : ℝ) * (∑' n, tripleSineTerm x n) := hexpand x
    _ = (3 / 4 : ℝ) * Real.sin x -
          (1 / 4 : ℝ) * Real.sin (3 * x) := by
        rw [hs.tsum_eq, ht.tsum_eq]
    _ = ∑' n, sineCubeTerm x n := hcube.tsum_eq.symm

end

end ProofGap.Exercise2853
