import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise2852

noncomputable section

def doubleCosineTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * (2 * x) ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)

def cosineSquareTail (x : ℝ) (n : ℕ) : ℝ :=
  let m := n + 1
  (-1 : ℝ) ^ m * (2 : ℝ) ^ (2 * m - 1) * x ^ (2 * m) /
    (Nat.factorial (2 * m) : ℝ)

private theorem half_doubleCosineTerm_succ (x : ℝ) (n : ℕ) :
    (1 / 2 : ℝ) * doubleCosineTerm x (n + 1) = cosineSquareTail x n := by
  simp only [doubleCosineTerm, cosineSquareTail]
  have hsub : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  have hpow : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
  rw [hsub, hpow, mul_pow]
  rw [pow_succ (2 : ℝ) (2 * n + 1), pow_succ x (2 * n + 1)]
  ring

theorem gap1 :
    ∀ x : ℝ, Real.cos x ^ 2 = (1 + Real.cos (2 * x)) / 2 := by
  intro x
  rw [Real.cos_two_mul]
  ring

theorem gap2
    (hidentity :
      ∀ x : ℝ, Real.cos x ^ 2 = (1 + Real.cos (2 * x)) / 2) :
    ∀ x : ℝ, (1 + Real.cos (2 * x)) / 2 =
      (1 / 2 : ℝ) + (1 / 2 : ℝ) * (∑' n, doubleCosineTerm x n) := by
  intro x
  have hseries : (∑' n : ℕ, doubleCosineTerm x n) = Real.cos (2 * x) := by
    have hcos := (Real.hasSum_cos (2 * x)).tsum_eq
    rw [← hcos]
    apply tsum_congr
    intro n
    simp only [doubleCosineTerm]
  rw [hseries]
  ring

theorem gap3
    (hidentity :
      ∀ x : ℝ, Real.cos x ^ 2 = (1 + Real.cos (2 * x)) / 2)
    (hcosine :
      ∀ x : ℝ, (1 + Real.cos (2 * x)) / 2 =
        (1 / 2 : ℝ) + (1 / 2 : ℝ) * (∑' n, doubleCosineTerm x n)) :
    ∀ x : ℝ,
      (1 / 2 : ℝ) + (1 / 2 : ℝ) * (∑' n, doubleCosineTerm x n) =
        1 + ∑' n, cosineSquareTail x n := by
  intro x
  have hsum : Summable (doubleCosineTerm x) := by
    have hcos : Summable (fun n : ℕ =>
        (-1 : ℝ) ^ n * (2 * x) ^ (2 * n) /
          (Nat.factorial (2 * n) : ℝ)) :=
      (Real.hasSum_cos (2 * x)).summable
    simpa only [doubleCosineTerm] using hcos
  have hsplit :
      (∑' n, doubleCosineTerm x n) =
        doubleCosineTerm x 0 + ∑' n, doubleCosineTerm x (n + 1) := by
    simpa [Nat.add_comm] using (hsum.sum_add_tsum_nat_add 1).symm
  have hzero : doubleCosineTerm x 0 = 1 := by
    norm_num [doubleCosineTerm]
  have htailTsum :
      (∑' n, (1 / 2 : ℝ) * doubleCosineTerm x (n + 1)) =
        ∑' n, cosineSquareTail x n := by
    apply tsum_congr
    intro n
    exact half_doubleCosineTerm_succ x n
  rw [hsplit, hzero]
  calc
    (1 / 2 : ℝ) + (1 / 2 : ℝ) *
        (1 + ∑' n, doubleCosineTerm x (n + 1)) =
        1 + (1 / 2 : ℝ) * ∑' n, doubleCosineTerm x (n + 1) := by ring
    _ = 1 + ∑' n, cosineSquareTail x n := by
      rw [← htailTsum, tsum_mul_left]

theorem gap4
    (hidentity :
      ∀ x : ℝ, Real.cos x ^ 2 = (1 + Real.cos (2 * x)) / 2)
    (hcosine :
      ∀ x : ℝ, (1 + Real.cos (2 * x)) / 2 =
        (1 / 2 : ℝ) + (1 / 2 : ℝ) * (∑' n, doubleCosineTerm x n))
    (hreindex :
      ∀ x : ℝ,
        (1 / 2 : ℝ) + (1 / 2 : ℝ) * (∑' n, doubleCosineTerm x n) =
          1 + ∑' n, cosineSquareTail x n) :
    ∀ x : ℝ, Real.cos x ^ 2 = 1 + ∑' n, cosineSquareTail x n := by
  intro x
  calc
    Real.cos x ^ 2 = (1 + Real.cos (2 * x)) / 2 := hidentity x
    _ = (1 / 2 : ℝ) + (1 / 2 : ℝ) * (∑' n, doubleCosineTerm x n) := hcosine x
    _ = 1 + ∑' n, cosineSquareTail x n := hreindex x

theorem gap5
    (hidentity :
      ∀ x : ℝ, Real.cos x ^ 2 = (1 + Real.cos (2 * x)) / 2)
    (hcosine :
      ∀ x : ℝ, (1 + Real.cos (2 * x)) / 2 =
        (1 / 2 : ℝ) + (1 / 2 : ℝ) * (∑' n, doubleCosineTerm x n))
    (hreindex :
      ∀ x : ℝ,
        (1 / 2 : ℝ) + (1 / 2 : ℝ) * (∑' n, doubleCosineTerm x n) =
          1 + ∑' n, cosineSquareTail x n)
    (hfinal :
      ∀ x : ℝ, Real.cos x ^ 2 = 1 + ∑' n, cosineSquareTail x n) :
    ∀ x : ℝ, Summable (cosineSquareTail x) := by
  intro x
  have hsum : Summable (doubleCosineTerm x) := by
    have hcos : Summable (fun n : ℕ =>
        (-1 : ℝ) ^ n * (2 * x) ^ (2 * n) /
          (Nat.factorial (2 * n) : ℝ)) :=
      (Real.hasSum_cos (2 * x)).summable
    simpa only [doubleCosineTerm] using hcos
  have hsucc : Function.Injective (fun n : ℕ => n + 1) := by
    intro a b hab
    exact Nat.add_right_cancel hab
  have hshift : Summable (fun n : ℕ => doubleCosineTerm x (n + 1)) := by
    exact hsum.comp_injective hsucc
  have hscaled :
      Summable (fun n : ℕ => (1 / 2 : ℝ) * doubleCosineTerm x (n + 1)) :=
    hshift.mul_left (1 / 2 : ℝ)
  simpa only [half_doubleCosineTerm_succ] using hscaled

end

end ProofGap.Exercise2852
