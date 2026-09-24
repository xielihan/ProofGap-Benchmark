import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2843

noncomputable section

def cosineAtDoubleTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * (2 : ℝ) ^ (2 * n) * x ^ (2 * n) /
    (Nat.factorial (2 * n) : ℝ)

def sineSquareTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * (2 : ℝ) ^ (2 * n + 1) * x ^ (2 * n + 2) /
    (Nat.factorial (2 * n + 2) : ℝ)

private theorem hasSum_cosineAtDoubleTerm (x : ℝ) :
    HasSum (cosineAtDoubleTerm x) (Real.cos (2 * x)) := by
  refine (Real.hasSum_cos (2 * x)).congr ?_
  intro n
  simp only [cosineAtDoubleTerm, mul_pow]
  ring

private theorem hasSum_sineSquareTerm (x : ℝ) :
    HasSum (sineSquareTerm x) ((1 - Real.cos (2 * x)) / 2) := by
  have htail :
      HasSum (fun n => cosineAtDoubleTerm x (n + 1))
        (Real.cos (2 * x) - 1) := by
    simpa [cosineAtDoubleTerm] using
      ((hasSum_nat_add_iff' 1).2 (hasSum_cosineAtDoubleTerm x))
  have hm :
      HasSum (fun n => -(1 / 2 : ℝ) * cosineAtDoubleTerm x (n + 1))
        (-(1 / 2 : ℝ) * (Real.cos (2 * x) - 1)) :=
    htail.mul_left (-(1 / 2 : ℝ))
  have hfun :
      sineSquareTerm x =
        fun n => -(1 / 2 : ℝ) * cosineAtDoubleTerm x (n + 1) := by
    funext n
    simp [sineSquareTerm, cosineAtDoubleTerm, pow_succ] <;> ring
  rw [hfun]
  convert hm using 1 <;> ring

theorem gap1 (f : ℝ → ℝ) (hf : ∀ x, f x = Real.sin x ^ 2) :
    ∀ x, f x = (1 - Real.cos (2 * x)) / 2 := by
  intro x
  rw [hf x, Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq x]

theorem gap2
    (f : ℝ → ℝ)
    (hf : ∀ x, f x = Real.sin x ^ 2)
    (htrig : ∀ x, f x = (1 - Real.cos (2 * x)) / 2) :
    ∀ x, (1 - Real.cos (2 * x)) / 2 =
      (1 / 2 : ℝ) * (1 - ∑' n, cosineAtDoubleTerm x n) := by
  intro x
  rw [(hasSum_cosineAtDoubleTerm x).tsum_eq]
  ring

theorem gap3
    (f : ℝ → ℝ)
    (hf : ∀ x, f x = Real.sin x ^ 2)
    (htrig : ∀ x, f x = (1 - Real.cos (2 * x)) / 2)
    (hcos :
      ∀ x, (1 - Real.cos (2 * x)) / 2 =
        (1 / 2 : ℝ) * (1 - ∑' n, cosineAtDoubleTerm x n)) :
    ∀ x, (1 / 2 : ℝ) * (1 - ∑' n, cosineAtDoubleTerm x n) =
      ∑' n, sineSquareTerm x n := by
  intro x
  rw [(hasSum_cosineAtDoubleTerm x).tsum_eq,
    (hasSum_sineSquareTerm x).tsum_eq]
  ring

theorem gap4
    (f : ℝ → ℝ)
    (hf : ∀ x, f x = Real.sin x ^ 2)
    (htrig : ∀ x, f x = (1 - Real.cos (2 * x)) / 2)
    (hcos :
      ∀ x, (1 - Real.cos (2 * x)) / 2 =
        (1 / 2 : ℝ) * (1 - ∑' n, cosineAtDoubleTerm x n))
    (hreindex :
      ∀ x, (1 / 2 : ℝ) * (1 - ∑' n, cosineAtDoubleTerm x n) =
        ∑' n, sineSquareTerm x n) :
    ∀ x, f x = ∑' n, sineSquareTerm x n := by
  intro x
  calc
    f x = (1 - Real.cos (2 * x)) / 2 := htrig x
    _ = (1 / 2 : ℝ) * (1 - ∑' n, cosineAtDoubleTerm x n) := hcos x
    _ = ∑' n, sineSquareTerm x n := hreindex x

theorem gap5
    (f : ℝ → ℝ)
    (hf : ∀ x, f x = Real.sin x ^ 2)
    (htrig : ∀ x, f x = (1 - Real.cos (2 * x)) / 2)
    (hcos :
      ∀ x, (1 - Real.cos (2 * x)) / 2 =
        (1 / 2 : ℝ) * (1 - ∑' n, cosineAtDoubleTerm x n))
    (hreindex :
      ∀ x, (1 / 2 : ℝ) * (1 - ∑' n, cosineAtDoubleTerm x n) =
        ∑' n, sineSquareTerm x n)
    (hfseries : ∀ x, f x = ∑' n, sineSquareTerm x n) :
    ∀ x, Summable (sineSquareTerm x) := by
  intro x
  exact (hasSum_sineSquareTerm x).summable

end

end ProofGap.Exercise2843
