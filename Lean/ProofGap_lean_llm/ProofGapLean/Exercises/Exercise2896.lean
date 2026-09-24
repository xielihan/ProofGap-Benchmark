import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise2896

noncomputable section

open scoped BigOperators

def coefficientTerm (a : ℕ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  a n * x ^ n

def partialSumCoefficient (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), a k

def partialSumTerm (a : ℕ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  partialSumCoefficient a n * x ^ n

theorem gap1
    (a : ℕ → ℝ) (f F : ℝ → ℝ)
    (hf : ∀ x, f x = ∑' n, coefficientTerm a x n)
    (hF : ∀ x, F x = f x / (1 - x)) :
    ∀ x, |x| < 1 → Summable (coefficientTerm a x) →
      F x =
        (∑' n₁, coefficientTerm a x n₁) * (∑' n₂ : ℕ, x ^ n₂) := by
  intro x hx hsum
  have hxnorm : ‖x‖ < 1 := by
    simpa [Real.norm_eq_abs] using hx
  have hgeom :
      (∑' n : ℕ, x ^ n) = (1 - x)⁻¹ :=
    (hasSum_geometric_of_norm_lt_one hxnorm).tsum_eq
  rw [hF x, hf x, hgeom]
  simp [div_eq_mul_inv]

theorem gap2
    (a : ℕ → ℝ) (f F : ℝ → ℝ)
    (hf : ∀ x, f x = ∑' n, coefficientTerm a x n)
    (hF : ∀ x, F x = f x / (1 - x)) :
    ∀ x, |x| < 1 → Summable (coefficientTerm a x) →
      F x = ∑' n, partialSumTerm a x n := by
  intro x hx hsum
  have hxnorm : ‖x‖ < 1 := by
    simpa [Real.norm_eq_abs] using hx
  have hcoefNorm :
      Summable (fun n : ℕ => ‖coefficientTerm a x n‖) :=
    hsum.norm
  have hgeomNorm : Summable (fun n : ℕ => ‖x ^ n‖) :=
    summable_norm_geometric_of_norm_lt_one hxnorm
  calc
    F x =
        (∑' n₁, coefficientTerm a x n₁) *
          (∑' n₂ : ℕ, x ^ n₂) :=
      gap1 a f F hf hF x hx hsum
    _ =
        ∑' n : ℕ,
          ∑ kl ∈ Finset.antidiagonal n,
            coefficientTerm a x kl.1 * x ^ kl.2 :=
      tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
        hcoefNorm hgeomNorm
    _ = ∑' n, partialSumTerm a x n := by
      apply tsum_congr
      intro n
      calc
        (∑ kl ∈ Finset.antidiagonal n,
            coefficientTerm a x kl.1 * x ^ kl.2) =
            ∑ i ∈ Finset.range (n + 1),
              coefficientTerm a x i * x ^ (n - i) := by
          symm
          refine Finset.sum_bij (fun i _ => (i, n - i)) ?_ ?_ ?_ ?_
          · intro i hi
            simp only [Finset.mem_antidiagonal]
            have hi' := Finset.mem_range.mp hi
            omega
          · intro i₁ hi₁ i₂ hi₂ heq
            exact congrArg Prod.fst heq
          · intro kl hkl
            have hsumkl := Finset.mem_antidiagonal.mp hkl
            refine ⟨kl.1, ?_, ?_⟩
            · apply Finset.mem_range.mpr
              omega
            · apply Prod.ext
              · rfl
              · dsimp
                omega
          · intro i hi
            rfl
        _ = partialSumTerm a x n := by
          unfold partialSumTerm partialSumCoefficient coefficientTerm
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          have hin : i ≤ n := by
            exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
          rw [mul_assoc, ← pow_add]
          congr 2
          omega

theorem gap3
    (a : ℕ → ℝ) (f F : ℝ → ℝ)
    (hf : ∀ x, f x = ∑' n, coefficientTerm a x n)
    (hF : ∀ x, F x = f x / (1 - x)) :
    ∀ x, |x| < 1 → Summable (coefficientTerm a x) →
      F x =
        ∑' n, (∑ k ∈ Finset.range (n + 1), a k) * x ^ n := by
  intro x hx hsum
  simpa [partialSumTerm, partialSumCoefficient] using
    gap2 a f F hf hF x hx hsum

end

end ProofGap.Exercise2896
