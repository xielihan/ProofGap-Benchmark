import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise2855

noncomputable section

def negativeTwoFalling (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (-2 - (k : ℝ))

def generalizedBinomialTerm (x : ℝ) (n : ℕ) : ℝ :=
  negativeTwoFalling n / (Nat.factorial n : ℝ) * (-x) ^ n

def reciprocalSquareTerm (x : ℝ) (n : ℕ) : ℝ :=
  (n + 1 : ℝ) * x ^ n

private theorem negativeTwoFalling_formula (n : ℕ) :
    negativeTwoFalling n = (-1 : ℝ) ^ n * (Nat.factorial (n + 1) : ℝ) := by
  induction n with
  | zero =>
      simp [negativeTwoFalling]
  | succ n ih =>
      have hrec :
          negativeTwoFalling (n + 1) =
            negativeTwoFalling n * (-2 - (n : ℝ)) := by
        simp [negativeTwoFalling, Finset.prod_range_succ]
      rw [hrec, ih]
      simp [pow_succ, Nat.factorial_succ] <;> ring

private theorem generalizedBinomialTerm_eq_reciprocalSquareTerm
    (x : ℝ) (n : ℕ) :
    generalizedBinomialTerm x n = reciprocalSquareTerm x n := by
  rw [generalizedBinomialTerm, reciprocalSquareTerm,
    negativeTwoFalling_formula, Nat.factorial_succ]
  norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hs : (-1 : ℝ) ^ n * (-x) ^ n = x ^ n := by
    rw [← mul_pow]
    simp
  field_simp [hf] <;> nlinarith [hs]

private theorem hasSum_reciprocalSquareTerm (x : ℝ) (hx : |x| < 1) :
    HasSum (fun n => reciprocalSquareTerm x n) (((1 - x)⁻¹) ^ 2) := by
  have hxnorm : ‖x‖ < 1 := by
    simpa [Real.norm_eq_abs] using hx
  have hs :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hxnorm).add
      (hasSum_geometric_of_norm_lt_one hxnorm)
  convert hs using 1
  · funext n
    simp [reciprocalSquareTerm]
    ring
  · have hxlt : x < 1 := (abs_lt.mp hx).2
    have hxne : 1 - x ≠ 0 := sub_ne_zero.mpr (ne_of_gt hxlt)
    field_simp [hxne] <;> ring

theorem gap1 :
    ∀ x : ℝ, 1 / (1 - x) ^ 2 = ((1 - x)⁻¹) ^ 2 := by
  intro x
  rw [one_div, inv_pow]

theorem gap2
    (hinverse : ∀ x : ℝ, 1 / (1 - x) ^ 2 = ((1 - x)⁻¹) ^ 2) :
    ∀ x : ℝ, |x| < 1 →
      1 / (1 - x) ^ 2 = ∑' n, generalizedBinomialTerm x n := by
  intro x hx
  rw [hinverse x]
  have heq :
      (fun n => generalizedBinomialTerm x n) =
        (fun n => reciprocalSquareTerm x n) := by
    funext n
    exact generalizedBinomialTerm_eq_reciprocalSquareTerm x n
  rw [heq]
  exact (hasSum_reciprocalSquareTerm x hx).tsum_eq.symm

theorem gap3
    (hinverse : ∀ x : ℝ, 1 / (1 - x) ^ 2 = ((1 - x)⁻¹) ^ 2)
    (hbinomial :
      ∀ x : ℝ, |x| < 1 →
        1 / (1 - x) ^ 2 = ∑' n, generalizedBinomialTerm x n) :
    ∀ x : ℝ, |x| < 1 →
      1 / (1 - x) ^ 2 = ∑' n, reciprocalSquareTerm x n := by
  intro x hx
  calc
    1 / (1 - x) ^ 2 = ∑' n, generalizedBinomialTerm x n := hbinomial x hx
    _ = ∑' n, reciprocalSquareTerm x n :=
      tsum_congr (fun n => generalizedBinomialTerm_eq_reciprocalSquareTerm x n)

end

end ProofGap.Exercise2855
