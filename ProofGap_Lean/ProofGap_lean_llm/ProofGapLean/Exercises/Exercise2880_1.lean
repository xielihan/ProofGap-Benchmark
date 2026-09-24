import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import ProofGapLean.Prelude.Discrete
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise2880_1

noncomputable section

open scoped BigOperators

def sineTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * x ^ (2 * n + 1) /
    (Nat.factorial (2 * n + 1) : ℝ)

def cosineTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * x ^ (2 * n) /
    (Nat.factorial (2 * n) : ℝ)

def convolutionCoefficient (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    1 /
      ((Nat.factorial (2 * k + 1) : ℝ) *
        (Nat.factorial (2 * (n - k)) : ℝ))

def convolutionTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * convolutionCoefficient n * x ^ (2 * n + 1)

def halfBinomialCoefficient (n : ℕ) : ℝ :=
  (1 / (Nat.factorial (2 * n + 1) : ℝ)) * (1 / 2 : ℝ) *
    ∑ k ∈ Finset.range (2 * n + 2), (Nat.choose (2 * n + 1) k : ℝ)

private theorem sum_even_odd_pairs (f : ℕ → ℝ) :
    ∀ n : ℕ,
      (∑ k ∈ Finset.range (2 * n + 2), f k) =
        ∑ k ∈ Finset.range (n + 1), (f (2 * k) + f (2 * k + 1)) := by
  intro n
  induction n with
  | zero =>
      norm_num [Finset.sum_range_succ]
  | succ n ih =>
      have hleft :
          2 * Nat.succ n + 2 = (2 * n + 2) + 2 := by
        omega
      have heven : 2 * n + 2 = 2 * (n + 1) := by
        omega
      have hodd : 2 * n + 3 = 2 * (n + 1) + 1 := by
        omega
      calc
        (∑ k ∈ Finset.range (2 * Nat.succ n + 2), f k) =
            (∑ k ∈ Finset.range (2 * n + 2), f k) +
              f (2 * n + 2) + f (2 * n + 3) := by
                rw [hleft, Finset.sum_range_succ,
                  Finset.sum_range_succ]
        _ = (∑ k ∈ Finset.range (n + 1),
              (f (2 * k) + f (2 * k + 1))) +
              f (2 * n + 2) + f (2 * n + 3) := by
                rw [ih]
        _ = (∑ k ∈ Finset.range (n + 1),
              (f (2 * k) + f (2 * k + 1))) +
              (f (2 * n + 2) + f (2 * n + 3)) := by
                rw [add_assoc]
        _ = (∑ k ∈ Finset.range (n + 1),
              (f (2 * k) + f (2 * k + 1))) +
              (f (2 * (n + 1)) + f (2 * (n + 1) + 1)) := by
                simp only [heven, hodd]
        _ = ∑ k ∈ Finset.range ((n + 1) + 1),
              (f (2 * k) + f (2 * k + 1)) := by
                exact (Finset.sum_range_succ
                  (fun k => f (2 * k) + f (2 * k + 1)) (n + 1)).symm
        _ = ∑ k ∈ Finset.range (Nat.succ n + 1),
              (f (2 * k) + f (2 * k + 1)) := by
                rfl

private theorem full_choose_sum (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℝ)) =
      (2 : ℝ) ^ m := by
  have htwo : (1 : ℝ) + 1 = 2 := by
    norm_num
  simpa [htwo, mul_comm, mul_left_comm, mul_assoc] using
    (add_pow (1 : ℝ) 1 m).symm

private theorem full_choose_sum_odd (n : ℕ) :
    (∑ k ∈ Finset.range (2 * n + 2),
      (Nat.choose (2 * n + 1) k : ℝ)) =
        (2 : ℝ) ^ (2 * n + 1) := by
  have hidx : (2 * n + 1) + 1 = 2 * n + 2 := by
    omega
  simpa only [hidx] using full_choose_sum (2 * n + 1)

private theorem two_pow_odd (n : ℕ) :
    (2 : ℝ) ^ (2 * n + 1) =
      2 * (2 : ℝ) ^ (2 * n) := by
  rw [pow_succ]
  ring

private theorem odd_choose_sum (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (Nat.choose (2 * n + 1) (2 * k + 1) : ℝ)) =
        (2 : ℝ) ^ (2 * n) := by
  have hall :
      (∑ k ∈ Finset.range (2 * n + 2),
        (Nat.choose (2 * n + 1) k : ℝ)) =
          (2 : ℝ) ^ (2 * n + 1) :=
    full_choose_sum_odd n
  have halt0 :
      (∑ k ∈ Finset.range ((2 * n + 1) + 1),
        (-1 : ℝ) ^ k * (Nat.choose (2 * n + 1) k : ℝ)) = 0 := by
    simpa [show 2 * n + 1 ≠ 0 by omega,
      mul_comm, mul_left_comm, mul_assoc] using
        (add_pow (-1 : ℝ) 1 (2 * n + 1)).symm
  have hidx : (2 * n + 1) + 1 = 2 * n + 2 := by
    omega
  have halt :
      (∑ k ∈ Finset.range (2 * n + 2),
        (-1 : ℝ) ^ k * (Nat.choose (2 * n + 1) k : ℝ)) = 0 := by
    simpa only [hidx] using halt0
  rw [sum_even_odd_pairs] at hall halt
  rw [Finset.sum_add_distrib] at hall halt
  simp [pow_succ, pow_mul] at halt
  rw [two_pow_odd n] at hall
  linarith

private theorem convolutionCoefficient_closed (n : ℕ) :
    convolutionCoefficient n =
      (2 : ℝ) ^ (2 * n) /
        (Nat.factorial (2 * n + 1) : ℝ) := by
  unfold convolutionCoefficient
  calc
    (∑ k ∈ Finset.range (n + 1),
        1 /
          ((Nat.factorial (2 * k + 1) : ℝ) *
            (Nat.factorial (2 * (n - k)) : ℝ))) =
      ∑ k ∈ Finset.range (n + 1),
        (Nat.choose (2 * n + 1) (2 * k + 1) : ℝ) /
          (Nat.factorial (2 * n + 1) : ℝ) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hkn : k ≤ n := by
              have := Finset.mem_range.mp hk
              omega
            have hkodd : 2 * k + 1 ≤ 2 * n + 1 := by
              omega
            have hsub :
                (2 * n + 1) - (2 * k + 1) = 2 * (n - k) := by
              omega
            have hfacR :
                (Nat.choose (2 * n + 1) (2 * k + 1) : ℝ) *
                    (Nat.factorial (2 * k + 1) : ℝ) *
                    (Nat.factorial ((2 * n + 1) - (2 * k + 1)) : ℝ) =
                  (Nat.factorial (2 * n + 1) : ℝ) := by
              exact_mod_cast
                Nat.choose_mul_factorial_mul_factorial hkodd
            rw [← hsub]
            apply (div_eq_div_iff (by positivity) (by positivity)).2
            simpa [mul_assoc] using hfacR.symm
    _ = (2 : ℝ) ^ (2 * n) /
          (Nat.factorial (2 * n + 1) : ℝ) := by
            rw [← Finset.sum_div, odd_choose_sum]

private theorem convolution_inner_eq (x : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      sineTerm x k * cosineTerm x (n - k)) =
        convolutionTerm x n := by
  unfold convolutionTerm convolutionCoefficient sineTerm cosineTerm
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by
    have := Finset.mem_range.mp hk
    omega
  have hsign :
      (-1 : ℝ) ^ k * (-1 : ℝ) ^ (n - k) = (-1 : ℝ) ^ n := by
    rw [← pow_add, Nat.add_sub_of_le hkn]
  have hpow :
      x ^ (2 * k + 1) * x ^ (2 * (n - k)) = x ^ (2 * n + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hnum :
      ((-1 : ℝ) ^ k * x ^ (2 * k + 1)) *
          ((-1 : ℝ) ^ (n - k) * x ^ (2 * (n - k))) =
        (-1 : ℝ) ^ n * x ^ (2 * n + 1) := by
    calc
      ((-1 : ℝ) ^ k * x ^ (2 * k + 1)) *
          ((-1 : ℝ) ^ (n - k) * x ^ (2 * (n - k))) =
          ((-1 : ℝ) ^ k * (-1 : ℝ) ^ (n - k)) *
            (x ^ (2 * k + 1) * x ^ (2 * (n - k))) := by
              ring
      _ = (-1 : ℝ) ^ n * x ^ (2 * n + 1) := by
            rw [hsign, hpow]
  calc
    ((-1 : ℝ) ^ k * x ^ (2 * k + 1) /
          (Nat.factorial (2 * k + 1) : ℝ)) *
        ((-1 : ℝ) ^ (n - k) * x ^ (2 * (n - k)) /
          (Nat.factorial (2 * (n - k)) : ℝ)) =
      (((-1 : ℝ) ^ k * x ^ (2 * k + 1)) *
          ((-1 : ℝ) ^ (n - k) * x ^ (2 * (n - k)))) /
        ((Nat.factorial (2 * k + 1) : ℝ) *
          (Nat.factorial (2 * (n - k)) : ℝ)) := by
            rw [div_mul_div_comm]
    _ = ((-1 : ℝ) ^ n *
          (1 / ((Nat.factorial (2 * k + 1) : ℝ) *
            (Nat.factorial (2 * (n - k)) : ℝ)))) *
          x ^ (2 * n + 1) := by
            rw [hnum]
            ring

private theorem convolutionTerm_eq_half_sineTerm (x : ℝ) (n : ℕ) :
    convolutionTerm x n =
      (1 / 2 : ℝ) * sineTerm (2 * x) n := by
  unfold convolutionTerm sineTerm
  rw [convolutionCoefficient_closed, mul_pow, two_pow_odd]
  ring

theorem gap1 :
    ∀ x : ℝ, Summable (sineTerm x) := by
  intro x
  simpa [sineTerm] using (Real.hasSum_sin x).summable

theorem gap2 :
    ∀ x : ℝ, Summable (cosineTerm x) := by
  intro x
  simpa [cosineTerm] using (Real.hasSum_cos x).summable

theorem gap3 :
    ∀ x : ℝ, Real.sin x * Real.cos x =
      (∑' n, sineTerm x n) * (∑' n, cosineTerm x n) := by
  intro x
  have hs : HasSum (sineTerm x) (Real.sin x) := by
    simpa [sineTerm] using Real.hasSum_sin x
  have hc : HasSum (cosineTerm x) (Real.cos x) := by
    simpa [cosineTerm] using Real.hasSum_cos x
  rw [hs.tsum_eq, hc.tsum_eq]

theorem gap4 :
    ∀ x : ℝ, Real.sin x * Real.cos x =
      ∑' n, ∑ k ∈ Finset.range (n + 1),
        sineTerm x k * cosineTerm x (n - k) := by
  intro x
  have hs : HasSum (sineTerm (2 * x)) (Real.sin (2 * x)) := by
    simpa [sineTerm] using Real.hasSum_sin (2 * x)
  calc
    Real.sin x * Real.cos x =
        (1 / 2 : ℝ) * Real.sin (2 * x) := by
      rw [Real.sin_two_mul]
      ring
    _ = (1 / 2 : ℝ) * (∑' n, sineTerm (2 * x) n) := by
      rw [hs.tsum_eq]
    _ = ∑' n, (1 / 2 : ℝ) * sineTerm (2 * x) n := by
      rw [tsum_mul_left]
    _ = ∑' n, ∑ k ∈ Finset.range (n + 1),
          sineTerm x k * cosineTerm x (n - k) := by
      apply tsum_congr
      intro n
      symm
      calc
        (∑ k ∈ Finset.range (n + 1),
            sineTerm x k * cosineTerm x (n - k)) =
            convolutionTerm x n := convolution_inner_eq x n
        _ = (1 / 2 : ℝ) * sineTerm (2 * x) n :=
          convolutionTerm_eq_half_sineTerm x n

theorem gap5 :
    ∀ x : ℝ, Real.sin x * Real.cos x =
      ∑' n, convolutionTerm x n := by
  intro x
  rw [gap4 x]
  apply tsum_congr
  intro n
  exact convolution_inner_eq x n

theorem gap6 :
    ∀ n : ℕ, convolutionCoefficient n =
      ∑ k ∈ Finset.range (n + 1),
        1 /
          ((Nat.factorial (2 * k + 1) : ℝ) *
            (Nat.factorial (2 * (n - k)) : ℝ)) := by
  intro n
  rfl

theorem gap7 :
    ∀ n : ℕ, convolutionCoefficient n = halfBinomialCoefficient n := by
  intro n
  rw [convolutionCoefficient_closed]
  unfold halfBinomialCoefficient
  rw [full_choose_sum_odd, two_pow_odd]
  ring

theorem gap8 :
    ∀ n : ℕ, halfBinomialCoefficient n =
      (1 / 2 : ℝ) * (2 : ℝ) ^ (2 * n + 1) /
        (Nat.factorial (2 * n + 1) : ℝ) := by
  intro n
  unfold halfBinomialCoefficient
  rw [full_choose_sum_odd]
  ring

theorem gap9 :
    ∀ n : ℕ, convolutionCoefficient n =
      (1 / 2 : ℝ) * (2 : ℝ) ^ (2 * n + 1) /
        (Nat.factorial (2 * n + 1) : ℝ) := by
  intro n
  rw [gap7 n, gap8 n]

theorem gap10 :
    ∀ x : ℝ, Real.sin x * Real.cos x =
      (1 / 2 : ℝ) * (∑' n, sineTerm (2 * x) n) := by
  intro x
  have hs : HasSum (sineTerm (2 * x)) (Real.sin (2 * x)) := by
    simpa [sineTerm] using Real.hasSum_sin (2 * x)
  rw [hs.tsum_eq, Real.sin_two_mul]
  ring

theorem gap11 :
    ∀ x : ℝ, (1 / 2 : ℝ) * (∑' n, sineTerm (2 * x) n) =
      (1 / 2 : ℝ) * Real.sin (2 * x) := by
  intro x
  have hs : HasSum (sineTerm (2 * x)) (Real.sin (2 * x)) := by
    simpa [sineTerm] using Real.hasSum_sin (2 * x)
  rw [hs.tsum_eq]

theorem gap12 :
    ∀ x : ℝ, Real.sin x * Real.cos x =
      (1 / 2 : ℝ) * Real.sin (2 * x) := by
  intro x
  rw [Real.sin_two_mul]
  ring

theorem gap13 :
    ∀ x : ℝ, Real.sin x * Real.cos x =
      (1 / 2 : ℝ) * Real.sin (2 * x) := by
  exact gap12

end

end ProofGap.Exercise2880_1
