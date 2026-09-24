import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Normed.Ring.InfiniteSum

namespace ProofGap.Exercise2880_2

noncomputable section

open scoped BigOperators

def sineTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * x ^ (2 * n + 1) /
    (Nat.factorial (2 * n + 1) : ℝ)

def cosineTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * x ^ (2 * n) /
    (Nat.factorial (2 * n) : ℝ)

def sineSquareCoefficient (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    1 /
      ((Nat.factorial (2 * k + 1) : ℝ) *
        (Nat.factorial (2 * (n - k) + 1) : ℝ))

def cosineSquareCoefficient (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    1 /
      ((Nat.factorial (2 * k) : ℝ) *
        (Nat.factorial (2 * (n - k)) : ℝ))

def cancellationCoefficient (n : ℕ) : ℝ :=
  cosineSquareCoefficient (n + 1) - sineSquareCoefficient n

def alternatingBinomialCoefficient (n : ℕ) : ℝ :=
  (1 / (Nat.factorial (2 * n + 2) : ℝ)) *
    ∑ s ∈ Finset.range (2 * n + 3),
      (-1 : ℝ) ^ s * (Nat.choose (2 * n + 2) s : ℝ)

private theorem sine_convolution (x : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), sineTerm x k * sineTerm x (n - k)) =
      (-1 : ℝ) ^ n * x ^ (2 * n + 2) * sineSquareCoefficient n := by
  rw [sineSquareCoefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  rw [sineTerm, sineTerm]
  have hpowneg : (-1 : ℝ) ^ k * (-1 : ℝ) ^ (n - k) = (-1 : ℝ) ^ n := by
    rw [← pow_add, Nat.add_sub_of_le hkn]
  have hpowx :
      x ^ (2 * k + 1) * x ^ (2 * (n - k) + 1) = x ^ (2 * n + 2) := by
    rw [← pow_add]
    congr 1
    omega
  simp only [div_eq_mul_inv, one_mul, mul_inv_rev]
  rw [← hpowneg, ← hpowx]
  ring

private theorem cosine_convolution (x : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), cosineTerm x k * cosineTerm x (n - k)) =
      (-1 : ℝ) ^ n * x ^ (2 * n) * cosineSquareCoefficient n := by
  rw [cosineSquareCoefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  rw [cosineTerm, cosineTerm]
  have hpowneg : (-1 : ℝ) ^ k * (-1 : ℝ) ^ (n - k) = (-1 : ℝ) ^ n := by
    rw [← pow_add, Nat.add_sub_of_le hkn]
  have hpowx : x ^ (2 * k) * x ^ (2 * (n - k)) = x ^ (2 * n) := by
    rw [← pow_add]
    congr 1
    omega
  simp only [div_eq_mul_inv, one_mul, mul_inv_rev]
  rw [← hpowneg, ← hpowx]
  ring

private theorem alternating_sum_even_odd (f : ℕ → ℝ) :
    ∀ n : ℕ,
      (∑ s ∈ Finset.range (2 * n + 3), (-1 : ℝ) ^ s * f s) =
        (∑ k ∈ Finset.range (n + 2), f (2 * k)) -
          (∑ k ∈ Finset.range (n + 1), f (2 * k + 1)) := by
  intro n
  induction n with
  | zero =>
      norm_num [Finset.sum_range_succ]
      ring
  | succ n ih =>
      have hleft :
          (∑ s ∈ Finset.range (2 * (n + 1) + 3), (-1 : ℝ) ^ s * f s) =
            (∑ s ∈ Finset.range (2 * n + 3), (-1 : ℝ) ^ s * f s) +
              (-1 : ℝ) ^ (2 * n + 3) * f (2 * n + 3) +
              (-1 : ℝ) ^ (2 * n + 4) * f (2 * n + 4) := by
        rw [show 2 * (n + 1) + 3 = (2 * n + 3) + 2 by omega]
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have heven :
          (∑ k ∈ Finset.range (n + 1 + 2), f (2 * k)) =
            (∑ k ∈ Finset.range (n + 2), f (2 * k)) +
              f (2 * n + 4) := by
        rw [show n + 1 + 2 = (n + 2) + 1 by omega,
          Finset.sum_range_succ]
        congr 1
      have hodd :
          (∑ k ∈ Finset.range (n + 1 + 1), f (2 * k + 1)) =
            (∑ k ∈ Finset.range (n + 1), f (2 * k + 1)) +
              f (2 * n + 3) := by
        rw [show n + 1 + 1 = (n + 1) + 1 by omega,
          Finset.sum_range_succ]
        congr 1
      rw [hleft, heven, hodd, ih]
      norm_num [pow_add, pow_mul]
      ring

private theorem reciprocal_factorials_eq_choose_div
    {N s : ℕ} (hs : s ≤ N) :
    1 / ((Nat.factorial s : ℝ) * (Nat.factorial (N - s) : ℝ)) =
      (Nat.choose N s : ℝ) / (Nat.factorial N : ℝ) := by
  rw [Nat.cast_choose ℝ hs]
  have hs0 : (Nat.factorial s : ℝ) ≠ 0 := by positivity
  have hNs0 : (Nat.factorial (N - s) : ℝ) ≠ 0 := by positivity
  have hN0 : (Nat.factorial N : ℝ) ≠ 0 := by positivity
  field_simp

theorem gap1 :
    ∀ x : ℝ, Summable (sineTerm x) := by
  intro x
  simpa [sineTerm] using (Real.hasSum_sin x).summable

theorem gap2 :
    ∀ x : ℝ, Summable (cosineTerm x) := by
  intro x
  simpa [cosineTerm] using (Real.hasSum_cos x).summable

theorem gap3 :
    ∀ x : ℝ, Real.sin x ^ 2 + Real.cos x ^ 2 =
      (∑' n₁, ∑' n₂, sineTerm x n₁ * sineTerm x n₂) +
        (∑' k₁, ∑' k₂, cosineTerm x k₁ * cosineTerm x k₂) := by
  intro x
  have hs : Summable (sineTerm x) := gap1 x
  have hc : Summable (cosineTerm x) := gap2 x
  have hsin : Real.sin x = ∑' n, sineTerm x n := by
    simpa [sineTerm] using (Real.hasSum_sin x).tsum_eq.symm
  have hcos : Real.cos x = ∑' n, cosineTerm x n := by
    simpa [cosineTerm] using (Real.hasSum_cos x).tsum_eq.symm
  rw [pow_two, pow_two, hsin, hcos]
  congr 1
  · calc
      (∑' n, sineTerm x n) * ∑' n, sineTerm x n =
          ∑' n, sineTerm x n * ∑' k, sineTerm x k :=
        (hs.tsum_mul_right _).symm
      _ = ∑' n, ∑' k, sineTerm x n * sineTerm x k := by
        apply tsum_congr
        intro n
        exact (hs.tsum_mul_left _).symm
  · calc
      (∑' n, cosineTerm x n) * ∑' n, cosineTerm x n =
          ∑' n, cosineTerm x n * ∑' k, cosineTerm x k :=
        (hc.tsum_mul_right _).symm
      _ = ∑' n, ∑' k, cosineTerm x n * cosineTerm x k := by
        apply tsum_congr
        intro n
        exact (hc.tsum_mul_left _).symm

theorem gap4 :
    ∀ x : ℝ, Real.sin x ^ 2 + Real.cos x ^ 2 =
      (∑' n, (-1 : ℝ) ^ n * x ^ (2 * n + 2) *
        sineSquareCoefficient n) +
      (∑' m, (-1 : ℝ) ^ m * x ^ (2 * m) *
        cosineSquareCoefficient m) := by
  intro x
  have hs : Summable (sineTerm x) := gap1 x
  have hc : Summable (cosineTerm x) := gap2 x
  have hsabs : Summable (fun n => ‖sineTerm x n‖) := by
    simpa only [Real.norm_eq_abs] using hs.abs
  have hcabs : Summable (fun n => ‖cosineTerm x n‖) := by
    simpa only [Real.norm_eq_abs] using hc.abs
  have hsin : Real.sin x = ∑' n, sineTerm x n := by
    simpa [sineTerm] using (Real.hasSum_sin x).tsum_eq.symm
  have hcos : Real.cos x = ∑' n, cosineTerm x n := by
    simpa [cosineTerm] using (Real.hasSum_cos x).tsum_eq.symm
  rw [pow_two, pow_two, hsin, hcos]
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hsabs hsabs]
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hcabs hcabs]
  congr 1
  · apply tsum_congr
    exact sine_convolution x
  · apply tsum_congr
    exact cosine_convolution x

theorem gap5 :
    ∀ x : ℝ, Real.sin x ^ 2 + Real.cos x ^ 2 =
      1 + ∑' n, (-1 : ℝ) ^ (n + 1) * x ^ (2 * n + 2) *
        cancellationCoefficient n := by
  intro x
  have hs : Summable (sineTerm x) := gap1 x
  have hc : Summable (cosineTerm x) := gap2 x
  have hsabs : Summable (fun n => ‖sineTerm x n‖) := by
    simpa only [Real.norm_eq_abs] using hs.abs
  have hcabs : Summable (fun n => ‖cosineTerm x n‖) := by
    simpa only [Real.norm_eq_abs] using hc.abs
  let S : ℕ → ℝ := fun n =>
    (-1 : ℝ) ^ n * x ^ (2 * n + 2) * sineSquareCoefficient n
  let C : ℕ → ℝ := fun n =>
    (-1 : ℝ) ^ n * x ^ (2 * n) * cosineSquareCoefficient n
  have hS : Summable S :=
    (summable_norm_sum_mul_range_of_summable_norm hsabs hsabs).of_norm.congr
      (sine_convolution x)
  have hC : Summable C :=
    (summable_norm_sum_mul_range_of_summable_norm hcabs hcabs).of_norm.congr
      (cosine_convolution x)
  have hCshift : Summable (fun n => C (n + 1)) :=
    hC.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  rw [gap4]
  change (∑' n, S n) + ∑' n, C n = _
  rw [← hC.sum_add_tsum_nat_add 1]
  simp only [C, pow_zero, Nat.mul_zero, one_mul, Nat.factorial_zero,
    Nat.cast_one, div_one, cosineSquareCoefficient, Finset.range_one,
    Finset.sum_singleton, Nat.zero_sub, zero_add]
  change (∑' n, S n) + (1 + ∑' n, C (n + 1)) = _
  rw [add_left_comm]
  rw [← hS.tsum_add hCshift]
  congr 1
  apply tsum_congr
  intro n
  simp only [S, C, cancellationCoefficient]
  have hexp : 2 * (n + 1) = 2 * n + 2 := by omega
  rw [hexp, pow_succ]
  ring

theorem gap6 :
    ∀ n : ℕ, cancellationCoefficient n =
      (∑ k ∈ Finset.range (n + 2),
        1 /
          ((Nat.factorial (2 * k) : ℝ) *
            (Nat.factorial (2 * (n + 1 - k)) : ℝ))) -
      (∑ k ∈ Finset.range (n + 1),
        1 /
          ((Nat.factorial (2 * k + 1) : ℝ) *
            (Nat.factorial (2 * (n - k) + 1) : ℝ))) := by
  intro n
  simp only [cancellationCoefficient, cosineSquareCoefficient,
    sineSquareCoefficient]

theorem gap7 :
    ∀ n : ℕ, cancellationCoefficient n =
      alternatingBinomialCoefficient n := by
  intro n
  rw [cancellationCoefficient, cosineSquareCoefficient,
    sineSquareCoefficient, alternatingBinomialCoefficient]
  have heven :
      (∑ k ∈ Finset.range (n + 2),
        1 /
          ((Nat.factorial (2 * k) : ℝ) *
            (Nat.factorial (2 * (n + 1 - k)) : ℝ))) =
        ∑ k ∈ Finset.range (n + 2),
          (Nat.choose (2 * n + 2) (2 * k) : ℝ) /
            (Nat.factorial (2 * n + 2) : ℝ) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n + 1 :=
      Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hsub : 2 * n + 2 - 2 * k = 2 * (n + 1 - k) := by omega
    simpa only [hsub] using
      (reciprocal_factorials_eq_choose_div
        (N := 2 * n + 2) (s := 2 * k) (by omega))
  have hodd :
      (∑ k ∈ Finset.range (n + 1),
        1 /
          ((Nat.factorial (2 * k + 1) : ℝ) *
            (Nat.factorial (2 * (n - k) + 1) : ℝ))) =
        ∑ k ∈ Finset.range (n + 1),
          (Nat.choose (2 * n + 2) (2 * k + 1) : ℝ) /
            (Nat.factorial (2 * n + 2) : ℝ) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hsub : 2 * n + 2 - (2 * k + 1) = 2 * (n - k) + 1 := by omega
    simpa only [hsub] using
      (reciprocal_factorials_eq_choose_div
        (N := 2 * n + 2) (s := 2 * k + 1) (by omega))
  rw [heven, hodd, ← Finset.sum_div, ← Finset.sum_div]
  rw [alternating_sum_even_odd
    (fun s => (Nat.choose (2 * n + 2) s : ℝ)) n]
  ring

theorem gap8 :
    ∀ n : ℕ, alternatingBinomialCoefficient n =
      (1 / (Nat.factorial (2 * n + 2) : ℝ)) *
        ((1 : ℝ) + (-1 : ℝ)) ^ (2 * n + 2) := by
  intro n
  rw [alternatingBinomialCoefficient]
  congr 1
  have h :
      (∑ s ∈ Finset.range ((2 * n + 2) + 1),
        (-1 : ℝ) ^ s * (Nat.choose (2 * n + 2) s : ℝ)) =
          ((-1 : ℝ) + 1) ^ (2 * n + 2) := by
    simpa only [one_pow, mul_one] using
      (add_pow (-1 : ℝ) 1 (2 * n + 2)).symm
  convert h using 1 <;> ring

theorem gap9 :
    ∀ n : ℕ,
      (1 / (Nat.factorial (2 * n + 2) : ℝ)) *
        ((1 : ℝ) + (-1 : ℝ)) ^ (2 * n + 2) = 0 := by
  intro n
  norm_num [show 0 < 2 * n + 2 by omega]

theorem gap10 :
    ∀ n : ℕ, cancellationCoefficient n = 0 := by
  intro n
  rw [gap7, gap8, gap9]

theorem gap11 :
    ∀ x : ℝ, Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by
  exact Real.sin_sq_add_cos_sq

theorem gap12 :
    ∀ x : ℝ, Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by
  exact Real.sin_sq_add_cos_sq

end

end ProofGap.Exercise2880_2
