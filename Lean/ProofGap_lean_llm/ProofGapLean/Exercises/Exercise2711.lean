import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2711

noncomputable section

open scoped BigOperators

def a (n : ℕ) : ℝ :=
  1 / (Nat.factorial n : ℝ)

def b (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / (Nat.factorial n : ℝ)

def convolution (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), a i * b (n - i)

theorem gap1 :
    Summable (fun n : ℕ => |a n|) := by
  simpa [a, abs_div] using Real.summable_pow_div_factorial 1

theorem gap2 :
    Summable (fun n : ℕ => |b n|) := by
  simpa [a, b, abs_div, abs_pow] using gap1

theorem gap3 :
    (∑' n : ℕ, a n) * (∑' n : ℕ, b n) =
      ∑' n : ℕ, convolution n := by
  simpa [convolution, Real.norm_eq_abs] using
    (tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
      (f := a) (g := b) gap1 gap2)

theorem gap4 :
    ∑' n : ℕ, convolution n =
      convolution 0 + ∑' n : ℕ, convolution (n + 1) := by
  have hnorm : Summable (fun n : ℕ => ‖convolution n‖) := by
    simpa [convolution, Real.norm_eq_abs] using
      (summable_norm_sum_mul_range_of_summable_norm
        (f := a) (g := b) gap1 gap2)
  exact hnorm.of_norm.tsum_eq_zero_add

theorem gap5 :
    convolution 0 + ∑' n : ℕ, convolution (n + 1) =
      1 + ∑' n : ℕ, convolution (n + 1) := by
  simp [convolution, a, b]

theorem gap6 :
    (∑' n : ℕ, a n) * (∑' n : ℕ, b n) =
      1 + ∑' n : ℕ, convolution (n + 1) := by
  exact gap3.trans (gap4.trans gap5)

theorem gap7 :
    ∀ n : ℕ,
      convolution n = ∑ i ∈ Finset.range (n + 1), a i * b (n - i) := by
  intro n
  rfl

theorem gap8 :
    ∀ n : ℕ,
      ∑ i ∈ Finset.range (n + 1), a i * b (n - i) =
        ∑ i ∈ Finset.range (n + 1),
          (1 / (Nat.factorial i : ℝ)) *
            ((-1 : ℝ) ^ (n - i) / (Nat.factorial (n - i) : ℝ)) := by
  intro n
  simp [a, b]

theorem gap9 :
    ∀ n : ℕ,
      convolution n =
        1 / (Nat.factorial n : ℝ) *
          ∑ i ∈ Finset.range (n + 1),
            (-1 : ℝ) ^ (n - i) *
              ((Nat.factorial n : ℝ) /
                ((Nat.factorial i : ℝ) * Nat.factorial (n - i))) := by
  intro n
  rw [gap7 n, gap8 n, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hn : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hi' : (Nat.factorial i : ℝ) ≠ 0 := by positivity
  have hni : (Nat.factorial (n - i) : ℝ) ≠ 0 := by positivity
  field_simp

theorem gap10 :
    ∀ n : ℕ,
      convolution n =
        1 / (Nat.factorial n : ℝ) * (1 - 1 : ℝ) ^ n := by
  intro n
  rw [gap9 n]
  congr 1
  calc
    (∑ i ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ (n - i) *
          ((Nat.factorial n : ℝ) /
            ((Nat.factorial i : ℝ) * Nat.factorial (n - i)))) =
        ∑ i ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ (n - i) * (Nat.choose n i : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hden :
          (Nat.factorial i : ℝ) * Nat.factorial (n - i) ≠ 0 := by
        positivity
      have hchoose :
          (Nat.factorial n : ℝ) /
              ((Nat.factorial i : ℝ) * Nat.factorial (n - i)) =
            (Nat.choose n i : ℝ) := by
        rw [div_eq_iff hden]
        norm_cast
        simpa [Nat.mul_assoc] using
          (Nat.choose_mul_factorial_mul_factorial hin).symm
      rw [hchoose]
    _ = (1 - 1 : ℝ) ^ n := by
      simpa [sub_eq_add_neg] using (add_pow (1 : ℝ) (-1 : ℝ) n).symm

theorem gap11 :
    ∀ n : ℕ, 1 ≤ n →
      1 / (Nat.factorial n : ℝ) * (1 - 1 : ℝ) ^ n = 0 := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  simp [hn0]

theorem gap12 :
    convolution 0 = 1 ∧ ∀ n : ℕ, 1 ≤ n → convolution n = 0 := by
  constructor
  · simp [convolution, a, b]
  · intro n hn
    rw [gap10 n]
    exact gap11 n hn

theorem gap13 :
    (∑' n : ℕ, a n) * (∑' n : ℕ, b n) =
      1 + ∑' n : ℕ, convolution (n + 1) := by
  exact gap6

theorem gap14 :
    1 + ∑' n : ℕ, convolution (n + 1) = 1 := by
  have hz (n : ℕ) : convolution (n + 1) = 0 :=
    gap12.2 (n + 1) (by omega)
  simp [hz]

theorem gap15 :
    (∑' n : ℕ, a n) * (∑' n : ℕ, b n) = 1 := by
  exact gap13.trans gap14

theorem gap16 :
    ∑' n : ℕ, a n = Real.exp 1 := by
  rw [Real.exp_eq_exp_ℝ]
  simpa [a] using
    (NormedSpace.expSeries_div_hasSum_exp (1 : ℝ)).tsum_eq

theorem gap17 :
    ∑' n : ℕ, b n = Real.exp (-1) := by
  rw [Real.exp_eq_exp_ℝ]
  simpa [b] using
    (NormedSpace.expSeries_div_hasSum_exp (-1 : ℝ)).tsum_eq

theorem gap18 :
    (∑' n : ℕ, a n) * (∑' n : ℕ, b n) =
      Real.exp 1 * Real.exp (-1) := by
  rw [gap16, gap17]

theorem gap19 :
    Real.exp 1 * Real.exp (-1) = 1 := by
  rw [← Real.exp_add]
  norm_num

theorem gap20 :
    (∑' n : ℕ, a n) * (∑' n : ℕ, b n) = 1 := by
  exact gap18.trans gap19

theorem gap21 :
    (∑' n : ℕ, a n) * (∑' n : ℕ, b n) = 1 := by
  exact gap20

end

end ProofGap.Exercise2711
