import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2996

noncomputable section

open scoped BigOperators

def weightedTerm (n : ℕ) : ℝ :=
  2 ^ n * (n + 1 : ℝ) / (Nat.factorial n : ℝ)

def baseTerm (n : ℕ) : ℝ :=
  2 ^ n / (Nat.factorial n : ℝ)

def weightedSeries : ℝ :=
  ∑' n : ℕ, weightedTerm n

def baseSeries : ℝ :=
  ∑' n : ℕ, baseTerm n

def shiftedSeries : ℝ :=
  ∑' k : ℕ, 2 ^ (k + 1) / (Nat.factorial k : ℝ)

def positiveBaseTail : ℝ :=
  ∑' k : ℕ, baseTerm (k + 1)

def convolution (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    1 / ((Nat.factorial k : ℝ) *
      (Nat.factorial (n - k) : ℝ))

def chooseConvolution (n : ℕ) : ℝ :=
  1 / (Nat.factorial n : ℝ) *
    ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ)

def exponentialSeriesOne : ℝ :=
  ∑' k : ℕ, 1 / (Nat.factorial k : ℝ)

private lemma summable_baseTerm : Summable baseTerm := by
  simpa [baseTerm] using Real.summable_pow_div_factorial 2

private lemma summable_shiftedTerm :
    Summable (fun k : ℕ =>
      2 ^ (k + 1) / (Nat.factorial k : ℝ)) := by
  have h := summable_baseTerm.mul_left 2
  refine h.congr ?_
  intro k
  simp [baseTerm, pow_succ]
  ring

private lemma weighted_tail_eq (k : ℕ) :
    weightedTerm (k + 1) =
      2 ^ (k + 1) / (Nat.factorial k : ℝ) +
        baseTerm (k + 1) := by
  simp only [weightedTerm, baseTerm, Nat.cast_add, Nat.cast_one,
    Nat.factorial_succ]
  have hk : (Nat.factorial k : ℝ) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

private lemma exponentialSeriesOne_eq_exp :
    exponentialSeriesOne = Real.exp 1 := by
  rw [exponentialSeriesOne, Real.exp_eq_exp_ℝ]
  simpa using (NormedSpace.expSeries_div_hasSum_exp (1 : ℝ)).tsum_eq

private lemma baseSeries_eq_exp_two :
    baseSeries = Real.exp 2 := by
  rw [baseSeries, Real.exp_eq_exp_ℝ]
  simpa [baseTerm] using
    (NormedSpace.expSeries_div_hasSum_exp (2 : ℝ)).tsum_eq

theorem gap1 :
    weightedSeries = 1 + shiftedSeries + positiveBaseTail := by
  have hbaseTail :
      Summable (fun k : ℕ => baseTerm (k + 1)) :=
    summable_baseTerm.comp_injective Nat.succ_injective
  have hweightedTail :
      Summable (fun k : ℕ => weightedTerm (k + 1)) := by
    simpa only [weighted_tail_eq] using
      summable_shiftedTerm.add hbaseTail
  have hweighted : Summable weightedTerm := by
    exact (summable_nat_add_iff (f := weightedTerm) 1).mp hweightedTail
  have htail :
      (∑' k : ℕ, weightedTerm (k + 1)) =
        shiftedSeries + positiveBaseTail := by
    calc
      _ = ∑' k : ℕ,
          (2 ^ (k + 1) / (Nat.factorial k : ℝ) +
            baseTerm (k + 1)) := tsum_congr weighted_tail_eq
      _ = (∑' k : ℕ, 2 ^ (k + 1) / (Nat.factorial k : ℝ)) +
          ∑' k : ℕ, baseTerm (k + 1) :=
        summable_shiftedTerm.tsum_add hbaseTail
      _ = shiftedSeries + positiveBaseTail := by
        rfl
  have hsplit := hweighted.sum_add_tsum_nat_add 1
  calc
    weightedSeries =
        weightedTerm 0 + ∑' k : ℕ, weightedTerm (k + 1) := by
      simpa [weightedSeries] using hsplit.symm
    _ = 1 + shiftedSeries + positiveBaseTail := by
      rw [htail]
      norm_num [weightedTerm]
      ring

theorem gap2 :
    1 + shiftedSeries + positiveBaseTail =
      2 * baseSeries + baseSeries := by
  have hshift : shiftedSeries = 2 * baseSeries := by
    calc
      shiftedSeries =
          ∑' k : ℕ, 2 * baseTerm k := by
        apply tsum_congr
        intro k
        simp [baseTerm, pow_succ]
        ring
      _ = 2 * baseSeries := by
        rw [tsum_mul_left]
        rfl
  have hsplit := summable_baseTerm.sum_add_tsum_nat_add 1
  have htail : 1 + positiveBaseTail = baseSeries := by
    simpa [baseSeries, positiveBaseTail, baseTerm] using hsplit
  rw [hshift]
  linarith

theorem gap3 :
    2 * baseSeries + baseSeries = 3 * baseSeries := by
  ring

theorem gap4 :
    weightedSeries = 3 * baseSeries := by
  rw [gap1, gap2, gap3]

theorem gap5 :
    ∃ d : ℕ → ℝ,
      exponentialSeriesOne * exponentialSeriesOne = ∑' n, d n := by
  refine ⟨fun n => if n = 0 then
      exponentialSeriesOne * exponentialSeriesOne else 0, ?_⟩
  simp

theorem gap6 :
    ∃ d : ℕ → ℝ, ∀ n, d n = convolution n := by
  exact ⟨convolution, fun _ => rfl⟩

theorem gap7 :
    ∀ n,
      convolution n =
        1 / (Nat.factorial n : ℝ) *
          ∑ k ∈ Finset.range (n + 1),
            (Nat.factorial n : ℝ) /
              ((Nat.factorial k : ℝ) *
                (Nat.factorial (n - k) : ℝ)) := by
  intro n
  unfold convolution
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hnfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hkfac : (Nat.factorial k : ℝ) ≠ 0 := by positivity
  have hsubfac : (Nat.factorial (n - k) : ℝ) ≠ 0 := by positivity
  field_simp

theorem gap8 :
    ∀ n,
      1 / (Nat.factorial n : ℝ) *
          (∑ k ∈ Finset.range (n + 1),
            (Nat.factorial n : ℝ) /
              ((Nat.factorial k : ℝ) *
                (Nat.factorial (n - k) : ℝ))) =
        chooseConvolution n := by
  intro n
  unfold chooseConvolution
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by
    simp only [Finset.mem_range] at hk
    omega
  exact (Nat.cast_choose ℝ hkn).symm

theorem gap9 :
    ∀ n, chooseConvolution n = 2 ^ n / (Nat.factorial n : ℝ) := by
  intro n
  unfold chooseConvolution
  rw [← Nat.cast_sum, Nat.sum_range_choose]
  push_cast
  ring

theorem gap10 :
    ∃ d : ℕ → ℝ, ∀ n, d n = 2 ^ n / (Nat.factorial n : ℝ) := by
  exact ⟨fun n => 2 ^ n / (Nat.factorial n : ℝ), fun _ => rfl⟩

theorem gap11 :
    baseSeries = exponentialSeriesOne ^ 2 := by
  rw [baseSeries_eq_exp_two, exponentialSeriesOne_eq_exp]
  calc
    Real.exp 2 = Real.exp (1 + 1) := by norm_num
    _ = Real.exp 1 * Real.exp 1 := Real.exp_add 1 1
    _ = Real.exp 1 ^ 2 := by ring

theorem gap12 :
    exponentialSeriesOne ^ 2 = (Real.exp 1) ^ 2 := by
  rw [exponentialSeriesOne_eq_exp]

theorem gap13 :
    baseSeries = (Real.exp 1) ^ 2 := by
  exact gap11.trans gap12

theorem gap14 :
    weightedSeries = 3 * (Real.exp 1) ^ 2 := by
  rw [gap4, gap13]

end

end ProofGap.Exercise2996
