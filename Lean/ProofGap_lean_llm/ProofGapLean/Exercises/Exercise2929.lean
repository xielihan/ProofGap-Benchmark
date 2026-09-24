import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

namespace ProofGap.Exercise2929

noncomputable section

open scoped BigOperators

def arctanTerm (q : ℕ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n /
    (((2 * n + 1 : ℕ) : ℝ) * (q : ℝ) ^ (2 * n + 1))

def arctanPartial (q m : ℕ) : ℝ :=
  ∑ n ∈ Finset.range m, arctanTerm q n

def firstError : ℝ :=
  |4 * Real.arctan (1 / 2 : ℝ) - 4 * arctanPartial 2 5|

def secondError : ℝ :=
  |4 * Real.arctan (1 / 3 : ℝ) - 4 * arctanPartial 3 4|

def combinedApproximation : ℝ :=
  4 * arctanPartial 2 5 + 4 * arctanPartial 3 4

def combinedError : ℝ :=
  |Real.pi - combinedApproximation|

def Approx (u v ε : ℝ) : Prop :=
  |u - v| < ε

private def arctanMagnitude (q n : ℕ) : ℝ :=
  (1 / (q : ℝ)) ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)

private theorem arctanTerm_eq_alternating (q n : ℕ) :
    arctanTerm q n = (-1 : ℝ) ^ n * arctanMagnitude q n := by
  simp only [arctanTerm, arctanMagnitude]
  ring

private theorem arctanMagnitude_antitone (q : ℕ) (hq : 1 ≤ q) :
    Antitone (arctanMagnitude q) := by
  apply antitone_nat_of_succ_le
  intro n
  simp only [arctanMagnitude]
  have hq0 : (0 : ℝ) < q := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hq1 : (1 / (q : ℝ)) ≤ 1 := by
    rw [div_le_one₀ hq0]
    exact_mod_cast hq
  have hx0 : (0 : ℝ) ≤ 1 / (q : ℝ) := by positivity
  have hp :
      (1 / (q : ℝ)) ^ (2 * (n + 1) + 1) ≤
        (1 / (q : ℝ)) ^ (2 * n + 1) := by
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, pow_add]
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ hx0 hq1)
  have hd0 : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by positivity
  have hd1 :
      ((2 * n + 1 : ℕ) : ℝ) ≤ ((2 * (n + 1) + 1 : ℕ) : ℝ) := by
    norm_num
  exact div_le_div₀ (by positivity) hp hd0 hd1

private theorem arctanTerm_hasSum (q : ℕ) (hq : 1 < q) :
    HasSum (arctanTerm q) (Real.arctan (1 / q : ℝ)) := by
  have hnorm : ‖(1 / q : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact (div_lt_one (by positivity)).2 (by exact_mod_cast hq)
  convert Real.hasSum_arctan hnorm using 1
  funext n
  rw [arctanTerm_eq_alternating]
  simp only [arctanMagnitude]
  ring

private theorem arctan_half_partial_bounds :
    arctanPartial 2 5 - arctanMagnitude 2 5 <
        Real.arctan (1 / 2 : ℝ) ∧
      Real.arctan (1 / 2 : ℝ) < arctanPartial 2 5 := by
  have hlim :
      Filter.Tendsto
        (fun n => ∑ i ∈ Finset.range n,
          (-1 : ℝ) ^ i * arctanMagnitude 2 i)
        Filter.atTop (nhds (Real.arctan (1 / 2 : ℝ))) := by
    simpa only [← arctanTerm_eq_alternating] using
      (arctanTerm_hasSum 2 (by omega)).tendsto_sum_nat
  have hanti := arctanMagnitude_antitone 2 (by omega)
  have hlo := hanti.alternating_series_le_tendsto hlim 4
  have hhi := hanti.tendsto_le_alternating_series hlim 3
  norm_num [arctanPartial, arctanTerm, arctanMagnitude,
    Finset.sum_range_succ] at hlo hhi ⊢
  constructor <;> linarith

private theorem arctan_third_partial_bounds :
    arctanPartial 3 4 < Real.arctan (1 / 3 : ℝ) ∧
      Real.arctan (1 / 3 : ℝ) <
        arctanPartial 3 4 + arctanMagnitude 3 4 := by
  have hlim :
      Filter.Tendsto
        (fun n => ∑ i ∈ Finset.range n,
          (-1 : ℝ) ^ i * arctanMagnitude 3 i)
        Filter.atTop (nhds (Real.arctan (1 / 3 : ℝ))) := by
    simpa only [← arctanTerm_eq_alternating] using
      (arctanTerm_hasSum 3 (by omega)).tendsto_sum_nat
  have hanti := arctanMagnitude_antitone 3 (by omega)
  have hlo := hanti.alternating_series_le_tendsto hlim 3
  have hhi := hanti.tendsto_le_alternating_series hlim 3
  norm_num [arctanPartial, arctanTerm, arctanMagnitude,
    Finset.sum_range_succ] at hlo hhi ⊢
  constructor <;> linarith

theorem gap1 :
    Real.pi / 4 =
      Real.arctan (1 / 2 : ℝ) + Real.arctan (1 / 3 : ℝ) := by
  simpa [div_eq_mul_inv] using Real.arctan_inv_2_add_arctan_inv_3.symm

theorem gap2 :
    Real.pi =
      4 * (∑' n : ℕ, arctanTerm 2 n) +
        4 * ∑' n : ℕ, arctanTerm 3 n := by
  have h2 := (arctanTerm_hasSum 2 (by omega)).tsum_eq
  have h3 := (arctanTerm_hasSum 3 (by omega)).tsum_eq
  rw [h2, h3]
  nlinarith [Real.arctan_inv_2_add_arctan_inv_3]

theorem gap3 :
    0 < firstError := by
  rw [firstError, abs_pos]
  intro hzero
  have hlt := arctan_half_partial_bounds.2
  nlinarith

theorem gap4 :
    firstError < 4 / (11 * 2 ^ 11 : ℝ) := by
  rw [firstError, abs_of_neg]
  · have hlo := arctan_half_partial_bounds.1
    norm_num [arctanMagnitude] at hlo ⊢
    nlinarith
  · have hhi := arctan_half_partial_bounds.2
    nlinarith

theorem gap5 :
    (4 / (11 * 2 ^ 11 : ℝ)) < (2 / 10000 : ℝ) := by
  norm_num

theorem gap6 :
    (0 : ℝ) < 2 / 10000 := by
  norm_num

theorem gap7 :
    0 < secondError := by
  rw [secondError, abs_pos]
  intro hzero
  have hlt := arctan_third_partial_bounds.1
  nlinarith

theorem gap8 :
    secondError < 4 / (9 * 3 ^ 9 : ℝ) := by
  rw [secondError, abs_of_pos]
  · have hhi := arctan_third_partial_bounds.2
    norm_num [arctanMagnitude] at hhi ⊢
    nlinarith
  · have hlo := arctan_third_partial_bounds.1
    nlinarith

theorem gap9 :
    (4 / (9 * 3 ^ 9 : ℝ)) < (3 / 100000 : ℝ) := by
  norm_num

theorem gap10 :
    (0 : ℝ) < 3 / 100000 := by
  norm_num

theorem gap11 :
    combinedError ≤ firstError + secondError := by
  unfold combinedError combinedApproximation firstError secondError
  calc
    |Real.pi - (4 * arctanPartial 2 5 + 4 * arctanPartial 3 4)| =
        |(4 * Real.arctan (1 / 2 : ℝ) - 4 * arctanPartial 2 5) +
          (4 * Real.arctan (1 / 3 : ℝ) - 4 * arctanPartial 3 4)| := by
            congr 1
            nlinarith [gap1]
    _ ≤ |4 * Real.arctan (1 / 2 : ℝ) - 4 * arctanPartial 2 5| +
          |4 * Real.arctan (1 / 3 : ℝ) - 4 * arctanPartial 3 4| :=
      abs_add_le _ _

theorem gap12 :
    firstError + secondError < (1 / 1000 : ℝ) := by
  nlinarith [gap4.trans gap5, gap8.trans gap9]

theorem gap13 :
    combinedError < (1 / 1000 : ℝ) := by
  exact gap11.trans_lt gap12

theorem gap14 :
    (31415 / 10000 : ℝ) < Real.pi := by
  nlinarith [Real.pi_gt_d4]

theorem gap15 :
    Real.pi < (31420 / 10000 : ℝ) := by
  nlinarith [Real.pi_lt_d4]

theorem gap16 :
    (31415 / 10000 : ℝ) < (31420 / 10000 : ℝ) := by
  norm_num

theorem gap17 :
    Approx Real.pi (3142 / 1000 : ℝ)
      (1 / 1000 : ℝ) := by
  rw [Approx, abs_lt]
  constructor <;> nlinarith [gap14, gap15]

end

end ProofGap.Exercise2929
