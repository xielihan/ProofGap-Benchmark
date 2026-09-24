import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace ProofGap.Exercise2927

noncomputable section

open scoped BigOperators

def x : ℝ :=
  1 / 5

def logTerm (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * x ^ (n + 1) / (n + 1 : ℕ)

def logPartial (m : ℕ) : ℝ :=
  ∑ n ∈ Finset.range m, logTerm n

def logRemainder (m : ℕ) : ℝ :=
  Real.log (6 / 5 : ℝ) - logPartial m

def nextTermBound (m : ℕ) : ℝ :=
  x ^ (m + 1) / (m + 1 : ℕ)

def Approx (u v ε : ℝ) : Prop :=
  |u - v| < ε

private def positiveTerm (n : ℕ) : ℝ :=
  x ^ (n + 1) / (n + 1 : ℕ)

private theorem hasSum_logTerm :
    HasSum logTerm (Real.log (1 + x)) := by
  have hx : |x| < 1 := by norm_num [x, abs_of_nonneg]
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one
    (x := -x) (by simpa only [abs_neg] using hx)).mul_left (-1)
  convert h using 1
  · ext n
    simp only [logTerm]
    rw [neg_pow, pow_succ]
    push_cast
    ring
  · simp only [sub_neg_eq_add]
    ring

private theorem strictAnti_positiveTerm : StrictAnti positiveTerm := by
  apply strictAnti_nat_of_succ_lt
  intro n
  simp only [positiveTerm, x]
  rw [pow_succ]
  push_cast
  have hp : 0 < (1 / 5 : ℝ) ^ (n + 1) := by positivity
  have hn1 : 0 < (n + 1 : ℝ) := by positivity
  have hn2 : 0 < (n : ℝ) + 1 + 1 := by positivity
  rw [div_lt_div_iff₀ hn2 hn1]
  nlinarith

private theorem logTerm_eq (n : ℕ) :
    logTerm n = (-1 : ℝ) ^ n * positiveTerm n := by
  simp only [logTerm, positiveTerm]
  ring

private theorem logTerm_even (k : ℕ) :
    logTerm (2 * k) = positiveTerm (2 * k) := by
  rw [logTerm_eq]
  simp

private theorem logTerm_odd (k : ℕ) :
    logTerm (2 * k + 1) = -positiveTerm (2 * k + 1) := by
  rw [logTerm_eq]
  rw [pow_add]
  simp

private theorem logPartial_succ (n : ℕ) :
    logPartial (n + 1) = logPartial n + logTerm n := by
  simp [logPartial, Finset.sum_range_succ]

private theorem logPartial_eq_alternating (n : ℕ) :
    logPartial n = ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * positiveTerm i := by
  apply Finset.sum_congr rfl
  intro i hi
  exact logTerm_eq i

private theorem tendsto_logPartial :
    Tendsto logPartial atTop (nhds (Real.log (1 + x))) := by
  exact hasSum_logTerm.tendsto_sum_nat

private theorem logPartial_even_add_two (k : ℕ) :
    logPartial (2 * k + 2) = logPartial (2 * k) +
      positiveTerm (2 * k) - positiveTerm (2 * k + 1) := by
  calc
    logPartial (2 * k + 2) =
        logPartial (2 * k + 1) + logTerm (2 * k + 1) := by
      simpa only [show 2 * k + 2 = (2 * k + 1) + 1 by omega] using
        logPartial_succ (2 * k + 1)
    _ = (logPartial (2 * k) + logTerm (2 * k)) + logTerm (2 * k + 1) := by
      rw [logPartial_succ]
    _ = logPartial (2 * k) + positiveTerm (2 * k) -
        positiveTerm (2 * k + 1) := by
      rw [logTerm_even, logTerm_odd]
      ring

private theorem logPartial_even_add_three (k : ℕ) :
    logPartial (2 * k + 3) = logPartial (2 * k) +
      positiveTerm (2 * k) - positiveTerm (2 * k + 1) +
        positiveTerm (2 * k + 2) := by
  have heven : logTerm (2 * k + 2) = positiveTerm (2 * k + 2) := by
    convert logTerm_even (k + 1) using 1 <;> omega
  calc
    logPartial (2 * k + 3) =
        logPartial (2 * k + 2) + logTerm (2 * k + 2) := by
      simpa only [show 2 * k + 3 = (2 * k + 2) + 1 by omega] using
        logPartial_succ (2 * k + 2)
    _ = logPartial (2 * k) + positiveTerm (2 * k) -
        positiveTerm (2 * k + 1) + positiveTerm (2 * k + 2) := by
      rw [logPartial_even_add_two, heven]

private theorem logPartial_odd_add_one (k : ℕ) :
    logPartial (2 * k + 2) = logPartial (2 * k + 1) -
      positiveTerm (2 * k + 1) := by
  calc
    logPartial (2 * k + 2) =
        logPartial (2 * k + 1) + logTerm (2 * k + 1) := by
      simpa only [show 2 * k + 2 = (2 * k + 1) + 1 by omega] using
        logPartial_succ (2 * k + 1)
    _ = logPartial (2 * k + 1) - positiveTerm (2 * k + 1) := by
      rw [logTerm_odd]
      ring

private theorem logPartial_odd_add_two (k : ℕ) :
    logPartial (2 * k + 3) = logPartial (2 * k + 1) -
      positiveTerm (2 * k + 1) + positiveTerm (2 * k + 2) := by
  have heven : logTerm (2 * k + 2) = positiveTerm (2 * k + 2) := by
    convert logTerm_even (k + 1) using 1 <;> omega
  calc
    logPartial (2 * k + 3) =
        logPartial (2 * k + 2) + logTerm (2 * k + 2) := by
      simpa only [show 2 * k + 3 = (2 * k + 2) + 1 by omega] using
        logPartial_succ (2 * k + 2)
    _ = logPartial (2 * k + 1) - positiveTerm (2 * k + 1) +
        positiveTerm (2 * k + 2) := by
      rw [logPartial_odd_add_one, heven]

private theorem logPartial_odd_add_three (k : ℕ) :
    logPartial (2 * k + 4) = logPartial (2 * k + 1) -
      positiveTerm (2 * k + 1) + positiveTerm (2 * k + 2) -
        positiveTerm (2 * k + 3) := by
  have hodd : logTerm (2 * k + 3) = -positiveTerm (2 * k + 3) := by
    convert logTerm_odd (k + 1) using 1 <;> omega
  calc
    logPartial (2 * k + 4) =
        logPartial (2 * k + 3) + logTerm (2 * k + 3) := by
      simpa only [show 2 * k + 4 = (2 * k + 3) + 1 by omega] using
        logPartial_succ (2 * k + 3)
    _ = logPartial (2 * k + 1) - positiveTerm (2 * k + 1) +
        positiveTerm (2 * k + 2) - positiveTerm (2 * k + 3) := by
      rw [logPartial_odd_add_two, hodd]
      ring

private theorem abs_log_error_lt_positiveTerm (n : ℕ) :
    |Real.log (1 + x) - logPartial n| < positiveTerm n := by
  have ha : Antitone positiveTerm := strictAnti_positiveTerm.antitone
  have hfl : Tendsto
      (fun m => ∑ i ∈ Finset.range m, (-1 : ℝ) ^ i * positiveTerm i)
      atTop (nhds (Real.log (1 + x))) := by
    simpa only [← logPartial_eq_alternating] using tendsto_logPartial
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp hn
    have hlo := ha.alternating_series_le_tendsto hfl (k + 1)
    have hhi := ha.tendsto_le_alternating_series hfl (k + 1)
    rw [← logPartial_eq_alternating] at hlo hhi
    have hlo' : logPartial (2 * k + 2) ≤ Real.log (1 + x) := by
      convert hlo using 1 <;> omega
    have hhi' : Real.log (1 + x) ≤ logPartial (2 * k + 3) := by
      convert hhi using 1 <;> omega
    rw [logPartial_even_add_two] at hlo'
    rw [logPartial_even_add_three] at hhi'
    have h01 : positiveTerm (2 * k + 1) < positiveTerm (2 * k) :=
      strictAnti_positiveTerm (by omega)
    have h12 : positiveTerm (2 * k + 2) < positiveTerm (2 * k + 1) :=
      strictAnti_positiveTerm (by omega)
    have hpos : 0 < Real.log (1 + x) - logPartial (2 * k) := by
      linarith
    rw [abs_of_pos hpos]
    linarith
  · obtain ⟨k, rfl⟩ := odd_iff_exists_bit1.mp hn
    have hlo := ha.alternating_series_le_tendsto hfl (k + 2)
    have hhi := ha.tendsto_le_alternating_series hfl (k + 1)
    rw [← logPartial_eq_alternating] at hlo hhi
    have hlo' : logPartial (2 * k + 4) ≤ Real.log (1 + x) := by
      convert hlo using 1 <;> omega
    have hhi' : Real.log (1 + x) ≤ logPartial (2 * k + 3) := by
      convert hhi using 1 <;> omega
    rw [logPartial_odd_add_three] at hlo'
    rw [logPartial_odd_add_two] at hhi'
    have h01 : positiveTerm (2 * k + 2) < positiveTerm (2 * k + 1) :=
      strictAnti_positiveTerm (by omega)
    have h12 : positiveTerm (2 * k + 3) < positiveTerm (2 * k + 2) :=
      strictAnti_positiveTerm (by omega)
    have hneg : Real.log (1 + x) - logPartial (2 * k + 1) < 0 := by
      linarith
    rw [abs_of_neg hneg]
    linarith

private theorem log_six_fifths_eq :
    Real.log (6 / 5 : ℝ) = Real.log (1 + x) := by
  norm_num [x]

private theorem abs_logRemainder_lt_nextTermBound (n : ℕ) :
    |logRemainder n| < nextTermBound n := by
  rw [logRemainder, log_six_fifths_eq]
  simpa only [nextTermBound, positiveTerm] using
    abs_log_error_lt_positiveTerm n

theorem gap1 :
    Real.log (6 / 5 : ℝ) = Real.log (1 + x) := by
  exact log_six_fifths_eq

theorem gap2 :
    Real.log (1 + x) = ∑' n : ℕ, logTerm n := by
  exact hasSum_logTerm.tsum_eq.symm

theorem gap3 :
    Real.log (6 / 5 : ℝ) = ∑' n : ℕ, logTerm n := by
  rw [log_six_fifths_eq]
  exact hasSum_logTerm.tsum_eq.symm

theorem gap4 :
    ∀ n : ℕ, |logRemainder n| < nextTermBound n := by
  exact abs_logRemainder_lt_nextTermBound

theorem gap5 :
    ∀ n : ℕ, nextTermBound n < (1 / 10 ^ 4 : ℝ) →
      |logRemainder n| < (1 / 10 ^ 4 : ℝ) := by
  intro n hn
  exact (abs_logRemainder_lt_nextTermBound n).trans hn

theorem gap6 :
    ∀ n : ℕ, n = 4 →
      nextTermBound n < (1 / 10 ^ 4 : ℝ) := by
  intro n hn
  subst n
  norm_num [nextTermBound, x]

theorem gap7 :
    ∀ n : ℕ, n = 4 →
      |logRemainder n| < (1 / 10 ^ 4 : ℝ) := by
  intro n hn
  subst n
  exact (abs_logRemainder_lt_nextTermBound 4).trans (by
    norm_num [nextTermBound, x])

theorem gap8 :
    |logRemainder 4| < (1 / 5 : ℝ) * x ^ 5 := by
  convert abs_logRemainder_lt_nextTermBound 4 using 1 <;>
    norm_num [nextTermBound, x]

theorem gap9 :
    (1 / 5 : ℝ) * x ^ 5 < (1 / 10 ^ 4 : ℝ) := by
  norm_num [x]

theorem gap10 :
    |logRemainder 4| < (1 / 10 ^ 4 : ℝ) := by
  exact (abs_logRemainder_lt_nextTermBound 4).trans (by
    norm_num [nextTermBound, x])

theorem gap11 :
    Approx (Real.log (6 / 5 : ℝ)) (logPartial 4)
      (1 / 10 ^ 4 : ℝ) := by
  exact abs_logRemainder_lt_nextTermBound 4 |>.trans (by
    norm_num [nextTermBound, x])

theorem gap12 :
    Approx (logPartial 4) (1823 / 10000 : ℝ)
      (1 / 10 ^ 4 : ℝ) := by
  norm_num [Approx, logPartial, logTerm, x, Finset.sum_range_succ, abs_lt]

theorem gap13 :
    Approx (Real.log (6 / 5 : ℝ)) (1823 / 10000 : ℝ)
      (1 / 10 ^ 4 : ℝ) := by
  rw [log_six_fifths_eq]
  have ha : Antitone positiveTerm := strictAnti_positiveTerm.antitone
  have hfl : Tendsto
      (fun m => ∑ i ∈ Finset.range m, (-1 : ℝ) ^ i * positiveTerm i)
      atTop (nhds (Real.log (1 + x))) := by
    simpa only [← logPartial_eq_alternating] using tendsto_logPartial
  have hlo := ha.alternating_series_le_tendsto hfl 2
  have hhi := ha.tendsto_le_alternating_series hfl 2
  rw [← logPartial_eq_alternating] at hlo hhi
  rw [Approx, abs_lt]
  constructor <;>
    norm_num [logPartial, logTerm, x, Finset.sum_range_succ] at hlo hhi ⊢ <;>
    linarith

end

end ProofGap.Exercise2927
