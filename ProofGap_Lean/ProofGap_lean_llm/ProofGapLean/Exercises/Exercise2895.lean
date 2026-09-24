import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace ProofGap.Exercise2895

noncomputable section

open scoped BigOperators

def legendreTerm (n k : ℕ) (t : ℝ) : ℝ :=
  (-1 : ℝ) ^ k * (Nat.factorial (2 * n - 2 * k) : ℝ) /
      ((2 : ℝ) ^ n * (Nat.factorial k : ℝ) *
        (Nat.factorial (n - k) : ℝ) *
        (Nat.factorial (n - 2 * k) : ℝ)) *
    t ^ (n - 2 * k)

def P (n : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n / 2 + 1), legendreTerm n k t

def generatingTerm (x t : ℝ) (n : ℕ) : ℝ :=
  P n t * x ^ n

def derivativeGeneratingTerm (x t : ℝ) (k : ℕ) : ℝ :=
  let n : ℕ := k + 1
  (n : ℝ) * P n t * x ^ k

def oddDoubleFactorial (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (2 * k + 1 : ℕ)

def normalizedLegendreTerm (n k : ℕ) (t : ℝ) : ℝ :=
  (-1 : ℝ) ^ k * (Nat.factorial n : ℝ) ^ 2 *
      (Nat.factorial (2 * n - 2 * k) : ℝ) /
      ((Nat.factorial k : ℝ) * (Nat.factorial (n - k) : ℝ) *
        (Nat.factorial (n - 2 * k) : ℝ) *
        (Nat.factorial (2 * n) : ℝ)) *
    t ^ (n - 2 * k)

def normalizedLegendrePolynomial (n : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n / 2 + 1), normalizedLegendreTerm n k t

private theorem even_factorial_eq (n : ℕ) :
    (Nat.factorial (2 * n) : ℝ) =
      (2 : ℝ) ^ n * (Nat.factorial n : ℝ) * oddDoubleFactorial n := by
  induction n with
  | zero =>
      norm_num [oddDoubleFactorial]
  | succ n ih =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
        Nat.factorial_succ]
      rw [show 2 * n + 1 = 2 * n + 1 by rfl, Nat.factorial_succ]
      push_cast
      rw [ih, pow_succ, Nat.factorial_succ]
      simp only [oddDoubleFactorial, Finset.prod_range_succ]
      push_cast
      ring

private def legendreCoeff (n k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * (Nat.factorial (2 * n - 2 * k) : ℝ) /
    ((2 : ℝ) ^ n * (Nat.factorial k : ℝ) *
      (Nat.factorial (n - k) : ℝ) *
      (Nat.factorial (n - 2 * k) : ℝ))

private theorem legendreTerm_eq_coeff (n k : ℕ) (t : ℝ) :
    legendreTerm n k t = legendreCoeff n k * t ^ (n - 2 * k) := by
  rfl

private theorem legendreCoeff_succ
    (n k : ℕ) (hk : 2 * k ≤ n) :
    ((n - 2 * k + 1 : ℕ) : ℝ) * legendreCoeff (n + 1) k =
      ((2 * (n - k) + 1 : ℕ) : ℝ) * legendreCoeff n k := by
  have hnum :
      Nat.factorial (2 * (n + 1) - 2 * k) =
        (2 * n - 2 * k + 2) * (2 * n - 2 * k + 1) *
          Nat.factorial (2 * n - 2 * k) := by
    rw [show 2 * (n + 1) - 2 * k = (2 * n - 2 * k + 1) + 1 by omega,
      Nat.factorial_succ]
    rw [show 2 * n - 2 * k + 1 = (2 * n - 2 * k) + 1 by omega,
      Nat.factorial_succ]
    ring
  have hnk :
      Nat.factorial (n + 1 - k) =
        (n - k + 1) * Nat.factorial (n - k) := by
    rw [show n + 1 - k = (n - k) + 1 by omega, Nat.factorial_succ]
  have hn2k :
      Nat.factorial (n + 1 - 2 * k) =
        (n - 2 * k + 1) * Nat.factorial (n - 2 * k) := by
    rw [show n + 1 - 2 * k = (n - 2 * k) + 1 by omega,
      Nat.factorial_succ]
  unfold legendreCoeff
  rw [hnum, hnk, hn2k, pow_succ]
  rw [show 2 * n - 2 * k = 2 * (n - k) by omega]
  push_cast
  field_simp

private theorem legendreCoeff_pred
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : 2 * k ≤ n) :
    ((n - 2 * k + 1 : ℕ) : ℝ) * legendreCoeff (n - 1) (k - 1) =
      -((2 * k : ℕ) : ℝ) * legendreCoeff n k := by
  have hnum :
      2 * (n - 1) - 2 * (k - 1) = 2 * n - 2 * k := by
    omega
  have hnk :
      n - 1 - (k - 1) = n - k := by
    omega
  have hn2k :
      n - 1 - 2 * (k - 1) = n - 2 * k + 1 := by
    omega
  have hfac_k :
      Nat.factorial k = k * Nat.factorial (k - 1) := by
    calc
      Nat.factorial k = Nat.factorial ((k - 1) + 1) := by
        congr 1
        omega
      _ = ((k - 1) + 1) * Nat.factorial (k - 1) :=
        Nat.factorial_succ _
      _ = k * Nat.factorial (k - 1) := by
        congr 1
        omega
  have hfac_b :
      Nat.factorial (n - 2 * k + 1) =
        (n - 2 * k + 1) * Nat.factorial (n - 2 * k) := by
    rw [show n - 2 * k + 1 = (n - 2 * k) + 1 by omega,
      Nat.factorial_succ]
  have hpow :
      (2 : ℝ) ^ n = 2 ^ (n - 1) * 2 := by
    calc
      (2 : ℝ) ^ n = 2 ^ ((n - 1) + 1) := by
        congr 1
        omega
      _ = 2 ^ (n - 1) * 2 := pow_succ _ _
  have hsign :
      (-1 : ℝ) ^ k = -((-1 : ℝ) ^ (k - 1)) := by
    calc
      (-1 : ℝ) ^ k = (-1) ^ ((k - 1) + 1) := by
        congr 1
        omega
      _ = -((-1 : ℝ) ^ (k - 1)) := by
        rw [pow_succ]
        ring
  unfold legendreCoeff
  rw [hnum, hnk, hn2k, hfac_k, hfac_b, hpow, hsign]
  push_cast
  field_simp

private theorem legendreCoeff_recurrence_zero (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * legendreCoeff (n + 1) 0 =
      ((2 * n + 1 : ℕ) : ℝ) * legendreCoeff n 0 := by
  simpa using legendreCoeff_succ n 0 (by omega)

private theorem legendreCoeff_recurrence_pos
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : 2 * k ≤ n) :
    ((n + 1 : ℕ) : ℝ) * legendreCoeff (n + 1) k =
      ((2 * n + 1 : ℕ) : ℝ) * legendreCoeff n k -
        (n : ℝ) * legendreCoeff (n - 1) (k - 1) := by
  have hs := legendreCoeff_succ n k hkn
  have hp := legendreCoeff_pred n k hn hk hkn
  let q : ℝ := ((n - 2 * k + 1 : ℕ) : ℝ)
  have hq : q ≠ 0 := by
    dsimp [q]
    positivity
  have hnk_cast :
      ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
    rw [Nat.cast_sub (by omega)]
  have hn2k_cast :
      ((n - 2 * k : ℕ) : ℝ) = (n : ℝ) - 2 * (k : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have halg :
      ((n + 1 : ℕ) : ℝ) * ((2 * (n - k) + 1 : ℕ) : ℝ) =
        ((2 * n + 1 : ℕ) : ℝ) * q +
          (n : ℝ) * ((2 * k : ℕ) : ℝ) := by
    dsimp [q]
    push_cast
    rw [hnk_cast, hn2k_cast]
    ring
  have hpq :
      q * legendreCoeff (n - 1) (k - 1) =
        -((2 * k : ℕ) : ℝ) * legendreCoeff n k := by
    simpa only [q] using hp
  apply (mul_left_cancel₀ hq)
  calc
    q * (((n + 1 : ℕ) : ℝ) * legendreCoeff (n + 1) k) =
        ((n + 1 : ℕ) : ℝ) *
          (q * legendreCoeff (n + 1) k) := by ring
    _ = ((n + 1 : ℕ) : ℝ) *
          (((2 * (n - k) + 1 : ℕ) : ℝ) *
            legendreCoeff n k) := by
      rw [show q = ((n - 2 * k + 1 : ℕ) : ℝ) by rfl, hs]
    _ = (((n + 1 : ℕ) : ℝ) *
          ((2 * (n - k) + 1 : ℕ) : ℝ)) *
            legendreCoeff n k := by ring
    _ = (((2 * n + 1 : ℕ) : ℝ) * q +
          (n : ℝ) * ((2 * k : ℕ) : ℝ)) *
            legendreCoeff n k := by rw [halg]
    _ = ((2 * n + 1 : ℕ) : ℝ) * q * legendreCoeff n k +
          (n : ℝ) * ((2 * k : ℕ) : ℝ) *
            legendreCoeff n k := by ring
    _ = ((2 * n + 1 : ℕ) : ℝ) * q * legendreCoeff n k -
          (n : ℝ) *
            (q * legendreCoeff (n - 1) (k - 1)) := by
      rw [hpq]
      ring
    _ = q * (((2 * n + 1 : ℕ) : ℝ) * legendreCoeff n k -
          (n : ℝ) * legendreCoeff (n - 1) (k - 1)) := by
      ring

private theorem legendreTerm_recurrence_zero (n : ℕ) (t : ℝ) :
    ((n + 1 : ℕ) : ℝ) * legendreTerm (n + 1) 0 t =
      ((2 * n + 1 : ℕ) : ℝ) * t * legendreTerm n 0 t := by
  rw [legendreTerm_eq_coeff, legendreTerm_eq_coeff]
  rw [show n + 1 - 2 * 0 = n + 1 by omega,
    show n - 2 * 0 = n by omega, pow_succ]
  linear_combination t ^ (n + 1) * legendreCoeff_recurrence_zero n

private theorem legendreTerm_recurrence_pos
    (n k : ℕ) (t : ℝ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : 2 * k ≤ n) :
    ((n + 1 : ℕ) : ℝ) * legendreTerm (n + 1) k t =
      ((2 * n + 1 : ℕ) : ℝ) * t * legendreTerm n k t -
        (n : ℝ) * legendreTerm (n - 1) (k - 1) t := by
  rw [legendreTerm_eq_coeff, legendreTerm_eq_coeff,
    legendreTerm_eq_coeff]
  rw [show n + 1 - 2 * k = (n - 2 * k) + 1 by omega,
    show n - 1 - 2 * (k - 1) = (n - 2 * k) + 1 by omega,
    pow_succ]
  linear_combination
    t ^ (n - 2 * k + 1) *
      legendreCoeff_recurrence_pos n k hn hk hkn

private theorem legendreCoeff_boundary
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hboundary : 2 * k = n + 1) :
    ((n + 1 : ℕ) : ℝ) * legendreCoeff (n + 1) k =
      -(n : ℝ) * legendreCoeff (n - 1) (k - 1) := by
  have hprev :=
    legendreCoeff_succ (n - 1) (k - 1) (by omega)
  have hnext :=
    legendreCoeff_pred (n + 1) k (by omega) hk (by omega)
  have hprev_factor :
      n - 1 - 2 * (k - 1) + 1 = 1 := by omega
  have hprev_index : n - 1 + 1 = n := by omega
  have hprev_scale :
      2 * (n - 1 - (k - 1)) + 1 = n := by omega
  have hnext_factor : n + 1 - 2 * k + 1 = 1 := by omega
  have hnext_index : n + 1 - 1 = n := by omega
  have hprev' :
      legendreCoeff n (k - 1) =
        (n : ℝ) * legendreCoeff (n - 1) (k - 1) := by
    rw [hprev_factor, hprev_index, hprev_scale] at hprev
    simpa using hprev
  have hnext' :
      legendreCoeff n (k - 1) =
        -((n + 1 : ℕ) : ℝ) * legendreCoeff (n + 1) k := by
    rw [hnext_factor, hnext_index, hboundary] at hnext
    simpa using hnext
  calc
    ((n + 1 : ℕ) : ℝ) * legendreCoeff (n + 1) k =
        -(-((n + 1 : ℕ) : ℝ) * legendreCoeff (n + 1) k) := by
      ring
    _ = -legendreCoeff n (k - 1) := by rw [hnext']
    _ = -(n : ℝ) * legendreCoeff (n - 1) (k - 1) := by
      rw [hprev']
      ring

private theorem legendreTerm_boundary
    (n k : ℕ) (t : ℝ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hboundary : 2 * k = n + 1) :
    ((n + 1 : ℕ) : ℝ) * legendreTerm (n + 1) k t =
      -(n : ℝ) * legendreTerm (n - 1) (k - 1) t := by
  rw [legendreTerm_eq_coeff, legendreTerm_eq_coeff]
  rw [show n + 1 - 2 * k = 0 by omega,
    show n - 1 - 2 * (k - 1) = 0 by omega]
  norm_num
  simpa only [Nat.cast_add, Nat.cast_one, neg_mul] using
    legendreCoeff_boundary n k hn hk hboundary

private theorem P_recurrence_even (m : ℕ) (hm : 1 ≤ m) (t : ℝ) :
    (((2 * m) + 1 : ℕ) : ℝ) * P ((2 * m) + 1) t =
      ((2 * (2 * m) + 1 : ℕ) : ℝ) * t * P (2 * m) t -
        ((2 * m : ℕ) : ℝ) * P ((2 * m) - 1) t := by
  let n : ℕ := 2 * m
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hnext_range : (n + 1) / 2 + 1 = m + 1 := by
    dsimp [n]
    omega
  have hcurrent_range : n / 2 + 1 = m + 1 := by
    dsimp [n]
    omega
  have hprev_range : (n - 1) / 2 + 1 = m := by
    dsimp [n]
    omega
  have hzero :
      (((n + 1 : ℕ) : ℝ) * legendreTerm (n + 1) 0 t =
        ((2 * n + 1 : ℕ) : ℝ) * t * legendreTerm n 0 t) :=
    legendreTerm_recurrence_zero n t
  have hshift :
      ((n + 1 : ℕ) : ℝ) *
          (∑ j ∈ Finset.range m, legendreTerm (n + 1) (j + 1) t) =
        ((2 * n + 1 : ℕ) : ℝ) * t *
            (∑ j ∈ Finset.range m, legendreTerm n (j + 1) t) -
          (n : ℝ) *
            (∑ j ∈ Finset.range m, legendreTerm (n - 1) j t) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < m := Finset.mem_range.mp hj
    simpa [Nat.add_sub_cancel] using
      legendreTerm_recurrence_pos n (j + 1) t hn (by omega) (by
        dsimp [n]
        omega)
  change
    ((n + 1 : ℕ) : ℝ) * P (n + 1) t =
      ((2 * n + 1 : ℕ) : ℝ) * t * P n t -
        (n : ℝ) * P (n - 1) t
  rw [P, P, P, hnext_range, hcurrent_range, hprev_range]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  linear_combination hzero + hshift

private theorem P_recurrence_odd (m : ℕ) (t : ℝ) :
    (((2 * m + 1) + 1 : ℕ) : ℝ) * P ((2 * m + 1) + 1) t =
      ((2 * (2 * m + 1) + 1 : ℕ) : ℝ) * t * P (2 * m + 1) t -
        ((2 * m + 1 : ℕ) : ℝ) * P ((2 * m + 1) - 1) t := by
  let n : ℕ := 2 * m + 1
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hnext_range : (n + 1) / 2 + 1 = m + 2 := by
    dsimp [n]
    omega
  have hcurrent_range : n / 2 + 1 = m + 1 := by
    dsimp [n]
    omega
  have hprev_range : (n - 1) / 2 + 1 = m + 1 := by
    dsimp [n]
    omega
  have hzero :
      (((n + 1 : ℕ) : ℝ) * legendreTerm (n + 1) 0 t =
        ((2 * n + 1 : ℕ) : ℝ) * t * legendreTerm n 0 t) :=
    legendreTerm_recurrence_zero n t
  have hshift :
      ((n + 1 : ℕ) : ℝ) *
          (∑ j ∈ Finset.range m, legendreTerm (n + 1) (j + 1) t) =
        ((2 * n + 1 : ℕ) : ℝ) * t *
            (∑ j ∈ Finset.range m, legendreTerm n (j + 1) t) -
          (n : ℝ) *
            (∑ j ∈ Finset.range m, legendreTerm (n - 1) j t) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < m := Finset.mem_range.mp hj
    simpa [Nat.add_sub_cancel] using
      legendreTerm_recurrence_pos n (j + 1) t hn (by omega) (by
        dsimp [n]
        omega)
  have hboundary :
      ((n + 1 : ℕ) : ℝ) * legendreTerm (n + 1) (m + 1) t =
        -(n : ℝ) * legendreTerm (n - 1) m t := by
    apply legendreTerm_boundary n (m + 1) t hn (by omega)
    dsimp [n]
    omega
  have hnext_sum :
      (∑ k ∈ Finset.range (m + 2), legendreTerm (n + 1) k t) =
        legendreTerm (n + 1) 0 t +
          (∑ j ∈ Finset.range m, legendreTerm (n + 1) (j + 1) t) +
          legendreTerm (n + 1) (m + 1) t := by
    rw [show m + 2 = (m + 1) + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ']
    ring
  have hcurrent_sum :
      (∑ k ∈ Finset.range (m + 1), legendreTerm n k t) =
        legendreTerm n 0 t +
          ∑ j ∈ Finset.range m, legendreTerm n (j + 1) t := by
    rw [Finset.sum_range_succ']
    ring
  have hprev_sum :
      (∑ k ∈ Finset.range (m + 1), legendreTerm (n - 1) k t) =
        (∑ j ∈ Finset.range m, legendreTerm (n - 1) j t) +
          legendreTerm (n - 1) m t := by
    rw [Finset.sum_range_succ]
  change
    ((n + 1 : ℕ) : ℝ) * P (n + 1) t =
      ((2 * n + 1 : ℕ) : ℝ) * t * P n t -
        (n : ℝ) * P (n - 1) t
  rw [P, P, P, hnext_range, hcurrent_range, hprev_range,
    hnext_sum, hcurrent_sum, hprev_sum]
  linear_combination hzero + hshift + hboundary

private theorem P_recurrence (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    ((n + 1 : ℕ) : ℝ) * P (n + 1) t =
      ((2 * n + 1 : ℕ) : ℝ) * t * P n t -
        (n : ℝ) * P (n - 1) t := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
  · subst n
    exact P_recurrence_even m (by omega) t
  · subst n
    exact P_recurrence_odd m t

private theorem descProd_neg_half (n : ℕ) :
    (∏ j ∈ Finset.range n, ((-1 / 2 : ℝ) - j)) =
      (-1 : ℝ) ^ n * oddDoubleFactorial n / (2 : ℝ) ^ n := by
  induction n with
  | zero =>
      norm_num [oddDoubleFactorial]
  | succ n ih =>
      rw [Finset.prod_range_succ, ih, pow_succ, pow_succ]
      simp only [oddDoubleFactorial, Finset.prod_range_succ]
      push_cast
      field_simp
      ring

private theorem choose_neg_half (n : ℕ) :
    Ring.choose (-1 / 2 : ℝ) n =
      (-1 : ℝ) ^ n * oddDoubleFactorial n /
        ((2 : ℝ) ^ n * (Nat.factorial n : ℝ)) := by
  rw [Ring.choose_eq_smul]
  simp only [smul_eq_mul]
  have hsmeval :
      (descPochhammer ℤ n).smeval (-1 / 2 : ℝ) =
        ∏ j ∈ Finset.range n, ((-1 / 2 : ℝ) - j) := by
    induction n with
    | zero =>
        simp
    | succ n ih =>
        rw [descPochhammer_succ_right, Polynomial.smeval_mul,
          Polynomial.smeval_sub, Polynomial.smeval_X,
          Polynomial.smeval_natCast, ih, Finset.prod_range_succ]
        simp
  rw [hsmeval, descProd_neg_half]
  field_simp

private theorem oddDoubleFactorial_hasSum
    (z : ℝ) (hz : |2 * z| < 1) :
    HasSum
      (fun n : ℕ =>
        oddDoubleFactorial n / (Nat.factorial n : ℝ) * z ^ n)
      (1 / Real.sqrt (1 - 2 * z)) := by
  have hseries :=
    Real.one_add_rpow_hasFPowerSeriesOnBall_zero
      (a := (-1 / 2 : ℝ))
  have hzmem : -2 * z ∈ Metric.eball (0 : ℝ) 1 := by
    simp only [Metric.mem_eball, edist_dist, dist_zero_right,
      ENNReal.ofReal_lt_one]
    simpa [Real.norm_eq_abs, abs_neg] using hz
  have hs := hseries.hasSum hzmem
  have hterm : ∀ n : ℕ,
      (binomialSeries ℝ (-1 / 2 : ℝ) n) (fun _ => -2 * z) =
        oddDoubleFactorial n / (Nat.factorial n : ℝ) * z ^ n := by
    intro n
    rw [binomialSeries_apply, choose_neg_half]
    simp only [List.ofFn_const, List.prod_replicate, smul_eq_mul]
    rw [mul_pow]
    field_simp
    have hsign : (-2 : ℝ) ^ n * (-1 : ℝ) ^ n = 2 ^ n := by
      rw [← mul_pow]
      norm_num
    calc
      (-1 : ℝ) ^ n * oddDoubleFactorial n * (-2 : ℝ) ^ n * z ^ n =
          oddDoubleFactorial n * z ^ n *
            ((-2 : ℝ) ^ n * (-1 : ℝ) ^ n) := by ring
      _ = oddDoubleFactorial n * 2 ^ n * z ^ n := by
        rw [hsign]
        ring
  have hbase : 0 < 1 - 2 * z := by
    have hz' : 2 * z < 1 := le_abs_self (2 * z) |>.trans_lt hz
    linarith
  have hvalue :
      (1 + -2 * z) ^ (-1 / 2 : ℝ) =
        1 / Real.sqrt (1 - 2 * z) := by
    rw [show 1 + -2 * z = 1 - 2 * z by ring, Real.sqrt_eq_rpow]
    rw [one_div, ← Real.rpow_neg hbase.le]
    congr 1
    ring
  have hs' :
      HasSum
        (fun n => (binomialSeries ℝ (-1 / 2 : ℝ) n) (fun _ => -2 * z))
        ((1 + -2 * z) ^ (-1 / 2 : ℝ)) := by
    simpa only [zero_add] using hs
  rw [hvalue] at hs'
  exact hs'.congr_fun (fun n => (hterm n).symm)

private def rawTerm (t x : ℝ) (p : Σ m : ℕ, Fin (m + 1)) : ℝ :=
  oddDoubleFactorial p.1 / (Nat.factorial p.1 : ℝ) *
    (Nat.choose p.1 p.2 : ℝ) *
    (t * x) ^ (p.1 - p.2) *
    (-x ^ 2 / 2) ^ (p.2 : ℕ)

private theorem oddTerm_expand (t x : ℝ) (m : ℕ) :
    oddDoubleFactorial m / (Nat.factorial m : ℝ) *
        (t * x - x ^ 2 / 2) ^ m =
      ∑ k : Fin (m + 1), rawTerm t x ⟨m, k⟩ := by
  simp only [rawTerm]
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ =>
      oddDoubleFactorial m / (Nat.factorial m : ℝ) *
        (Nat.choose m k : ℝ) *
        (t * x) ^ (m - k) *
        (-x ^ 2 / 2) ^ k)]
  rw [show t * x - x ^ 2 / 2 = -x ^ 2 / 2 + t * x by ring]
  rw [add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private def triangularEquiv :
    (Σ m : ℕ, Fin (m + 1)) ≃ (Σ n : ℕ, Fin (n / 2 + 1)) where
  toFun p :=
    ⟨p.1 + p.2, ⟨p.2, by
      have hp := p.2.isLt
      omega⟩⟩
  invFun q :=
    ⟨q.1 - q.2, ⟨q.2, by
      have hq := q.2.isLt
      omega⟩⟩
  left_inv p := by
    rcases p with ⟨m, k⟩
    change
      (⟨(m + (k : ℕ)) - (k : ℕ), ⟨(k : ℕ), _⟩⟩ :
        Σ m : ℕ, Fin (m + 1)) = ⟨m, k⟩
    have hm : m + (k : ℕ) - (k : ℕ) = m :=
      Nat.add_sub_cancel_right m k
    refine Sigma.ext hm ?_
    exact (Fin.heq_ext_iff (congrArg (fun j => j + 1) hm)).2 rfl
  right_inv q := by
    rcases q with ⟨n, k⟩
    have hk : (k : ℕ) ≤ n := by
      have hq := k.isLt
      omega
    change
      (⟨(n - (k : ℕ)) + (k : ℕ), ⟨(k : ℕ), _⟩⟩ :
        Σ n : ℕ, Fin (n / 2 + 1)) = ⟨n, k⟩
    have hn : n - (k : ℕ) + (k : ℕ) = n :=
      Nat.sub_add_cancel hk
    refine Sigma.ext hn ?_
    exact
      (Fin.heq_ext_iff
        (congrArg (fun j => j / 2 + 1) hn)).2 rfl

private theorem rawTerm_eq_legendreTerm
    (t x : ℝ) (p : Σ m : ℕ, Fin (m + 1)) :
    rawTerm t x p =
      legendreTerm (p.1 + p.2) p.2 t * x ^ (p.1 + p.2) := by
  rcases p with ⟨m, k⟩
  have hk : (k : ℕ) ≤ m := by
    have hk' := k.isLt
    omega
  simp only [rawTerm, legendreTerm, Sigma.fst, Sigma.snd]
  rw [show 2 * (m + (k : ℕ)) - 2 * (k : ℕ) = 2 * m by omega]
  rw [show m + (k : ℕ) - (k : ℕ) = m by omega]
  rw [show m + (k : ℕ) - 2 * (k : ℕ) = m - (k : ℕ) by omega]
  rw [even_factorial_eq, Nat.cast_choose ℝ hk]
  rw [mul_pow, div_pow]
  rw [show (-x ^ 2) ^ (k : ℕ) =
      (-1 : ℝ) ^ (k : ℕ) * x ^ (2 * (k : ℕ)) by
        rw [show -x ^ 2 = (-1 : ℝ) * x ^ 2 by ring, mul_pow, pow_mul]]
  have hx : x ^ (m + (k : ℕ)) =
      x ^ (m - (k : ℕ)) * x ^ (2 * (k : ℕ)) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hx]
  have htwo : (2 : ℝ) ^ (m + (k : ℕ)) =
      2 ^ m * 2 ^ (k : ℕ) := by
    rw [pow_add]
  rw [htwo]
  field_simp

private theorem sum_norm_rawTerm (t x : ℝ) (m : ℕ) :
    (∑ k : Fin (m + 1), ‖rawTerm t x ⟨m, k⟩‖) =
      oddDoubleFactorial m / (Nat.factorial m : ℝ) *
        (|t * x| + x ^ 2 / 2) ^ m := by
  simp only [rawTerm]
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ =>
      ‖oddDoubleFactorial m / (Nat.factorial m : ℝ) *
        (Nat.choose m k : ℝ) *
        (t * x) ^ (m - k) *
        (-x ^ 2 / 2) ^ k‖)]
  rw [show |t * x| + x ^ 2 / 2 = x ^ 2 / 2 + |t * x| by ring]
  rw [add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hodd : 0 ≤ oddDoubleFactorial m := by
    unfold oddDoubleFactorial
    positivity
  have hfac : 0 ≤ (Nat.factorial m : ℝ) := by positivity
  have hchoose : 0 ≤ (Nat.choose m k : ℝ) := by positivity
  have hx : 0 ≤ x ^ 2 / 2 := by positivity
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow]
  simp only [Real.norm_eq_abs, abs_of_nonneg hodd, abs_of_nonneg hfac,
    abs_of_nonneg hchoose, abs_div, abs_neg]
  norm_num
  ring

private theorem rawTerm_summable
    (t x : ℝ) (h : x ^ 2 + 2 * |t * x| < 1) :
    Summable (rawTerm t x) := by
  apply Summable.of_norm
  rw [summable_sigma_of_nonneg (fun p => norm_nonneg (rawTerm t x p))]
  constructor
  · intro m
    exact (hasSum_fintype (fun k => ‖rawTerm t x ⟨m, k⟩‖)).summable
  ·
    have hq : 0 ≤ |t * x| + x ^ 2 / 2 := by positivity
    have hz : |2 * (|t * x| + x ^ 2 / 2)| < 1 := by
      rw [abs_of_nonneg (mul_nonneg (by norm_num) hq)]
      nlinarith
    have hs :=
      (oddDoubleFactorial_hasSum (|t * x| + x ^ 2 / 2) hz).summable
    simpa only [tsum_fintype, sum_norm_rawTerm] using hs

private theorem rawTerm_symm_eq
    (t x : ℝ) (q : Σ n : ℕ, Fin (n / 2 + 1)) :
    rawTerm t x (triangularEquiv.symm q) =
      legendreTerm q.1 q.2 t * x ^ q.1 := by
  rw [rawTerm_eq_legendreTerm]
  have he := triangularEquiv.apply_symm_apply q
  have hn :
      (triangularEquiv.symm q).1 + (triangularEquiv.symm q).2 = q.1 :=
    congrArg Sigma.fst he
  have hk :
      ((triangularEquiv.symm q).2 : ℕ) = (q.2 : ℕ) :=
    congrArg (fun r => (r.2 : ℕ)) he
  rw [hn, hk]

private theorem generating_hasSum
    (x t : ℝ) (h : x ^ 2 + 2 * |t * x| < 1) :
    HasSum (generatingTerm x t)
      (1 / Real.sqrt (1 - 2 * t * x + x ^ 2)) := by
  have hzle :
      |2 * (t * x - x ^ 2 / 2)| ≤ 2 * |t * x| + x ^ 2 := by
    calc
      |2 * (t * x - x ^ 2 / 2)| = |2 * (t * x) - x ^ 2| := by
        congr 1
        ring
      _ ≤ |2 * (t * x)| + |x ^ 2| := abs_sub _ _
      _ = 2 * |t * x| + x ^ 2 := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg x)]
        norm_num
  have hz : |2 * (t * x - x ^ 2 / 2)| < 1 :=
    hzle.trans_lt (by linarith)
  have houter :
      HasSum
        (fun m : ℕ =>
          oddDoubleFactorial m / (Nat.factorial m : ℝ) *
            (t * x - x ^ 2 / 2) ^ m)
        (1 / Real.sqrt (1 - 2 * t * x + x ^ 2)) := by
    have hs :=
      oddDoubleFactorial_hasSum (t * x - x ^ 2 / 2) hz
    rw [show 1 - 2 * (t * x - x ^ 2 / 2) =
      1 - 2 * t * x + x ^ 2 by ring] at hs
    exact hs
  have hsigma :
      HasSum (rawTerm t x)
        (1 / Real.sqrt (1 - 2 * t * x + x ^ 2)) := by
    refine houter.sigma_of_hasSum (fun m => ?_) (rawTerm_summable t x h)
    rw [oddTerm_expand]
    exact hasSum_fintype _
  have hreindexed :
      HasSum (rawTerm t x ∘ triangularEquiv.symm)
        (1 / Real.sqrt (1 - 2 * t * x + x ^ 2)) :=
    triangularEquiv.symm.hasSum_iff.mpr hsigma
  have hterms :
      HasSum
        (fun q : Σ n : ℕ, Fin (n / 2 + 1) =>
          legendreTerm q.1 q.2 t * x ^ q.1)
        (1 / Real.sqrt (1 - 2 * t * x + x ^ 2)) := by
    exact hreindexed.congr_fun (fun q => (rawTerm_symm_eq t x q).symm)
  have hfiber (n : ℕ) :
      HasSum
        (fun k : Fin (n / 2 + 1) => legendreTerm n k t * x ^ n)
        (generatingTerm x t n) := by
    unfold generatingTerm P
    rw [Finset.sum_mul]
    convert hasSum_fintype
      (fun k : Fin (n / 2 + 1) => legendreTerm n k t * x ^ n) using 1
    rw [Fin.sum_univ_eq_sum_range
      (fun k : ℕ => legendreTerm n k t * x ^ n)]
  exact hterms.sigma hfiber

private def legendrePowerSeries (t : ℝ) :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ (fun n => P n t)

private theorem exists_larger_radius
    (t x : ℝ) (h : x ^ 2 + 2 * |t * x| < 1) :
    ∃ r : ℝ, |x| < r ∧ 0 < r ∧ r ^ 2 + 2 * |t * r| < 1 := by
  let a : ℝ := |t|
  let u : ℝ := |x|
  let R : ℝ := Real.sqrt (a ^ 2 + 1) - a
  let r : ℝ := (u + R) / 2
  have ha : 0 ≤ a := by simp [a]
  have hu : 0 ≤ u := by simp [u]
  have hsqrt : 0 ≤ Real.sqrt (a ^ 2 + 1) :=
    Real.sqrt_nonneg _
  have hsqrt_sq :
      (Real.sqrt (a ^ 2 + 1)) ^ 2 = a ^ 2 + 1 :=
    Real.sq_sqrt (by positivity)
  have ha_sqrt : a < Real.sqrt (a ^ 2 + 1) := by
    nlinarith
  have hR : 0 < R := by
    dsimp [R]
    linarith
  have hRroot : R ^ 2 + 2 * a * R = 1 := by
    dsimp [R]
    nlinarith
  have hinput : u ^ 2 + 2 * a * u < 1 := by
    simpa only [u, a, sq_abs, abs_mul, mul_assoc] using h
  have huR : u < R := by
    by_contra hnot
    have hRu : R ≤ u := le_of_not_gt hnot
    have hnonneg : 0 ≤ (u - R) * (u + R + 2 * a) := by
      apply mul_nonneg (sub_nonneg.mpr hRu)
      nlinarith
    nlinarith
  have hur : u < r := by
    dsimp [r]
    linarith
  have hrR : r < R := by
    dsimp [r]
    linarith
  have hr : 0 < r := hu.trans_lt hur
  have hdiff : 0 < (R - r) * (R + r + 2 * a) := by
    apply mul_pos (sub_pos.mpr hrR)
    nlinarith
  have hrcond : r ^ 2 + 2 * a * r < 1 := by
    nlinarith
  refine ⟨r, ?_, hr, ?_⟩
  · simpa only [u] using hur
  · simpa only [a, abs_mul, abs_of_pos hr, mul_assoc] using hrcond

private theorem derivative_series_hasSum_deriv
    (t x : ℝ) (h : x ^ 2 + 2 * |t * x| < 1) :
    HasSum (derivativeGeneratingTerm x t)
      (deriv
        (fun y : ℝ => 1 / Real.sqrt (1 - 2 * t * y + y ^ 2)) x) := by
  obtain ⟨r, hxr, hr, hrcond⟩ := exists_larger_radius t x h
  let rnn : NNReal := ⟨r, hr.le⟩
  let p : FormalMultilinearSeries ℝ ℝ ℝ := legendrePowerSeries t
  have ht0 :
      Filter.Tendsto (generatingTerm r t) Filter.atTop (nhds 0) :=
    (generating_hasSum r t hrcond).summable.tendsto_atTop_zero
  have htnorm :
      Filter.Tendsto (fun n => ‖generatingTerm r t n‖)
        Filter.atTop (nhds 0) := by
    simpa using tendsto_norm.comp ht0
  have hp_tendsto :
      Filter.Tendsto (fun n => ‖p n‖ * (rnn : ℝ) ^ n)
        Filter.atTop (nhds 0) := by
    simpa [p, rnn, legendrePowerSeries, generatingTerm,
      FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow,
      abs_of_pos hr] using htnorm
  have hradius : (rnn : ENNReal) ≤ p.radius :=
    p.le_radius_of_tendsto hp_tendsto
  have hpower :
      HasFPowerSeriesOnBall
        (fun y : ℝ => 1 / Real.sqrt (1 - 2 * t * y + y ^ 2))
        p 0 (rnn : ENNReal) := by
    refine ⟨hradius, ?_, ?_⟩
    · simpa [rnn] using hr
    · intro y hy
      have hyr_enorm := mem_eball_zero_iff.1 hy
      have hyr : |y| < r := by
        simpa [enorm, rnn, Real.norm_eq_abs] using hyr_enorm
      have ha : 0 ≤ |t| := abs_nonneg t
      have hy0 : 0 ≤ |y| := abs_nonneg y
      have hdiff :
          0 < (r - |y|) * (r + |y| + 2 * |t|) := by
        apply mul_pos (sub_pos.mpr hyr)
        nlinarith
      have hrcond' : r ^ 2 + 2 * |t| * r < 1 := by
        simpa only [abs_mul, abs_of_pos hr, mul_assoc] using hrcond
      have hycond : y ^ 2 + 2 * |t * y| < 1 := by
        rw [abs_mul, ← sq_abs]
        nlinarith
      have hsum := generating_hasSum y t hycond
      have hpterms :
          HasSum (fun n => p n fun _ : Fin n => y)
            (1 / Real.sqrt (1 - 2 * t * y + y ^ 2)) := by
        apply hsum.congr_fun
        intro n
        simp only [p, legendrePowerSeries,
          FormalMultilinearSeries.ofScalars_apply_eq, generatingTerm,
          smul_eq_mul]
      simpa using hpterms
  have hxmem : x ∈ Metric.eball (0 : ℝ) (rnn : ENNReal) := by
    apply mem_eball_zero_iff.2
    simpa [enorm, rnn, Real.norm_eq_abs] using hxr
  have hlinear :=
    hpower.fderiv.hasSum hxmem
  have hscalar :=
    (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).hasSum hlinear
  have hscalar' :
      HasSum
        (fun n => (p.derivSeries n fun _ : Fin n => x) 1)
        (deriv
          (fun y : ℝ => 1 / Real.sqrt (1 - 2 * t * y + y ^ 2)) x) := by
    simpa [fderiv_apply_one_eq_deriv] using hscalar
  apply hscalar'.congr_fun
  intro n
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul,
    FormalMultilinearSeries.derivSeries_coeff_one]
  simp only [p, legendrePowerSeries,
    FormalMultilinearSeries.coeff_ofScalars]
  unfold derivativeGeneratingTerm
  push_cast
  ring

private theorem generatingFunction_hasDerivAt
    (t x : ℝ) (h : x ^ 2 + 2 * |t * x| < 1) :
    HasDerivAt
      (fun y : ℝ => 1 / Real.sqrt (1 - 2 * t * y + y ^ 2))
      ((t - x) /
        (1 - 2 * t * x + x ^ 2) ^ (3 / 2 : ℝ)) x := by
  let g : ℝ := 1 - 2 * t * x + x ^ 2
  have hgpos : 0 < g := by
    have htx := le_abs_self (t * x)
    dsimp [g]
    nlinarith
  have hg :
      HasDerivAt
        (fun y : ℝ => 1 - 2 * t * y + y ^ 2)
        (-2 * t + 2 * x) x := by
    convert
      ((hasDerivAt_const x 1).sub
        ((hasDerivAt_id x).const_mul (2 * t))).add
          (hasDerivAt_pow 2 x) using 1 <;>
      norm_num <;> ring
  have hsqrt := hg.sqrt hgpos.ne'
  have hsqrt_ne : Real.sqrt g ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hgpos
  have hinv := hsqrt.inv hsqrt_ne
  have hinv' :
      HasDerivAt
        (fun y : ℝ => 1 / Real.sqrt (1 - 2 * t * y + y ^ 2))
        (-((-2 * t + 2 * x) / (2 * Real.sqrt g)) /
          (Real.sqrt g) ^ 2) x := by
    simpa only [one_div] using hinv
  have hsqrt_sq : (Real.sqrt g) ^ 2 = g :=
    Real.sq_sqrt hgpos.le
  have hpow :
      g ^ (3 / 2 : ℝ) = g * Real.sqrt g := by
    calc
      g ^ (3 / 2 : ℝ) = g ^ ((1 : ℝ) + (1 / 2 : ℝ)) := by
        congr 1
        norm_num
      _ = g ^ (1 : ℝ) * g ^ (1 / 2 : ℝ) :=
        Real.rpow_add hgpos _ _
      _ = g * Real.sqrt g := by
        rw [Real.rpow_one, ← Real.sqrt_eq_rpow]
  convert hinv' using 1
  dsimp [g] at hgpos hsqrt_ne hsqrt_sq hpow ⊢
  rw [hpow, hsqrt_sq]
  field_simp
  ring

theorem gap1 :
    ∀ x t : ℝ, x ^ 2 + 2 * |t * x| < 1 →
      1 / Real.sqrt (1 - 2 * t * x + x ^ 2) =
        ∑' n, generatingTerm x t n := by
  intro x t h
  exact (generating_hasSum x t h).tsum_eq.symm

theorem gap2 :
    ∀ t x : ℝ, x ^ 2 + 2 * |t * x| < 1 →
      (t - x) / (1 - 2 * t * x + x ^ 2) ^ (3 / 2 : ℝ) =
        ∑' k, derivativeGeneratingTerm x t k := by
  intro t x h
  have hs := derivative_series_hasSum_deriv t x h
  rw [(generatingFunction_hasDerivAt t x h).deriv] at hs
  exact hs.tsum_eq.symm

theorem gap3 :
    ∀ t x : ℝ, x ^ 2 + 2 * |t * x| < 1 →
      (1 - 2 * t * x + x ^ 2) *
          (∑' k, derivativeGeneratingTerm x t k) =
        (t - x) * (∑' n, generatingTerm x t n) := by
  intro t x h
  rw [(derivative_series_hasSum_deriv t x h).tsum_eq,
    (generating_hasSum x t h).tsum_eq,
    (generatingFunction_hasDerivAt t x h).deriv]
  let g : ℝ := 1 - 2 * t * x + x ^ 2
  have hgpos : 0 < g := by
    have htx := le_abs_self (t * x)
    dsimp [g]
    nlinarith
  have hsqrt_ne : Real.sqrt g ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hgpos
  have hpow :
      g ^ (3 / 2 : ℝ) = g * Real.sqrt g := by
    calc
      g ^ (3 / 2 : ℝ) = g ^ ((1 : ℝ) + (1 / 2 : ℝ)) := by
        congr 1
        norm_num
      _ = g ^ (1 : ℝ) * g ^ (1 / 2 : ℝ) :=
        Real.rpow_add hgpos _ _
      _ = g * Real.sqrt g := by
        rw [Real.rpow_one, ← Real.sqrt_eq_rpow]
  change g * ((t - x) / g ^ (3 / 2 : ℝ)) =
    (t - x) * (1 / Real.sqrt g)
  rw [hpow]
  field_simp

theorem gap4 :
    ∀ t : ℝ, P 1 t = t := by
  intro t
  norm_num [P, legendreTerm, Finset.sum_range_succ]

theorem gap5 :
    ∀ t : ℝ, 2 * P 2 t - 2 * t * P 1 t = t * P 1 t - 1 := by
  intro t
  norm_num [P, legendreTerm, Finset.sum_range_succ]
  ring

theorem gap6 :
    ∀ n : ℕ, 1 ≤ n → ∀ t : ℝ,
      (n + 1 : ℝ) * P (n + 1) t -
          2 * n * t * P n t + (n - 1 : ℕ) * P (n - 1) t =
        t * P n t - P (n - 1) t := by
  intro n hn t
  have hr := P_recurrence n hn t
  push_cast at hr ⊢
  rw [Nat.cast_sub hn]
  linear_combination hr

theorem gap7 :
    ∀ t : ℝ, P 1 t = t := by
  intro t
  norm_num [P, legendreTerm, Finset.sum_range_succ]

theorem gap8 :
    ∀ t : ℝ, P 2 t = (3 * t ^ 2 - 1) / 2 := by
  intro t
  norm_num [P, legendreTerm, Finset.sum_range_succ]
  ring

theorem gap9 :
    ∀ n : ℕ, ∀ t : ℝ,
      P (n + 1) t =
        ((2 * n + 1 : ℕ) : ℝ) / (n + 1 : ℝ) * t * P n t -
          (n : ℝ) / (n + 1 : ℝ) * P (n - 1) t := by
  intro n t
  by_cases hn : n = 0
  · subst n
    norm_num [P, legendreTerm, Finset.sum_range_succ]
  ·
    have hr := P_recurrence n (Nat.one_le_iff_ne_zero.mpr hn) t
    have hden : (n + 1 : ℝ) ≠ 0 := by positivity
    push_cast at hr ⊢
    field_simp
    linear_combination hr

theorem gap10 :
    ∀ t : ℝ, P 3 t =
      (5 / 3 : ℝ) * t * ((3 * t ^ 2 - 1) / 2) - (2 / 3 : ℝ) * t := by
  intro t
  norm_num [P, legendreTerm, Finset.sum_range_succ]
  ring

theorem gap11 :
    ∀ t : ℝ,
      (5 / 3 : ℝ) * t * ((3 * t ^ 2 - 1) / 2) - (2 / 3 : ℝ) * t =
        (15 / (Nat.factorial 3 : ℝ)) *
          (t ^ 3 - (6 / (2 * 5) : ℝ) * t) := by
  intro t
  norm_num
  ring

theorem gap12 :
    ∀ t : ℝ, P 3 t =
      (15 / (Nat.factorial 3 : ℝ)) *
        (t ^ 3 - (6 / (2 * 5) : ℝ) * t) := by
  intro t
  norm_num [P, legendreTerm, Finset.sum_range_succ]
  ring

theorem gap13 :
    ∀ n : ℕ, ∀ t : ℝ,
      P n t =
        oddDoubleFactorial n / (Nat.factorial n : ℝ) *
          normalizedLegendrePolynomial n t := by
  intro n t
  rw [P, normalizedLegendrePolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [legendreTerm, normalizedLegendreTerm, even_factorial_eq]
  have hodd : oddDoubleFactorial n ≠ 0 := by
    unfold oddDoubleFactorial
    positivity
  field_simp [hodd]

end

end ProofGap.Exercise2895
