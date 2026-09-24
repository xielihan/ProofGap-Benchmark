import ProofGapLean.Prelude.Full
import Mathlib.Analysis.Complex.ExponentialBounds

open Filter

/-!
# Exercise 74

Semantic formalization of `proof_gap/exercise_74/{1,...,20}.txt`.
-/

namespace ProofGap.Exercise74

noncomputable section

def euler : ℝ :=
  Real.exp 1

def logSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico 1 n, Real.log (k : ℝ)

def x (n : ℕ) : ℝ :=
  ((n : ℝ) / euler) ^ n

def telescopingProduct (n : ℕ) : ℝ :=
  x 1 * ∏ j ∈ Finset.Icc 2 n, x j / x (j - 1)

/-- Source: `proof_gap/exercise_74/1.txt`; the intended range `k ≤ n` is explicit. -/
theorem gap1 :
    ∀ k n : ℕ, k ≤ n →
      Real.sqrt ((k : ℝ) * ((n : ℝ) - (k : ℝ))) ≤ (n : ℝ) / 2 := by
  intro k n hkn
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · nlinarith [sq_nonneg ((k : ℝ) - (n : ℝ) / 2)]

/-- Source: `proof_gap/exercise_74/2.txt`; logarithms use `0 < k < n`. -/
theorem gap2 :
    ∀ k n : ℕ, 0 < k → k < n →
      (1 / 2 : ℝ) *
        (Real.log (k : ℝ) + Real.log ((n : ℝ) - (k : ℝ))) ≤
          Real.log ((n : ℝ) / 2) := by
  intro k n hk hkn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkRlt : (k : ℝ) < n := by exact_mod_cast hkn
  have hdiff : (0 : ℝ) < (n : ℝ) - k := by linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hk.trans hkn
  have heq :
      (1 / 2 : ℝ) *
          (Real.log (k : ℝ) + Real.log ((n : ℝ) - (k : ℝ))) =
        Real.log (Real.sqrt ((k : ℝ) * ((n : ℝ) - (k : ℝ)))) := by
    rw [Real.log_sqrt (mul_nonneg hkR.le hdiff.le),
      Real.log_mul hkR.ne' hdiff.ne']
    ring
  rw [heq]
  rw [Real.log_le_log_iff (Real.sqrt_pos.2 (mul_pos hkR hdiff))
    (div_pos hnR (by norm_num))]
  exact gap1 k n hkn.le

/-- Source: `proof_gap/exercise_74/3.txt`; the omitted logarithmic sum is finite. -/
theorem gap3 :
    ∀ n : ℕ, 0 < n →
      logSum n ≤ ((n : ℝ) - 1) * Real.log ((n : ℝ) / 2) := by
  intro n hn
  have hsum :
      (∑ k ∈ Finset.Ico 1 n,
        (1 / 2 : ℝ) *
          (Real.log (k : ℝ) + Real.log ((n : ℝ) - (k : ℝ)))) ≤
        ∑ _k ∈ Finset.Ico 1 n, Real.log ((n : ℝ) / 2) := by
    apply Finset.sum_le_sum
    intro k hk
    exact gap2 k n (Finset.mem_Ico.mp hk).1
      (Finset.mem_Ico.mp hk).2
  have hreflect :
      (∑ k ∈ Finset.Ico 1 n, Real.log ((n : ℝ) - (k : ℝ))) =
        ∑ k ∈ Finset.Ico 1 n, Real.log (k : ℝ) := by
    have h := Finset.sum_Ico_reflect
      (fun k : ℕ => Real.log (k : ℝ)) 1 (m := n) (n := n) (by omega)
    rw [show n + 1 - n = 1 by omega, show n + 1 - 1 = n by omega] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := (Finset.mem_Ico.mp hk).2.le
    congr 1
    exact (Nat.cast_sub hkn).symm
  unfold logSum
  rw [← Finset.mul_sum, Finset.sum_add_distrib, hreflect] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  push_cast at hsum
  have hscaled := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2)
  ring_nf at hscaled
  simpa [Nat.cast_sub (show 1 ≤ n by omega)] using hscaled

/-- Source: `proof_gap/exercise_74/4.txt`. -/
theorem gap4 :
    ∀ n : ℕ,
      (Nat.factorial (n - 1) : ℝ) ≤ ((n : ℝ) / 2) ^ (n - 1) := by
  intro n
  by_cases hn : n ≤ 1
  · interval_cases n <;> norm_num
  · have hnpos : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hlog :
        Real.log (Nat.factorial (n - 1) : ℝ) = logSum n := by
      unfold logSum
      rw [← Real.log_prod (fun k hk => by
        have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
        positivity)]
      congr 1
      have hnat :
          Nat.factorial (n - 1) = ∏ k ∈ Finset.Ico 1 n, k := by
        rw [Finset.prod_Ico_eq_prod_range]
        simpa [Nat.add_comm] using
          (Finset.prod_range_add_one_eq_factorial (n - 1)).symm
      have hcast := congrArg (fun z : ℕ => (z : ℝ)) hnat
      push_cast at hcast
      exact hcast
    rw [← Real.log_le_log_iff (by positivity)
      (pow_pos (div_pos hnR (by norm_num)) _)]
    rw [hlog, Real.log_pow]
    push_cast
    simpa [Nat.cast_sub (show 1 ≤ n by omega)] using gap3 n hnpos

/-- Source: `proof_gap/exercise_74/5.txt`. -/
theorem gap5 :
    ∀ n : ℕ,
      (1 / 2 : ℝ) * (Nat.factorial n : ℝ) ≤ ((n : ℝ) / 2) ^ n := by
  intro n
  by_cases hn : n = 0
  · subst n
    norm_num
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hmul := mul_le_mul_of_nonneg_left (gap4 n)
      (show (0 : ℝ) ≤ (n : ℝ) / 2 by positivity)
    have hpred : n - 1 + 1 = n := by omega
    have hpow :
        (n : ℝ) / 2 * ((n : ℝ) / 2) ^ (n - 1) =
          ((n : ℝ) / 2) ^ n := by
      rw [mul_comm, ← pow_succ, hpred]
    rw [hpow] at hmul
    rw [show (Nat.factorial n : ℝ) =
      (n : ℝ) * (Nat.factorial (n - 1) : ℝ) by
        exact_mod_cast
          (show Nat.factorial n = n * Nat.factorial (n - 1) by
            calc
              Nat.factorial n = Nat.factorial (n - 1 + 1) := by
                congr 1
                omega
              _ = (n - 1 + 1) * Nat.factorial (n - 1) :=
                Nat.factorial_succ (n - 1)
              _ = n * Nat.factorial (n - 1) := by rw [hpred])]
    nlinarith

/-- Source: `proof_gap/exercise_74/6.txt`. -/
theorem gap6 :
    ∀ n : ℕ,
      (Nat.factorial n : ℝ) ≤ 2 * ((n : ℝ) / 2) ^ n := by
  intro n
  nlinarith [gap5 n]

/-- Source: `proof_gap/exercise_74/7.txt`. -/
theorem gap7 :
    ∀ n : ℕ,
      2 * ((n : ℝ) / 2) ^ n < euler * ((n : ℝ) / 2) ^ n := by
  intro n
  have hp : 0 < ((n : ℝ) / 2) ^ n := by
    cases n with
    | zero => norm_num
    | succ n => positivity
  unfold euler
  exact mul_lt_mul_of_pos_right Real.exp_one_gt_two hp

/-- Source: `proof_gap/exercise_74/8.txt`. -/
theorem gap8 :
    ∀ n : ℕ,
      (Nat.factorial n : ℝ) < euler * ((n : ℝ) / 2) ^ n := by
  intro n
  exact (gap6 n).trans_lt (gap7 n)

/-- Source: `proof_gap/exercise_74/9.txt`; the zero-index failure is excluded. -/
theorem gap9 :
    ∀ n : ℕ, 0 < n →
      x n / x (n - 1) =
        (n : ℝ) ^ n / (((n : ℝ) - 1) ^ (n - 1) * euler) := by
  intro n hn
  by_cases h1 : n = 1
  · subst n
    norm_num [x, euler]
  · have hnR : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have he : euler ≠ 0 := by
      unfold euler
      positivity
    have hnm : (n : ℝ) - 1 ≠ 0 := by linarith
    unfold x
    rw [Nat.cast_sub (show 1 ≤ n by omega)]
    have hpred : n - 1 + 1 = n := by omega
    have hepow : euler ^ n = euler ^ (n - 1) * euler := by
      rw [← pow_succ, hpred]
    rw [div_pow, div_pow, hepow]
    field_simp
    ring

/-- Source: `proof_gap/exercise_74/10.txt`; the positive-index domain is restored. -/
theorem gap10 :
    ∀ n : ℕ, 0 < n →
      (n : ℝ) ^ n / (((n : ℝ) - 1) ^ (n - 1) * euler) =
        ((1 + 1 / ((n : ℝ) - 1)) ^ (n - 1) * (n : ℝ)) / euler := by
  intro n hn
  by_cases h1 : n = 1
  · subst n
    norm_num
  · have hnR : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hnm : (n : ℝ) - 1 ≠ 0 := by linarith
    have he : euler ≠ 0 := by
      unfold euler
      positivity
    have hbase :
        1 + 1 / ((n : ℝ) - 1) = (n : ℝ) / ((n : ℝ) - 1) := by
      field_simp
      ring
    have hpred : n - 1 + 1 = n := by omega
    have hnpow : (n : ℝ) ^ n = (n : ℝ) ^ (n - 1) * (n : ℝ) := by
      rw [← pow_succ, hpred]
    rw [hbase, div_pow, hnpow]
    field_simp

/-- Source: `proof_gap/exercise_74/11.txt`. -/
theorem gap11 :
    ∀ n : ℕ, 0 < n →
      ((1 + 1 / ((n : ℝ) - 1)) ^ (n - 1) * (n : ℝ)) / euler <
        (n : ℝ) := by
  intro n hn
  by_cases h1 : n = 1
  · subst n
    norm_num [euler]
    exact inv_lt_one_of_one_lt₀
      (Real.one_lt_exp_iff.mpr (by norm_num))
  · have hnR : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    let b : ℝ := 1 + 1 / ((n : ℝ) - 1)
    have hb : 1 < b := by
      dsimp [b]
      have : 0 < 1 / ((n : ℝ) - 1) := one_div_pos.mpr (by linarith)
      linarith
    have hbpos : 0 < b := lt_trans zero_lt_one hb
    have hlog := Real.log_lt_sub_one_of_pos hbpos (by linarith : b ≠ 1)
    have hpow : b ^ (n - 1) < Real.exp 1 := by
      rw [← Real.exp_log (pow_pos hbpos _), Real.log_pow]
      rw [Real.exp_lt_exp]
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num
      have hbsub : b - 1 = 1 / ((n : ℝ) - 1) := by
        dsimp [b]
        ring
      rw [hbsub] at hlog
      have hnsub : (0 : ℝ) < (n : ℝ) - 1 := by linarith
      have hcancel : ((n : ℝ) - 1) * (1 / ((n : ℝ) - 1)) = 1 := by
        field_simp
      nlinarith
    unfold euler
    rw [div_lt_iff₀ (Real.exp_pos 1)]
    nlinarith [mul_lt_mul_of_pos_right hpow (by linarith : (0 : ℝ) < n)]

/-- Source: `proof_gap/exercise_74/12.txt`. -/
theorem gap12 :
    ∀ n : ℕ, 0 < n → x n / x (n - 1) < (n : ℝ) := by
  intro n hn
  rw [gap9 n hn, gap10 n hn]
  exact gap11 n hn

/-- Source: `proof_gap/exercise_74/13.txt`. -/
theorem gap13 :
    x 1 = 1 / euler := by
  norm_num [x]

/-- Source: `proof_gap/exercise_74/14.txt`. -/
theorem gap14 :
    1 / euler < 1 := by
  unfold euler
  rw [div_lt_one (Real.exp_pos 1)]
  exact Real.one_lt_exp_iff.mpr (by norm_num)

/-- Source: `proof_gap/exercise_74/15.txt`. -/
theorem gap15 :
    x 1 < 1 := by
  rw [gap13]
  exact gap14

/-- Source: `proof_gap/exercise_74/16.txt`; the telescoping product is explicit. -/
private theorem x_pos (n : ℕ) : 0 < x n := by
  by_cases hn : n = 0
  · subst n
    norm_num [x]
  · unfold x euler
    exact pow_pos (div_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) (Real.exp_pos 1)) _

theorem gap16 :
    ∀ n : ℕ, 0 < n → x n = telescopingProduct n := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        simp [telescopingProduct]
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        unfold telescopingProduct
        rw [Finset.prod_Icc_succ_top (by omega)]
        rw [Nat.add_sub_cancel]
        rw [← mul_assoc]
        change x (n + 1) = telescopingProduct n * (x (n + 1) / x n)
        rw [← ih hnpos]
        field_simp [ne_of_gt (x_pos n)]

private theorem x_lt_factorial :
    ∀ n : ℕ, 0 < n → x n < (Nat.factorial n : ℝ) := by
  intro n
  induction n with
  | zero =>
      intro hn
      omega
  | succ n ih =>
      intro _
      by_cases hn0 : n = 0
      · subst n
        simpa using gap15
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        have hih := ih hnpos
        have hratio := gap12 (n + 1) (by omega)
        simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hratio
        have hratio_pos : 0 < x (n + 1) / x n :=
          div_pos (x_pos (n + 1)) (x_pos n)
        have hfirst :
            x n * (x (n + 1) / x n) <
              (Nat.factorial n : ℝ) * (x (n + 1) / x n) :=
          mul_lt_mul_of_pos_right hih hratio_pos
        have hsecond :
            (Nat.factorial n : ℝ) * (x (n + 1) / x n) <
              (Nat.factorial n : ℝ) * ((n : ℝ) + 1) :=
          mul_lt_mul_of_pos_left hratio (by positivity)
        have hid : x (n + 1) = x n * (x (n + 1) / x n) := by
          field_simp [ne_of_gt (x_pos n)]
        rw [hid]
        calc
          _ < (Nat.factorial n : ℝ) * (x (n + 1) / x n) := hfirst
          _ < (Nat.factorial n : ℝ) * ((n : ℝ) + 1) := hsecond
          _ = (Nat.factorial (n + 1) : ℝ) := by
            rw [Nat.factorial_succ]
            push_cast
            ring

/-- Source: `proof_gap/exercise_74/17.txt`; the omitted product is explicit. -/
theorem gap17 :
    ∀ n : ℕ, 0 < n →
      telescopingProduct n < (Nat.factorial n : ℝ) := by
  intro n hn
  rw [← gap16 n hn]
  exact x_lt_factorial n hn

/-- Source: `proof_gap/exercise_74/18.txt`. -/
theorem gap18 :
    ∀ n : ℕ, 0 < n → x n < (Nat.factorial n : ℝ) := by
  exact x_lt_factorial

/-- Source: `proof_gap/exercise_74/19.txt`; the source sequence starts at one. -/
theorem gap19 :
    ∀ n : ℕ, 0 < n →
      ((n : ℝ) / euler) ^ n < (Nat.factorial n : ℝ) := by
  intro n hn
  exact gap18 n hn

/-- Source: `proof_gap/exercise_74/20.txt`. -/
theorem gap20 :
    ∀ n : ℕ, 0 < n →
      ((n : ℝ) / euler) ^ n < (Nat.factorial n : ℝ) ∧
      (Nat.factorial n : ℝ) < euler * ((n : ℝ) / 2) ^ n := by
  intro n hn
  exact ⟨gap19 n hn, gap8 n⟩

end

end ProofGap.Exercise74
