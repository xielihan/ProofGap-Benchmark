import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise2629

noncomputable section

open Filter

def term (n : ℕ) : ℝ :=
  1 / Real.sqrt n - Real.sqrt (Real.log ((n + 1 : ℝ) / n))

def telescopingMajorant (n : ℕ) : ℝ :=
  1 / Real.sqrt n - 1 / Real.sqrt (n + 1)

def powerMajorant (n : ℕ) : ℝ :=
  1 / (2 * Real.rpow n (3 / 2 : ℝ))

theorem gap1 (x : ℝ) (hx : -1 < x) (hx0 : x ≠ 0) :
    Real.log (1 + x) < x := by
  have hpos : 0 < 1 + x := by linarith
  have hne : 1 + x ≠ 1 := by
    intro h
    apply hx0
    linarith
  have h := Real.log_lt_sub_one_of_pos hpos hne
  linarith

theorem gap2 (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((n + 1 : ℝ) / n) = Real.log (1 + 1 / (n : ℝ)) := by
  apply congrArg Real.log
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  field_simp [ne_of_gt hnR]
  <;> ring

theorem gap3 (n : ℕ) (hn : 1 ≤ n) :
    Real.log (1 + 1 / (n : ℝ)) < 1 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  apply gap1
  · have hpos : 0 < 1 / (n : ℝ) := by positivity
    linarith
  · exact div_ne_zero one_ne_zero (ne_of_gt hnR)

theorem gap4 (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((n + 1 : ℝ) / n) < 1 / (n : ℝ) := by
  rw [gap2 n hn]
  exact gap3 n hn

theorem gap5 (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((n + 1 : ℝ) / n) = -Real.log ((n : ℝ) / (n + 1)) := by
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn1R : (0 : ℝ) < n + 1 := by positivity
  rw [Real.log_div (ne_of_gt hn1R) (ne_of_gt hnR),
    Real.log_div (ne_of_gt hnR) (ne_of_gt hn1R)]
  ring

theorem gap6 (n : ℕ) (hn : 1 ≤ n) :
    -Real.log ((n : ℝ) / (n + 1)) =
      -Real.log (1 - 1 / (n + 1 : ℝ)) := by
  apply congrArg (fun x : ℝ => -Real.log x)
  have hn1R : (0 : ℝ) < n + 1 := by positivity
  field_simp [ne_of_gt hn1R]
  <;> ring

theorem gap7 (n : ℕ) (hn : 1 ≤ n) :
    1 / (n + 1 : ℝ) <
      -Real.log (1 - 1 / (n + 1 : ℝ)) := by
  have hn1R : (0 : ℝ) < n + 1 := by positivity
  have hfrac : 1 / (n + 1 : ℝ) < 1 := by
    apply (div_lt_one hn1R).2
    exact_mod_cast Nat.lt_succ_of_le hn
  have hne : (-1 / (n + 1 : ℝ)) ≠ 0 := by
    apply div_ne_zero
    · norm_num
    · exact ne_of_gt hn1R
  have hneg : -1 / (n + 1 : ℝ) = -(1 / (n + 1 : ℝ)) := by ring
  have hx : -1 < -1 / (n + 1 : ℝ) := by
    rw [hneg]
    linarith
  have h := gap1 (-1 / (n + 1 : ℝ)) hx hne
  have heq : 1 + (-1 / (n + 1 : ℝ)) = 1 - 1 / (n + 1 : ℝ) := by
    ring
  rw [heq] at h
  linarith

theorem gap8 (n : ℕ) (hn : 1 ≤ n) :
    1 / (n + 1 : ℝ) < Real.log ((n + 1 : ℝ) / n) := by
  rw [gap5 n hn, gap6 n hn]
  exact gap7 n hn

theorem gap9 (n : ℕ) (hn : 1 ≤ n) :
    1 / (n + 1 : ℝ) < Real.log ((n + 1 : ℝ) / n) := by
  exact gap8 n hn

theorem gap10 (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((n + 1 : ℝ) / n) < 1 / (n : ℝ) := by
  exact gap4 n hn

theorem gap11 (n : ℕ) (hn : 1 ≤ n) :
    1 / (n + 1 : ℝ) < 1 / (n : ℝ) := by
  apply one_div_lt_one_div_of_lt
  · positivity
  · exact_mod_cast Nat.lt_succ_self n

theorem gap12 (n : ℕ) (hn : 1 ≤ n) :
    0 < term n := by
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hloglt := gap4 n hn
  have hloglow := gap8 n hn
  have hlogpos : 0 < Real.log ((n + 1 : ℝ) / n) := by
    have : 0 < 1 / (n + 1 : ℝ) := by positivity
    linarith
  have hsqrtlog_sq :
      (Real.sqrt (Real.log ((n + 1 : ℝ) / n))) ^ 2 =
        Real.log ((n + 1 : ℝ) / n) :=
    Real.sq_sqrt (le_of_lt hlogpos)
  have hinvsqrt_sq :
      (1 / Real.sqrt n) ^ 2 = 1 / (n : ℝ) := by
    calc
      (1 / Real.sqrt n) ^ 2 = 1 / (Real.sqrt n) ^ 2 := by ring
      _ = 1 / (n : ℝ) := by rw [Real.sq_sqrt (le_of_lt hnR)]
  have hsqrtlt :
      Real.sqrt (Real.log ((n + 1 : ℝ) / n)) < 1 / Real.sqrt n := by
    have hsqrt_nonneg := Real.sqrt_nonneg (Real.log ((n + 1 : ℝ) / n))
    have hinv_pos : 0 < 1 / Real.sqrt n := by positivity
    nlinarith
  unfold term
  linarith

theorem gap13 (n : ℕ) (hn : 1 ≤ n) :
    term n < telescopingMajorant n := by
  have hloglow := gap8 n hn
  have hlogpos : 0 < Real.log ((n + 1 : ℝ) / n) := by
    have : 0 < 1 / (n + 1 : ℝ) := by positivity
    linarith
  have hn1R : (0 : ℝ) < n + 1 := by positivity
  have hsqrtlog_sq :
      (Real.sqrt (Real.log ((n + 1 : ℝ) / n))) ^ 2 =
        Real.log ((n + 1 : ℝ) / n) :=
    Real.sq_sqrt (le_of_lt hlogpos)
  have hinvsqrt_sq :
      (1 / Real.sqrt (n + 1)) ^ 2 = 1 / (n + 1 : ℝ) := by
    calc
      (1 / Real.sqrt (n + 1)) ^ 2 = 1 / (Real.sqrt (n + 1)) ^ 2 := by ring
      _ = 1 / (n + 1 : ℝ) := by rw [Real.sq_sqrt (le_of_lt hn1R)]
  have hinvlt :
      1 / Real.sqrt (n + 1) <
        Real.sqrt (Real.log ((n + 1 : ℝ) / n)) := by
    have hsqrt_nonneg := Real.sqrt_nonneg (Real.log ((n + 1 : ℝ) / n))
    have hinv_pos : 0 < 1 / Real.sqrt (n + 1) := by positivity
    nlinarith
  unfold term telescopingMajorant
  linarith

theorem gap14 (n : ℕ) (hn : 1 ≤ n) :
    telescopingMajorant n =
      (1 / (n : ℝ) - 1 / (n + 1 : ℝ)) /
        (1 / Real.sqrt n + 1 / Real.sqrt (n + 1)) := by
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn1R : (0 : ℝ) < n + 1 := by positivity
  have hn_sq : (1 / Real.sqrt n) ^ 2 = 1 / (n : ℝ) := by
    calc
      (1 / Real.sqrt n) ^ 2 = 1 / (Real.sqrt n) ^ 2 := by ring
      _ = 1 / (n : ℝ) := by rw [Real.sq_sqrt (le_of_lt hnR)]
  have hn1_sq :
      (1 / Real.sqrt (n + 1)) ^ 2 = 1 / (n + 1 : ℝ) := by
    calc
      (1 / Real.sqrt (n + 1)) ^ 2 =
          1 / (Real.sqrt (n + 1)) ^ 2 := by ring
      _ = 1 / (n + 1 : ℝ) := by rw [Real.sq_sqrt (le_of_lt hn1R)]
  have hsum :
      1 / Real.sqrt n + 1 / Real.sqrt (n + 1) ≠ 0 := by
    positivity
  rw [telescopingMajorant, ← hn_sq, ← hn1_sq]
  apply (eq_div_iff hsum).2
  ring

theorem gap15 (n : ℕ) (hn : 1 ≤ n) :
    (1 / (n : ℝ) - 1 / (n + 1 : ℝ)) /
        (1 / Real.sqrt n + 1 / Real.sqrt (n + 1)) <
      (1 / ((n : ℝ) * (n + 1))) / (2 / Real.sqrt (n + 1)) := by
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn1R : (0 : ℝ) < n + 1 := by positivity
  have hnum :
      1 / (n : ℝ) - 1 / (n + 1 : ℝ) =
        1 / ((n : ℝ) * (n + 1)) := by
    field_simp [ne_of_gt hnR, ne_of_gt hn1R]
    <;> ring
  have hsqrt_n_pos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  have hsqrt_n1_pos : 0 < Real.sqrt (n + 1) := Real.sqrt_pos.2 hn1R
  have hsqrtlt : Real.sqrt n < Real.sqrt (n + 1) := by
    have hn_sq := Real.sq_sqrt (le_of_lt hnR)
    have hn1_sq := Real.sq_sqrt (le_of_lt hn1R)
    have hnlt : (n : ℝ) < n + 1 := by norm_num
    nlinarith [Real.sqrt_nonneg (n : ℝ), Real.sqrt_nonneg (n + 1 : ℝ)]
  have hinvlt :
      1 / Real.sqrt (n + 1) < 1 / Real.sqrt n := by
    exact one_div_lt_one_div_of_lt hsqrt_n_pos hsqrtlt
  have hdenlt :
      2 / Real.sqrt (n + 1) <
        1 / Real.sqrt n + 1 / Real.sqrt (n + 1) := by
    rw [show 2 / Real.sqrt (n + 1) =
      1 / Real.sqrt (n + 1) + 1 / Real.sqrt (n + 1) by ring]
    nlinarith
  rw [hnum]
  have hnumpos : 0 < 1 / ((n : ℝ) * (n + 1)) := by positivity
  have hden1pos :
      0 < 1 / Real.sqrt n + 1 / Real.sqrt (n + 1) := by positivity
  have hden2pos : 0 < 2 / Real.sqrt (n + 1) := by positivity
  apply (div_lt_div_iff₀ hden1pos hden2pos).2
  nlinarith [mul_pos hnumpos (sub_pos.mpr hdenlt)]

theorem gap16 (n : ℕ) (hn : 1 ≤ n) :
    (1 / ((n : ℝ) * (n + 1))) / (2 / Real.sqrt (n + 1)) <
      powerMajorant n := by
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn1R : (0 : ℝ) < n + 1 := by positivity
  have hsqrt_n_pos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  have hsqrt_n1_pos : 0 < Real.sqrt (n + 1) := Real.sqrt_pos.2 hn1R
  have hsqrtlt : Real.sqrt n < Real.sqrt (n + 1) := by
    have hn_sq := Real.sq_sqrt (le_of_lt hnR)
    have hn1_sq := Real.sq_sqrt (le_of_lt hn1R)
    have hnlt : (n : ℝ) < n + 1 := by norm_num
    nlinarith [Real.sqrt_nonneg (n : ℝ), Real.sqrt_nonneg (n + 1 : ℝ)]
  have hrpow :
      Real.rpow n (3 / 2 : ℝ) = (n : ℝ) * Real.sqrt n := by
    calc
      Real.rpow n (3 / 2 : ℝ) = Real.rpow n (1 + 1 / 2 : ℝ) := by norm_num
      _ = Real.rpow n 1 * Real.rpow n (1 / 2 : ℝ) := by
        exact Real.rpow_add hnR 1 (1 / 2 : ℝ)
      _ = (n : ℝ) * Real.sqrt n := by
        rw [show Real.rpow n 1 = (n : ℝ) by
          exact Real.rpow_one (n : ℝ)]
        congr 1
        exact (Real.sqrt_eq_rpow (n : ℝ)).symm
  have hlhs :
      (1 / ((n : ℝ) * (n + 1))) / (2 / Real.sqrt (n + 1)) =
        1 / (2 * (n : ℝ) * Real.sqrt (n + 1)) := by
    have hn1_sq := Real.sq_sqrt (le_of_lt hn1R)
    field_simp [ne_of_gt hnR, ne_of_gt hn1R, ne_of_gt hsqrt_n1_pos]
    nlinarith
  rw [hlhs, powerMajorant, hrpow]
  apply one_div_lt_one_div_of_lt
  · positivity
  · have hfactor : 0 < 2 * (n : ℝ) := by positivity
    nlinarith [mul_pos hfactor (sub_pos.mpr hsqrtlt)]

theorem gap17 (n : ℕ) (hn : 1 ≤ n) :
    0 < powerMajorant n := by
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hrpowpos : 0 < Real.rpow n (3 / 2 : ℝ) := by
    exact Real.rpow_pos_of_pos hnR _
  unfold powerMajorant
  positivity

theorem gap18 :
    Summable (fun n : ℕ => 1 / Real.rpow (n + 1) (3 / 2 : ℝ)) := by
  have hbase :
      Summable (fun n : ℕ => 1 / Real.rpow n (3 / 2 : ℝ)) := by
    change Summable (fun n : ℕ => 1 / (n : ℝ) ^ (3 / 2 : ℝ))
    exact Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have hshift :
      Summable (fun n : ℕ => 1 / Real.rpow (n + 1 : ℕ) (3 / 2 : ℝ)) :=
    (summable_nat_add_iff 1).2 hbase
  simpa only [Nat.cast_add, Nat.cast_one] using hshift

theorem gap19 :
    Summable (fun n : ℕ => term (n + 1)) := by
  have hpower : Summable (fun n : ℕ => powerMajorant (n + 1)) := by
    have h := gap18.mul_left (1 / 2 : ℝ)
    apply h.congr
    intro n
    unfold powerMajorant
    norm_num [Nat.cast_add, add_comm]
    ring
  apply Summable.of_nonneg_of_le
    (fun n => le_of_lt (gap12 (n + 1) (Nat.succ_le_succ (Nat.zero_le n))))
    _ hpower
  intro n
  have hn : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  apply le_of_lt
  apply (gap13 (n + 1) hn).trans
  rw [gap14 (n + 1) hn]
  exact (gap15 (n + 1) hn).trans (gap16 (n + 1) hn)

theorem gap20 :
    Summable (fun n : ℕ => term (n + 1)) := by
  exact gap19

end

end ProofGap.Exercise2629
