import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2647

noncomputable section

open scoped Interval

def integrand (x : ℝ) : ℝ :=
  Real.rpow (1 + x ^ 4) (1 / 4 : ℝ)

def denominator (n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..n, integrand x

def u (n : ℕ) : ℝ :=
  1 / denominator n

def majorant (n : ℕ) : ℝ :=
  2 / (n : ℝ) ^ 2

private theorem le_integrand {x : ℝ} (hx : 0 ≤ x) : x ≤ integrand x := by
  have hroot : Real.rpow (x ^ 4) (1 / 4 : ℝ) = x := by
    have h := Real.pow_rpow_inv_natCast hx (by norm_num : (4 : ℕ) ≠ 0)
    norm_num at h
    exact h
  calc
    x = Real.rpow (x ^ 4) (1 / 4 : ℝ) := hroot.symm
    _ ≤ Real.rpow (1 + x ^ 4) (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (pow_nonneg hx 4) (by linarith) (by norm_num)
    _ = integrand x := by rfl

private theorem integral_id_le_denominator (n : ℕ) :
    (∫ x in (0 : ℝ)..n, x) ≤ denominator n := by
  have hint : Continuous integrand := by
    unfold integrand
    exact (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 4)).comp (by fun_prop)
  unfold denominator
  exact intervalIntegral.integral_mono_on (by positivity)
    (continuous_id.intervalIntegrable _ _) (hint.intervalIntegrable _ _)
    (fun x hx => le_integrand hx.1)

theorem gap1 :
    ∀ n : ℕ, 1 ≤ n → 0 < u n := by
  intro n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hidpos : 0 < ∫ x in (0 : ℝ)..n, x := by
    rw [integral_id]
    norm_num
    positivity
  have hden : 0 < denominator n := hidpos.trans_le (integral_id_le_denominator n)
  unfold u
  exact one_div_pos.mpr hden

theorem gap2 :
    ∀ n : ℕ, 1 ≤ n →
      u n ≤ 1 / (∫ x in (0 : ℝ)..n, x) := by
  intro n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hidpos : 0 < ∫ x in (0 : ℝ)..n, x := by
    rw [integral_id]
    norm_num
    positivity
  unfold u
  exact one_div_le_one_div_of_le hidpos (integral_id_le_denominator n)

theorem gap3 :
    ∀ n : ℕ, 1 ≤ n →
      1 / (∫ x in (0 : ℝ)..n, x) = majorant n := by
  intro n hn
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
  rw [integral_id]
  unfold majorant
  norm_num

theorem gap4 :
    ∀ n : ℕ, 1 ≤ n → 0 < majorant n := by
  intro n hn
  unfold majorant
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  positivity

theorem gap5 :
    Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
  have hfull : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  exact (summable_nat_add_iff 1).mpr hfull

theorem gap6
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 ≤ u n)
    (hbound : ∀ n : ℕ, 1 ≤ n → u n ≤ majorant n) :
    Summable (fun n : ℕ => u (n + 1)) := by
  have hmajorant : Summable (fun n : ℕ => majorant (n + 1)) := by
    have h := gap5.mul_left 2
    simpa [majorant] using h
  exact hmajorant.of_nonneg_of_le
    (fun n => hpos (n + 1) (by omega))
    (fun n => hbound (n + 1) (by omega))

theorem gap7
    (hsum : Summable (fun n : ℕ => u (n + 1))) :
    Summable (fun n : ℕ => u (n + 1)) := by
  exact hsum

end

end ProofGap.Exercise2647
