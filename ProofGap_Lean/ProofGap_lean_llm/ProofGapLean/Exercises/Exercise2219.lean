import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace ProofGap.Exercise2219
noncomputable section

open Filter
open scoped BigOperators Interval

def displayedSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n - 1), (((i : ℝ) + 1) / (n : ℝ) ^ 2)

def riemannSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, ((i : ℝ) / n) * (1 / (n : ℝ))

theorem gap1 (n : ℕ) :
    displayedSum n = riemannSum n := by
  cases n with
  | zero =>
      simp [displayedSum, riemannSum]
  | succ n =>
      unfold displayedSum riemannSum
      simp only [Nat.succ_sub_one]
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_div, zero_mul, add_zero]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Nat.cast_add, Nat.cast_one]
      have hnpos : (0 : ℝ) < (n : ℝ) + 1 :=
        add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one
      have hn : (n : ℝ) + 1 ≠ 0 := ne_of_gt hnpos
      field_simp [hn] <;> ring

theorem gap2 :
    Tendsto riemannSum atTop (nhds (1 / 2 : ℝ)) := by
  have hsum : ∀ n : ℕ,
      (∑ i ∈ Finset.range n, (i : ℝ)) =
        (n : ℝ) * ((n : ℝ) - 1) / 2 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        simp only [Nat.cast_succ]
        ring
  have hformula (n : ℕ) (hn : n ≠ 0) :
      riemannSum n = (1 / 2 : ℝ) - 1 / (2 * (n : ℝ)) := by
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    unfold riemannSum
    rw [← Finset.sum_mul, ← Finset.sum_div, hsum n]
    field_simp [hnR] <;> ring
  have heq : ∀ᶠ n : ℕ in atTop,
      riemannSum n = (1 / 2 : ℝ) - 1 / (2 * (n : ℝ)) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact hformula n (Nat.ne_of_gt hn)
  have hone :
      Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hscaled :
      Tendsto (fun n : ℕ => (1 / 2 : ℝ) * (1 / (n : ℝ)))
        atTop (nhds ((1 / 2 : ℝ) * 0)) :=
    tendsto_const_nhds.mul hone
  have hinv2 :
      Tendsto (fun n : ℕ => 1 / (2 * (n : ℝ))) atTop (nhds 0) := by
    simpa [div_eq_mul_inv, mul_comm] using hscaled
  have hlim :
      Tendsto (fun n : ℕ => (1 / 2 : ℝ) - 1 / (2 * (n : ℝ)))
        atTop (nhds (1 / 2 : ℝ)) := by
    simpa using (tendsto_const_nhds.sub hinv2)
  rw [tendsto_congr' heq]
  exact hlim

theorem gap3 :
    (∫ x in (0 : ℝ)..1, x) = 1 / 2 := by
  have hderiv (x : ℝ) :
      HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
    convert ((hasDerivAt_id x).pow 2).div_const 2 using 1 <;>
      simp [id_eq] <;> ring
  calc
    (∫ x in (0 : ℝ)..1, x) =
        (1 : ℝ) ^ 2 / 2 - (0 : ℝ) ^ 2 / 2 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hderiv x)
      exact continuous_id.intervalIntegrable 0 1
    _ = 1 / 2 := by norm_num

theorem gap4 :
    Tendsto displayedSum atTop (nhds (1 / 2 : ℝ)) := by
  rw [show displayedSum = riemannSum from funext gap1]
  exact gap2

end
end ProofGap.Exercise2219
