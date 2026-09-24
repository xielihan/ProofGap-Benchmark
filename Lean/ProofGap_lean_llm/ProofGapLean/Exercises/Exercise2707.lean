import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2707

noncomputable section

def firstSeries (n : ℕ) : ℝ :=
  1 / (3 : ℝ) ^ (n + 1) +
    (-1 : ℝ) ^ (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 3

def secondSeries (n : ℕ) : ℝ :=
  1 / (3 : ℝ) ^ (n + 2) +
    (-1 : ℝ) ^ (n + 2) / ((n + 1 : ℕ) : ℝ) ^ 3

def geometricSumTerm (n : ℕ) : ℝ :=
  4 / (3 : ℝ) ^ (n + 2)

theorem gap1 :
    Summable firstSeries := by
  have hgeo0 : Summable (fun n : ℕ => (1 / 3 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hgeo : Summable (fun n : ℕ => 1 / (3 : ℝ) ^ (n + 1)) := by
    simpa [one_div, div_pow] using
      (summable_nat_add_iff (f := fun n : ℕ => (1 / 3 : ℝ) ^ n) 1).mpr hgeo0
  have hp0 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hp : Summable
      (fun n : ℕ => (-1 : ℝ) ^ (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 3) := by
    apply Summable.of_norm
    refine ((summable_nat_add_iff
      (f := fun n : ℕ => 1 / (n : ℝ) ^ 3) 1).mpr hp0).congr ?_
    intro n
    simp [Real.norm_eq_abs, abs_div, abs_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
  exact hgeo.add hp

theorem gap2 :
    Summable secondSeries := by
  have hgeo0 : Summable (fun n : ℕ => (1 / 3 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hgeo : Summable (fun n : ℕ => 1 / (3 : ℝ) ^ (n + 2)) := by
    simpa [one_div, div_pow] using
      (summable_nat_add_iff (f := fun n : ℕ => (1 / 3 : ℝ) ^ n) 2).mpr hgeo0
  have hp0 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hp : Summable
      (fun n : ℕ => (-1 : ℝ) ^ (n + 2) / ((n + 1 : ℕ) : ℝ) ^ 3) := by
    apply Summable.of_norm
    refine ((summable_nat_add_iff
      (f := fun n : ℕ => 1 / (n : ℝ) ^ 3) 1).mpr hp0).congr ?_
    intro n
    simp [Real.norm_eq_abs, abs_div, abs_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
  exact hgeo.add hp

theorem gap3 :
    (∑' n : ℕ, firstSeries n) + (∑' n : ℕ, secondSeries n) =
      ∑' n : ℕ, geometricSumTerm n := by
  rw [← Summable.tsum_add gap1 gap2]
  apply tsum_congr
  intro n
  unfold firstSeries secondSeries geometricSumTerm
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ, pow_succ]
  field_simp [pow_ne_zero]
  ring

theorem gap4 :
    ∑' n : ℕ, geometricSumTerm n =
      (4 / (3 : ℝ) ^ 2) * (1 / (1 - 1 / 3)) := by
  have hsum :=
    (hasSum_geometric_of_norm_lt_one (ξ := (1 / 3 : ℝ)) (by norm_num)).mul_left
      (4 / 9 : ℝ)
  have hterm : HasSum geometricSumTerm
      ((4 / 9 : ℝ) * (1 - 1 / 3)⁻¹) := by
    apply hsum.congr_fun
    intro n
    unfold geometricSumTerm
    rw [pow_add]
    rw [div_pow]
    norm_num
    field_simp [pow_ne_zero]
  rw [hterm.tsum_eq]
  norm_num [one_div]

theorem gap5 :
    (4 / (3 : ℝ) ^ 2) * (1 / (1 - 1 / 3)) = 2 / 3 := by
  norm_num

theorem gap6 :
    (∑' n : ℕ, firstSeries n) + (∑' n : ℕ, secondSeries n) =
      2 / 3 := by
  rw [gap3, gap4, gap5]

end

end ProofGap.Exercise2707
