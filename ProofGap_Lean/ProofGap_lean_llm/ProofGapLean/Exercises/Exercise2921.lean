import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2921

noncomputable section

open scoped BigOperators

def cubeRoot (x : ℝ) : ℝ :=
  Real.rpow x (1 / 3 : ℝ)

def generalizedBinomial (a : ℝ) (n : ℕ) : ℝ :=
  (∏ k ∈ Finset.range n, (a - (k : ℝ))) /
    (Nat.factorial n : ℝ)

def binomialTerm (n : ℕ) : ℝ :=
  generalizedBinomial (1 / 3 : ℝ) n * (1 / 8 : ℝ) ^ n

def binomialPartial (m : ℕ) : ℝ :=
  2 * ∑ n ∈ Finset.range m, binomialTerm n

def remainder (m : ℕ) : ℝ :=
  cubeRoot 9 - binomialPartial m

def quadraticApproximation : ℝ :=
  2 *
    (1 + (1 / 3 : ℝ) * (1 / 8 : ℝ) -
      (1 / (Nat.factorial 2 : ℝ)) * (2 / 9 : ℝ) *
        (1 / (8 ^ 2 : ℝ)))

def Approx (x y ε : ℝ) : Prop :=
  |x - y| < ε

private theorem generalizedNumerator_eq_smeval (a : ℝ) (n : ℕ) :
    (∏ k ∈ Finset.range n, (a - (k : ℝ))) =
      (descPochhammer ℤ n).smeval a := by
  induction n with
  | zero =>
      simp [descPochhammer_zero]
  | succ n ih =>
      rw [Finset.prod_range_succ, ih, descPochhammer_succ_right,
        Polynomial.smeval_mul]
      simp [Polynomial.smeval_natCast]

private theorem generalizedBinomial_eq_choose (a : ℝ) (n : ℕ) :
    generalizedBinomial a n = Ring.choose a n := by
  unfold generalizedBinomial
  rw [Ring.choose_eq_smul]
  simp only [smul_eq_mul]
  rw [← generalizedNumerator_eq_smeval]
  ring

private theorem binomial_hasSum :
    HasSum binomialTerm
      (Real.rpow (1 + (1 / 8 : ℝ)) (1 / 3 : ℝ)) := by
  have hz : (1 / 8 : ℝ) ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_dist, Real.dist_eq]
    rw [ENNReal.ofReal_lt_one, sub_zero]
    norm_num
  have h :=
    (Real.one_add_rpow_hasFPowerSeriesOnBall_zero
      (a := (1 / 3 : ℝ))).hasSum hz
  simp only [Real.rpow_eq_pow]
  convert h using 1 with n
  · funext n
    unfold binomialTerm
    rw [generalizedBinomial_eq_choose]
    simp [binomialSeries, FormalMultilinearSeries.coeff_ofScalars,
      smul_eq_mul]
    ring
  · norm_num

private theorem binomialPartial_three :
    binomialPartial 3 = 599 / 288 := by
  norm_num [binomialPartial, binomialTerm, generalizedBinomial,
    Finset.sum_range_succ, Finset.prod_range_succ]

private theorem quadratic_value :
    quadraticApproximation = 599 / 288 := by
  norm_num [quadraticApproximation]

private theorem cubeRoot_cube :
    cubeRoot 9 ^ 3 = 9 := by
  unfold cubeRoot
  convert Real.rpow_inv_natCast_pow (x := (9 : ℝ)) (n := 3)
    (by norm_num) (by norm_num) using 1
  all_goals norm_num

private theorem center_lt_cubeRoot :
    (599 / 288 : ℝ) < cubeRoot 9 := by
  rw [← (show Odd 3 by decide).pow_lt_pow, cubeRoot_cube]
  norm_num

private theorem cubeRoot_lt_center_add_bound :
    cubeRoot 9 <
      (599 / 288 : ℝ) +
        2 * (1 / (Nat.factorial 3 : ℝ)) * (2 * 5 / 3 ^ 3 : ℝ) *
          (1 / 8 ^ 3 : ℝ) := by
  rw [← (show Odd 3 by decide).pow_lt_pow, cubeRoot_cube]
  norm_num

theorem gap1 :
    cubeRoot 9 =
      2 * Real.rpow (1 + (1 / 8 : ℝ)) (1 / 3 : ℝ) := by
  unfold cubeRoot
  have h8 : Real.rpow (8 : ℝ) (1 / 3 : ℝ) = 2 := by
    convert Real.pow_rpow_inv_natCast (x := (2 : ℝ)) (n := 3)
      (by norm_num) (by norm_num) using 1
    all_goals norm_num
  calc
    Real.rpow 9 (1 / 3 : ℝ) =
        Real.rpow (8 * (1 + (1 / 8 : ℝ))) (1 / 3 : ℝ) := by
      norm_num
    _ = Real.rpow 8 (1 / 3 : ℝ) *
        Real.rpow (1 + (1 / 8 : ℝ)) (1 / 3 : ℝ) := by
      simp only [Real.rpow_eq_pow]
      rw [Real.mul_rpow (by norm_num) (by norm_num)]
    _ = 2 * Real.rpow (1 + (1 / 8 : ℝ)) (1 / 3 : ℝ) := by
      rw [h8]

theorem gap2 :
    cubeRoot 9 = 2 * ∑' n : ℕ, binomialTerm n := by
  calc
    cubeRoot 9 =
        2 * Real.rpow (1 + (1 / 8 : ℝ)) (1 / 3 : ℝ) := gap1
    _ = 2 * ∑' n : ℕ, binomialTerm n := by
      rw [binomial_hasSum.tsum_eq]

theorem gap3 :
    |remainder 3| <
      2 * (1 / (Nat.factorial 3 : ℝ)) * (2 * 5 / 3 ^ 3 : ℝ) *
        (1 / 8 ^ 3 : ℝ) := by
  have hcenter := center_lt_cubeRoot
  have hupper := cubeRoot_lt_center_add_bound
  have hbound :
      0 <
        2 * (1 / (Nat.factorial 3 : ℝ)) * (2 * 5 / 3 ^ 3 : ℝ) *
          (1 / 8 ^ 3 : ℝ) := by
    norm_num
  rw [remainder, binomialPartial_three, abs_lt]
  constructor <;> linarith

theorem gap4 :
    2 * (1 / (Nat.factorial 3 : ℝ)) * (2 * 5 / 3 ^ 3 : ℝ) *
        (1 / 8 ^ 3 : ℝ) =
      10 / (3 ^ 4 * 8 ^ 3 : ℝ) := by
  norm_num

theorem gap5 :
    (10 / (3 ^ 4 * 8 ^ 3 : ℝ)) < (1 / 1000 : ℝ) := by
  norm_num

theorem gap6 :
    |remainder 3| < (1 / 1000 : ℝ) := by
  calc
    |remainder 3| <
        2 * (1 / (Nat.factorial 3 : ℝ)) * (2 * 5 / 3 ^ 3 : ℝ) *
          (1 / 8 ^ 3 : ℝ) := gap3
    _ = 10 / (3 ^ 4 * 8 ^ 3 : ℝ) := gap4
    _ < 1 / 1000 := gap5

theorem gap7 :
    Approx (cubeRoot 9) quadraticApproximation (1 / 1000 : ℝ) := by
  simpa [Approx, remainder, binomialPartial_three, quadratic_value] using gap6

theorem gap8 :
    Approx quadraticApproximation (2080 / 1000 : ℝ)
      (1 / 1000 : ℝ) := by
  norm_num [Approx, quadraticApproximation]

theorem gap9 :
    Approx (cubeRoot 9) (2080 / 1000 : ℝ)
      (1 / 1000 : ℝ) := by
  unfold Approx
  have hrem :
      |cubeRoot 9 - quadraticApproximation| <
        2 * (1 / (Nat.factorial 3 : ℝ)) * (2 * 5 / 3 ^ 3 : ℝ) *
          (1 / 8 ^ 3 : ℝ) := by
    simpa [remainder, binomialPartial_three, quadratic_value] using gap3
  have hquad :
      |quadraticApproximation - (2080 / 1000 : ℝ)| = 1 / 7200 := by
    norm_num [quadraticApproximation]
  calc
    |cubeRoot 9 - (2080 / 1000 : ℝ)| =
        |(cubeRoot 9 - quadraticApproximation) +
          (quadraticApproximation - (2080 / 1000 : ℝ))| := by
      congr 1
      ring
    _ ≤ |cubeRoot 9 - quadraticApproximation| +
          |quadraticApproximation - (2080 / 1000 : ℝ)| :=
      abs_add_le _ _
    _ <
        2 * (1 / (Nat.factorial 3 : ℝ)) * (2 * 5 / 3 ^ 3 : ℝ) *
            (1 / 8 ^ 3 : ℝ) +
          |quadraticApproximation - (2080 / 1000 : ℝ)| :=
      by linarith
    _ =
        2 * (1 / (Nat.factorial 3 : ℝ)) * (2 * 5 / 3 ^ 3 : ℝ) *
            (1 / 8 ^ 3 : ℝ) +
          1 / 7200 := by
      rw [hquad]
    _ < 1 / 1000 := by
      norm_num

end

end ProofGap.Exercise2921
