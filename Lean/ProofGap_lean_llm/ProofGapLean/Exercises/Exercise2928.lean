import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2928

noncomputable section

open scoped BigOperators

def x : ℝ :=
  1 / 2

def arcsinTerm (n : ℕ) : ℝ :=
  (Nat.choose (2 * n) n : ℝ) * x ^ (2 * n + 1) /
    ((4 : ℝ) ^ n * (2 * n + 1 : ℕ))

def arcsinPartial (m : ℕ) : ℝ :=
  ∑ n ∈ Finset.range m, arcsinTerm n

def piRemainder : ℝ :=
  Real.pi - 6 * arcsinPartial 6

def remainderBound : ℝ :=
  6 * (Nat.choose 12 6 : ℝ) / ((4 : ℝ) ^ 6 * 13) *
    x ^ 13 * ∑' n : ℕ, x ^ (2 * n)

def Approx (u v ε : ℝ) : Prop :=
  |u - v| < ε

private def centralCoefficient (n : ℕ) : ℝ :=
  (Nat.centralBinom n : ℝ) / (4 : ℝ) ^ n

private def positiveHalfChoose (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * Ring.choose (-(1 / 2 : ℝ)) n

private theorem ringChoose_succ (r : ℝ) (n : ℕ) :
    Ring.choose r (n + 1) =
      Ring.choose r n * (r - n) / (n + 1) := by
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul]
  simp only [smul_eq_mul, descPochhammer_succ_right,
    Polynomial.smeval_mul, Polynomial.smeval_sub,
    Polynomial.smeval_X, Polynomial.smeval_natCast,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hf, hn]
  ring

private theorem positiveHalfChoose_succ (n : ℕ) :
    positiveHalfChoose (n + 1) =
      positiveHalfChoose n * (2 * (n : ℝ) + 1) /
        (2 * ((n : ℝ) + 1)) := by
  rw [positiveHalfChoose, positiveHalfChoose, ringChoose_succ, pow_succ]
  push_cast
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hn]
  ring

private theorem centralCoefficient_succ (n : ℕ) :
    centralCoefficient (n + 1) =
      centralCoefficient n * (2 * (n : ℝ) + 1) /
        (2 * ((n : ℝ) + 1)) := by
  have hnat := Nat.succ_mul_centralBinom_succ n
  have hreal := congrArg (fun m : ℕ => (m : ℝ)) hnat
  push_cast at hreal
  rw [centralCoefficient, centralCoefficient, pow_succ]
  have hp : (4 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hp, hn]
  nlinarith

private theorem positiveHalfChoose_eq_centralCoefficient (n : ℕ) :
    positiveHalfChoose n = centralCoefficient n := by
  induction n with
  | zero =>
      norm_num [positiveHalfChoose, centralCoefficient,
        Ring.choose_zero_right, Nat.centralBinom]
  | succ n ih =>
      rw [positiveHalfChoose_succ, centralCoefficient_succ, ih]

private theorem centralCoefficient_nonneg (n : ℕ) :
    0 ≤ centralCoefficient n := by
  exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)

private theorem centralCoefficient_le_one (n : ℕ) :
    centralCoefficient n ≤ 1 := by
  rw [centralCoefficient]
  apply (div_le_one (by positivity)).2
  exact_mod_cast Nat.centralBinom_le_four_pow n

private def arcsinSeriesTerm (n : ℕ) (t : ℝ) : ℝ :=
  centralCoefficient n * t ^ (2 * n + 1) / (2 * n + 1 : ℕ)

private def arcsinSeries (t : ℝ) : ℝ :=
  ∑' n, arcsinSeriesTerm n t

private theorem arcsinSeriesTerm_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (arcsinSeriesTerm n)
      (centralCoefficient n * t ^ (2 * n)) t := by
  convert ((((hasDerivAt_id t).pow (2 * n + 1)).const_mul
    (centralCoefficient n)).div_const (((2 * n + 1 : ℕ) : ℝ))) using 1 <;>
    simp only [arcsinSeriesTerm, id_eq, Nat.add_sub_cancel,
      Nat.cast_add, Nat.cast_mul] <;>
    field_simp <;>
    ring

private theorem centralSeries_hasSum (t : ℝ) (ht : |t| < 1) :
    HasSum (fun n => centralCoefficient n * t ^ (2 * n))
      (1 / Real.sqrt (1 - t ^ 2)) := by
  have hzabs : |-(t ^ 2)| < 1 := by
    rw [abs_neg, abs_pow]
    nlinarith [abs_nonneg t]
  have hz : -(t ^ 2) ∈ Metric.eball (0 : ℝ) 1 := by
    simp only [Metric.mem_eball, edist_dist, dist_zero_right,
      ENNReal.ofReal_lt_one]
    simpa [Real.norm_eq_abs] using hzabs
  have h :=
    (Real.one_add_rpow_hasFPowerSeriesOnBall_zero
      (a := -(1 / 2 : ℝ))).hasSum hz
  have hfun :
      (fun n : ℕ =>
        (binomialSeries ℝ (-(1 / 2 : ℝ)) n)
          (fun _ => -(t ^ 2))) =
        fun n => centralCoefficient n * t ^ (2 * n) := by
    funext n
    rw [binomialSeries_apply]
    simp only [smul_eq_mul]
    rw [show (List.ofFn (fun _ : Fin n => -(t ^ 2))).prod =
        (-(t ^ 2)) ^ n by simp]
    rw [show -(t ^ 2) = (-1 : ℝ) * t ^ 2 by ring, mul_pow,
      pow_mul]
    rw [← positiveHalfChoose_eq_centralCoefficient]
    simp only [positiveHalfChoose]
    ring
  rw [hfun] at h
  have hpos : 0 < 1 - t ^ 2 := by
    have hsq : t ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one t).2 ht
    linarith
  have hvalue :
      (1 - t ^ 2) ^ (-(1 / 2 : ℝ)) =
        1 / Real.sqrt (1 - t ^ 2) := by
    rw [Real.sqrt_eq_rpow]
    rw [Real.rpow_neg hpos.le]
    simp [one_div]
  convert h using 1
  simpa [sub_eq_add_neg] using hvalue.symm

private theorem derivativeBound (n : ℕ) (t : ℝ)
    (ht : t ∈ Set.Ioo (-(3 / 4 : ℝ)) (3 / 4 : ℝ)) :
    ‖centralCoefficient n * t ^ (2 * n)‖ ≤
      (3 / 4 : ℝ) ^ (2 * n) := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg
    (centralCoefficient_nonneg n), abs_pow]
  calc
    centralCoefficient n * |t| ^ (2 * n) ≤
        1 * |t| ^ (2 * n) := by
      gcongr
      exact centralCoefficient_le_one n
    _ ≤ 1 * (3 / 4 : ℝ) ^ (2 * n) := by
      gcongr
      exact (abs_lt.2 ht).le
    _ = (3 / 4 : ℝ) ^ (2 * n) := one_mul _

private theorem derivativeBound_summable :
    Summable (fun n : ℕ => (3 / 4 : ℝ) ^ (2 * n)) := by
  have h :
      Summable (fun n : ℕ => (((3 / 4 : ℝ) ^ 2) ^ n)) :=
    summable_geometric_of_norm_lt_one
      (by norm_num [Real.norm_eq_abs])
  simpa [pow_mul] using h

private theorem arcsinSeries_hasDerivAt (t : ℝ)
    (ht : t ∈ Set.Ioo (-(3 / 4 : ℝ)) (3 / 4 : ℝ)) :
    HasDerivAt arcsinSeries (1 / Real.sqrt (1 - t ^ 2)) t := by
  have h :=
    hasDerivAt_tsum_of_isPreconnected derivativeBound_summable
      isOpen_Ioo isPreconnected_Ioo
      (fun n y hy => arcsinSeriesTerm_hasDerivAt n y)
      (fun n y hy => derivativeBound n y hy)
      (show (0 : ℝ) ∈ Set.Ioo (-(3 / 4 : ℝ)) (3 / 4 : ℝ) by
        norm_num)
      (show Summable (fun n : ℕ => arcsinSeriesTerm n 0) by
        simp [arcsinSeriesTerm])
      ht
  have ht1 : |t| < 1 :=
    (abs_lt.2 ht).trans (by norm_num)
  rw [(centralSeries_hasSum t ht1).tsum_eq] at h
  simpa only [arcsinSeries] using h

private theorem arcsinSeries_eq_arcsin_on :
    Set.EqOn arcsinSeries Real.arcsin
      (Set.Ioo (-(3 / 4 : ℝ)) (3 / 4 : ℝ)) := by
  have harcsin (t : ℝ)
      (ht : t ∈ Set.Ioo (-(3 / 4 : ℝ)) (3 / 4 : ℝ)) :
      HasDerivAt Real.arcsin (1 / Real.sqrt (1 - t ^ 2)) t := by
    apply Real.hasDerivAt_arcsin
    · intro heq
      rw [heq] at ht
      norm_num at ht
    · intro heq
      rw [heq] at ht
      norm_num at ht
  apply isOpen_Ioo.eqOn_of_deriv_eq (x := (0 : ℝ)) isPreconnected_Ioo
  · intro t ht
    exact (arcsinSeries_hasDerivAt t ht).differentiableAt.differentiableWithinAt
  · intro t ht
    exact (harcsin t ht).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(arcsinSeries_hasDerivAt t ht).deriv, (harcsin t ht).deriv]
  · norm_num
  · simp [arcsinSeries, arcsinSeriesTerm, Real.arcsin_zero]

private theorem arcsinTerm_eq_seriesTerm (n : ℕ) :
    arcsinTerm n = arcsinSeriesTerm n x := by
  rw [arcsinTerm, arcsinSeriesTerm, centralCoefficient,
    Nat.centralBinom]
  have h4 : (4 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hm : (((2 * n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [h4, hm]

private theorem arcsin_tsum :
    Real.arcsin x = ∑' n : ℕ, arcsinTerm n := by
  calc
    Real.arcsin x = arcsinSeries x := by
      symm
      apply arcsinSeries_eq_arcsin_on
      norm_num [x]
    _ = ∑' n : ℕ, arcsinTerm n := by
      apply tsum_congr
      intro n
      exact (arcsinTerm_eq_seriesTerm n).symm

private theorem tsum_x_even :
    (∑' n : ℕ, x ^ (2 * n)) = (4 / 3 : ℝ) := by
  calc
    (∑' n : ℕ, x ^ (2 * n)) =
        ∑' n : ℕ, (1 / 4 : ℝ) ^ n := by
      apply tsum_congr
      intro n
      rw [pow_mul]
      norm_num [x]
    _ = (1 - (1 / 4 : ℝ))⁻¹ :=
      tsum_geometric_of_norm_lt_one
        (by norm_num [Real.norm_eq_abs])
    _ = (4 / 3 : ℝ) := by norm_num

theorem gap1 :
    Real.pi = 6 * Real.arcsin x := by
  have harcsin : Real.arcsin x = Real.pi / 6 := by
    rw [x, ← Real.sin_pi_div_six]
    apply Real.arcsin_sin <;> linarith [Real.pi_pos]
  rw [harcsin]
  ring

theorem gap2 :
    Real.pi = 6 * ∑' n : ℕ, arcsinTerm n := by
  rw [gap1, arcsin_tsum]

theorem gap3 :
    |piRemainder| < remainderBound := by
  rw [piRemainder, remainderBound, tsum_x_even, abs_lt]
  constructor
  · norm_num [arcsinPartial, arcsinTerm, x, Nat.choose,
      Finset.sum_range_succ]
    linarith [Real.pi_gt_d20]
  · norm_num [arcsinPartial, arcsinTerm, x, Nat.choose,
      Finset.sum_range_succ]
    linarith [Real.pi_lt_d20]

theorem gap4 :
    remainderBound < (1 / 10 ^ 4 : ℝ) := by
  rw [remainderBound, tsum_x_even]
  norm_num [x, Nat.choose]

theorem gap5 :
    |piRemainder| < (1 / 10 ^ 4 : ℝ) := by
  exact gap3.trans gap4

theorem gap6 :
    Approx Real.pi (31416 / 10000 : ℝ)
      (1 / 10 ^ 4 : ℝ) := by
  rw [Approx, abs_lt]
  constructor
  · norm_num
    linarith [Real.pi_gt_d4]
  · norm_num
    linarith [Real.pi_lt_d4]

end

end ProofGap.Exercise2928
