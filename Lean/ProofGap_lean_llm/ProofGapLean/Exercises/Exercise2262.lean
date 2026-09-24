import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open scoped Interval

namespace ProofGap.Exercise2262

noncomputable section

def baseFunction (x : ℝ) : ℝ := Real.cos (Real.log (1 / x))

def originalIntegral (n : ℕ) : ℝ :=
  ∫ x in Real.exp (-2 * Real.pi * (n : ℝ))..1, |deriv baseFunction x|

def sineAbsIntegral (n : ℕ) : ℝ :=
  ∫ t in 0..2 * Real.pi * (n : ℝ), |Real.sin t|

def blockSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (2 * n),
    ∫ t in (k : ℝ) * Real.pi..((k + 1 : ℕ) : ℝ) * Real.pi, |Real.sin t|

def repeatedHalfPeriod (n : ℕ) : ℝ :=
  ∑ _k ∈ Finset.range (2 * n), ∫ t in 0..Real.pi, Real.sin t

private theorem absSinBlocksAux (m : ℕ) :
    (∫ t in 0..(m : ℝ) * Real.pi, |Real.sin t|) =
      ∑ k ∈ Finset.range m,
        ∫ t in (k : ℝ) * Real.pi..((k + 1 : ℕ) : ℝ) * Real.pi,
          |Real.sin t| := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ← ih]
      symm
      exact intervalIntegral.integral_add_adjacent_intervals
        (Real.continuous_sin.abs.intervalIntegrable
          0 ((m : ℝ) * Real.pi))
        (Real.continuous_sin.abs.intervalIntegrable
          ((m : ℝ) * Real.pi) (((m + 1 : ℕ) : ℝ) * Real.pi))

private theorem absSinPiPeriodic :
    Function.Periodic (fun t : ℝ => |Real.sin t|) Real.pi := by
  intro t
  change |Real.sin (t + Real.pi)| = |Real.sin t|
  rw [Real.sin_add_pi, abs_neg]

private theorem absSinHalfPeriodBlock (k : ℕ) :
    (∫ t in (k : ℝ) * Real.pi..((k + 1 : ℕ) : ℝ) * Real.pi,
      |Real.sin t|) =
      ∫ t in 0..Real.pi, Real.sin t := by
  have hchange :
      (∫ u in 0..Real.pi,
        |Real.sin (u + (k : ℝ) * Real.pi)|) =
        ∫ t in (k : ℝ) * Real.pi..Real.pi + (k : ℝ) * Real.pi,
          |Real.sin t| := by
    simpa [mul_comm] using
      (intervalIntegral.integral_comp_mul_deriv
        (f := fun u : ℝ => u + (k : ℝ) * Real.pi)
        (f' := fun _u : ℝ => 1)
        (g := fun t : ℝ => |Real.sin t|)
        (a := 0) (b := Real.pi)
        (fun u _ => (hasDerivAt_id u).add_const ((k : ℝ) * Real.pi))
        ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).continuousOn)
        Real.continuous_sin.abs)
  calc
    (∫ t in (k : ℝ) * Real.pi..((k + 1 : ℕ) : ℝ) * Real.pi,
      |Real.sin t|) =
        ∫ u in 0..Real.pi,
          |Real.sin (u + (k : ℝ) * Real.pi)| := by
      simpa [Nat.cast_add, Nat.cast_one, add_mul, add_comm, add_left_comm,
        add_assoc] using hchange.symm
    _ = ∫ u in 0..Real.pi, Real.sin u := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le Real.pi_pos.le] at hu
      have hperiod :
          |Real.sin (u + (k : ℝ) * Real.pi)| = |Real.sin u| := by
        simpa [nsmul_eq_mul] using (absSinPiPeriodic.nsmul k) u
      change |Real.sin (u + (k : ℝ) * Real.pi)| = Real.sin u
      rw [hperiod, abs_of_nonneg]
      exact Real.sin_nonneg_of_nonneg_of_le_pi hu.1 hu.2

private theorem integralSinZeroPi :
    (∫ t in 0..Real.pi, Real.sin t) = 2 := by
  have hderiv :
      ∀ t ∈ Set.uIcc (0 : ℝ) Real.pi,
        HasDerivAt (fun u : ℝ => -Real.cos u) (Real.sin t) t := by
    intro t ht
    simpa using (Real.hasDerivAt_cos t).neg
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (Real.continuous_sin.intervalIntegrable 0 Real.pi)
  calc
    (∫ t in 0..Real.pi, Real.sin t) =
        (-Real.cos Real.pi) - (-Real.cos 0) := h
    _ = 2 := by
      rw [Real.cos_pi, Real.cos_zero]
      norm_num

theorem gap1 (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt baseFunction (Real.sin (-Real.log x) / x) x := by
  unfold baseFunction
  convert
    (Real.hasDerivAt_cos (-Real.log x)).comp x
      ((Real.hasDerivAt_log hx).neg) using 1 <;>
    simp [Function.comp_def, Real.log_inv, div_eq_mul_inv]

theorem gap2 (t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-t)) t := by
  simpa using
    (Real.hasDerivAt_exp (-t)).comp t ((hasDerivAt_id t).neg)

theorem gap3 (t : ℝ) (x : ℝ) (hx : x = Real.exp (-t)) :
    Real.sin (-Real.log x) / x = Real.exp t * Real.sin t := by
  subst x
  simp [Real.log_exp, Real.exp_neg, div_eq_mul_inv, mul_comm]

theorem gap4 (n : ℕ) (hn : 0 < n) :
    originalIntegral n = sineAbsIntegral n := by
  unfold originalIntegral sineAbsIntegral
  let A : ℝ := 2 * Real.pi * (n : ℝ)
  have hlower : (-2 : ℝ) * Real.pi * (n : ℝ) = -A := by
    dsimp [A]
    ring
  rw [hlower]
  change (∫ x in Real.exp (-A)..1, |deriv baseFunction x|) =
    ∫ t in 0..A, |Real.sin t|
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (Nat.cast_nonneg n)
  have hexp_le : Real.exp (-A) ≤ 1 := by
    calc
      Real.exp (-A) ≤ Real.exp 0 := Real.exp_le_exp.mpr (neg_nonpos.mpr hA)
      _ = 1 := Real.exp_zero
  have hderiv :
      (∫ x in Real.exp (-A)..1, |deriv baseFunction x|) =
        ∫ x in Real.exp (-A)..1,
          |Real.sin (-Real.log x) / x| := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hexp_le] at hx
    have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos (-A)) hx.1
    exact congrArg abs (gap1 x hxpos.ne').deriv
  have hlogDeriv :
      ∀ x ∈ Set.uIcc (Real.exp (-A)) 1,
        HasDerivAt (fun y : ℝ => -Real.log y) (-(x⁻¹)) x := by
    intro x hx
    rw [Set.uIcc_of_le hexp_le] at hx
    have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos (-A)) hx.1
    simpa [one_div] using (Real.hasDerivAt_log hxpos.ne').neg
  have hrecipCont :
      ContinuousOn (fun x : ℝ => -(x⁻¹))
        (Set.uIcc (Real.exp (-A)) 1) := by
    intro x hx
    rw [Set.uIcc_of_le hexp_le] at hx
    have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos (-A)) hx.1
    have hrecip :
        ContinuousAt (fun y : ℝ => (1 : ℝ) / y) x :=
      continuousAt_const.div continuousAt_id hxpos.ne'
    simpa [one_div] using hrecip.neg.continuousWithinAt
  have hsubst :
      (∫ x in Real.exp (-A)..1,
        |Real.sin (-Real.log x)| * x⁻¹) =
        ∫ t in A..0, -|Real.sin t| := by
    simpa [Function.comp_def, Real.log_exp, mul_comm] using
      (intervalIntegral.integral_comp_mul_deriv
        (f := fun x : ℝ => -Real.log x)
        (f' := fun x : ℝ => -(x⁻¹))
        (g := fun t : ℝ => -|Real.sin t|)
        (a := Real.exp (-A)) (b := 1)
        hlogDeriv hrecipCont Real.continuous_sin.abs.neg)
  have habs :
      (∫ x in Real.exp (-A)..1,
        |Real.sin (-Real.log x) / x|) =
        ∫ x in Real.exp (-A)..1,
          |Real.sin (-Real.log x)| * x⁻¹ := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hexp_le] at hx
    have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos (-A)) hx.1
    change |Real.sin (-Real.log x) / x| =
      |Real.sin (-Real.log x)| * x⁻¹
    rw [abs_div, abs_of_pos hxpos]
    simp [div_eq_mul_inv]
  have hreverse :
      (∫ t in A..0, -|Real.sin t|) =
        ∫ t in 0..A, |Real.sin t| := by
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_symm]
    ring
  calc
    (∫ x in Real.exp (-A)..1, |deriv baseFunction x|) =
        ∫ x in Real.exp (-A)..1,
          |Real.sin (-Real.log x) / x| := hderiv
    _ = ∫ x in Real.exp (-A)..1,
          |Real.sin (-Real.log x)| * x⁻¹ := habs
    _ = ∫ t in A..0, -|Real.sin t| := hsubst
    _ = ∫ t in 0..A, |Real.sin t| := hreverse

theorem gap5 (n : ℕ) :
    sineAbsIntegral n = blockSum n := by
  unfold sineAbsIntegral blockSum
  rw [show (2 : ℝ) * Real.pi * (n : ℝ) =
      ((2 * n : ℕ) : ℝ) * Real.pi by
    norm_num [Nat.cast_mul] <;> ring]
  exact absSinBlocksAux (2 * n)

theorem gap6 (n : ℕ) :
    blockSum n = repeatedHalfPeriod n := by
  unfold blockSum repeatedHalfPeriod
  apply Finset.sum_congr rfl
  intro k hk
  exact absSinHalfPeriodBlock k

theorem gap7 (n : ℕ) :
    repeatedHalfPeriod n = 2 * 2 * (n : ℝ) := by
  norm_num [repeatedHalfPeriod, integralSinZeroPi, Nat.cast_mul]
  ring

theorem gap8 (n : ℕ) :
    (2 : ℝ) * 2 * (n : ℝ) = 4 * (n : ℝ) := by
  ring

theorem gap9 (n : ℕ) (hn : 0 < n) :
    originalIntegral n = 4 * (n : ℝ) := by
  calc
    originalIntegral n = sineAbsIntegral n := gap4 n hn
    _ = blockSum n := gap5 n
    _ = repeatedHalfPeriod n := gap6 n
    _ = 2 * 2 * (n : ℝ) := gap7 n
    _ = 4 * (n : ℝ) := gap8 n

end

end ProofGap.Exercise2262
