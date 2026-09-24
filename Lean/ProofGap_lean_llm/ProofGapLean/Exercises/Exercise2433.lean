import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise2433
noncomputable section

open scoped Interval

def y (a x : ℝ) : ℝ := a * Real.cosh (x / a)
def s (a b : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..b, Real.sqrt (1 + Real.sinh (x / a) ^ 2)

theorem gap1 (a b : ℝ) :
    s a b =
      ∫ x in (0 : ℝ)..b, Real.sqrt (1 + Real.sinh (x / a) ^ 2) := by
  rfl

theorem gap2 (a b : ℝ) :
    (∫ x in (0 : ℝ)..b, Real.sqrt (1 + Real.sinh (x / a) ^ 2)) =
      ∫ x in (0 : ℝ)..b, Real.cosh (x / a) := by
  apply intervalIntegral.integral_congr
  intro x hx
  change
    Real.sqrt (1 + Real.sinh (x / a) ^ 2) =
      Real.cosh (x / a)
  have hsq :
      1 + Real.sinh (x / a) ^ 2 = Real.cosh (x / a) ^ 2 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq (x / a)]
  rw [hsq, Real.sqrt_sq_eq_abs,
    abs_of_pos (Real.cosh_pos (x / a))]

theorem gap3 (a b : ℝ) (ha : a ≠ 0) :
    (∫ x in (0 : ℝ)..b, Real.cosh (x / a)) =
      a * Real.sinh (b / a) - a * Real.sinh 0 := by
  have hd : ∀ x : ℝ,
      HasDerivAt (fun t : ℝ => a * Real.sinh (t / a))
        (Real.cosh (x / a)) x := by
    intro x
    have h :=
      ((Real.hasDerivAt_sinh (x / a)).comp x
        ((hasDerivAt_id x).div_const a)).const_mul a
    convert h using 1 <;> field_simp [ha]
  have hc : Continuous (fun x : ℝ => Real.cosh (x / a)) :=
    Real.continuous_cosh.comp (continuous_id.div_const a)
  have hfund :
      (∫ x in (0 : ℝ)..b, Real.cosh (x / a)) =
        (fun t : ℝ => a * Real.sinh (t / a)) b -
          (fun t : ℝ => a * Real.sinh (t / a)) 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hd x) (hc.intervalIntegrable 0 b)
  simpa using hfund

theorem gap4 (a b : ℝ) :
    a * Real.sinh (b / a) - a * Real.sinh 0 =
      a * Real.sinh (b / a) := by
  simp

theorem gap5 (a b h : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hh : h = y a b) :
    a * Real.sinh (b / a) = Real.sqrt (h ^ 2 - a ^ 2) := by
  rw [hh]
  change
    a * Real.sinh (b / a) =
      Real.sqrt ((a * Real.cosh (b / a)) ^ 2 - a ^ 2)
  have hdiv : 0 ≤ b / a := div_nonneg hb (le_of_lt ha)
  have hsinh : 0 ≤ Real.sinh (b / a) :=
    Real.sinh_nonneg_iff.mpr hdiv
  have hprod : 0 ≤ a * Real.sinh (b / a) :=
    mul_nonneg (le_of_lt ha) hsinh
  have hhyper :
      Real.cosh (b / a) ^ 2 - 1 = Real.sinh (b / a) ^ 2 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq (b / a)]
  have hsquare :
      (a * Real.cosh (b / a)) ^ 2 - a ^ 2 =
        (a * Real.sinh (b / a)) ^ 2 := by
    calc
      (a * Real.cosh (b / a)) ^ 2 - a ^ 2 =
          a ^ 2 * (Real.cosh (b / a) ^ 2 - 1) := by ring
      _ = a ^ 2 * Real.sinh (b / a) ^ 2 := by rw [hhyper]
      _ = (a * Real.sinh (b / a)) ^ 2 := by ring
  rw [hsquare, Real.sqrt_sq_eq_abs, abs_of_nonneg hprod]

theorem gap6 (a b h : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hh : h = y a b) :
    s a b = Real.sqrt (h ^ 2 - a ^ 2) := by
  calc
    s a b =
        ∫ x in (0 : ℝ)..b,
          Real.sqrt (1 + Real.sinh (x / a) ^ 2) := gap1 a b
    _ = ∫ x in (0 : ℝ)..b, Real.cosh (x / a) := gap2 a b
    _ = a * Real.sinh (b / a) - a * Real.sinh 0 :=
      gap3 a b (ne_of_gt ha)
    _ = a * Real.sinh (b / a) := gap4 a b
    _ = Real.sqrt (h ^ 2 - a ^ 2) := gap5 a b h ha hb hh

end
end ProofGap.Exercise2433
