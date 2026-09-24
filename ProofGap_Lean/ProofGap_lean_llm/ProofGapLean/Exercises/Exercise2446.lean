import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise2446
noncomputable section

open scoped Interval

def speed (a φ : ℝ) : ℝ := Real.sqrt (a ^ 2 * φ ^ 2 + a ^ 2)
def s (a : ℝ) : ℝ := ∫ φ in (0 : ℝ)..2 * Real.pi, speed a φ
def primitive (a φ : ℝ) : ℝ :=
  a * (φ / 2 * Real.sqrt (φ ^ 2 + 1) +
    (1 / 2 : ℝ) * Real.log (φ + Real.sqrt (φ ^ 2 + 1)))

private theorem hasDerivAt_primitive_aux (a x : ℝ) :
    HasDerivAt (primitive a) (a * Real.sqrt (x ^ 2 + 1)) x := by
  have hxpos : 0 < x ^ 2 + 1 := by
    nlinarith [sq_nonneg x]
  have hqpos : 0 < Real.sqrt (x ^ 2 + 1) :=
    Real.sqrt_pos.2 hxpos
  have hqsq : Real.sqrt (x ^ 2 + 1) ^ 2 = x ^ 2 + 1 :=
    Real.sq_sqrt (le_of_lt hxpos)
  have hpoly :
      HasDerivAt (fun y : ℝ => y ^ 2 + 1) (2 * x) x := by
    simpa using ((hasDerivAt_id x).pow 2).add_const 1
  have hroot :
      HasDerivAt (fun y : ℝ => Real.sqrt (y ^ 2 + 1))
        (x / Real.sqrt (x ^ 2 + 1)) x := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hxpos)).comp x hpoly using 1
    field_simp [ne_of_gt hqpos] <;> ring
  have hargpos : 0 < x + Real.sqrt (x ^ 2 + 1) := by
    by_contra hn
    have hle : x + Real.sqrt (x ^ 2 + 1) ≤ 0 := le_of_not_gt hn
    have hleft : 0 ≤ -x - Real.sqrt (x ^ 2 + 1) := by
      linarith
    have hright : 0 ≤ -x + Real.sqrt (x ^ 2 + 1) := by
      linarith
    have hmul := mul_nonneg hleft hright
    nlinarith [hqsq]
  have hlog :
      HasDerivAt
        (fun y : ℝ =>
          Real.log (y + Real.sqrt (y ^ 2 + 1)))
        (1 / Real.sqrt (x ^ 2 + 1)) x := by
    convert
      (Real.hasDerivAt_log (ne_of_gt hargpos)).comp x
        ((hasDerivAt_id x).add hroot) using 1
    field_simp [ne_of_gt hqpos, ne_of_gt hargpos] <;> ring
  have hbase :
      HasDerivAt
        (fun y : ℝ =>
          y / 2 * Real.sqrt (y ^ 2 + 1) +
            (1 / 2 : ℝ) *
              Real.log (y + Real.sqrt (y ^ 2 + 1)))
        (Real.sqrt (x ^ 2 + 1)) x := by
    convert
      ((((hasDerivAt_id x).div_const 2).mul hroot).add
        (hlog.const_mul (1 / 2 : ℝ))) using 1
    simp only [id_eq]
    field_simp [ne_of_gt hqpos]
    nlinarith [hqsq]
  change
    HasDerivAt
      (fun y : ℝ =>
        a * (y / 2 * Real.sqrt (y ^ 2 + 1) +
          (1 / 2 : ℝ) *
            Real.log (y + Real.sqrt (y ^ 2 + 1))))
      (a * Real.sqrt (x ^ 2 + 1)) x
  exact hbase.const_mul a

theorem gap1 (a : ℝ) :
    s a = ∫ φ in (0 : ℝ)..2 * Real.pi,
      Real.sqrt (a ^ 2 * φ ^ 2 + a ^ 2) := by
  rfl

theorem gap2 (a : ℝ) (ha : 0 ≤ a) :
    s a = primitive a (2 * Real.pi) - primitive a 0 := by
  rw [gap1]
  have hsqrt (x : ℝ) :
      Real.sqrt (a ^ 2 * x ^ 2 + a ^ 2) =
        a * Real.sqrt (x ^ 2 + 1) := by
    rw [show a ^ 2 * x ^ 2 + a ^ 2 = a ^ 2 * (x ^ 2 + 1) by ring]
    rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs, abs_of_nonneg ha]
  simp_rw [hsqrt]
  have hinside : Continuous (fun y : ℝ => y ^ 2 + 1) :=
    (continuous_id.pow 2).add continuous_const
  have hsqrtcont : Continuous (fun y : ℝ => Real.sqrt (y ^ 2 + 1)) :=
    Real.continuous_sqrt.comp hinside
  have hcont : Continuous (fun y : ℝ => a * Real.sqrt (y ^ 2 + 1)) :=
    continuous_const.mul hsqrtcont
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    exact hasDerivAt_primitive_aux a x
  · exact hcont.intervalIntegrable 0 (2 * Real.pi)

theorem gap3 (a : ℝ) (ha : 0 ≤ a) :
    s a =
      a * (Real.pi * Real.sqrt (1 + 4 * Real.pi ^ 2) +
        (1 / 2 : ℝ) *
          Real.log (2 * Real.pi + Real.sqrt (1 + 4 * Real.pi ^ 2))) := by
  have hsq : (2 * Real.pi) ^ 2 + 1 =
      1 + 4 * Real.pi ^ 2 := by
    ring
  rw [gap2 a ha]
  norm_num [primitive, hsq]

end
end ProofGap.Exercise2446
