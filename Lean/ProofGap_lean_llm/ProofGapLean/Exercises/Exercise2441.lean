import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise2441
noncomputable section

open Set
open scoped Interval

def curveX (a c t : ℝ) : ℝ := c ^ 2 / a * Real.cos t ^ 3
def curveY (b c t : ℝ) : ℝ := c ^ 2 / b * Real.sin t ^ 3
def speedFormula (a b c t : ℝ) : ℝ :=
  3 * c ^ 2 / (a * b) * Real.sin t * Real.cos t *
    Real.sqrt (b ^ 2 * Real.cos t ^ 2 + a ^ 2 * Real.sin t ^ 2)
def s (a b c : ℝ) : ℝ :=
  4 * ∫ t in (0 : ℝ)..Real.pi / 2, speedFormula a b c t
def primitive (a b c t : ℝ) : ℝ :=
  12 * c ^ 2 / (3 * a * b * (a ^ 2 - b ^ 2)) *
    Real.rpow (b ^ 2 + (a ^ 2 - b ^ 2) * Real.sin t ^ 2) (3 / 2 : ℝ)

private theorem primitive_derivative
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : b < a) (t : ℝ) :
    HasDerivAt (primitive a b c) (4 * speedFormula a b c t) t := by
  have hd : 0 < a ^ 2 - b ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hab) (add_pos ha hb)]
  have hbase_pos :
      0 < b ^ 2 + (a ^ 2 - b ^ 2) * Real.sin t ^ 2 := by
    nlinarith [sq_pos_of_pos hb, sq_nonneg (Real.sin t)]
  have hinner :
      HasDerivAt
        (fun x => b ^ 2 + (a ^ 2 - b ^ 2) * Real.sin x ^ 2)
        (2 * (a ^ 2 - b ^ 2) * Real.sin t * Real.cos t) t := by
    convert
      (hasDerivAt_const t (b ^ 2)).add
        (((Real.hasDerivAt_sin t).pow 2).const_mul (a ^ 2 - b ^ 2)) using 1 <;>
      ring
  have hpow :
      HasDerivAt
        (fun x => Real.rpow
          (b ^ 2 + (a ^ 2 - b ^ 2) * Real.sin x ^ 2) (3 / 2 : ℝ))
        ((3 / 2 : ℝ) *
          Real.rpow (b ^ 2 + (a ^ 2 - b ^ 2) * Real.sin t ^ 2)
            ((3 / 2 : ℝ) - 1) *
          (2 * (a ^ 2 - b ^ 2) * Real.sin t * Real.cos t)) t := by
    exact
      (Real.hasDerivAt_rpow_const (p := (3 / 2 : ℝ))
        (Or.inl (ne_of_gt hbase_pos))).comp t hinner
  have hbase_eq :
      b ^ 2 + (a ^ 2 - b ^ 2) * Real.sin t ^ 2 =
        b ^ 2 * Real.cos t ^ 2 + a ^ 2 * Real.sin t ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hexp : (3 / 2 : ℝ) - 1 = 1 / 2 := by norm_num
  have hrpow_sqrt :
      Real.rpow
          (b ^ 2 + (a ^ 2 - b ^ 2) * Real.sin t ^ 2) (1 / 2 : ℝ) =
        Real.sqrt (b ^ 2 + (a ^ 2 - b ^ 2) * Real.sin t ^ 2) := by
    exact (Real.sqrt_eq_rpow _).symm
  have hcoef :
      (12 * c ^ 2 / (3 * a * b * (a ^ 2 - b ^ 2))) *
          ((3 / 2 : ℝ) *
            Real.rpow (b ^ 2 + (a ^ 2 - b ^ 2) * Real.sin t ^ 2)
              ((3 / 2 : ℝ) - 1) *
            (2 * (a ^ 2 - b ^ 2) * Real.sin t * Real.cos t)) =
        4 * speedFormula a b c t := by
    rw [hexp, hrpow_sqrt, hbase_eq]
    unfold speedFormula
    field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hd]
    ring
  have hp := hpow.const_mul
    (12 * c ^ 2 / (3 * a * b * (a ^ 2 - b ^ 2)))
  rw [hcoef] at hp
  simpa only [primitive] using hp

private theorem sq_rpow_three_halves (x : ℝ) (hx : 0 < x) :
    Real.rpow (x ^ 2) (3 / 2 : ℝ) = x ^ 3 := by
  calc
    Real.rpow (x ^ 2) (3 / 2 : ℝ) =
        Real.exp (Real.log (x ^ 2) * (3 / 2 : ℝ)) :=
      Real.rpow_def_of_pos (sq_pos_of_pos hx) _
    _ = Real.exp ((2 : ℝ) * Real.log x * (3 / 2 : ℝ)) := by
      rw [Real.log_pow]
      norm_num
    _ = Real.exp (Real.log x * 3) := by
      congr 1
      ring
    _ = x ^ 3 := by
      rw [show Real.log x * 3 = Real.log x + Real.log x + Real.log x by ring,
        Real.exp_add, Real.exp_add, Real.exp_log hx]
      ring

theorem gap1 (a b c t : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : b < a) (ht : t ∈ Icc 0 (Real.pi / 2)) :
    Real.sqrt
        (deriv (curveX a c) t ^ 2 + deriv (curveY b c) t ^ 2) =
      speedFormula a b c t := by
  have hx :
      HasDerivAt (curveX a c)
        (-3 * (c ^ 2 / a) * Real.cos t ^ 2 * Real.sin t) t := by
    unfold curveX
    convert ((Real.hasDerivAt_cos t).pow 3).const_mul (c ^ 2 / a) using 1 <;>
      ring
  have hy :
      HasDerivAt (curveY b c)
        (3 * (c ^ 2 / b) * Real.sin t ^ 2 * Real.cos t) t := by
    unfold curveY
    convert ((Real.hasDerivAt_sin t).pow 3).const_mul (c ^ 2 / b) using 1 <;>
      ring
  have htpi : t ≤ Real.pi := by
    nlinarith [ht.2, Real.pi_pos]
  have hsin : 0 ≤ Real.sin t :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht.1 htpi
  have hcos : 0 ≤ Real.cos t := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [ht.1, ht.2, Real.pi_pos]
  rw [hx.deriv, hy.deriv]
  have harg :
      0 ≤
        (-3 * (c ^ 2 / a) * Real.cos t ^ 2 * Real.sin t) ^ 2 +
          (3 * (c ^ 2 / b) * Real.sin t ^ 2 * Real.cos t) ^ 2 := by
    positivity
  have hspeed : 0 ≤ speedFormula a b c t := by
    unfold speedFormula
    positivity
  have hrad :
      0 ≤ b ^ 2 * Real.cos t ^ 2 + a ^ 2 * Real.sin t ^ 2 := by
    positivity
  have hsq :
      speedFormula a b c t ^ 2 =
        (-3 * (c ^ 2 / a) * Real.cos t ^ 2 * Real.sin t) ^ 2 +
          (3 * (c ^ 2 / b) * Real.sin t ^ 2 * Real.cos t) ^ 2 := by
    unfold speedFormula
    field_simp [ne_of_gt ha, ne_of_gt hb]
    rw [Real.sq_sqrt hrad]
  have hsqrt := Real.sqrt_nonneg
    ((-3 * (c ^ 2 / a) * Real.cos t ^ 2 * Real.sin t) ^ 2 +
      (3 * (c ^ 2 / b) * Real.sin t ^ 2 * Real.cos t) ^ 2)
  have hsqrt_sq := Real.sq_sqrt harg
  nlinarith

theorem gap2 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : b < a) :
    s a b c =
      4 * ∫ t in (0 : ℝ)..Real.pi / 2, speedFormula a b c t := by
  rfl

theorem gap3 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : b < a) (hc2 : c ^ 2 = a ^ 2 - b ^ 2) :
    s a b c =
      primitive a b c (Real.pi / 2) - primitive a b c 0 := by
  rw [s, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    exact primitive_derivative a b c ha hb hab t
  · have hcont : Continuous (fun t => 4 * speedFormula a b c t) := by
      unfold speedFormula
      fun_prop
    exact hcont.intervalIntegrable _ _

theorem gap4 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : b < a) (hc2 : c ^ 2 = a ^ 2 - b ^ 2) :
    primitive a b c (Real.pi / 2) - primitive a b c 0 =
      4 * (a ^ 3 - b ^ 3) / (a * b) := by
  have hd : 0 < a ^ 2 - b ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hab) (add_pos ha hb)]
  unfold primitive
  simp only [Real.sin_pi_div_two, Real.sin_zero, one_pow, mul_one]
  rw [show b ^ 2 + (a ^ 2 - b ^ 2) = a ^ 2 by ring]
  have hzero_sq : (0 : ℝ) ^ 2 = 0 := by norm_num
  simp only [hzero_sq, mul_zero, add_zero]
  rw [sq_rpow_three_halves a ha, sq_rpow_three_halves b hb, hc2]
  field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hd]
  ring

theorem gap5 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : b < a) (hc2 : c ^ 2 = a ^ 2 - b ^ 2) :
    s a b c = 4 * (a ^ 3 - b ^ 3) / (a * b) := by
  rw [gap3 a b c ha hb hc hab hc2]
  exact gap4 a b c ha hb hc hab hc2

end
end ProofGap.Exercise2441
