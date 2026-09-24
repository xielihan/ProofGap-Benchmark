import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

namespace ProofGap.Exercise919

noncomputable section

def q (x : ℝ) : ℝ :=
  x / (1 + x)

def y (x : ℝ) : ℝ :=
  x * Real.arcsin (Real.sqrt (q x)) +
    Real.arctan (Real.sqrt x) - Real.sqrt x

def expandedDerivative (x : ℝ) : ℝ :=
  Real.arcsin (Real.sqrt (q x)) +
    x / Real.sqrt (1 - q x) *
      (1 / (2 * Real.sqrt (q x))) *
      ((1 + x - x) / (1 + x) ^ 2) +
    1 / (2 * Real.sqrt x * (1 + x)) -
    1 / (2 * Real.sqrt x)

def finalDerivative (x : ℝ) : ℝ :=
  Real.arcsin (Real.sqrt (q x))

/-- Exercise 919, gap 1; `x > 0` places every square root
and the inverse-sine argument in the required strict domains. -/
theorem gap1 (x : ℝ) (hx : 0 < x) :
    HasDerivAt y (expandedDerivative x) x := by
  have hx1 : 0 < 1 + x := by linarith
  have hq_pos : 0 < q x := by
    rw [q]
    exact div_pos hx hx1
  have hq_lt : q x < 1 := by
    rw [q]
    exact (div_lt_one hx1).2 (by linarith)
  have h1q_pos : 0 < 1 - q x := by linarith
  have hsqrtq_pos : 0 < Real.sqrt (q x) := Real.sqrt_pos.2 hq_pos
  have hsqrt1q_pos : 0 < Real.sqrt (1 - q x) := Real.sqrt_pos.2 h1q_pos
  have hsqrtx_pos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hq_sq : (Real.sqrt (q x)) ^ 2 = q x :=
    Real.sq_sqrt (le_of_lt hq_pos)
  have hx_sq : (Real.sqrt x) ^ 2 = x :=
    Real.sq_sqrt (le_of_lt hx)
  have harg : Real.sqrt (q x) ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor <;> nlinarith [Real.sqrt_nonneg (q x), hq_sq]
  have hden : HasDerivAt (fun z : ℝ => 1 + z) 1 x := by
    simpa using
      ((hasDerivAt_const (x := x) (c := (1 : ℝ))).add
        (hasDerivAt_id x))
  have hq_deriv :
      HasDerivAt q ((1 + x - x) / (1 + x) ^ 2) x := by
    have hquot := (hasDerivAt_id x).div hden hx1.ne'
    convert hquot using 1 <;> simp <;> ring
  have hsqrtq :
      HasDerivAt (fun z : ℝ => Real.sqrt (q z))
        (1 / (2 * Real.sqrt (q x)) *
          ((1 + x - x) / (1 + x) ^ 2)) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_sqrt hq_pos.ne').comp x hq_deriv
  have hasin :
      HasDerivAt (fun z : ℝ => Real.arcsin (Real.sqrt (q z)))
        (1 / Real.sqrt (1 - (Real.sqrt (q x)) ^ 2) *
          (1 / (2 * Real.sqrt (q x)) *
            ((1 + x - x) / (1 + x) ^ 2))) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_arcsin harg.1.ne' harg.2.ne).comp x hsqrtq
  have hsqrtx :
      HasDerivAt (fun z : ℝ => Real.sqrt z)
        (1 / (2 * Real.sqrt x)) x := by
    simpa using Real.hasDerivAt_sqrt hx.ne'
  have hatan :
      HasDerivAt (fun z : ℝ => Real.arctan (Real.sqrt z))
        (1 / (1 + (Real.sqrt x) ^ 2) *
          (1 / (2 * Real.sqrt x))) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_arctan (Real.sqrt x)).comp x hsqrtx
  have htotal :=
    (((hasDerivAt_id x).mul hasin).add hatan).sub hsqrtx
  unfold y expandedDerivative
  convert htotal using 1 <;>
    simp only [Function.comp_apply, id_eq, one_mul]
  rw [hq_sq, hx_sq]
  field_simp [hsqrtq_pos.ne', hsqrt1q_pos.ne', hsqrtx_pos.ne', hx1.ne']

/-- Exercise 919, gap 2; positivity makes all displayed
root and rational denominators nonzero. -/
theorem gap2 (x : ℝ) (hx : 0 < x) :
    expandedDerivative x = finalDerivative x := by
  have hx1 : 0 < 1 + x := by linarith
  have hq_pos : 0 < q x := by
    rw [q]
    exact div_pos hx hx1
  have hq_lt : q x < 1 := by
    rw [q]
    exact (div_lt_one hx1).2 (by linarith)
  have h1q_pos : 0 < 1 - q x := by linarith
  have hsqrtq_pos : 0 < Real.sqrt (q x) := Real.sqrt_pos.2 hq_pos
  have hsqrt1q_pos : 0 < Real.sqrt (1 - q x) := Real.sqrt_pos.2 h1q_pos
  have hsqrtx_pos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hq_cross :
      (Real.sqrt (q x)) ^ 2 * (1 + x) = x := by
    rw [Real.sq_sqrt (le_of_lt hq_pos), q]
    field_simp [hx1.ne'] <;> ring
  have h1q_cross :
      (Real.sqrt (1 - q x)) ^ 2 * (1 + x) = 1 := by
    rw [Real.sq_sqrt (le_of_lt h1q_pos), q]
    field_simp [hx1.ne'] <;> ring
  have hx_sq : (Real.sqrt x) ^ 2 = x :=
    Real.sq_sqrt (le_of_lt hx)
  have hprod_sq :
      (Real.sqrt (q x) * Real.sqrt (1 - q x) * (1 + x)) ^ 2 =
        (Real.sqrt x) ^ 2 := by
    calc
      (Real.sqrt (q x) * Real.sqrt (1 - q x) * (1 + x)) ^ 2 =
          ((Real.sqrt (q x)) ^ 2 * (1 + x)) *
            ((Real.sqrt (1 - q x)) ^ 2 * (1 + x)) := by ring
      _ = x * 1 := by rw [hq_cross, h1q_cross]
      _ = (Real.sqrt x) ^ 2 := by rw [hx_sq, mul_one]
  have hprod_pos :
      0 < Real.sqrt (q x) * Real.sqrt (1 - q x) * (1 + x) :=
    mul_pos (mul_pos hsqrtq_pos hsqrt1q_pos) hx1
  have hprod :
      Real.sqrt (q x) * Real.sqrt (1 - q x) * (1 + x) =
        Real.sqrt x := by
    nlinarith [hprod_sq, Real.sqrt_nonneg x,
      sq_nonneg
        (Real.sqrt (q x) * Real.sqrt (1 - q x) * (1 + x) -
          Real.sqrt x),
      sq_nonneg
        (Real.sqrt (q x) * Real.sqrt (1 - q x) * (1 + x) +
          Real.sqrt x)]
  unfold expandedDerivative finalDerivative
  field_simp [hsqrtq_pos.ne', hsqrt1q_pos.ne', hsqrtx_pos.ne', hx1.ne'] <;>
    linear_combination -x * hprod

/-- Exercise 919, gap 3; retain the positive domain of the
staged square-root derivation. -/
theorem gap3 (x : ℝ) (hx : 0 < x) :
    HasDerivAt y (finalDerivative x) x := by
  simpa only [gap2 x hx] using (gap1 x hx)

end

end ProofGap.Exercise919
