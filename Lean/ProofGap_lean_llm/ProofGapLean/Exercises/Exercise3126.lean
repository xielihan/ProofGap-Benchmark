import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace ProofGap.Exercise3126

noncomputable section

open scoped Interval

def lagrangeModel (x : ℝ) : ℝ :=
  ((x - 0.5) * (x - 1) * (x - 1.5) * (x - 2)) /
      ((-0.5 : ℝ) * (-1) * (-1.5) * (-2)) * 5 +
    (x * (x - 1) * (x - 1.5) * (x - 2)) /
      ((0.5 : ℝ) * (-0.5) * (-1) * (-1.5)) * 4.5 +
    (x * (x - 0.5) * (x - 1.5) * (x - 2)) /
      ((1 : ℝ) * 0.5 * (-0.5) * (-1)) * 3 +
    (x * (x - 0.5) * (x - 1) * (x - 2)) /
      ((1.5 : ℝ) * 1 * 0.5 * (-0.5)) * 2.5 +
    (x * (x - 0.5) * (x - 1) * (x - 1.5)) /
      ((2 : ℝ) * 1.5 * 1 * 0.5) * 5

def cubicModel (x : ℝ) : ℝ :=
  (8 / 3 : ℝ) * x ^ 3 - 6 * x ^ 2 + (4 / 3 : ℝ) * x + 5

def antiderivative (x : ℝ) : ℝ :=
  (2 / 3 : ℝ) * x ^ 4 - 2 * x ^ 3 + (2 / 3 : ℝ) * x ^ 2 + 5 * x

def modelIntegral : ℝ :=
  ∫ x in (0 : ℝ)..2, cubicModel x

def Within (actual approximate tolerance : ℝ) : Prop :=
  |actual - approximate| ≤ tolerance

/--
Source: `proof_gap/exercise_3126/1.txt`; the node data determine an
interpolating polynomial, not the values of an otherwise arbitrary `y`.
-/
theorem gap1 :
    ∀ x : ℝ,
      lagrangeModel x =
        ((x - 0.5) * (x - 1) * (x - 1.5) * (x - 2)) /
            ((-0.5 : ℝ) * (-1) * (-1.5) * (-2)) * 5 +
          (x * (x - 1) * (x - 1.5) * (x - 2)) /
            ((0.5 : ℝ) * (-0.5) * (-1) * (-1.5)) * 4.5 +
          (x * (x - 0.5) * (x - 1.5) * (x - 2)) /
            ((1 : ℝ) * 0.5 * (-0.5) * (-1)) * 3 +
          (x * (x - 0.5) * (x - 1) * (x - 2)) /
            ((1.5 : ℝ) * 1 * 0.5 * (-0.5)) * 2.5 +
          (x * (x - 0.5) * (x - 1) * (x - 1.5)) /
            ((2 : ℝ) * 1.5 * 1 * 0.5) * 5 := by
  intro x
  rfl

/-- Source: `proof_gap/exercise_3126/2.txt`; expand the interpolating polynomial exactly. -/
theorem gap2 :
    ∀ x : ℝ, lagrangeModel x = cubicModel x := by
  intro x
  norm_num [lagrangeModel, cubicModel] <;> ring

/--
Source: `proof_gap/exercise_3126/3.txt`; a uniform function error is
the missing hypothesis needed to control the integral error.
-/
theorem gap3 (y : ℝ → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hy : IntervalIntegrable y MeasureTheory.volume 0 2)
    (hbound : ∀ x ∈ Set.Icc (0 : ℝ) 2, |y x - cubicModel x| ≤ ε) :
    Within (∫ x in (0 : ℝ)..2, y x) modelIntegral (2 * ε) := by
  have hc_cont : Continuous cubicModel := by
    unfold cubicModel
    fun_prop
  have hc :
      IntervalIntegrable cubicModel MeasureTheory.volume (0 : ℝ) 2 :=
    hc_cont.intervalIntegrable 0 2
  unfold Within modelIntegral
  rw [← intervalIntegral.integral_sub hy hc]
  have hnorm :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 2) (C := ε)
      (f := fun x : ℝ => y x - cubicModel x)
      (by
        intro x hx
        norm_num at hx
        rw [Real.norm_eq_abs]
        exact hbound x ⟨le_of_lt hx.1, hx.2⟩)
  simpa [Real.norm_eq_abs, mul_comm] using hnorm

/-- Source: `proof_gap/exercise_3126/4.txt`; fundamental theorem for the polynomial. -/
theorem gap4 :
    modelIntegral = antiderivative 2 - antiderivative 0 := by
  unfold modelIntegral
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have h2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
      convert (hasDerivAt_id x).mul (hasDerivAt_id x) using 1 <;>
        (try funext t) <;>
        simp [id_eq, pow_succ] <;>
        ring_nf
    have h3 : HasDerivAt (fun t : ℝ => t ^ 3) (3 * x ^ 2) x := by
      convert h2.mul (hasDerivAt_id x) using 1 <;>
        (try funext t) <;>
        simp [id_eq, pow_succ] <;>
        ring_nf
    have h4 : HasDerivAt (fun t : ℝ => t ^ 4) (4 * x ^ 3) x := by
      convert h3.mul (hasDerivAt_id x) using 1 <;>
        (try funext t) <;>
        simp [id_eq, pow_succ] <;>
        ring_nf
    unfold antiderivative cubicModel
    convert
      (((((hasDerivAt_const x (2 / 3 : ℝ)).mul h4).sub
        ((hasDerivAt_const x (2 : ℝ)).mul h3)).add
      ((hasDerivAt_const x (2 / 3 : ℝ)).mul h2)).add
      ((hasDerivAt_const x (5 : ℝ)).mul (hasDerivAt_id x))) using 1 <;>
        (try funext t) <;>
        simp [id_eq, pow_succ] <;>
        ring_nf
  · have hc_cont : Continuous cubicModel := by
      unfold cubicModel
      fun_prop
    exact hc_cont.intervalIntegrable 0 2

/-- Source: `proof_gap/exercise_3126/5.txt`; evaluate the endpoints. -/
theorem gap5 :
    antiderivative 2 - antiderivative 0 = 22 / 3 := by
  norm_num [antiderivative]

/--
Source: `proof_gap/exercise_3126/6.txt`; propagate the same uniform
error bound to the final integral estimate.
-/
theorem gap6 (y : ℝ → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hy : IntervalIntegrable y MeasureTheory.volume 0 2)
    (hbound : ∀ x ∈ Set.Icc (0 : ℝ) 2, |y x - cubicModel x| ≤ ε) :
    Within (∫ x in (0 : ℝ)..2, y x) (22 / 3) (2 * ε) := by
  simpa only [gap4, gap5] using gap3 y ε hε hy hbound

end

end ProofGap.Exercise3126
