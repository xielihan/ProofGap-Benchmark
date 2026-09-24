import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped Interval

namespace ProofGap.Exercise2277

noncomputable section

def integrand (x : ℝ) : ℝ :=
  Real.sin x * Real.sin (2 * x) * Real.sin (3 * x)

def expandedIntegrand (x : ℝ) : ℝ :=
  (1 / 4 : ℝ) * Real.sin (4 * x) -
    (1 / 4 : ℝ) * (Real.sin (6 * x) - Real.sin (2 * x))

def primitive (x : ℝ) : ℝ :=
  -(1 / 16 : ℝ) * Real.cos (4 * x) +
    (1 / 24 : ℝ) * Real.cos (6 * x) -
    (1 / 8 : ℝ) * Real.cos (2 * x)

theorem gap1 (x : ℝ) :
    integrand x =
      (1 / 2 : ℝ) * (Real.cos (2 * x) - Real.cos (4 * x)) *
        Real.sin (2 * x) := by
  have h :
      Real.sin x * Real.sin (3 * x) =
        (1 / 2 : ℝ) * (Real.cos (2 * x) - Real.cos (4 * x)) := by
    rw [show 2 * x = 3 * x - x by ring,
      show 4 * x = 3 * x + x by ring]
    rw [Real.cos_sub, Real.cos_add]
    ring
  unfold integrand
  calc
    Real.sin x * Real.sin (2 * x) * Real.sin (3 * x) =
        (Real.sin x * Real.sin (3 * x)) * Real.sin (2 * x) := by ring
    _ = (1 / 2 : ℝ) * (Real.cos (2 * x) - Real.cos (4 * x)) *
        Real.sin (2 * x) := by rw [h]

theorem gap2 (x : ℝ) :
    (1 / 2 : ℝ) * (Real.cos (2 * x) - Real.cos (4 * x)) *
        Real.sin (2 * x) = expandedIntegrand x := by
  have h4 :
      Real.sin (4 * x) =
        2 * Real.sin (2 * x) * Real.cos (2 * x) := by
    rw [show 4 * x = 2 * x + 2 * x by ring, Real.sin_add]
    ring
  have h6 :
      Real.sin (6 * x) =
        Real.sin (4 * x) * Real.cos (2 * x) +
          Real.cos (4 * x) * Real.sin (2 * x) := by
    rw [show 6 * x = 4 * x + 2 * x by ring, Real.sin_add]
  have h2 :
      Real.sin (2 * x) =
        Real.sin (4 * x) * Real.cos (2 * x) -
          Real.cos (4 * x) * Real.sin (2 * x) := by
    calc
      Real.sin (2 * x) = Real.sin (4 * x - 2 * x) := by congr 1 <;> ring
      _ = Real.sin (4 * x) * Real.cos (2 * x) -
          Real.cos (4 * x) * Real.sin (2 * x) := Real.sin_sub _ _
  have h62 :
      Real.sin (6 * x) - Real.sin (2 * x) =
        2 * Real.cos (4 * x) * Real.sin (2 * x) := by
    linarith [h6, h2]
  unfold expandedIntegrand
  rw [h4, h62]
  ring

theorem gap3 (x : ℝ) :
    integrand x = expandedIntegrand x := by
  calc
    integrand x =
        (1 / 2 : ℝ) * (Real.cos (2 * x) - Real.cos (4 * x)) *
          Real.sin (2 * x) := gap1 x
    _ = expandedIntegrand x := gap2 x

theorem gap4 :
    (∫ x in 0..Real.pi / 2, integrand x) =
      primitive (Real.pi / 2) - primitive 0 := by
  have hcos (c x : ℝ) :
      HasDerivAt (fun y : ℝ => Real.cos (c * y))
        (-c * Real.sin (c * x)) x := by
    convert (Real.hasDerivAt_cos (c * x)).comp x
      ((hasDerivAt_id x).const_mul c) using 1 <;> ring
  have hderiv (x : ℝ) :
      HasDerivAt primitive (expandedIntegrand x) x := by
    unfold primitive expandedIntegrand
    have h :=
      (((hcos 4 x).const_mul (-(1 / 16 : ℝ))).add
        ((hcos 6 x).const_mul (1 / 24 : ℝ))).sub
        ((hcos 2 x).const_mul (1 / 8 : ℝ))
    convert h using 1 <;> ring
  have hsin (c : ℝ) :
      Continuous (fun x : ℝ => Real.sin (c * x)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hcont : Continuous expandedIntegrand := by
    unfold expandedIntegrand
    exact
      (continuous_const.mul (hsin 4)).sub
        (continuous_const.mul ((hsin 6).sub (hsin 2)))
  have heq : integrand = expandedIntegrand := funext gap3
  rw [heq]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hderiv x)
    (hcont.intervalIntegrable 0 (Real.pi / 2))

theorem gap5 :
    primitive (Real.pi / 2) - primitive 0 = (1 / 6 : ℝ) := by
  have hcos3 : Real.cos (3 * Real.pi) = (-1 : ℝ) := by
    rw [show 3 * Real.pi = 2 * Real.pi + Real.pi by ring,
      Real.cos_add, Real.cos_two_pi, Real.sin_two_pi,
      Real.cos_pi, Real.sin_pi]
    norm_num
  have h4 : 4 * (Real.pi / 2) = 2 * Real.pi := by ring
  have h6 : 6 * (Real.pi / 2) = 3 * Real.pi := by ring
  have h2 : 2 * (Real.pi / 2) = Real.pi := by ring
  unfold primitive
  rw [h4, h6, h2, Real.cos_two_pi, hcos3, Real.cos_pi]
  norm_num [Real.cos_zero]

theorem gap6 :
    (∫ x in 0..Real.pi / 2, integrand x) = (1 / 6 : ℝ) := by
  calc
    (∫ x in 0..Real.pi / 2, integrand x) =
        primitive (Real.pi / 2) - primitive 0 := gap4
    _ = (1 / 6 : ℝ) := gap5

end

end ProofGap.Exercise2277
