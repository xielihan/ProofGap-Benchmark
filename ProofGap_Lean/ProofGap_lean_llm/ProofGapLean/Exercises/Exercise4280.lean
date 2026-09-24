import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4280

noncomputable section

open scoped Interval

abbrev Point3 := ℝ × ℝ × ℝ

def curve (a b t : ℝ) : Point3 :=
  (a * Real.cos t, a * Real.sin t, b * t)

def field (p : Point3) : Point3 :=
  (p.2.1, p.2.2, p.1)

def dot (u v : Point3) : ℝ :=
  u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2

def tangent (γ : ℝ → Point3) (t : ℝ) : Point3 :=
  (deriv (fun s => (γ s).1) t,
    deriv (fun s => (γ s).2.1) t,
    deriv (fun s => (γ s).2.2) t)

def lineIntegral (a b : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..2 * Real.pi,
    dot (field (curve a b t)) (tangent (curve a b) t)

def pulledIntegrand (a b t : ℝ) : ℝ :=
  -a ^ 2 * Real.sin t * Real.sin t +
    a * b * t * Real.cos t + a * b * Real.cos t

def antiderivative (a b t : ℝ) : ℝ :=
  -(a ^ 2 * t) / 2 + a ^ 2 * Real.sin (2 * t) / 4 +
    a * b * t * Real.sin t + a * b * Real.cos t +
    a * b * Real.sin t

private theorem antiderivative_hasDerivAt (a b t : ℝ) :
    HasDerivAt (antiderivative a b) (pulledIntegrand a b t) t := by
  have h1 := (((hasDerivAt_id t).const_mul (a ^ 2)).neg.div_const 2)
  have h2 :=
    (((Real.hasDerivAt_sin (2 * t)).comp t
      ((hasDerivAt_id t).const_mul 2)).const_mul (a ^ 2)).div_const 4
  have h3 :=
    ((hasDerivAt_id t).const_mul (a * b)).mul (Real.hasDerivAt_sin t)
  have h4 := (Real.hasDerivAt_cos t).const_mul (a * b)
  have h5 := (Real.hasDerivAt_sin t).const_mul (a * b)
  have hraw :
      HasDerivAt (antiderivative a b)
        (-((a ^ 2) * 1) / 2 +
          (a ^ 2) * (Real.cos (2 * t) * (2 * 1)) / 4 +
          ((a * b) * 1 * Real.sin t + (a * b) * t * Real.cos t) +
          (a * b) * (-Real.sin t) +
          (a * b) * Real.cos t) t := by
    simpa only [antiderivative] using ((((h1.add h2).add h3).add h4).add h5)
  have hcos_sq : Real.cos t ^ 2 = 1 - Real.sin t ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq t]
  have heq :
      -((a ^ 2) * 1) / 2 +
          (a ^ 2) * (Real.cos (2 * t) * (2 * 1)) / 4 +
          ((a * b) * 1 * Real.sin t + (a * b) * t * Real.cos t) +
          (a * b) * (-Real.sin t) +
          (a * b) * Real.cos t =
        pulledIntegrand a b t := by
    rw [Real.cos_two_mul, hcos_sq]
    unfold pulledIntegrand
    ring
  exact heq ▸ hraw

theorem gap1 (a b : ℝ) :
    lineIntegral a b =
      ∫ t in (0 : ℝ)..2 * Real.pi, pulledIntegrand a b t := by
  unfold lineIntegral
  apply intervalIntegral.integral_congr
  intro t _
  have hcos :
      deriv (fun s : ℝ => a * Real.cos s) t = a * (-Real.sin t) :=
    ((Real.hasDerivAt_cos t).const_mul a).deriv
  have hsin :
      deriv (fun s : ℝ => a * Real.sin s) t = a * Real.cos t :=
    ((Real.hasDerivAt_sin t).const_mul a).deriv
  have hlin : deriv (fun s : ℝ => b * s) t = b := by
    simpa using ((hasDerivAt_id t).const_mul b).deriv
  change
    (a * Real.sin t) * deriv (fun s : ℝ => a * Real.cos s) t +
        (b * t) * deriv (fun s : ℝ => a * Real.sin s) t +
        (a * Real.cos t) * deriv (fun s : ℝ => b * s) t =
      pulledIntegrand a b t
  rw [hcos, hsin, hlin]
  unfold pulledIntegrand
  ring

theorem gap2 (a b : ℝ) :
    lineIntegral a b =
      antiderivative a b (2 * Real.pi) - antiderivative a b 0 := by
  have hcont : Continuous (pulledIntegrand a b) := by
    unfold pulledIntegrand
    fun_prop
  calc
    lineIntegral a b =
        ∫ t in (0 : ℝ)..2 * Real.pi, pulledIntegrand a b t := gap1 a b
    _ = ∫ t in (0 : ℝ)..2 * Real.pi,
          deriv (antiderivative a b) t := by
      apply intervalIntegral.integral_congr
      intro t _
      exact (antiderivative_hasDerivAt a b t).deriv.symm
    _ = antiderivative a b (2 * Real.pi) - antiderivative a b 0 := by
      apply intervalIntegral.integral_deriv_eq_sub
      · intro t _
        exact (antiderivative_hasDerivAt a b t).differentiableAt
      · rw [show deriv (antiderivative a b) = pulledIntegrand a b by
          funext t
          exact (antiderivative_hasDerivAt a b t).deriv]
        exact hcont.intervalIntegrable _ _

theorem gap3 (a b : ℝ) :
    antiderivative a b (2 * Real.pi) - antiderivative a b 0 =
      -Real.pi * a ^ 2 := by
  unfold antiderivative
  have hfourpi :
      (2 : ℝ) * (2 * Real.pi) = 2 * Real.pi + 2 * Real.pi := by
    ring
  rw [hfourpi]
  simp
  ring

theorem gap4 (a b : ℝ) :
    lineIntegral a b = -Real.pi * a ^ 2 := by
  exact (gap2 a b).trans (gap3 a b)

end

end ProofGap.Exercise4280
