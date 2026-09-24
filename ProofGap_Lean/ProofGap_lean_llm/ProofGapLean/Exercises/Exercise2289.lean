import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open scoped Interval

namespace ProofGap.Exercise2289

noncomputable section

def parameter (α β : ℝ) : ℂ := (α : ℂ) + Complex.I * (β : ℂ)
def integrand (α β x : ℝ) : ℂ :=
  Complex.exp (parameter α β * (x : ℂ))
def primitive (α β x : ℝ) : ℂ :=
  integrand α β x / parameter α β

private theorem parameter_ne_zero {α β : ℝ} (h : α ≠ 0 ∨ β ≠ 0) :
    parameter α β ≠ 0 := by
  intro hz
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp [parameter] at hre him
  exact h.elim (fun ha => ha hre) (fun hb => hb him)

private theorem conjugateParameter_ne_zero {α β : ℝ} (h : α ≠ 0 ∨ β ≠ 0) :
    (α : ℂ) - Complex.I * β ≠ 0 := by
  intro hz
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp at hre him
  exact h.elim (fun ha => ha hre) (fun hb => hb him)

private theorem integrand_euler (α β x : ℝ) :
    integrand α β x =
      (Real.exp (α * x) * Real.cos (β * x) : ℝ) +
        Complex.I * (Real.exp (α * x) * Real.sin (β * x) : ℝ) := by
  unfold integrand parameter
  have harg :
      ((α : ℂ) + Complex.I * (β : ℂ)) * (x : ℂ) =
        ((α * x : ℝ) : ℂ) + ((β * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_add_mul_I]
  simp [Complex.ofReal_exp]
  ring

theorem gap1 (α β a b : ℝ) :
    (∫ x in a..b, integrand α β x) =
      (∫ x in a..b,
          (Real.exp (α * x) * Real.cos (β * x) : ℝ)) +
        Complex.I * ∫ x in a..b,
          (Real.exp (α * x) * Real.sin (β * x) : ℝ) := by
  have hcR : Continuous (fun x : ℝ =>
      Real.exp (α * x) * Real.cos (β * x)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have hsR : Continuous (fun x : ℝ =>
      Real.exp (α * x) * Real.sin (β * x)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  have hc : IntervalIntegrable (fun x : ℝ =>
      ((Real.exp (α * x) * Real.cos (β * x) : ℝ) : ℂ))
      MeasureTheory.volume a b :=
    by simpa only [Function.comp_apply] using
      (Complex.continuous_ofReal.comp hcR).intervalIntegrable a b
  have hs : IntervalIntegrable (fun x : ℝ =>
      ((Real.exp (α * x) * Real.sin (β * x) : ℝ) : ℂ))
      MeasureTheory.volume a b :=
    by simpa only [Function.comp_apply] using
      (Complex.continuous_ofReal.comp hsR).intervalIntegrable a b
  have hIs := hs.const_mul Complex.I
  have hmul :
      (∫ x in a..b, Complex.I *
        ((Real.exp (α * x) * Real.sin (β * x) : ℝ) : ℂ)) =
        Complex.I * ∫ x in a..b,
          ((Real.exp (α * x) * Real.sin (β * x) : ℝ) : ℂ) := by
    simpa only using
      (intervalIntegral.integral_const_mul
        (μ := MeasureTheory.volume) (a := a) (b := b)
        (r := Complex.I)
        (f := fun x : ℝ =>
          ((Real.exp (α * x) * Real.sin (β * x) : ℝ) : ℂ)))
  calc
    (∫ x in a..b, integrand α β x) =
        ∫ x in a..b,
          ((Real.exp (α * x) * Real.cos (β * x) : ℝ) : ℂ) +
            Complex.I *
              ((Real.exp (α * x) * Real.sin (β * x) : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact integrand_euler α β x
    _ = (∫ x in a..b,
          ((Real.exp (α * x) * Real.cos (β * x) : ℝ) : ℂ)) +
        ∫ x in a..b,
          Complex.I *
            ((Real.exp (α * x) * Real.sin (β * x) : ℝ) : ℂ) := by
      rw [intervalIntegral.integral_add hc hIs]
    _ = (∫ x in a..b,
          (Real.exp (α * x) * Real.cos (β * x) : ℝ)) +
        Complex.I * ∫ x in a..b,
          (Real.exp (α * x) * Real.sin (β * x) : ℝ) := by
      rw [intervalIntegral.integral_ofReal]
      rw [hmul]
      rw [intervalIntegral.integral_ofReal]

theorem gap2 (α β a b : ℝ) (h : α ≠ 0 ∨ β ≠ 0) :
    (∫ x in a..b, integrand α β x) =
      primitive α β b - primitive α β a := by
  have hp := parameter_ne_zero h
  have hi := integral_exp_mul_complex (a := a) (b := b) hp
  unfold integrand
  convert hi using 1
  unfold primitive integrand
  ring

theorem gap3 (α β a b : ℝ) (h : α ≠ 0 ∨ β ≠ 0) :
    (∫ x in a..b, integrand α β x) =
      (integrand α β b * ((α : ℂ) - Complex.I * β) /
          (parameter α β * ((α : ℂ) - Complex.I * β))) -
        (integrand α β a * ((α : ℂ) - Complex.I * β) /
          (parameter α β * ((α : ℂ) - Complex.I * β))) := by
  rw [gap2 α β a b h]
  unfold primitive
  have hp := parameter_ne_zero h
  have hc := conjugateParameter_ne_zero h
  field_simp [hp, hc]

theorem gap4 (α β a b : ℝ) (h : α ≠ 0 ∨ β ≠ 0) :
    (∫ x in a..b, integrand α β x) =
      primitive α β b - primitive α β a := by
  exact gap2 α β a b h

theorem gap5 (α β a b : ℝ) (h : α ≠ 0 ∨ β ≠ 0) :
    primitive α β b - primitive α β a =
      (integrand α β b - integrand α β a) / parameter α β := by
  unfold primitive
  ring

theorem gap6 (α β a b : ℝ) (h : α ≠ 0 ∨ β ≠ 0) :
    (∫ x in a..b, integrand α β x) =
      (integrand α β b - integrand α β a) / parameter α β := by
  exact (gap4 α β a b h).trans (gap5 α β a b h)

theorem gap7 (α β a b : ℝ) (h : α ≠ 0 ∨ β ≠ 0) :
    (∫ x in a..b, integrand α β x) =
      (Complex.exp ((b : ℂ) * parameter α β) -
          Complex.exp ((a : ℂ) * parameter α β)) / parameter α β := by
  calc
    (∫ x in a..b, integrand α β x) =
        (integrand α β b - integrand α β a) / parameter α β :=
      gap6 α β a b h
    _ = (Complex.exp ((b : ℂ) * parameter α β) -
          Complex.exp ((a : ℂ) * parameter α β)) / parameter α β := by
      unfold integrand
      rw [mul_comm (parameter α β) (b : ℂ),
        mul_comm (parameter α β) (a : ℂ)]

end

end ProofGap.Exercise2289
