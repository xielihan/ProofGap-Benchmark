import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3446

noncomputable section

open scoped Interval

def d1 (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv f x

def d2 (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv f) x

def weight (u : ℝ → ℝ) (x₀ x : ℝ) : ℝ :=
  Real.exp (∫ s in x₀..x, u s)

def ScaleInvariantZero (Φ : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ c a b d, c ≠ 0 →
    (Φ (c * a) (c * b) (c * d) = 0 ↔ Φ a b d = 0)

theorem gap1 (u y : ℝ → ℝ) (x₀ : ℝ)
    (hRepresentation : ∀ x, y x = weight u x₀ x)
    (hu : Continuous u) :
    ∀ x, d1 y x = u x * weight u x₀ x := by
  intro x
  have hIntegrable :
      IntervalIntegrable u MeasureTheory.volume x₀ x :=
    hu.intervalIntegrable x₀ x
  have hMeasurable :
      StronglyMeasurableAtFilter u (nhds x) MeasureTheory.volume :=
    hu.stronglyMeasurable.stronglyMeasurableAtFilter
  have hInt :
      HasDerivAt (fun z : ℝ => ∫ s in x₀..z, u s) (u x) x :=
    intervalIntegral.integral_hasDerivAt_right
      hIntegrable hMeasurable hu.continuousAt
  have hExp := (Real.hasDerivAt_exp _).comp x hInt
  rw [show y = weight u x₀ from funext hRepresentation]
  simpa only [d1, weight, mul_comm] using hExp.deriv

theorem gap2 (u y : ℝ → ℝ) (x₀ : ℝ)
    (hRepresentation : ∀ x, y x = weight u x₀ x)
    (hu : ContDiff ℝ 1 u) :
    ∀ x,
      d2 y x =
        (d1 u x + (u x) ^ 2) * weight u x₀ x := by
  intro x
  have huc : Continuous u := hu.continuous
  have hdy : deriv y = fun z => u z * weight u x₀ z := by
    funext z
    simpa only [d1] using
      (gap1 u y x₀ hRepresentation huc z)
  have hu' : HasDerivAt u (d1 u x) x := by
    simpa only [d1] using
      (hu.differentiable one_ne_zero).differentiableAt.hasDerivAt
  have hIntegrable :
      IntervalIntegrable u MeasureTheory.volume x₀ x :=
    huc.intervalIntegrable x₀ x
  have hMeasurable :
      StronglyMeasurableAtFilter u (nhds x) MeasureTheory.volume :=
    huc.stronglyMeasurable.stronglyMeasurableAtFilter
  have hInt :
      HasDerivAt (fun z : ℝ => ∫ s in x₀..z, u s) (u x) x :=
    intervalIntegral.integral_hasDerivAt_right
      hIntegrable hMeasurable huc.continuousAt
  have hw' :
      HasDerivAt (weight u x₀) (u x * weight u x₀ x) x := by
    simpa only [weight, mul_comm] using
      ((Real.hasDerivAt_exp _).comp x hInt)
  calc
    d2 y x = deriv (fun z => u z * weight u x₀ z) x := by
      simp only [d2, hdy]
    _ = d1 u x * weight u x₀ x +
          u x * (u x * weight u x₀ x) :=
      (hu'.mul hw').deriv
    _ = (d1 u x + (u x) ^ 2) * weight u x₀ x := by
      ring

theorem gap3 (Φ : ℝ → ℝ → ℝ → ℝ) (u y : ℝ → ℝ) (x₀ : ℝ)
    (hODE : ∀ x, Φ (y x) (d1 y x) (d2 y x) = 0)
    (hRepresentation : ∀ x, y x = weight u x₀ x)
    (hFirst :
      ∀ x, d1 y x = u x * weight u x₀ x)
    (hSecond :
      ∀ x,
        d2 y x =
          (d1 u x + (u x) ^ 2) * weight u x₀ x)
    (hScale : ScaleInvariantZero Φ) :
    ∀ x, Φ 1 (u x) (d1 u x + (u x) ^ 2) = 0 := by
  intro x
  have hODE' := hODE x
  rw [hRepresentation x, hFirst x, hSecond x] at hODE'
  have hw : weight u x₀ x ≠ 0 := by
    simp [weight]
  have hscaled :
      Φ (weight u x₀ x * 1)
        (weight u x₀ x * u x)
        (weight u x₀ x * (d1 u x + (u x) ^ 2)) = 0 := by
    simpa [mul_comm] using hODE'
  exact
    (hScale (weight u x₀ x) 1 (u x)
      (d1 u x + (u x) ^ 2) hw).mp hscaled

end

end ProofGap.Exercise3446
