import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise3718_2

noncomputable section

open scoped Interval

def integralFunction (a b α : ℝ) : ℝ :=
  ∫ x in a + α..b + α, Real.sin (α * x) / x

def leibnizDerivative (a b α : ℝ) : ℝ :=
  Real.sin (α * (b + α)) / (b + α) -
      Real.sin (α * (a + α)) / (a + α) +
    ∫ x in a + α..b + α, Real.cos (α * x)

def closedDerivative (a b α : ℝ) : ℝ :=
  (1 / α + 1 / (b + α)) * Real.sin (α * (b + α)) -
    (1 / α + 1 / (a + α)) * Real.sin (α * (a + α))

theorem gap1 (a b α : ℝ) (ha : a + α ≠ 0) (hb : b + α ≠ 0) :
    deriv (integralFunction a b) α = leibnizDerivative a b α := by
  let S : ℝ → ℝ := fun y => ∫ t in (0 : ℝ)..y, Real.sinc t
  have hS (y : ℝ) : HasDerivAt S (Real.sinc y) y := by
    simpa [S] using
      intervalIntegral.integral_hasDerivAt_right
        (a := (0 : ℝ))
        (Real.continuous_sinc.intervalIntegrable (0 : ℝ) y)
        Real.continuous_sinc.stronglyMeasurable.stronglyMeasurableAtFilter
        Real.continuous_sinc.continuousAt
  have hrepr (β l u : ℝ) :
      (∫ x in l..u, Real.sin (β * x) / x) =
        S (β * u) - S (β * l) := by
    have hzero : ∀ᵐ x : ℝ ∂MeasureTheory.volume, x ≠ 0 := by
      change MeasureTheory.volume {x : ℝ | ¬ x ≠ 0} = 0
      simp
    have hae : ∀ᵐ x ∂MeasureTheory.volume,
        Real.sin (β * x) / x = β * Real.sinc (β * x) := by
      filter_upwards [hzero] with x hx
      by_cases hβ : β = 0
      · subst β
        simp
      · have hβx : β * x ≠ 0 := mul_ne_zero hβ hx
        simp only [Real.sinc, if_neg hβx]
        field_simp [hβ, hx, hβx] <;> ring_nf
    have hant (x : ℝ) :
        HasDerivAt (fun y : ℝ => S (β * y))
          (β * Real.sinc (β * x)) x := by
      simpa [mul_comm] using
        (hS (β * x)).comp x
          ((hasDerivAt_const x β).mul (hasDerivAt_id x))
    have hc : Continuous (fun x : ℝ => β * Real.sinc (β * x)) :=
      continuous_const.mul
        (Real.continuous_sinc.comp (continuous_const.mul continuous_id))
    calc
      (∫ x in l..u, Real.sin (β * x) / x) =
          ∫ x in l..u, β * Real.sinc (β * x) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hae] with x hx
        intro _
        exact hx
      _ = S (β * u) - S (β * l) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x _ => hant x) (hc.intervalIntegrable l u)
  have hfun : integralFunction a b = fun β : ℝ =>
      S (β * (b + β)) - S (β * (a + β)) := by
    funext β
    simpa [integralFunction] using hrepr β (a + β) (b + β)
  have hu : HasDerivAt (fun β : ℝ => β * (b + β))
      (b + α + α) α := by
    convert (hasDerivAt_id α).mul
      ((hasDerivAt_const α b).add (hasDerivAt_id α)) using 1 <;>
      simp <;> ring
  have hl : HasDerivAt (fun β : ℝ => β * (a + β))
      (a + α + α) α := by
    convert (hasDerivAt_id α).mul
      ((hasDerivAt_const α a).add (hasDerivAt_id α)) using 1 <;>
      simp <;> ring
  have hd : HasDerivAt
      (fun β : ℝ => S (β * (b + β)) - S (β * (a + β)))
      (Real.sinc (α * (b + α)) * (b + α + α) -
        Real.sinc (α * (a + α)) * (a + α + α)) α := by
    simpa [Function.comp_apply] using
      (((hS (α * (b + α))).comp α hu).sub
        ((hS (α * (a + α))).comp α hl))
  rw [hfun, hd.deriv]
  by_cases hα : α = 0
  · subst α
    simp [leibnizDerivative, Real.sinc] <;> ring
  · have hint : (∫ x in a + α..b + α, Real.cos (α * x)) =
        Real.sin (α * (b + α)) / α -
          Real.sin (α * (a + α)) / α := by
      have hanti (x : ℝ) :
          HasDerivAt (fun y : ℝ => Real.sin (α * y) / α)
            (Real.cos (α * x)) x := by
        simpa [hα] using
          (((Real.hasDerivAt_sin (α * x)).comp x
            ((hasDerivAt_const x α).mul (hasDerivAt_id x))).div_const α)
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hanti x)
        ((Real.continuous_cos.comp
          (continuous_const.mul continuous_id)).intervalIntegrable _ _)
    unfold leibnizDerivative
    rw [hint]
    have hαb : α * (b + α) ≠ 0 := mul_ne_zero hα hb
    have hαa : α * (a + α) ≠ 0 := mul_ne_zero hα ha
    simp only [Real.sinc, if_neg hαb, if_neg hαa]
    field_simp [hα, ha, hb] <;> ring

theorem gap2 (a b α : ℝ) (hα : α ≠ 0)
    (ha : a + α ≠ 0) (hb : b + α ≠ 0) :
    deriv (integralFunction a b) α = closedDerivative a b α := by
  rw [gap1 a b α ha hb]
  have hanti (x : ℝ) :
      HasDerivAt (fun y : ℝ => Real.sin (α * y) / α)
        (Real.cos (α * x)) x := by
    simpa [hα] using
      (((Real.hasDerivAt_sin (α * x)).comp x
        ((hasDerivAt_const x α).mul (hasDerivAt_id x))).div_const α)
  have hint : (∫ x in a + α..b + α, Real.cos (α * x)) =
      Real.sin (α * (b + α)) / α -
        Real.sin (α * (a + α)) / α := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hanti x)
      ((Real.continuous_cos.comp
        (continuous_const.mul continuous_id)).intervalIntegrable _ _)
  unfold leibnizDerivative closedDerivative
  rw [hint]
  field_simp [hα, ha, hb] <;> ring

end

end ProofGap.Exercise3718_2
