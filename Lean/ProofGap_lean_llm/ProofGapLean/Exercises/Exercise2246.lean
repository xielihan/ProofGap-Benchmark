import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped Interval

namespace ProofGap.Exercise2246

noncomputable section

def xOfT (a t : ℝ) : ℝ := a * Real.sin t
def jacobian (a t : ℝ) : ℝ := a * Real.cos t
def trigIntegrand (t : ℝ) : ℝ := Real.sin t ^ 2 * Real.cos t ^ 2
def primitive (a t : ℝ) : ℝ :=
  (a ^ 4 / 8) * (t - (1 / 4 : ℝ) * Real.sin (4 * t))

theorem gap1 (a : ℝ) (ha : 0 ≤ a) :
    (∫ x in (0 : ℝ)..a, x ^ 2 * Real.sqrt (a ^ 2 - x ^ 2)) =
      a ^ 4 * ∫ t in (0 : ℝ)..Real.pi / 2, trigIntegrand t := by
  have hsub :
      (∫ t in (0 : ℝ)..Real.pi / 2,
          ((xOfT a t) ^ 2 * Real.sqrt (a ^ 2 - (xOfT a t) ^ 2)) *
            jacobian a t) =
        ∫ x in xOfT a 0..xOfT a (Real.pi / 2),
          x ^ 2 * Real.sqrt (a ^ 2 - x ^ 2) := by
    have hderiv :
        ∀ t ∈ Set.uIcc (0 : ℝ) (Real.pi / 2),
          HasDerivAt (xOfT a) (jacobian a t) t := by
      intro t _
      simpa [xOfT, jacobian] using
        (Real.hasDerivAt_sin t).const_mul a
    have hjac : Continuous (jacobian a) := by
      simpa only [jacobian] using
        (continuous_const.mul Real.continuous_cos)
    have hintegrand :
        Continuous
          (fun x : ℝ => x ^ 2 * Real.sqrt (a ^ 2 - x ^ 2)) :=
      (continuous_id.pow 2).mul
        ((continuous_const.sub (continuous_id.pow 2)).sqrt)
    simpa only [Function.comp_apply] using
      (intervalIntegral.integral_comp_mul_deriv
        (a := (0 : ℝ)) (b := Real.pi / 2)
        (f := xOfT a) (f' := jacobian a)
        (g := fun x : ℝ => x ^ 2 * Real.sqrt (a ^ 2 - x ^ 2))
        hderiv hjac.continuousOn hintegrand)
  calc
    (∫ x in (0 : ℝ)..a, x ^ 2 * Real.sqrt (a ^ 2 - x ^ 2)) =
        ∫ t in (0 : ℝ)..Real.pi / 2,
          ((xOfT a t) ^ 2 * Real.sqrt (a ^ 2 - (xOfT a t) ^ 2)) *
            jacobian a t := by
      simpa [xOfT] using hsub.symm
    _ = ∫ t in (0 : ℝ)..Real.pi / 2, a ^ 4 * trigIntegrand t := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
      have ht' : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
        simpa only [Set.uIcc_of_le hpi] using ht
      have hcos : 0 ≤ Real.cos t := by
        apply Real.cos_nonneg_of_mem_Icc
        constructor
        · linarith [Real.pi_pos, ht'.1]
        · exact ht'.2
      have htrig : 1 - Real.sin t ^ 2 = Real.cos t ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq t]
      have hsquare :
          a ^ 2 - (a * Real.sin t) ^ 2 = (a * Real.cos t) ^ 2 := by
        calc
          a ^ 2 - (a * Real.sin t) ^ 2 =
              a ^ 2 * (1 - Real.sin t ^ 2) := by ring
          _ = a ^ 2 * Real.cos t ^ 2 := by rw [htrig]
          _ = (a * Real.cos t) ^ 2 := by ring
      have hsqrt :
          Real.sqrt (a ^ 2 - (a * Real.sin t) ^ 2) =
            a * Real.cos t := by
        rw [hsquare, Real.sqrt_sq_eq_abs,
          abs_of_nonneg (mul_nonneg ha hcos)]
      change
        (a * Real.sin t) ^ 2 *
              Real.sqrt (a ^ 2 - (a * Real.sin t) ^ 2) *
              (a * Real.cos t) =
          a ^ 4 * (Real.sin t ^ 2 * Real.cos t ^ 2)
      rw [hsqrt]
      ring
    _ = a ^ 4 * ∫ t in (0 : ℝ)..Real.pi / 2, trigIntegrand t := by
      rw [intervalIntegral.integral_const_mul]

theorem gap2 (a : ℝ) :
    a ^ 4 * (∫ t in (0 : ℝ)..Real.pi / 2, trigIntegrand t) =
      (a ^ 4 / 4) *
        ∫ t in (0 : ℝ)..Real.pi / 2, Real.sin (2 * t) ^ 2 := by
  have h :
      (∫ t in (0 : ℝ)..Real.pi / 2, trigIntegrand t) =
        (1 / 4 : ℝ) *
          ∫ t in (0 : ℝ)..Real.pi / 2, Real.sin (2 * t) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    change
      Real.sin t ^ 2 * Real.cos t ^ 2 =
        (1 / 4 : ℝ) * Real.sin (2 * t) ^ 2
    rw [Real.sin_two_mul]
    ring
  rw [h]
  ring

theorem gap3 (a : ℝ) :
    (a ^ 4 / 4) *
        (∫ t in (0 : ℝ)..Real.pi / 2, Real.sin (2 * t) ^ 2) =
      primitive a (Real.pi / 2) - primitive a 0 := by
  have hderiv : ∀ t : ℝ,
      HasDerivAt (primitive a)
        ((a ^ 4 / 4) * Real.sin (2 * t) ^ 2) t := by
    intro t
    have hsin :
        HasDerivAt (fun s : ℝ => Real.sin (4 * s))
          (4 * Real.cos (4 * t)) t := by
      simpa only [Function.comp_def, mul_comm, one_mul] using
        (Real.hasDerivAt_sin (4 * t)).comp t
          ((hasDerivAt_id t).const_mul 4)
    have hraw :
        HasDerivAt (primitive a)
          ((a ^ 4 / 8) *
            (1 - (1 / 4 : ℝ) * (4 * Real.cos (4 * t)))) t := by
      simpa only [primitive] using
        (((hasDerivAt_id t).sub
          (hsin.const_mul (1 / 4 : ℝ))).const_mul (a ^ 4 / 8))
    have hdouble := Real.cos_two_mul (2 * t)
    rw [show 2 * (2 * t) = 4 * t by ring] at hdouble
    have htrig :
        1 - Real.cos (4 * t) = 2 * Real.sin (2 * t) ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq (2 * t), hdouble]
    have hvalue :
        (a ^ 4 / 8) *
            (1 - (1 / 4 : ℝ) * (4 * Real.cos (4 * t))) =
          (a ^ 4 / 4) * Real.sin (2 * t) ^ 2 := by
      calc
        (a ^ 4 / 8) *
            (1 - (1 / 4 : ℝ) * (4 * Real.cos (4 * t))) =
            (a ^ 4 / 8) * (1 - Real.cos (4 * t)) := by ring
        _ = (a ^ 4 / 8) * (2 * Real.sin (2 * t) ^ 2) := by
          rw [htrig]
        _ = (a ^ 4 / 4) * Real.sin (2 * t) ^ 2 := by ring
    rw [hvalue] at hraw
    exact hraw
  have hcontinuous :
      Continuous
        (fun t : ℝ => (a ^ 4 / 4) * Real.sin (2 * t) ^ 2) :=
    continuous_const.mul
      ((Real.continuous_sin.comp
        (continuous_const.mul continuous_id)).pow 2)
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hderiv t) (hcontinuous.intervalIntegrable _ _)

theorem gap4 (a : ℝ) :
    primitive a (Real.pi / 2) - primitive a 0 =
      Real.pi * a ^ 4 / 16 := by
  unfold primitive
  rw [show 4 * (Real.pi / 2) = 2 * Real.pi by ring,
    Real.sin_two_pi]
  simp only [mul_zero, Real.sin_zero]
  ring

theorem gap5 (a : ℝ) (ha : 0 ≤ a) :
    (∫ x in (0 : ℝ)..a, x ^ 2 * Real.sqrt (a ^ 2 - x ^ 2)) =
      Real.pi * a ^ 4 / 16 := by
  calc
    (∫ x in (0 : ℝ)..a, x ^ 2 * Real.sqrt (a ^ 2 - x ^ 2)) =
        a ^ 4 * ∫ t in (0 : ℝ)..Real.pi / 2, trigIntegrand t :=
      gap1 a ha
    _ = (a ^ 4 / 4) *
        ∫ t in (0 : ℝ)..Real.pi / 2, Real.sin (2 * t) ^ 2 :=
      gap2 a
    _ = primitive a (Real.pi / 2) - primitive a 0 := gap3 a
    _ = Real.pi * a ^ 4 / 16 := gap4 a

end

end ProofGap.Exercise2246
