import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Defs.Filter

open scoped Interval

namespace ProofGap.Exercise2248

noncomputable section

def xOfT (t : ℝ) : ℝ := Real.log (1 + t ^ 2)
def jacobian (t : ℝ) : ℝ := 2 * t / (1 + t ^ 2)
def pullback (t : ℝ) : ℝ := 2 * t ^ 2 / (1 + t ^ 2)
def primitive (t : ℝ) : ℝ := 2 * (t - Real.arctan t)

private theorem intervalIntegral.integral_deriv_eq_sub_of_hasDerivAt
    {f f' : ℝ → ℝ} {a b : ℝ}
    (hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt f (f' x) x)
    (hint : IntervalIntegrable f' MeasureTheory.volume a b) :
    (∫ x in a..b, f' x) = f b - f a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

theorem gap1 :
    (∫ x in (0 : ℝ)..Real.log 2, Real.sqrt (Real.exp x - 1)) =
      2 * ∫ t in (0 : ℝ)..1, t ^ 2 / (1 + t ^ 2) := by
  have hx_deriv : ∀ t : ℝ, HasDerivAt xOfT (jacobian t) t := by
    intro t
    have hinner :
        HasDerivAt (fun u : ℝ => 1 + u ^ 2) (2 * t) t := by
      convert (hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).pow 2) using 1 <;>
        norm_num <;> ring
    have hlog :=
      (Real.hasDerivAt_log (show 1 + t ^ 2 ≠ 0 by positivity)).comp t hinner
    simpa [xOfT, jacobian, Function.comp_def, div_eq_mul_inv, mul_comm] using hlog
  have hjac : Continuous jacobian := by
    have h : Continuous (fun t : ℝ => 2 * t / (1 + t ^ 2)) :=
      (continuous_const.mul continuous_id).div
        (continuous_const.add (continuous_id.pow 2))
        (fun t => by positivity)
    simpa [jacobian] using h
  have hint : Continuous (fun x : ℝ => Real.sqrt (Real.exp x - 1)) :=
    Real.continuous_sqrt.comp (Real.continuous_exp.sub continuous_const)
  have hxcont : Continuous xOfT :=
    continuous_iff_continuousAt.mpr (fun t => (hx_deriv t).continuousAt)
  have htrans :
      Continuous
        (fun t : ℝ =>
          jacobian t * Real.sqrt (Real.exp (xOfT t) - 1)) :=
    hjac.mul (hint.comp hxcont)
  have hanti :
      ∀ t : ℝ,
        HasDerivAt
          (fun u : ℝ =>
            ∫ x in (0 : ℝ)..xOfT u, Real.sqrt (Real.exp x - 1))
          (jacobian t * Real.sqrt (Real.exp (xOfT t) - 1)) t := by
    intro t
    have hmeas :
        StronglyMeasurableAtFilter
          (fun x : ℝ => Real.sqrt (Real.exp x - 1))
          (nhds (xOfT t)) MeasureTheory.volume :=
      hint.stronglyMeasurable.stronglyMeasurableAtFilter
    have hbase :
        HasDerivAt
          (fun u : ℝ =>
            ∫ x in (0 : ℝ)..u, Real.sqrt (Real.exp x - 1))
          (Real.sqrt (Real.exp (xOfT t) - 1)) (xOfT t) :=
      intervalIntegral.integral_hasDerivAt_right
        (hint.intervalIntegrable 0 (xOfT t)) hmeas hint.continuousAt
    simpa [Function.comp_def, mul_comm] using hbase.comp t (hx_deriv t)
  have hchange :
      (∫ t in (0 : ℝ)..1,
          jacobian t * Real.sqrt (Real.exp (xOfT t) - 1)) =
        (∫ x in (0 : ℝ)..xOfT 1, Real.sqrt (Real.exp x - 1)) -
          ∫ x in (0 : ℝ)..xOfT 0, Real.sqrt (Real.exp x - 1) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hanti t) (htrans.intervalIntegrable 0 1)
  have hx0 : xOfT 0 = 0 := by
    norm_num [xOfT]
  have hx1 : xOfT 1 = Real.log 2 := by
    norm_num [xOfT]
  have hchange' :
      (∫ t in (0 : ℝ)..1,
          jacobian t * Real.sqrt (Real.exp (xOfT t) - 1)) =
        ∫ x in (0 : ℝ)..Real.log 2, Real.sqrt (Real.exp x - 1) := by
    simpa [hx0, hx1] using hchange
  calc
    (∫ x in (0 : ℝ)..Real.log 2, Real.sqrt (Real.exp x - 1)) =
        ∫ t in (0 : ℝ)..1,
          jacobian t * Real.sqrt (Real.exp (xOfT t) - 1) := hchange'.symm
    _ = ∫ t in (0 : ℝ)..1, 2 * (t ^ 2 / (1 + t ^ 2)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht_bounds : (0 : ℝ) ≤ t ∧ t ≤ 1 := by
        simpa [Set.mem_uIcc] using ht
      change
        jacobian t * Real.sqrt (Real.exp (xOfT t) - 1) =
          2 * (t ^ 2 / (1 + t ^ 2))
      have hsqrt : Real.sqrt (Real.exp (xOfT t) - 1) = t := by
        change Real.sqrt (Real.exp (Real.log (1 + t ^ 2)) - 1) = t
        have hexp : Real.exp (Real.log (1 + t ^ 2)) = 1 + t ^ 2 :=
          Real.exp_log (show 0 < 1 + t ^ 2 by positivity)
        rw [hexp]
        rw [show 1 + t ^ 2 - 1 = t ^ 2 by ring]
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_bounds.1]
      rw [hsqrt]
      unfold jacobian
      ring
    _ = 2 * ∫ t in (0 : ℝ)..1, t ^ 2 / (1 + t ^ 2) := by
      rw [intervalIntegral.integral_const_mul]

theorem gap2 :
    2 * (∫ t in (0 : ℝ)..1, t ^ 2 / (1 + t ^ 2)) =
      primitive 1 - primitive 0 := by
  have hderiv :
      ∀ t : ℝ,
        HasDerivAt primitive (2 * (t ^ 2 / (1 + t ^ 2))) t := by
    intro t
    have hden : 1 + t ^ 2 ≠ 0 := by positivity
    have halg :
        2 * (1 - (1 + t ^ 2)⁻¹) = 2 * (t ^ 2 / (1 + t ^ 2)) := by
      field_simp [hden]
      <;> ring
    rw [← halg]
    simpa [primitive] using
      ((hasDerivAt_id t).sub (Real.hasDerivAt_arctan t)).const_mul 2
  have hcont : Continuous (fun t : ℝ => 2 * (t ^ 2 / (1 + t ^ 2))) := by
    have hquot : Continuous (fun t : ℝ => t ^ 2 / (1 + t ^ 2)) :=
      (continuous_id.pow 2).div
        (continuous_const.add (continuous_id.pow 2))
        (fun t => by positivity)
    exact continuous_const.mul hquot
  calc
    2 * (∫ t in (0 : ℝ)..1, t ^ 2 / (1 + t ^ 2)) =
        ∫ t in (0 : ℝ)..1, 2 * (t ^ 2 / (1 + t ^ 2)) := by
      rw [intervalIntegral.integral_const_mul]
    _ = primitive 1 - primitive 0 := by
      exact intervalIntegral.integral_deriv_eq_sub_of_hasDerivAt
        (fun t _ => hderiv t) (hcont.intervalIntegrable 0 1)

theorem gap3 :
    primitive 1 - primitive 0 = 2 - Real.pi / 2 := by
  simp only [primitive, Real.arctan_one, Real.arctan_zero]
  ring

theorem gap4 :
    (∫ x in (0 : ℝ)..Real.log 2, Real.sqrt (Real.exp x - 1)) =
      2 - Real.pi / 2 := by
  calc
    (∫ x in (0 : ℝ)..Real.log 2, Real.sqrt (Real.exp x - 1)) =
        2 * ∫ t in (0 : ℝ)..1, t ^ 2 / (1 + t ^ 2) := gap1
    _ = primitive 1 - primitive 0 := gap2
    _ = 2 - Real.pi / 2 := gap3

end

end ProofGap.Exercise2248
