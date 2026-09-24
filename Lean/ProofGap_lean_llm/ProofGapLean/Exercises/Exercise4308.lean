import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4308

noncomputable section

open MeasureTheory
open scoped Interval

def ellipse (a b t : ℝ) : ℝ × ℝ :=
  (a * Real.cos t, b * Real.sin t)

def ellipseRegion (a b : ℝ) : Set (ℝ × ℝ) :=
  {z | (z.1 / a) ^ 2 + (z.2 / b) ^ 2 ≤ 1}

def ellipseArea (a b : ℝ) : ℝ :=
  ∫ _z in ellipseRegion a b, (1 : ℝ)

def orientedAreaIntegral (a b : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ∫ t in (0 : ℝ)..2 * Real.pi,
      (ellipse a b t).1 * deriv (fun s => (ellipse a b s).2) t -
        (ellipse a b t).2 * deriv (fun s => (ellipse a b s).1) t

private def unitDisk : Set (ℝ × ℝ) :=
  {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1}

private noncomputable def divideMap (a b : ℝ) :
    (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
    !![a⁻¹, 0; 0, b⁻¹]

private theorem unitDisk_volume :
    volume unitDisk = ENNReal.ofReal Real.pi := by
  let e : (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ) :=
    MeasurableEquiv.finTwoArrow
  let T : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2) :=
    WithLp.toLp 2
  have hpre :
      e ⁻¹' unitDisk = T ⁻¹' Metric.closedBall 0 1 := by
    ext x
    simp only [Set.mem_preimage, unitDisk, Set.mem_setOf_eq,
      Metric.mem_closedBall, dist_zero_right]
    change x 0 ^ 2 + x 1 ^ 2 ≤ 1 ↔ ‖WithLp.toLp 2 x‖ ≤ 1
    rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_two]
  have hball : MeasurableSet (Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin 2)) 1) := measurableSet_closedBall
  have hdisk : MeasurableSet unitDisk := by
    exact measurableSet_le
      ((continuous_fst.pow 2).add (continuous_snd.pow 2)).measurable
      measurable_const
  have he := MeasureTheory.volume_preserving_piFinTwo
    (fun _ : Fin 2 => ℝ)
  have hT := PiLp.volume_preserving_toLp (Fin 2)
  calc
    volume unitDisk = volume (e ⁻¹' unitDisk) := by
      symm
      exact he.measure_preimage hdisk.nullMeasurableSet
    _ = volume (T ⁻¹' Metric.closedBall 0 1) := by rw [hpre]
    _ = volume (Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
      exact hT.measure_preimage hball.nullMeasurableSet
    _ = ENNReal.ofReal Real.pi := by simp

private theorem ellipse_volume (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    volume (ellipseRegion a b) =
      ENNReal.ofReal (Real.pi * a * b) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  let f := divideMap a b
  have hf (z : ℝ × ℝ) : f z = (z.1 / a, z.2 / b) := by
    simp [f, divideMap, Matrix.toLin_finTwoProd_apply, div_eq_mul_inv,
      mul_comm]
  have hpre : f ⁻¹' unitDisk = ellipseRegion a b := by
    ext z
    simp [unitDisk, ellipseRegion, hf]
  have hdet : LinearMap.det f = a⁻¹ * b⁻¹ := by
    simp [f, divideMap, LinearMap.det_toLin, Matrix.det_fin_two]
  have hdet0 : LinearMap.det f ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero (inv_ne_zero ha0) (inv_ne_zero hb0)
  rw [← hpre,
    MeasureTheory.Measure.addHaar_preimage_linearMap volume hdet0,
    unitDisk_volume, hdet]
  have hab : 0 < a * b := mul_pos ha hb
  rw [← ENNReal.ofReal_mul (abs_nonneg ((a⁻¹ * b⁻¹)⁻¹))]
  congr 1
  have hinvpos : 0 < (a⁻¹ * b⁻¹)⁻¹ := by positivity
  rw [abs_of_pos hinvpos]
  field_simp [ha0, hb0]

private theorem ellipseArea_eq (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ellipseArea a b = Real.pi * a * b := by
  unfold ellipseArea
  rw [MeasureTheory.setIntegral_one_eq_measureReal]
  have hnonneg : 0 ≤ Real.pi * a * b := by positivity
  rw [Measure.real, ellipse_volume a b ha hb,
    ENNReal.toReal_ofReal hnonneg]

private theorem oriented_integrand_eq (a b t : ℝ) :
    (ellipse a b t).1 * deriv (fun s => (ellipse a b s).2) t -
        (ellipse a b t).2 * deriv (fun s => (ellipse a b s).1) t =
      a * b * ((Real.cos t) ^ 2 + (Real.sin t) ^ 2) := by
  have hsin :
      deriv (fun s => (ellipse a b s).2) t = b * Real.cos t := by
    simpa [ellipse] using ((Real.hasDerivAt_sin t).const_mul b).deriv
  have hcos :
      deriv (fun s => (ellipse a b s).1) t =
        a * (-Real.sin t) := by
    simpa [ellipse] using ((Real.hasDerivAt_cos t).const_mul a).deriv
  rw [hsin, hcos]
  simp only [ellipse]
  ring

private theorem trig_area_integral (a b : ℝ) :
    (1 / 2 : ℝ) *
        (∫ t in (0 : ℝ)..2 * Real.pi,
          a * b * ((Real.cos t) ^ 2 + (Real.sin t) ^ 2)) =
      Real.pi * a * b := by
  have hfun :
      (fun t : ℝ =>
        a * b * ((Real.cos t) ^ 2 + (Real.sin t) ^ 2)) =
      fun _ : ℝ => a * b := by
    funext t
    rw [add_comm, Real.sin_sq_add_cos_sq]
    ring
  rw [hfun]
  simp
  ring

private theorem orientedAreaIntegral_eq (a b : ℝ) :
    orientedAreaIntegral a b = Real.pi * a * b := by
  unfold orientedAreaIntegral
  rw [intervalIntegral.integral_congr
    (fun t _ => oriented_integrand_eq a b t)]
  exact trig_area_integral a b

theorem gap1 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ellipseArea a b = orientedAreaIntegral a b := by
  rw [ellipseArea_eq a b ha hb, orientedAreaIntegral_eq]

theorem gap2 (a b : ℝ) :
    orientedAreaIntegral a b =
      (1 / 2 : ℝ) *
        ∫ t in (0 : ℝ)..2 * Real.pi,
          a * b * ((Real.cos t) ^ 2 + (Real.sin t) ^ 2) := by
  unfold orientedAreaIntegral
  rw [intervalIntegral.integral_congr
    (fun t _ => oriented_integrand_eq a b t)]

theorem gap3 (a b : ℝ) :
    (1 / 2 : ℝ) *
        (∫ t in (0 : ℝ)..2 * Real.pi,
          a * b * ((Real.cos t) ^ 2 + (Real.sin t) ^ 2)) =
      Real.pi * a * b := by
  exact trig_area_integral a b

theorem gap4 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ellipseArea a b = Real.pi * a * b := by
  exact ellipseArea_eq a b ha hb

end

end ProofGap.Exercise4308
