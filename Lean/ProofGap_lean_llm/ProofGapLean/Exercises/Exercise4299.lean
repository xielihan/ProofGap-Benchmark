import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4299

noncomputable section

open MeasureTheory
open scoped Interval

abbrev Point := ℝ × ℝ

def P (p : Point) : ℝ :=
  p.1 + p.2

def Q (p : Point) : ℝ :=
  -(p.1 - p.2)

def ellipse (a b t : ℝ) : Point :=
  (a * Real.cos t, b * Real.sin t)

def lineIntegral (a b : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..2 * Real.pi,
    P (ellipse a b t) * deriv (fun s => (ellipse a b s).1) t +
      Q (ellipse a b t) * deriv (fun s => (ellipse a b s).2) t

def ellipseRegion (a b : ℝ) : Set Point :=
  {p | p.1 ^ 2 / a ^ 2 + p.2 ^ 2 / b ^ 2 ≤ 1}

def areaIntegral (a b : ℝ) : ℝ :=
  ∫ _p in ellipseRegion a b, (-2 : ℝ)

def rawIntegrand (a b t : ℝ) : ℝ :=
  (a * Real.cos t + b * Real.sin t) * (-a * Real.sin t) -
    (a * Real.cos t - b * Real.sin t) * (b * Real.cos t)

def simplifiedIntegrand (a b t : ℝ) : ℝ :=
  (b ^ 2 - a ^ 2) * Real.cos t * Real.sin t - a * b

private def scaleCLM (a b : ℝ) : Point →L[ℝ] Point :=
  (ContinuousLinearMap.lsmul ℝ ℝ a).prodMap
    (ContinuousLinearMap.lsmul ℝ ℝ b)

private def unitDisk : Set Point :=
  {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1}

private theorem ellipse_image (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    scaleCLM a b '' unitDisk = ellipseRegion a b := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    change
      (a * q.1) ^ 2 / a ^ 2 +
          (b * q.2) ^ 2 / b ^ 2 ≤ 1
    change q.1 ^ 2 + q.2 ^ 2 ≤ 1 at hq
    field_simp [ne_of_gt ha, ne_of_gt hb] at *
    nlinarith
  · intro hp
    refine ⟨(p.1 / a, p.2 / b), ?_, ?_⟩
    · change (p.1 / a) ^ 2 + (p.2 / b) ^ 2 ≤ 1
      change
        p.1 ^ 2 / a ^ 2 + p.2 ^ 2 / b ^ 2 ≤ 1 at hp
      simpa [div_pow] using hp
    · apply Prod.ext
      · change a * (p.1 / a) = p.1
        field_simp [ne_of_gt ha]
      · change b * (p.2 / b) = p.2
        field_simp [ne_of_gt hb]

private theorem scale_inj (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    Function.Injective (scaleCLM a b) := by
  intro p q h
  apply Prod.ext
  · have h1 := congrArg Prod.fst h
    change a * p.1 = a * q.1 at h1
    exact mul_left_cancel₀ (ne_of_gt ha) h1
  · have h2 := congrArg Prod.snd h
    change b * p.2 = b * q.2 at h2
    exact mul_left_cancel₀ (ne_of_gt hb) h2

private theorem ellipse_change (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    (∫ p in ellipseRegion a b, c) =
      ∫ p in unitDisk, (a * b) * c := by
  have hdisk : MeasurableSet unitDisk := by
    unfold unitDisk
    exact
      (isClosed_le
        ((continuous_fst.pow 2).add (continuous_snd.pow 2))
        continuous_const).measurableSet
  have hdet : (scaleCLM a b).det = a * b := by
    unfold scaleCLM ContinuousLinearMap.det
    change
      (LinearMap.prodMap (LinearMap.mulLeft ℝ a)
        (LinearMap.mulLeft ℝ b)).det = a * b
    rw [LinearMap.det_prodMap, LinearMap.det_mulLeft,
      LinearMap.det_mulLeft]
  have hcv :=
    integral_image_eq_integral_abs_det_fderiv_smul
      (volume : Measure Point) hdisk
      (fun p hp =>
        (scaleCLM a b).hasFDerivAt.hasFDerivWithinAt)
      (fun x hx y hy h => scale_inj a b ha hb h)
      (fun _p : Point => c)
  rw [ellipse_image a b ha hb] at hcv
  simpa [hdet, abs_of_pos (mul_pos ha hb), smul_eq_mul]
    using hcv

private theorem angular_full :
    (∫ θ in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ)) =
      2 * Real.pi := by
  calc
    _ = ∫ θ in Set.Ioc (-Real.pi) Real.pi, (1 : ℝ) :=
      (integral_Ioc_eq_integral_Ioo
        (f := fun _ : ℝ => (1 : ℝ))).symm
    _ = ∫ θ in -Real.pi..Real.pi, (1 : ℝ) := by
      rw [intervalIntegral.integral_of_le]
      exact neg_le_self Real.pi_nonneg
    _ = 2 * Real.pi := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      ring

private theorem radial_linear (c : ℝ) :
    (∫ r in (0 : ℝ)..1, r * c) = c / 2 := by
  have hd (r : ℝ) :
      HasDerivAt (fun x : ℝ => x ^ 2 / 2) r r := by
    convert ((hasDerivAt_id r).pow 2).div_const 2 using 1 <;>
      simp
  have hi :
      (∫ r in (0 : ℝ)..1, r) = (1 : ℝ) / 2 := by
    simpa using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := (0 : ℝ)) (b := (1 : ℝ))
        (fun r hr => hd r)
        (continuous_id.intervalIntegrable (0 : ℝ) 1))
  rw [intervalIntegral.integral_mul_const, hi]
  ring

private theorem unitDisk_const (c : ℝ) :
    (∫ p in unitDisk, c) = c * Real.pi := by
  have hdisk : MeasurableSet unitDisk := by
    unfold unitDisk
    exact
      (isClosed_le
        ((continuous_fst.pow 2).add (continuous_snd.pow 2))
        continuous_const).measurableSet
  have hp := integral_comp_polarCoord_symm
    (unitDisk.indicator (fun _p : Point => c))
  rw [integral_indicator hdisk] at hp
  have hpoint (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
      p.1 • unitDisk.indicator (fun _q : Point => c)
          (polarCoord.symm p) =
        (Set.Iic (1 : ℝ)).indicator
            (fun r : ℝ => r * c) p.1 * (1 : ℝ) := by
    rcases p with ⟨r, θ⟩
    have hr : 0 < r := hp.1
    have htrig :
        (r * Real.cos θ) ^ 2 +
            (r * Real.sin θ) ^ 2 = r ^ 2 := by
      calc
        _ = r ^ 2 *
            (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by
          ring
        _ = r ^ 2 := by
          rw [Real.cos_sq_add_sin_sq]
          ring
    have hmem :
        polarCoord.symm (r, θ) ∈ unitDisk ↔ r ≤ 1 := by
      rw [polarCoord_symm_apply]
      simp only [unitDisk, Set.mem_setOf_eq]
      rw [htrig]
      simpa using sq_le_sq₀ hr.le zero_le_one
    simp only [Set.indicator, hmem, Set.mem_Iic,
      smul_eq_mul]
    by_cases hr1 : r ≤ 1 <;> simp [hr1]
  have hprod :
      (∫ p in polarCoord.target,
        p.1 • unitDisk.indicator (fun _q : Point => c)
          (polarCoord.symm p)) =
        (∫ r in Set.Ioi (0 : ℝ),
          (Set.Iic (1 : ℝ)).indicator
            (fun r : ℝ => r * c) r) *
        ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          (1 : ℝ) := by
    rw [polarCoord_target]
    calc
      _ = ∫ p in
          Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          (Set.Iic (1 : ℝ)).indicator
              (fun r : ℝ => r * c) p.1 * (1 : ℝ) := by
        apply setIntegral_congr_fun
          (measurableSet_Ioi.prod measurableSet_Ioo)
        intro p hp'
        exact hpoint p hp'
      _ = _ := by
        exact setIntegral_prod_mul
          ((Set.Iic (1 : ℝ)).indicator
            (fun r : ℝ => r * c))
          (fun _θ : ℝ => (1 : ℝ))
          (Set.Ioi (0 : ℝ))
          (Set.Ioo (-Real.pi) Real.pi)
  have hrad :
      (∫ r in Set.Ioi (0 : ℝ),
        (Set.Iic (1 : ℝ)).indicator
          (fun r : ℝ => r * c) r) =
        ∫ r in (0 : ℝ)..1, r * c := by
    rw [setIntegral_indicator measurableSet_Iic]
    have hinter :
        Set.Ioi (0 : ℝ) ∩ Set.Iic 1 =
          Set.Ioc (0 : ℝ) 1 := by
      ext r
      simp
    rw [hinter,
      intervalIntegral.integral_of_le zero_le_one]
  rw [hprod, hrad, angular_full, radial_linear] at hp
  rw [← hp]
  ring

private theorem area_value (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    areaIntegral a b = -2 * Real.pi * a * b := by
  unfold areaIntegral
  rw [ellipse_change a b (-2) ha hb, unitDisk_const]
  ring

private theorem line_raw (a b : ℝ) :
    lineIntegral a b =
      ∫ t in (0 : ℝ)..2 * Real.pi,
        rawIntegrand a b t := by
  have hx (t : ℝ) :
      deriv (fun s => (ellipse a b s).1) t =
        -a * Real.sin t := by
    simpa [ellipse] using
      ((Real.hasDerivAt_cos t).const_mul a).deriv
  have hy (t : ℝ) :
      deriv (fun s => (ellipse a b s).2) t =
        b * Real.cos t := by
    simpa [ellipse] using
      ((Real.hasDerivAt_sin t).const_mul b).deriv
  unfold lineIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  change
    P (ellipse a b t) *
          deriv (fun s => (ellipse a b s).1) t +
        Q (ellipse a b t) *
          deriv (fun s => (ellipse a b s).2) t =
      rawIntegrand a b t
  rw [hx, hy]
  simp only [P, Q, ellipse, rawIntegrand]
  ring

private theorem raw_simplified (a b : ℝ) :
    (∫ t in (0 : ℝ)..2 * Real.pi,
      rawIntegrand a b t) =
      ∫ t in (0 : ℝ)..2 * Real.pi,
        simplifiedIntegrand a b t := by
  apply intervalIntegral.integral_congr
  intro t ht
  unfold rawIntegrand simplifiedIntegrand
  calc
    _ = (b ^ 2 - a ^ 2) *
          Real.cos t * Real.sin t - a * b +
        a * b *
          (1 - (Real.sin t ^ 2 + Real.cos t ^ 2)) := by
      ring
    _ = _ := by
      rw [Real.sin_sq_add_cos_sq]
      ring

private theorem simplified_value (a b : ℝ) :
    (∫ t in (0 : ℝ)..2 * Real.pi,
      simplifiedIntegrand a b t) =
      -2 * Real.pi * a * b := by
  let F : ℝ → ℝ := fun t =>
    (b ^ 2 - a ^ 2) / 2 * Real.sin t ^ 2 -
      a * b * t
  have hF (t : ℝ) :
      HasDerivAt F (simplifiedIntegrand a b t) t := by
    have hsin := Real.hasDerivAt_sin t
    have hraw :=
      ((hsin.pow 2).const_mul
        ((b ^ 2 - a ^ 2) / 2)).sub
          ((hasDerivAt_id t).const_mul (a * b))
    convert hraw using 1 <;>
      simp [simplifiedIntegrand] <;> ring
  have hcont :
      Continuous (simplifiedIntegrand a b) := by
    unfold simplifiedIntegrand
    fun_prop
  calc
    (∫ t in (0 : ℝ)..2 * Real.pi,
      simplifiedIntegrand a b t) =
        F (2 * Real.pi) - F 0 := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => hF t)
        (hcont.intervalIntegrable _ _)
    _ = -2 * Real.pi * a * b := by
      dsimp [F]
      rw [Real.sin_two_pi, Real.sin_zero]
      ring

private theorem line_value (a b : ℝ) :
    lineIntegral a b = -2 * Real.pi * a * b := by
  rw [line_raw, raw_simplified, simplified_value]

theorem gap1 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    lineIntegral a b = areaIntegral a b := by
  calc
    lineIntegral a b = -2 * Real.pi * a * b :=
      line_value a b
    _ = areaIntegral a b := (area_value a b ha hb).symm

theorem gap2 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    areaIntegral a b = -2 * Real.pi * a * b := by
  exact area_value a b ha hb

theorem gap3 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    lineIntegral a b = -2 * Real.pi * a * b := by
  exact line_value a b

theorem gap4 (a b : ℝ) :
    lineIntegral a b =
      ∫ t in (0 : ℝ)..2 * Real.pi,
        rawIntegrand a b t := by
  exact line_raw a b

theorem gap5 (a b : ℝ) :
    (∫ t in (0 : ℝ)..2 * Real.pi, rawIntegrand a b t) =
      ∫ t in (0 : ℝ)..2 * Real.pi,
        simplifiedIntegrand a b t := by
  exact raw_simplified a b

theorem gap6 (a b : ℝ) :
    (∫ t in (0 : ℝ)..2 * Real.pi,
      simplifiedIntegrand a b t) =
      -2 * Real.pi * a * b := by
  exact simplified_value a b

theorem gap7 (a b : ℝ) :
    lineIntegral a b = -2 * Real.pi * a * b := by
  exact line_value a b

end

end ProofGap.Exercise4299
