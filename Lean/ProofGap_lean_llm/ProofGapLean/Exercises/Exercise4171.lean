import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod

namespace ProofGap.Exercise4171

noncomputable section

open Filter MeasureTheory
open scoped ENNReal

abbrev Point := ℝ × ℝ

def disk : Set Point :=
  {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1}

def diskIntegral : ℝ≥0∞ :=
  ∫⁻ z in disk,
    ENNReal.ofReal (1 / Real.sqrt (1 - z.1 ^ 2 - z.2 ^ 2))

def polarIntegral : ℝ≥0∞ :=
  ∫⁻ _θ in Set.Icc (0 : ℝ) (2 * Real.pi),
    ∫⁻ r in Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal (r / Real.sqrt (1 - r ^ 2))

private def radialReal (r : ℝ) : ℝ :=
  r / Real.sqrt (1 - r ^ 2)

private def radial (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (radialReal r)

private def radialLIntegral : ℝ≥0∞ :=
  ∫⁻ r in Set.Icc (0 : ℝ) 1, radial r

private theorem disk_measurable : MeasurableSet disk := by
  unfold disk
  measurability

private theorem radial_measurable : Measurable radial := by
  unfold radial radialReal
  fun_prop

private theorem polarIntegral_factor :
    polarIntegral =
      ENNReal.ofReal (2 * Real.pi) * radialLIntegral := by
  unfold polarIntegral radialLIntegral radial radialReal
  rw [setLIntegral_const, Real.volume_Icc]
  simp only [sub_zero]
  rw [mul_comm]

private theorem diskIntegral_factor :
    diskIntegral =
      ENNReal.ofReal (2 * Real.pi) * radialLIntegral := by
  let f : ℝ × ℝ → ℝ≥0∞ := fun z =>
    disk.indicator
      (fun w =>
        ENNReal.ofReal
          (1 / Real.sqrt (1 - w.1 ^ 2 - w.2 ^ 2))) z
  have hf : diskIntegral = ∫⁻ z : ℝ × ℝ, f z := by
    unfold diskIntegral
    rw [← lintegral_indicator disk_measurable]
  rw [hf, ← lintegral_comp_polarCoord_symm]
  let rect : Set (ℝ × ℝ) :=
    Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi
  have htarget : MeasurableSet polarCoord.target :=
    polarCoord.open_target.measurableSet
  have hrect : MeasurableSet rect :=
    measurableSet_Ioc.prod measurableSet_Ioo
  have hrestrict :
      (∫⁻ u in polarCoord.target,
          ENNReal.ofReal u.1 • f (polarCoord.symm u)) =
        ∫⁻ u in rect, radial u.1 := by
    rw [← lintegral_indicator htarget, ← lintegral_indicator hrect]
    apply lintegral_congr
    intro u
    by_cases hu : u ∈ polarCoord.target
    · rw [Set.indicator_of_mem hu]
      have hrpos : 0 < u.1 := hu.1
      have hsq :
          (polarCoord.symm u).1 ^ 2 +
              (polarCoord.symm u).2 ^ 2 = u.1 ^ 2 := by
        simp only [polarCoord_symm_apply]
        nlinarith [Real.sin_sq_add_cos_sq u.2]
      by_cases hr : u.1 ≤ 1
      · have hur : u ∈ rect := ⟨⟨hrpos, hr⟩, hu.2⟩
        have hdisk : polarCoord.symm u ∈ disk := by
          change
            (polarCoord.symm u).1 ^ 2 +
              (polarCoord.symm u).2 ^ 2 ≤ 1
          rw [hsq]
          nlinarith [sq_nonneg (u.1 - 1)]
        rw [Set.indicator_of_mem hur]
        unfold f
        rw [Set.indicator_of_mem hdisk]
        unfold radial radialReal
        rw [show
            1 - (polarCoord.symm u).1 ^ 2 -
                (polarCoord.symm u).2 ^ 2 =
              1 - u.1 ^ 2 by linarith [hsq]]
        simp only [smul_eq_mul]
        rw [← ENNReal.ofReal_mul hrpos.le]
        congr 1
        ring
      · have hur : u ∉ rect := by
          intro h
          exact hr h.1.2
        have hdisk : polarCoord.symm u ∉ disk := by
          intro h
          apply hr
          change
            (polarCoord.symm u).1 ^ 2 +
              (polarCoord.symm u).2 ^ 2 ≤ 1 at h
          rw [hsq] at h
          nlinarith [sq_nonneg (u.1 - 1)]
        rw [Set.indicator_of_notMem hur]
        unfold f
        rw [Set.indicator_of_notMem hdisk]
        simp
    · rw [Set.indicator_of_notMem hu]
      have hur : u ∉ rect := by
        intro h
        apply hu
        exact ⟨h.1.1, h.2⟩
      rw [Set.indicator_of_notMem hur]
  rw [hrestrict]
  have hi :
      AEMeasurable (fun u : ℝ × ℝ => radial u.1)
        ((volume.prod volume).restrict rect) :=
    (radial_measurable.comp measurable_fst).aemeasurable
  change
    (∫⁻ u in rect, radial u.1 ∂volume.prod volume) =
      ENNReal.ofReal (2 * Real.pi) * radialLIntegral
  rw [setLIntegral_prod _ hi]
  have htheta : ∀ r : ℝ,
      (∫⁻ _θ in Set.Ioo (-Real.pi) Real.pi, radial r) =
        ENNReal.ofReal (2 * Real.pi) * radial r := by
    intro r
    rw [setLIntegral_const, Real.volume_Ioo]
    have hangle :
        ENNReal.ofReal (Real.pi - -Real.pi) =
          ENNReal.ofReal (2 * Real.pi) := by
      congr 1
      ring
    rw [hangle, mul_comm]
  simp_rw [htheta]
  rw [lintegral_const_mul
    (ENNReal.ofReal (2 * Real.pi)) radial_measurable]
  unfold radialLIntegral
  rw [setLIntegral_congr
    (Ioc_ae_eq_Icc : Set.Ioc (0 : ℝ) 1 =ᵐ[volume] Set.Icc 0 1)]

private theorem radial_derivative
    (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun x : ℝ => -Real.sqrt (1 - x ^ 2))
      (radialReal r) r := by
  have hpos : 0 < 1 - r ^ 2 := by
    have hrsq : r ^ 2 < (1 : ℝ) ^ 2 :=
      (sq_lt_sq₀ hr.1.le zero_le_one).2 hr.2
    nlinarith
  have hinner :
      HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * r) r := by
    convert (hasDerivAt_const r 1).sub ((hasDerivAt_id r).pow 2)
      using 1 <;> simp only [id_eq] <;> ring
  have hsqrt :
      HasDerivAt (fun x : ℝ => Real.sqrt (1 - x ^ 2))
        (1 / (2 * Real.sqrt (1 - r ^ 2)) * (-2 * r)) r := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_sqrt hpos.ne').comp r hinner
  unfold radialReal
  convert hsqrt.neg using 1
  field_simp [Real.sqrt_ne_zero'.mpr hpos]

private theorem radial_intervalIntegrable :
    IntervalIntegrable radialReal volume (0 : ℝ) 1 := by
  let F : ℝ → ℝ := fun x => -Real.sqrt (1 - x ^ 2)
  have hcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
    unfold F
    fun_prop
  have hder : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt F (radialReal r) r := by
    intro r hr
    exact radial_derivative r hr
  have hpos : ∀ r ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ radialReal r := by
    intro r hr
    unfold radialReal
    exact div_nonneg hr.1.le (Real.sqrt_nonneg _)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact intervalIntegral.integrableOn_deriv_of_nonneg hcont hder hpos

private theorem radial_real_integral :
    (∫ r in Set.Icc (0 : ℝ) 1, radialReal r) = 1 := by
  let F : ℝ → ℝ := fun x => -Real.sqrt (1 - x ^ 2)
  have hcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
    unfold F
    fun_prop
  have hder : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt F (radialReal r) r := by
    intro r hr
    exact radial_derivative r hr
  have hFTC :
      (∫ r in (0 : ℝ)..1, radialReal r) = F 1 - F 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      zero_le_one hcont hder radial_intervalIntegrable
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one]
  rw [hFTC]
  norm_num [F]

private theorem radialLIntegral_value :
    radialLIntegral = 1 := by
  have hi : IntegrableOn radialReal (Set.Icc (0 : ℝ) 1) := by
    exact
      (intervalIntegrable_iff_integrableOn_Icc_of_le
        (f := radialReal) zero_le_one).mp radial_intervalIntegrable
  have hn : 0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] radialReal := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    unfold radialReal
    exact div_nonneg hr.1 (Real.sqrt_nonneg _)
  unfold radialLIntegral radial
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn]
  rw [radial_real_integral]
  norm_num

theorem gap1 :
    diskIntegral = polarIntegral := by
  rw [diskIntegral_factor, polarIntegral_factor]

theorem gap2 :
    polarIntegral = ENNReal.ofReal (2 * Real.pi) := by
  rw [polarIntegral_factor, radialLIntegral_value, mul_one]

theorem gap3 :
    diskIntegral = ENNReal.ofReal (2 * Real.pi) := by
  rw [diskIntegral_factor, radialLIntegral_value, mul_one]

end

end ProofGap.Exercise4171
