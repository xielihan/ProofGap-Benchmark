import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4312

noncomputable section

open MeasureTheory
open scoped ENNReal Interval

def radius (a φ : ℝ) : ℝ :=
  a * Real.sqrt (Real.cos (2 * φ))

def quarterCurve (a φ : ℝ) : ℝ × ℝ :=
  (radius a φ * Real.cos φ, radius a φ * Real.sin φ)

def axisSegment (a t : ℝ) : ℝ × ℝ := (t, 0)

def quarterOrientedArea (a : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ∫ φ in (0 : ℝ)..Real.pi / 4,
      (quarterCurve a φ).1 *
          deriv (fun θ => (quarterCurve a θ).2) φ -
        (quarterCurve a φ).2 *
          deriv (fun θ => (quarterCurve a θ).1) φ

def lemniscateRegion (a : ℝ) : Set (ℝ × ℝ) :=
  {z | (z.1 ^ 2 + z.2 ^ 2) ^ 2 ≤ a ^ 2 * (z.1 ^ 2 - z.2 ^ 2)}

def lemniscateArea (a : ℝ) : ℝ :=
  ∫ _z in lemniscateRegion a, (1 : ℝ)

private def cosPos (θ : ℝ) : ℝ :=
  max (Real.cos (2 * θ)) 0

private def radialBound (a θ : ℝ) : ℝ :=
  a * Real.sqrt (cosPos θ)

private theorem cosPos_periodic :
    Function.Periodic cosPos Real.pi := by
  intro θ
  unfold cosPos
  rw [show 2 * (θ + Real.pi) = 2 * θ + 2 * Real.pi by ring,
    Real.cos_add_two_pi]

private theorem cosPos_pi_sub (θ : ℝ) :
    cosPos (Real.pi - θ) = cosPos θ := by
  unfold cosPos
  rw [show 2 * (Real.pi - θ) = 2 * Real.pi - 2 * θ by ring,
    Real.cos_two_pi_sub]

private theorem cosPos_integral_quarter :
    (∫ θ in (0 : ℝ)..Real.pi / 2, cosPos θ) = 1 / 2 := by
  have hcont : Continuous cosPos := by
    unfold cosPos
    exact (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).max continuous_const
  have hleft :
      (∫ θ in (0 : ℝ)..Real.pi / 4, cosPos θ) =
        ∫ θ in (0 : ℝ)..Real.pi / 4, Real.cos (2 * θ) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 4)] at hθ
    unfold cosPos
    rw [max_eq_left]
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [hθ.1, hθ.2, Real.pi_pos.le]
  have hright :
      (∫ θ in Real.pi / 4..Real.pi / 2, cosPos θ) = 0 := by
    rw [show (0 : ℝ) =
      ∫ _θ in Real.pi / 4..Real.pi / 2, (0 : ℝ) by simp]
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le
      (by nlinarith [Real.pi_pos] :
        Real.pi / 4 ≤ Real.pi / 2)] at hθ
    unfold cosPos
    rw [max_eq_right]
    have harg :
        2 * θ - Real.pi ∈
          Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> nlinarith [hθ.1, hθ.2]
    have hc := Real.cos_nonneg_of_mem_Icc harg
    rw [Real.cos_sub_pi] at hc
    linarith
  have hcos :
      (∫ θ in (0 : ℝ)..Real.pi / 4, Real.cos (2 * θ)) =
        1 / 2 := by
    let F : ℝ → ℝ := fun θ => Real.sin (2 * θ) / 2
    have hF (θ : ℝ) : HasDerivAt F (Real.cos (2 * θ)) θ := by
      have hlin : HasDerivAt (fun x : ℝ => 2 * x) 2 θ := by
        simpa using (hasDerivAt_id θ).const_mul 2
      have hs :
          HasDerivAt (fun x : ℝ => Real.sin (2 * x))
            (Real.cos (2 * θ) * 2) θ :=
        (Real.hasDerivAt_sin (2 * θ)).comp θ hlin
      convert hs.div_const 2 using 1 <;> ring
    have hint : IntervalIntegrable (fun θ : ℝ => Real.cos (2 * θ))
        volume 0 (Real.pi / 4) :=
      (Real.continuous_cos.comp
        (continuous_const.mul continuous_id)).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun θ _ => hF θ) hint]
    simp only [F]
    norm_num
    rw [show 2 * (Real.pi / 4) = Real.pi / 2 by ring,
      Real.sin_pi_div_two]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (b := Real.pi / 4)
    (hcont.intervalIntegrable _ _)
    (hcont.intervalIntegrable _ _)]
  rw [hleft, hright, hcos]
  ring

private theorem cosPos_integral_half :
    (∫ θ in (0 : ℝ)..Real.pi, cosPos θ) = 1 := by
  have hcont : Continuous cosPos := by
    unfold cosPos
    exact (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).max continuous_const
  have hsym :
      (∫ θ in Real.pi / 2..Real.pi, cosPos θ) =
        ∫ θ in (0 : ℝ)..Real.pi / 2, cosPos θ := by
    have hcomp := intervalIntegral.integral_comp_sub_left
      (f := cosPos) (a := 0) (b := Real.pi / 2) Real.pi
    rw [show Real.pi - Real.pi / 2 = Real.pi / 2 by ring,
      sub_zero] at hcomp
    calc
      (∫ θ in Real.pi / 2..Real.pi, cosPos θ) =
          ∫ θ in (0 : ℝ)..Real.pi / 2, cosPos (Real.pi - θ) :=
        hcomp.symm
      _ = ∫ θ in (0 : ℝ)..Real.pi / 2, cosPos θ := by
        apply intervalIntegral.integral_congr
        intro θ hθ
        exact cosPos_pi_sub θ
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (b := Real.pi / 2)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  rw [hsym, cosPos_integral_quarter]
  ring

private theorem cosPos_integral_full :
    (∫ θ in -Real.pi..Real.pi, cosPos θ) = 2 := by
  have hcont : Continuous cosPos := by
    unfold cosPos
    exact (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).max continuous_const
  have hp2 : Function.Periodic cosPos (2 * Real.pi) := by
    simpa [two_mul] using cosPos_periodic.nsmul 2
  have hshift := hp2.intervalIntegral_add_eq (-Real.pi) 0
  have htwice := cosPos_periodic.intervalIntegral_add_zsmul_eq
    (2 : ℤ) 0 (fun u v => hcont.intervalIntegrable u v)
  norm_num [zsmul_eq_mul] at htwice
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring,
    show (0 : ℝ) + 2 * Real.pi = 2 * Real.pi by ring] at hshift
  rw [hshift, htwice, cosPos_integral_half]
  ring

private theorem radial_iff (a r θ : ℝ) (ha : 0 < a) (hr : 0 < r) :
    r ^ 2 ≤ a ^ 2 * Real.cos (2 * θ) ↔
      r ∈ Set.Ioc 0 (radialBound a θ) := by
  by_cases hc : 0 ≤ Real.cos (2 * θ)
  · have hcp : cosPos θ = Real.cos (2 * θ) := max_eq_left hc
    have hsqrt : (Real.sqrt (cosPos θ)) ^ 2 =
        Real.cos (2 * θ) := by
      rw [hcp, Real.sq_sqrt hc]
    have hbound : 0 ≤ radialBound a θ :=
      mul_nonneg ha.le (Real.sqrt_nonneg _)
    constructor
    · intro h
      constructor
      · exact hr
      · apply (sq_le_sq₀ hr.le hbound).mp
        unfold radialBound
        rw [mul_pow, hsqrt]
        exact h
    · intro h
      have hsquares := (sq_le_sq₀ hr.le hbound).mpr h.2
      unfold radialBound at hsquares
      rwa [mul_pow, hsqrt] at hsquares
  · have hcneg : Real.cos (2 * θ) < 0 := lt_of_not_ge hc
    have hcp : cosPos θ = 0 := max_eq_right hcneg.le
    constructor
    · intro h
      nlinarith [sq_pos_of_pos hr, sq_pos_of_pos ha]
    · intro h
      simp [radialBound, hcp] at h

private theorem polar_mem_iff (a r θ : ℝ) (hr : 0 < r) :
    polarCoord.symm (r, θ) ∈ lemniscateRegion a ↔
      r ^ 2 ≤ a ^ 2 * Real.cos (2 * θ) := by
  have hsum :
      (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    calc
      (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 =
          r ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
      _ = r ^ 2 := by rw [Real.sin_sq_add_cos_sq]; ring
  have hdiff :
      (r * Real.cos θ) ^ 2 - (r * Real.sin θ) ^ 2 =
        r ^ 2 * Real.cos (2 * θ) := by
    calc
      (r * Real.cos θ) ^ 2 - (r * Real.sin θ) ^ 2 =
          r ^ 2 * (Real.cos θ ^ 2 - Real.sin θ ^ 2) := by ring
      _ = r ^ 2 * (2 * Real.cos θ ^ 2 - 1) := by
        have htrig : Real.cos θ ^ 2 - Real.sin θ ^ 2 =
            2 * Real.cos θ ^ 2 - 1 := by
          nlinarith [Real.sin_sq_add_cos_sq θ]
        rw [htrig]
      _ = r ^ 2 * Real.cos (2 * θ) := by rw [Real.cos_two_mul]
  change
    (((r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2) ^ 2 ≤
      a ^ 2 * ((r * Real.cos θ) ^ 2 - (r * Real.sin θ) ^ 2)) ↔ _
  rw [hsum, hdiff]
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  constructor <;> intro h
  · nlinarith [sq_nonneg (a ^ 2 * Real.cos (2 * θ) - r ^ 2)]
  · nlinarith [sq_nonneg (a ^ 2 * Real.cos (2 * θ) - r ^ 2)]

private theorem lintegral_Ioc_id (B : ℝ) (hB : 0 ≤ B) :
    (∫⁻ r in Set.Ioc 0 B, ENNReal.ofReal r) =
      ENNReal.ofReal (B ^ 2 / 2) := by
  have hint : Integrable (fun r : ℝ => r)
      (volume.restrict (Set.Ioc 0 B)) :=
    (continuous_id.intervalIntegrable 0 B).1
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 B)] (fun r : ℝ => r) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc]
      with r hr
    exact hr.1.le
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn]
  rw [← intervalIntegral.integral_of_le hB]
  let F : ℝ → ℝ := fun r => r ^ 2 / 2
  have hF (r : ℝ) : HasDerivAt F r r := by
    convert ((hasDerivAt_id r).pow 2).div_const 2 using 1 <;>
      simp [id_eq]
  have hInt : IntervalIntegrable (fun r : ℝ => r) volume 0 B :=
    continuous_id.intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => hF r) hInt]
  simp [F]

private theorem radial_lintegral (a θ : ℝ) (ha : 0 < a) :
    (∫⁻ r in Set.Ioi (0 : ℝ),
      ENNReal.ofReal r *
        (lemniscateRegion a).indicator (fun _ => (1 : ℝ≥0∞))
          (polarCoord.symm (r, θ))) =
      ENNReal.ofReal ((radialBound a θ) ^ 2 / 2) := by
  have hB : 0 ≤ radialBound a θ :=
    mul_nonneg ha.le (Real.sqrt_nonneg _)
  calc
    (∫⁻ r in Set.Ioi (0 : ℝ),
      ENNReal.ofReal r *
        (lemniscateRegion a).indicator (fun _ => (1 : ℝ≥0∞))
          (polarCoord.symm (r, θ))) =
        ∫⁻ r in Set.Ioc 0 (radialBound a θ), ENNReal.ofReal r := by
      rw [← MeasureTheory.lintegral_indicator measurableSet_Ioi,
        ← MeasureTheory.lintegral_indicator measurableSet_Ioc]
      apply lintegral_congr
      intro r
      by_cases hr : 0 < r
      · have hmem :
            polarCoord.symm (r, θ) ∈ lemniscateRegion a ↔
              r ∈ Set.Ioc 0 (radialBound a θ) :=
          (polar_mem_iff a r θ hr).trans (radial_iff a r θ ha hr)
        by_cases hm : polarCoord.symm (r, θ) ∈ lemniscateRegion a
        · have hI := hmem.mp hm
          have hrI : r ∈ Set.Ioi (0 : ℝ) := hr
          simp only [Set.indicator_apply]
          rw [if_pos hrI, Set.indicator_of_mem hm, if_pos hI]
          simp
        · have hI : r ∉ Set.Ioc 0 (radialBound a θ) :=
            fun h => hm (hmem.mpr h)
          have hrI : r ∈ Set.Ioi (0 : ℝ) := hr
          simp only [Set.indicator_apply]
          rw [if_pos hrI, Set.indicator_of_notMem hm, if_neg hI]
          simp
      · have hIoi : r ∉ Set.Ioi (0 : ℝ) := hr
        have hIoc : r ∉ Set.Ioc 0 (radialBound a θ) :=
          fun h => hr h.1
        simp only [Set.indicator_apply]
        rw [if_neg hIoi, if_neg hIoc]
    _ = ENNReal.ofReal ((radialBound a θ) ^ 2 / 2) :=
      lintegral_Ioc_id _ hB

private theorem radialBound_sq_div_two (a θ : ℝ) :
    (radialBound a θ) ^ 2 / 2 =
      (a ^ 2 / 2) * cosPos θ := by
  have hcp : 0 ≤ cosPos θ := le_max_right _ _
  unfold radialBound
  rw [mul_pow, Real.sq_sqrt hcp]
  ring

private theorem lemniscate_volume (a : ℝ) (ha : 0 < a) :
    volume (lemniscateRegion a) = ENNReal.ofReal (a ^ 2) := by
  have hregion : MeasurableSet (lemniscateRegion a) := by
    unfold lemniscateRegion
    exact measurableSet_le
      (((continuous_fst.pow 2).add (continuous_snd.pow 2)).pow 2).measurable
      ((continuous_const.mul
        ((continuous_fst.pow 2).sub (continuous_snd.pow 2)))).measurable
  let F : ℝ × ℝ → ℝ≥0∞ :=
    fun z => (lemniscateRegion a).indicator (fun _ => 1) z
  have hpolar :
      (∫⁻ p in polarCoord.target,
        ENNReal.ofReal p.1 * F (polarCoord.symm p)) =
        volume (lemniscateRegion a) := by
    have hp := lintegral_comp_polarCoord_symm F
    dsimp only [F] at hp
    have hrhs :
        (∫⁻ p : ℝ × ℝ,
          (lemniscateRegion a).indicator
            (fun _ => (1 : ℝ≥0∞)) p) =
          volume (lemniscateRegion a) := by
      simpa only [Pi.one_apply] using
        (MeasureTheory.lintegral_indicator_one hregion)
    rw [hrhs] at hp
    simpa [smul_eq_mul] using hp
  have hFmeas : Measurable F :=
    Measurable.indicator measurable_const hregion
  have hintegrand : Measurable
      (fun p : ℝ × ℝ =>
        ENNReal.ofReal p.1 * F (polarCoord.symm p)) :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul
      (hFmeas.comp continuous_polarCoord_symm.measurable)
  rw [polarCoord_target] at hpolar
  have htonelli :
      (∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal p.1 * F (polarCoord.symm p)) =
        ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
          ∫⁻ r in Set.Ioi (0 : ℝ),
            ENNReal.ofReal r * F (polarCoord.symm (r, θ)) :=
    MeasureTheory.setLIntegral_prod_symm _ hintegrand.aemeasurable
  rw [htonelli] at hpolar
  have hradial (θ : ℝ) :
      (∫⁻ r in Set.Ioi (0 : ℝ),
        ENNReal.ofReal r * F (polarCoord.symm (r, θ))) =
        ENNReal.ofReal ((a ^ 2 / 2) * cosPos θ) := by
    rw [show F = fun z =>
      (lemniscateRegion a).indicator (fun _ => (1 : ℝ≥0∞)) z by rfl,
      radial_lintegral a θ ha, radialBound_sq_div_two]
  simp_rw [hradial] at hpolar
  let g : ℝ → ℝ := fun θ => (a ^ 2 / 2) * cosPos θ
  have hgcont : Continuous g :=
    continuous_const.mul
      ((Real.continuous_cos.comp
        (continuous_const.mul continuous_id)).max continuous_const)
  have hle : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hgint : Integrable g
      (volume.restrict (Set.Ioo (-Real.pi) Real.pi)) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hle).mp
      (hgcont.intervalIntegrable _ _)
  have hgnn : 0 ≤ᵐ[
      volume.restrict (Set.Ioo (-Real.pi) Real.pi)] g :=
    Filter.Eventually.of_forall fun θ =>
      mul_nonneg (by positivity) (le_max_right _ _)
  have hang :
      (∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal ((a ^ 2 / 2) * cosPos θ)) =
        ENNReal.ofReal (a ^ 2) := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hgint hgnn]
    congr 1
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hle]
    change (∫ θ in -Real.pi..Real.pi,
      (a ^ 2 / 2) * cosPos θ) = a ^ 2
    rw [intervalIntegral.integral_const_mul, cosPos_integral_full]
    ring
  rw [hang] at hpolar
  exact hpolar.symm

private theorem lemniscateArea_eq (a : ℝ) (ha : 0 < a) :
    lemniscateArea a = a ^ 2 := by
  unfold lemniscateArea
  rw [MeasureTheory.setIntegral_one_eq_measureReal, Measure.real,
    lemniscate_volume a ha, ENNReal.toReal_ofReal (sq_nonneg a)]

private theorem radius_sq
    (a φ : ℝ) (ha : 0 < a)
    (hφ : φ ∈ Set.Icc (0 : ℝ) (Real.pi / 4)) :
    (radius a φ) ^ 2 = a ^ 2 * Real.cos (2 * φ) := by
  have hcos : 0 ≤ Real.cos (2 * φ) := by
    apply Real.cos_nonneg_of_mem_Icc
    rcases hφ with ⟨hlo, hhi⟩
    constructor <;> nlinarith [Real.pi_pos.le]
  unfold radius
  rw [mul_pow, Real.sq_sqrt hcos]

private theorem quarter_integrand_eq
    (a φ : ℝ) (ha : 0 < a)
    (hφ : φ ∈ Set.Icc (0 : ℝ) (Real.pi / 4)) :
    (quarterCurve a φ).1 *
          deriv (fun θ => (quarterCurve a θ).2) φ -
        (quarterCurve a φ).2 *
          deriv (fun θ => (quarterCurve a θ).1) φ =
      a ^ 2 * Real.cos (2 * φ) := by
  have hcos : 0 ≤ Real.cos (2 * φ) := by
    apply Real.cos_nonneg_of_mem_Icc
    rcases hφ with ⟨hlo, hhi⟩
    constructor <;> nlinarith [Real.pi_pos.le]
  by_cases hc : Real.cos (2 * φ) = 0
  · have hsqrt : Real.sqrt (Real.cos (2 * φ)) = 0 := by
      rw [hc]
      simp
    simp [quarterCurve, radius, hc]
  · have hlin : DifferentiableAt ℝ (fun θ : ℝ => 2 * θ) φ :=
      ((hasDerivAt_id φ).const_mul 2).differentiableAt
    have hcosDiff :
        DifferentiableAt ℝ (fun θ : ℝ => Real.cos (2 * θ)) φ :=
      Real.differentiableAt_cos.comp φ hlin
    have hr :
        DifferentiableAt ℝ (fun θ : ℝ => radius a θ) φ :=
      (hcosDiff.sqrt hc).const_mul a
    have hx :
        deriv (fun θ => (quarterCurve a θ).1) φ =
          deriv (fun θ => radius a θ) φ * Real.cos φ +
            radius a φ * (-Real.sin φ) := by
      simpa [quarterCurve] using
        (hr.hasDerivAt.mul (Real.hasDerivAt_cos φ)).deriv
    have hy :
        deriv (fun θ => (quarterCurve a θ).2) φ =
          deriv (fun θ => radius a θ) φ * Real.sin φ +
            radius a φ * Real.cos φ := by
      simpa [quarterCurve] using
        (hr.hasDerivAt.mul (Real.hasDerivAt_sin φ)).deriv
    rw [hx, hy]
    simp only [quarterCurve]
    calc
      radius a φ * Real.cos φ *
            (deriv (fun θ => radius a θ) φ * Real.sin φ +
              radius a φ * Real.cos φ) -
          radius a φ * Real.sin φ *
            (deriv (fun θ => radius a θ) φ * Real.cos φ +
              radius a φ * -Real.sin φ) =
          (radius a φ) ^ 2 *
            ((Real.sin φ) ^ 2 + (Real.cos φ) ^ 2) := by ring
      _ = (radius a φ) ^ 2 := by
        rw [Real.sin_sq_add_cos_sq]
        ring
      _ = a ^ 2 * Real.cos (2 * φ) := radius_sq a φ ha hφ

private theorem quarter_cos_integral (a : ℝ) :
    (∫ φ in (0 : ℝ)..Real.pi / 4,
      a ^ 2 * Real.cos (2 * φ)) = a ^ 2 / 2 := by
  let F : ℝ → ℝ := fun φ => (a ^ 2 / 2) * Real.sin (2 * φ)
  have hF (φ : ℝ) :
      HasDerivAt F (a ^ 2 * Real.cos (2 * φ)) φ := by
    have hlin : HasDerivAt (fun x : ℝ => 2 * x) 2 φ := by
      simpa using (hasDerivAt_id φ).const_mul 2
    have hsin :
        HasDerivAt (fun x : ℝ => Real.sin (2 * x))
          (Real.cos (2 * φ) * 2) φ :=
      (Real.hasDerivAt_sin (2 * φ)).comp φ hlin
    convert hsin.const_mul (a ^ 2 / 2) using 1 <;> ring
  have hint : IntervalIntegrable
      (fun φ : ℝ => a ^ 2 * Real.cos (2 * φ))
      volume 0 (Real.pi / 4) :=
    (continuous_const.mul
      (Real.continuous_cos.comp
        (continuous_const.mul continuous_id))).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun φ _ => hF φ) hint]
  simp only [F, mul_zero, Real.sin_zero, sub_zero]
  rw [show 2 * (Real.pi / 4) = Real.pi / 2 by ring,
    Real.sin_pi_div_two]
  ring

private theorem quarterOrientedArea_eq (a : ℝ) (ha : 0 < a) :
    quarterOrientedArea a = a ^ 2 / 4 := by
  unfold quarterOrientedArea
  have hpi4 : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have hcongr :
      (∫ φ in (0 : ℝ)..Real.pi / 4,
        (quarterCurve a φ).1 *
            deriv (fun θ => (quarterCurve a θ).2) φ -
          (quarterCurve a φ).2 *
            deriv (fun θ => (quarterCurve a θ).1) φ) =
        ∫ φ in (0 : ℝ)..Real.pi / 4,
          a ^ 2 * Real.cos (2 * φ) := by
    apply intervalIntegral.integral_congr
    intro φ hφ
    apply quarter_integrand_eq a φ ha
    simpa [Set.uIcc_of_le hpi4] using hφ
  rw [hcongr, quarter_cos_integral]
  ring

theorem gap1 (a φ : ℝ) :
    (quarterCurve a φ).1 = radius a φ * Real.cos φ := by
  rfl

theorem gap2 (a φ : ℝ) :
    (quarterCurve a φ).2 = radius a φ * Real.sin φ := by
  rfl

theorem gap3
    (a φ : ℝ) (ha : 0 < a)
    (hφ : φ ∈ Set.Icc (0 : ℝ) (Real.pi / 4)) :
    (radius a φ) ^ 2 = a ^ 2 * Real.cos (2 * φ) := by
  exact radius_sq a φ ha hφ

theorem gap4
    (a φ : ℝ) (ha : 0 < a)
    (hφ : φ ∈ Set.Icc (0 : ℝ) (Real.pi / 4)) :
    (quarterCurve a φ).1 *
          deriv (fun θ => (quarterCurve a θ).2) φ -
        (quarterCurve a φ).2 *
          deriv (fun θ => (quarterCurve a θ).1) φ =
      a ^ 2 * Real.cos (2 * φ) := by
  exact quarter_integrand_eq a φ ha hφ

theorem gap5 (a : ℝ) :
    ∫ t in (0 : ℝ)..a,
      (axisSegment a t).1 * deriv (fun s => (axisSegment a s).2) t -
        (axisSegment a t).2 * deriv (fun s => (axisSegment a s).1) t =
      0 := by
  simp [axisSegment]

theorem gap6 (a : ℝ) (ha : 0 < a) :
    lemniscateArea a = 4 * quarterOrientedArea a := by
  rw [lemniscateArea_eq a ha, quarterOrientedArea_eq a ha]
  ring

theorem gap7 (a : ℝ) (ha : 0 < a) :
    4 * quarterOrientedArea a =
      2 * ∫ φ in (0 : ℝ)..Real.pi / 4,
        a ^ 2 * Real.cos (2 * φ) := by
  rw [quarterOrientedArea_eq a ha, quarter_cos_integral]
  ring

theorem gap8 (a : ℝ) :
    2 * (∫ φ in (0 : ℝ)..Real.pi / 4,
        a ^ 2 * Real.cos (2 * φ)) =
      a ^ 2 := by
  rw [quarter_cos_integral]
  ring

theorem gap9 (a : ℝ) (ha : 0 < a) :
    lemniscateArea a = a ^ 2 := by
  exact lemniscateArea_eq a ha

end

end ProofGap.Exercise4312
