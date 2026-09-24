import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3951

noncomputable section

open MeasureTheory
open scoped Interval

def unitDisk : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1}

def radialDiskIntegral (f : ℝ → ℝ) : ℝ :=
  ∫ p in unitDisk, f (Real.sqrt (p.1 ^ 2 + p.2 ^ 2))

private theorem unitDisk_closed : IsClosed unitDisk := by
  exact isClosed_le ((continuous_fst.pow 2).add (continuous_snd.pow 2))
    continuous_const

private theorem radialDiskIntegral_eq (f : ℝ → ℝ)
    (hf : IntegrableOn
      (fun p : ℝ × ℝ => f (Real.sqrt (p.1 ^ 2 + p.2 ^ 2)))
      unitDisk) :
    radialDiskIntegral f =
      2 * Real.pi * ∫ r in (0 : ℝ)..1, r * f r := by
  let g : ℝ × ℝ → ℝ := fun p =>
    f (Real.sqrt (p.1 ^ 2 + p.2 ^ 2))
  let rect : Set (ℝ × ℝ) :=
    Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi
  let radial : ℝ × ℝ → ℝ := fun p => p.1 * f p.1
  have hg_disk : IntegrableOn g unitDisk := by
    simpa only [g] using hf
  have hg_ind : Integrable (unitDisk.indicator g) :=
    (integrable_indicator_iff unitDisk_closed.measurableSet).2 hg_disk
  have hrect_meas : MeasurableSet rect :=
    measurableSet_Ioc.prod measurableSet_Ioo
  have hpolar_point (p : ℝ × ℝ) :
      polarCoord.target.indicator
          (fun q => q.1 * unitDisk.indicator g (polarCoord.symm q)) p =
        rect.indicator radial p := by
    by_cases ht : p ∈ polarCoord.target
    · have hrpos : 0 < p.1 := ht.1
      have hang : p.2 ∈ Set.Ioo (-Real.pi) Real.pi := ht.2
      have hnorm :
          (polarCoord.symm p).1 ^ 2 +
              (polarCoord.symm p).2 ^ 2 =
            p.1 ^ 2 := by
        simp only [polarCoord_symm_apply]
        rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]
      have hgpolar : g (polarCoord.symm p) = f p.1 := by
        dsimp only [g]
        rw [hnorm, Real.sqrt_sq_eq_abs, abs_of_pos hrpos]
      by_cases hr1 : p.1 ≤ 1
      · have hd : polarCoord.symm p ∈ unitDisk := by
          change
            (polarCoord.symm p).1 ^ 2 +
                (polarCoord.symm p).2 ^ 2 ≤ 1
          rw [hnorm]
          nlinarith
        have hp_rect : p ∈ rect := ⟨⟨hrpos, hr1⟩, hang⟩
        rw [Set.indicator_of_mem ht, Set.indicator_of_mem hp_rect,
          Set.indicator_of_mem hd, hgpolar]
      · have hd : polarCoord.symm p ∉ unitDisk := by
          intro hd
          apply hr1
          change
            (polarCoord.symm p).1 ^ 2 +
                (polarCoord.symm p).2 ^ 2 ≤ 1 at hd
          rw [hnorm] at hd
          nlinarith
        have hp_rect : p ∉ rect := fun hp => hr1 hp.1.2
        rw [Set.indicator_of_mem ht, Set.indicator_of_notMem hd,
          Set.indicator_of_notMem hp_rect]
        simp
    · have hp_rect : p ∉ rect := by
        intro hp
        apply ht
        exact ⟨hp.1.1, hp.2⟩
      rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem hp_rect]
  have hweighted_on :
      IntegrableOn
        (fun p : ℝ × ℝ =>
          |(fderivPolarCoordSymm p).det| •
            unitDisk.indicator g (polarCoord.symm p))
        polarCoord.target := by
    have hsource :
        IntegrableOn (unitDisk.indicator g) polarCoord.source :=
      hg_ind.integrableOn
    have hchange :=
      (MeasureTheory.integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
        (μ := volume) polarCoord.open_target.measurableSet
        (fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)
        polarCoord.symm.injOn (unitDisk.indicator g))
    rw [polarCoord.symm_image_target_eq_source] at hchange
    exact hchange.mp hsource
  have hweighted_on' :
      IntegrableOn
        (fun p : ℝ × ℝ =>
          p.1 * unitDisk.indicator g (polarCoord.symm p))
        polarCoord.target := by
    refine hweighted_on.congr_fun (fun p hp => ?_)
      polarCoord.open_target.measurableSet
    rw [det_fderivPolarCoordSymm, abs_of_pos hp.1]
    rfl
  have htarget_ind :
      Integrable
        (polarCoord.target.indicator
          (fun p : ℝ × ℝ =>
            p.1 * unitDisk.indicator g (polarCoord.symm p))) :=
    (integrable_indicator_iff polarCoord.open_target.measurableSet).2
      hweighted_on'
  have hrect_integrable : Integrable (rect.indicator radial) := by
    refine htarget_ind.congr (Filter.Eventually.of_forall fun p => ?_)
    exact hpolar_point p
  have hpolar :
      radialDiskIntegral f =
        ∫ p : ℝ × ℝ, rect.indicator radial p := by
    have hp := integral_comp_polarCoord_symm (unitDisk.indicator g)
    calc
      radialDiskIntegral f =
          ∫ p : ℝ × ℝ, unitDisk.indicator g p := by
        rw [integral_indicator unitDisk_closed.measurableSet]
        rfl
      _ =
          ∫ p in polarCoord.target,
            p.1 * unitDisk.indicator g (polarCoord.symm p) := by
        simpa only [smul_eq_mul] using hp.symm
      _ =
          ∫ p : ℝ × ℝ, rect.indicator radial p := by
        rw [← integral_indicator polarCoord.open_target.measurableSet]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with p
        exact hpolar_point p
  have hrect_eval :
      (∫ p : ℝ × ℝ, rect.indicator radial p) =
        2 * Real.pi * ∫ r in (0 : ℝ)..1, r * f r := by
    change
      (∫ p : ℝ × ℝ, rect.indicator radial p
        ∂((volume : Measure ℝ).prod volume)) = _
    change Integrable (rect.indicator radial)
      ((volume : Measure ℝ).prod volume) at hrect_integrable
    rw [integral_prod _ hrect_integrable]
    have hsection (r : ℝ) :
        (∫ phi : ℝ, rect.indicator radial (r, phi)) =
          (Set.Ioc (0 : ℝ) 1).indicator
            (fun r => 2 * Real.pi * (r * f r)) r := by
      by_cases hr : r ∈ Set.Ioc (0 : ℝ) 1
      · rw [Set.indicator_of_mem hr]
        calc
          (∫ phi : ℝ, rect.indicator radial (r, phi)) =
              ∫ _phi in Set.Ioo (-Real.pi) Real.pi, r * f r := by
            rw [← integral_indicator measurableSet_Ioo]
            apply MeasureTheory.integral_congr_ae
            filter_upwards with phi
            by_cases hphi : phi ∈ Set.Ioo (-Real.pi) Real.pi
            · simp [rect, radial, hr, hphi]
            · simp [rect, radial, hr, hphi]
          _ = 2 * Real.pi * (r * f r) := by
            rw [MeasureTheory.setIntegral_const]
            have hvol :
                (volume : Measure ℝ).real
                    (Set.Ioo (-Real.pi) Real.pi) =
                  2 * Real.pi := by
              simp [Measure.real, Real.volume_Ioo, Real.pi_pos.le]
              ring
            rw [hvol]
            simp [smul_eq_mul]
      · have hz :
          (fun phi : ℝ => rect.indicator radial (r, phi)) = 0 := by
          funext phi
          simp [rect, hr]
        rw [hz]
        simp [hr]
    simp_rw [hsection]
    rw [integral_indicator measurableSet_Ioc,
      ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_const_mul]
  exact hpolar.trans hrect_eval

theorem gap1 (f : ℝ → ℝ)
    (hf : IntegrableOn
      (fun p : ℝ × ℝ => f (Real.sqrt (p.1 ^ 2 + p.2 ^ 2)))
      unitDisk) :
    radialDiskIntegral f =
      ∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..1, f r * r := by
  rw [radialDiskIntegral_eq f hf]
  have hinner :
      (∫ r in (0 : ℝ)..1, f r * r) =
        ∫ r in (0 : ℝ)..1, r * f r := by
    apply intervalIntegral.integral_congr
    intro r hr
    ring
  rw [hinner, intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]

theorem gap2 (f : ℝ → ℝ)
    (hf : IntervalIntegrable (fun r : ℝ => r * f r) volume 0 1) :
    (∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..1, f r * r) =
      2 * Real.pi * ∫ r in (0 : ℝ)..1, r * f r := by
  have hinner :
      (∫ r in (0 : ℝ)..1, f r * r) =
        ∫ r in (0 : ℝ)..1, r * f r := by
    apply intervalIntegral.integral_congr
    intro r hr
    ring
  rw [hinner, intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]

theorem gap3 (f : ℝ → ℝ)
    (hf : IntegrableOn
      (fun p : ℝ × ℝ => f (Real.sqrt (p.1 ^ 2 + p.2 ^ 2)))
      unitDisk) :
    radialDiskIntegral f =
      2 * Real.pi * ∫ r in (0 : ℝ)..1, r * f r := by
  exact radialDiskIntegral_eq f hf

end

end ProofGap.Exercise3951
