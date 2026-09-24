import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3954

noncomputable section

open MeasureTheory
open scoped Interval

def disk (a : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2 ^ 2 ≤ a ^ 2}

def radiusIntegral (a : ℝ) : ℝ :=
  ∫ p in disk a, Real.sqrt (p.1 ^ 2 + p.2 ^ 2)

private theorem disk_closed (a : ℝ) : IsClosed (disk a) := by
  exact isClosed_le ((continuous_fst.pow 2).add (continuous_snd.pow 2))
    continuous_const

private theorem radiusIntegral_eq (a : ℝ) (ha : 0 ≤ a) :
    radiusIntegral a =
      2 * Real.pi * ∫ r in (0 : ℝ)..a, r * r := by
  let g : ℝ × ℝ → ℝ := fun p =>
    Real.sqrt (p.1 ^ 2 + p.2 ^ 2)
  let rect : Set (ℝ × ℝ) :=
    Set.Ioc (0 : ℝ) a ×ˢ Set.Ioo (-Real.pi) Real.pi
  let radial : ℝ × ℝ → ℝ := fun p => p.1 * p.1
  have hdisk_sub :
      disk a ⊆ Set.Icc (-a) a ×ˢ Set.Icc (-a) a := by
    intro p hp
    change p.1 ^ 2 + p.2 ^ 2 ≤ a ^ 2 at hp
    have hx : |p.1| ≤ a := by
      rw [← sq_le_sq₀ (abs_nonneg p.1) ha, sq_abs]
      nlinarith [sq_nonneg p.2]
    have hy : |p.2| ≤ a := by
      rw [← sq_le_sq₀ (abs_nonneg p.2) ha, sq_abs]
      nlinarith [sq_nonneg p.1]
    exact ⟨abs_le.1 hx, abs_le.1 hy⟩
  have hdisk_compact : IsCompact (disk a) :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset
      (disk_closed a) hdisk_sub
  have hg_cont : Continuous g := by
    dsimp [g]
    fun_prop
  have hg_disk : IntegrableOn g (disk a) :=
    hg_cont.continuousOn.integrableOn_compact hdisk_compact
  have hrect_meas : MeasurableSet rect :=
    measurableSet_Ioc.prod measurableSet_Ioo
  have hrect_sub :
      rect ⊆ Set.Icc (0 : ℝ) a ×ˢ Set.Icc (-Real.pi) Real.pi := by
    intro p hp
    exact ⟨⟨hp.1.1.le, hp.1.2⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
  have hradial_cont : Continuous radial := by
    dsimp [radial]
    fun_prop
  have hrect_integrable : Integrable (rect.indicator radial) := by
    rw [integrable_indicator_iff hrect_meas]
    exact
      (hradial_cont.continuousOn.integrableOn_compact
        (isCompact_Icc.prod isCompact_Icc)).mono_set hrect_sub
  have hpolar_point (p : ℝ × ℝ) :
      polarCoord.target.indicator
          (fun q => q.1 * (disk a).indicator g (polarCoord.symm q)) p =
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
      have hgpolar : g (polarCoord.symm p) = p.1 := by
        dsimp only [g]
        rw [hnorm, Real.sqrt_sq_eq_abs, abs_of_pos hrpos]
      by_cases hra : p.1 ≤ a
      · have hd : polarCoord.symm p ∈ disk a := by
          change
            (polarCoord.symm p).1 ^ 2 +
                (polarCoord.symm p).2 ^ 2 ≤ a ^ 2
          rw [hnorm]
          nlinarith
        have hp_rect : p ∈ rect := ⟨⟨hrpos, hra⟩, hang⟩
        rw [Set.indicator_of_mem ht, Set.indicator_of_mem hp_rect,
          Set.indicator_of_mem hd, hgpolar]
      · have hd : polarCoord.symm p ∉ disk a := by
          intro hd
          apply hra
          change
            (polarCoord.symm p).1 ^ 2 +
                (polarCoord.symm p).2 ^ 2 ≤ a ^ 2 at hd
          rw [hnorm] at hd
          nlinarith
        have hp_rect : p ∉ rect := fun hp => hra hp.1.2
        rw [Set.indicator_of_mem ht, Set.indicator_of_notMem hd,
          Set.indicator_of_notMem hp_rect]
        simp
    · have hp_rect : p ∉ rect := by
        intro hp
        apply ht
        exact ⟨hp.1.1, hp.2⟩
      rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem hp_rect]
  have hpolar :
      radiusIntegral a =
        ∫ p : ℝ × ℝ, rect.indicator radial p := by
    have hp := integral_comp_polarCoord_symm ((disk a).indicator g)
    calc
      radiusIntegral a =
          ∫ p : ℝ × ℝ, (disk a).indicator g p := by
        rw [integral_indicator (disk_closed a).measurableSet]
        rfl
      _ =
          ∫ p in polarCoord.target,
            p.1 * (disk a).indicator g (polarCoord.symm p) := by
        simpa only [smul_eq_mul] using hp.symm
      _ =
          ∫ p : ℝ × ℝ, rect.indicator radial p := by
        rw [← integral_indicator polarCoord.open_target.measurableSet]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with p
        exact hpolar_point p
  have hrect_eval :
      (∫ p : ℝ × ℝ, rect.indicator radial p) =
        2 * Real.pi * ∫ r in (0 : ℝ)..a, r * r := by
    change
      (∫ p : ℝ × ℝ, rect.indicator radial p
        ∂((volume : Measure ℝ).prod volume)) = _
    change Integrable (rect.indicator radial)
      ((volume : Measure ℝ).prod volume) at hrect_integrable
    rw [integral_prod _ hrect_integrable]
    have hsection (r : ℝ) :
        (∫ phi : ℝ, rect.indicator radial (r, phi)) =
          (Set.Ioc (0 : ℝ) a).indicator
            (fun r => 2 * Real.pi * (r * r)) r := by
      by_cases hr : r ∈ Set.Ioc (0 : ℝ) a
      · rw [Set.indicator_of_mem hr]
        calc
          (∫ phi : ℝ, rect.indicator radial (r, phi)) =
              ∫ _phi in Set.Ioo (-Real.pi) Real.pi, r * r := by
            rw [← integral_indicator measurableSet_Ioo]
            apply MeasureTheory.integral_congr_ae
            filter_upwards with phi
            by_cases hphi : phi ∈ Set.Ioo (-Real.pi) Real.pi
            · simp [rect, radial, hr, hphi]
            · simp [rect, radial, hr, hphi]
          _ = 2 * Real.pi * (r * r) := by
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
      ← intervalIntegral.integral_of_le ha,
      intervalIntegral.integral_const_mul]
  exact hpolar.trans hrect_eval

theorem gap1 (a : ℝ) (ha : 0 ≤ a) :
    radiusIntegral a =
      ∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..a, r * r := by
  rw [radiusIntegral_eq a ha]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]

theorem gap2 (a : ℝ) (ha : 0 ≤ a) :
    (∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..a, r * r) =
      2 * Real.pi * a ^ 3 / 3 := by
  rw [intervalIntegral.integral_const]
  rw [show (fun r : ℝ => r * r) = fun r => r ^ 2 by
    funext r
    ring]
  rw [integral_pow]
  norm_num
  ring

theorem gap3 (a : ℝ) (ha : 0 ≤ a) :
    radiusIntegral a = 2 * Real.pi * a ^ 3 / 3 := by
  rw [gap1 a ha, gap2 a ha]

end

end ProofGap.Exercise3954
