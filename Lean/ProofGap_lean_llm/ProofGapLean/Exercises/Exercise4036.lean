import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4036

noncomputable section

open MeasureTheory
open scoped Interval

def graphHeight (a x y : ℝ) : ℝ :=
  (x ^ 2 + y ^ 2) / (2 * a)

def surfaceArea (a : ℝ) : ℝ :=
  ∫ x in -a..a,
    ∫ y in -Real.sqrt (a ^ 2 - x ^ 2)..Real.sqrt (a ^ 2 - x ^ 2),
      Real.sqrt (1 + (y / a) ^ 2 + (x / a) ^ 2)

private theorem ae_real_ne (u : ℝ) :
    ∀ᵐ x : ℝ ∂(volume : Measure ℝ), x ≠ u := by
  rw [ae_iff]
  simpa using measure_singleton u

private theorem integral_indicator_Icc_eq_interval
    (u v : ℝ) (f : ℝ → ℝ) (huv : u ≤ v) :
    (∫ x : ℝ, (Set.Icc u v).indicator f x) = ∫ x in u..v, f x := by
  rw [intervalIntegral.integral_of_le huv]
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [ae_real_ne u] with x hx
  by_cases hxc : x ∈ Set.Icc u v
  · have hxo : x ∈ Set.Ioc u v :=
      ⟨lt_of_le_of_ne hxc.1 (Ne.symm hx), hxc.2⟩
    simp [hxc, hxo]
  · have hxo : x ∉ Set.Ioc u v := fun h => hxc ⟨h.1.le, h.2⟩
    simp [hxc, hxo]

private theorem disk_sliced_sqrt_eq_quarter_polar (a : ℝ) (ha : 0 < a) :
    (∫ x in -a..a,
      ∫ y in -Real.sqrt (a ^ 2 - x ^ 2)..Real.sqrt (a ^ 2 - x ^ 2),
        Real.sqrt (a ^ 2 + x ^ 2 + y ^ 2)) =
      4 *
        ∫ φ in (0 : ℝ)..Real.pi / 2,
          ∫ r in (0 : ℝ)..a, r * Real.sqrt (a ^ 2 + r ^ 2) := by
  let disk : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 ≤ a ^ 2}
  let g : ℝ × ℝ → ℝ := fun p => Real.sqrt (a ^ 2 + p.1 ^ 2 + p.2 ^ 2)
  have hdisk_closed : IsClosed disk := by
    dsimp [disk]
    exact isClosed_le ((continuous_fst.pow 2).add (continuous_snd.pow 2))
      continuous_const
  have hdisk_sub :
      disk ⊆ Set.Icc (-a) a ×ˢ Set.Icc (-a) a := by
    intro p hp
    change p.1 ^ 2 + p.2 ^ 2 ≤ a ^ 2 at hp
    have hx : |p.1| ≤ a := by
      rw [← sq_le_sq₀ (abs_nonneg p.1) ha.le, sq_abs]
      nlinarith [sq_nonneg p.2]
    have hy : |p.2| ≤ a := by
      rw [← sq_le_sq₀ (abs_nonneg p.2) ha.le, sq_abs]
      nlinarith [sq_nonneg p.1]
    exact ⟨abs_le.1 hx, abs_le.1 hy⟩
  have hdisk_compact : IsCompact disk :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hdisk_closed hdisk_sub
  have hg_cont : Continuous g := by
    dsimp [g]
    fun_prop
  have hg_disk : IntegrableOn g disk :=
    hg_cont.continuousOn.integrableOn_compact hdisk_compact
  have hind : Integrable (disk.indicator g) :=
    (integrable_indicator_iff hdisk_closed.measurableSet).2 hg_disk
  have hindicator (x y : ℝ) :
      disk.indicator g (x, y) =
        (Set.Icc (-a) a).indicator
          (fun x =>
            (Set.Icc (-Real.sqrt (a ^ 2 - x ^ 2))
                (Real.sqrt (a ^ 2 - x ^ 2))).indicator
              (fun y => Real.sqrt (a ^ 2 + x ^ 2 + y ^ 2)) y) x := by
    by_cases hx : x ∈ Set.Icc (-a) a
    · have hrad : 0 ≤ a ^ 2 - x ^ 2 := by
        have hprod : 0 ≤ (a - x) * (a + x) :=
          mul_nonneg (sub_nonneg.2 hx.2) (by linarith [hx.1])
        nlinarith
      have hs : Real.sqrt (a ^ 2 - x ^ 2) ^ 2 = a ^ 2 - x ^ 2 :=
        Real.sq_sqrt hrad
      by_cases hy :
          y ∈ Set.Icc (-Real.sqrt (a ^ 2 - x ^ 2))
            (Real.sqrt (a ^ 2 - x ^ 2))
      · have hymem : (x, y) ∈ disk := by
          change x ^ 2 + y ^ 2 ≤ a ^ 2
          have hprod :
              0 ≤ (Real.sqrt (a ^ 2 - x ^ 2) - y) *
                (Real.sqrt (a ^ 2 - x ^ 2) + y) :=
            mul_nonneg (sub_nonneg.2 hy.2) (by linarith [hy.1])
          nlinarith
        simp [hymem, hx, hy, g]
      · have hynmem : (x, y) ∉ disk := by
          intro hmem
          apply hy
          change x ^ 2 + y ^ 2 ≤ a ^ 2 at hmem
          have hybound : |y| ≤ Real.sqrt (a ^ 2 - x ^ 2) := by
            rw [← sq_le_sq₀ (abs_nonneg y) (Real.sqrt_nonneg _), sq_abs, hs]
            linarith
          exact abs_le.1 hybound
        simp [hynmem, hx, hy]
    · have hxnmem : ∀ y : ℝ, (x, y) ∉ disk := by
        intro y hmem
        apply hx
        change x ^ 2 + y ^ 2 ≤ a ^ 2 at hmem
        have hxabs : |x| ≤ a := by
          rw [← sq_le_sq₀ (abs_nonneg x) ha.le, sq_abs]
          nlinarith [sq_nonneg y]
        exact abs_le.1 hxabs
      simp [hx, hxnmem y]
  have hslice :
      (∫ p in disk, g p) =
        ∫ x in -a..a,
          ∫ y in -Real.sqrt (a ^ 2 - x ^ 2)..Real.sqrt (a ^ 2 - x ^ 2),
            Real.sqrt (a ^ 2 + x ^ 2 + y ^ 2) := by
    rw [← integral_indicator hdisk_closed.measurableSet]
    change
      (∫ p : ℝ × ℝ, disk.indicator g p
        ∂((volume : Measure ℝ).prod volume)) = _
    change Integrable (disk.indicator g)
      ((volume : Measure ℝ).prod volume) at hind
    rw [integral_prod _ hind]
    have hcollapse (x : ℝ) :
        (∫ y : ℝ,
          (Set.Icc (-a) a).indicator
            (fun x =>
              (Set.Icc (-Real.sqrt (a ^ 2 - x ^ 2))
                  (Real.sqrt (a ^ 2 - x ^ 2))).indicator
                (fun y => Real.sqrt (a ^ 2 + x ^ 2 + y ^ 2)) y) x) =
          (Set.Icc (-a) a).indicator
            (fun x =>
              ∫ y : ℝ,
                (Set.Icc (-Real.sqrt (a ^ 2 - x ^ 2))
                    (Real.sqrt (a ^ 2 - x ^ 2))).indicator
                  (fun y => Real.sqrt (a ^ 2 + x ^ 2 + y ^ 2)) y) x := by
      by_cases hx : x ∈ Set.Icc (-a) a <;> simp [hx]
    simp_rw [hindicator, hcollapse]
    rw [integral_indicator_Icc_eq_interval (-a) a _ (by linarith)]
    apply intervalIntegral.integral_congr
    intro x hx
    exact integral_indicator_Icc_eq_interval
      (-Real.sqrt (a ^ 2 - x ^ 2)) (Real.sqrt (a ^ 2 - x ^ 2)) _
      (by linarith [Real.sqrt_nonneg (a ^ 2 - x ^ 2)])
  let rect : Set (ℝ × ℝ) :=
    Set.Ioc (0 : ℝ) a ×ˢ Set.Ioo (-Real.pi) Real.pi
  let radial : ℝ × ℝ → ℝ :=
    fun p => p.1 * Real.sqrt (a ^ 2 + p.1 ^ 2)
  have hrect_meas : MeasurableSet rect := measurableSet_Ioc.prod measurableSet_Ioo
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
          (fun q =>
            q.1 *
              disk.indicator g (polarCoord.symm q)) p =
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
      have hgpolar :
          g (polarCoord.symm p) =
            Real.sqrt (a ^ 2 + p.1 ^ 2) := by
        dsimp only [g]
        congr 1
        calc
          a ^ 2 + (polarCoord.symm p).1 ^ 2 +
                (polarCoord.symm p).2 ^ 2 =
              a ^ 2 +
                ((polarCoord.symm p).1 ^ 2 +
                  (polarCoord.symm p).2 ^ 2) := by ring
          _ = a ^ 2 + p.1 ^ 2 := by rw [hnorm]
      by_cases hra : p.1 ≤ a
      · have hd : polarCoord.symm p ∈ disk := by
          change
            (polarCoord.symm p).1 ^ 2 +
                (polarCoord.symm p).2 ^ 2 ≤ a ^ 2
          rw [hnorm]
          nlinarith
        have hp_rect : p ∈ rect := ⟨⟨hrpos, hra⟩, hang⟩
        rw [Set.indicator_of_mem ht, Set.indicator_of_mem hp_rect,
          Set.indicator_of_mem hd, hgpolar]
      · have hd : polarCoord.symm p ∉ disk := by
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
      (∫ p in disk, g p) = ∫ p : ℝ × ℝ, rect.indicator radial p := by
    have hp := integral_comp_polarCoord_symm (disk.indicator g)
    calc
      (∫ p in disk, g p) =
          ∫ p : ℝ × ℝ, disk.indicator g p := by
        rw [integral_indicator hdisk_closed.measurableSet]
      _ =
          ∫ p in polarCoord.target,
            p.1 * disk.indicator g (polarCoord.symm p) := by
        simpa only [smul_eq_mul] using hp.symm
      _ =
          ∫ p : ℝ × ℝ, rect.indicator radial p := by
        rw [← integral_indicator polarCoord.open_target.measurableSet]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with p
        exact hpolar_point p
  have hrect_eval :
      (∫ p : ℝ × ℝ, rect.indicator radial p) =
        2 * Real.pi *
          ∫ r in (0 : ℝ)..a, r * Real.sqrt (a ^ 2 + r ^ 2) := by
    change
      (∫ p : ℝ × ℝ, rect.indicator radial p
        ∂((volume : Measure ℝ).prod volume)) = _
    change Integrable (rect.indicator radial)
      ((volume : Measure ℝ).prod volume) at hrect_integrable
    rw [integral_prod _ hrect_integrable]
    have hsection (r : ℝ) :
        (∫ φ : ℝ, rect.indicator radial (r, φ)) =
          (Set.Ioc (0 : ℝ) a).indicator
            (fun r => 2 * Real.pi * (r * Real.sqrt (a ^ 2 + r ^ 2))) r := by
      by_cases hr : r ∈ Set.Ioc (0 : ℝ) a
      · rw [Set.indicator_of_mem hr]
        calc
          (∫ φ : ℝ, rect.indicator radial (r, φ)) =
              ∫ φ in Set.Ioo (-Real.pi) Real.pi,
                r * Real.sqrt (a ^ 2 + r ^ 2) := by
            rw [← integral_indicator measurableSet_Ioo]
            apply MeasureTheory.integral_congr_ae
            filter_upwards with φ
            by_cases hφ : φ ∈ Set.Ioo (-Real.pi) Real.pi
            · simp [rect, radial, hr, hφ]
            · simp [rect, radial, hr, hφ]
          _ = 2 * Real.pi * (r * Real.sqrt (a ^ 2 + r ^ 2)) := by
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
          (fun φ : ℝ => rect.indicator radial (r, φ)) = 0 := by
          funext φ
          simp [rect, hr]
        rw [hz]
        simp [hr]
    simp_rw [hsection]
    rw [integral_indicator measurableSet_Ioc,
      ← intervalIntegral.integral_of_le ha.le,
      intervalIntegral.integral_const_mul]
  have hquarter :
      4 *
          (∫ φ in (0 : ℝ)..Real.pi / 2,
            ∫ r in (0 : ℝ)..a, r * Real.sqrt (a ^ 2 + r ^ 2)) =
        2 * Real.pi *
          ∫ r in (0 : ℝ)..a, r * Real.sqrt (a ^ 2 + r ^ 2) := by
    simp
    ring
  rw [← hslice, hpolar, hrect_eval, hquarter]

theorem gap1 (a : ℝ) (ha : 0 < a) :
    surfaceArea a =
      ∫ x in -a..a,
        ∫ y in -Real.sqrt (a ^ 2 - x ^ 2)..Real.sqrt (a ^ 2 - x ^ 2),
          Real.sqrt (1 + (y / a) ^ 2 + (x / a) ^ 2) := by
  rfl

theorem gap2 (a : ℝ) (ha : 0 < a) :
    surfaceArea a =
      ∫ x in -a..a,
        ∫ y in -Real.sqrt (a ^ 2 - x ^ 2)..Real.sqrt (a ^ 2 - x ^ 2),
          Real.sqrt ((a ^ 2 + x ^ 2 + y ^ 2) / a ^ 2) := by
  rw [gap1 a ha]
  apply intervalIntegral.integral_congr
  intro x hx
  apply intervalIntegral.integral_congr
  intro y hy
  congr 1
  field_simp [ha.ne']
  ring

theorem gap3 (a : ℝ) (ha : 0 < a) :
    surfaceArea a =
      1 / a *
        ∫ x in -a..a,
          ∫ y in -Real.sqrt (a ^ 2 - x ^ 2)..Real.sqrt (a ^ 2 - x ^ 2),
            Real.sqrt (a ^ 2 + x ^ 2 + y ^ 2) := by
  rw [gap2 a ha, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  change
    (∫ y in -Real.sqrt (a ^ 2 - x ^ 2)..Real.sqrt (a ^ 2 - x ^ 2),
      Real.sqrt ((a ^ 2 + x ^ 2 + y ^ 2) / a ^ 2)) =
      1 / a *
        ∫ y in -Real.sqrt (a ^ 2 - x ^ 2)..Real.sqrt (a ^ 2 - x ^ 2),
          Real.sqrt (a ^ 2 + x ^ 2 + y ^ 2)
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro y hy
  change
    Real.sqrt ((a ^ 2 + x ^ 2 + y ^ 2) / a ^ 2) =
      1 / a * Real.sqrt (a ^ 2 + x ^ 2 + y ^ 2)
  have hnum : 0 ≤ a ^ 2 + x ^ 2 + y ^ 2 := by positivity
  rw [Real.sqrt_div hnum, Real.sqrt_sq_eq_abs, abs_of_pos ha]
  ring

theorem gap4 (a : ℝ) (ha : 0 < a) :
    surfaceArea a =
      4 / a *
        ∫ φ in (0 : ℝ)..Real.pi / 2,
          ∫ r in (0 : ℝ)..a, r * Real.sqrt (a ^ 2 + r ^ 2) := by
  rw [gap3 a ha, disk_sliced_sqrt_eq_quarter_polar a ha]
  ring

theorem gap5 (a : ℝ) (ha : 0 < a) :
    4 / a *
        (∫ φ in (0 : ℝ)..Real.pi / 2,
          ∫ r in (0 : ℝ)..a, r * Real.sqrt (a ^ 2 + r ^ 2)) =
      2 * Real.pi * a ^ 2 / 3 * (2 * Real.sqrt 2 - 1) := by
  have hrad :
      (∫ r in (0 : ℝ)..a, r * Real.sqrt (a ^ 2 + r ^ 2)) =
        a ^ 3 / 3 * (2 * Real.sqrt 2 - 1) := by
    let F : ℝ → ℝ :=
      fun r => (a ^ 2 + r ^ 2) * Real.sqrt (a ^ 2 + r ^ 2) / 3
    have hderiv :
        ∀ r ∈ Set.uIcc (0 : ℝ) a,
          HasDerivAt F (r * Real.sqrt (a ^ 2 + r ^ 2)) r := by
      intro r hr
      have hq : 0 < a ^ 2 + r ^ 2 := by
        nlinarith [sq_pos_of_pos ha, sq_nonneg r]
      have hpoly :
          HasDerivAt (fun t : ℝ => a ^ 2 + t ^ 2) (2 * r) r := by
        convert (hasDerivAt_const r (a ^ 2)).add ((hasDerivAt_id r).pow 2)
          using 1 <;> simp <;> ring
      have hsqrt :
          HasDerivAt (fun t : ℝ => Real.sqrt (a ^ 2 + t ^ 2))
            (r / Real.sqrt (a ^ 2 + r ^ 2)) r := by
        convert (Real.hasDerivAt_sqrt hq.ne').comp r hpoly using 1 <;>
          field_simp [Real.sqrt_pos.2 hq |>.ne'] <;> ring
      have hsquare :
          Real.sqrt (a ^ 2 + r ^ 2) ^ 2 = a ^ 2 + r ^ 2 :=
        Real.sq_sqrt hq.le
      have htotal :=
        (hpoly.mul hsqrt).div_const 3
      have htotal' :
          HasDerivAt F
            ((2 * r * Real.sqrt (a ^ 2 + r ^ 2) +
                (a ^ 2 + r ^ 2) *
                  (r / Real.sqrt (a ^ 2 + r ^ 2))) / 3) r := by
        simpa [F] using htotal
      have hcoef :
          (2 * r * Real.sqrt (a ^ 2 + r ^ 2) +
                (a ^ 2 + r ^ 2) *
                  (r / Real.sqrt (a ^ 2 + r ^ 2))) / 3 =
            r * Real.sqrt (a ^ 2 + r ^ 2) := by
        field_simp [Real.sqrt_pos.2 hq |>.ne']
        rw [hsquare]
        ring
      simpa [hcoef] using htotal'
    have hint :
        IntervalIntegrable (fun r : ℝ => r * Real.sqrt (a ^ 2 + r ^ 2))
          volume 0 a := by
      exact
        (continuous_id.mul
          (Real.continuous_sqrt.comp
            (continuous_const.add (continuous_id.pow 2)))).intervalIntegrable 0 a
    have hzero : Real.sqrt (a ^ 2 + (0 : ℝ) ^ 2) = a := by
      simp [Real.sqrt_sq_eq_abs, abs_of_pos ha]
    have htwo :
        Real.sqrt (a ^ 2 + a ^ 2) = a * Real.sqrt 2 := by
      rw [show a ^ 2 + a ^ 2 = a ^ 2 * 2 by ring, Real.sqrt_mul (sq_nonneg a),
        Real.sqrt_sq_eq_abs, abs_of_pos ha]
    calc
      (∫ r in (0 : ℝ)..a, r * Real.sqrt (a ^ 2 + r ^ 2)) =
          F a - F 0 :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
      _ = a ^ 3 / 3 * (2 * Real.sqrt 2 - 1) := by
        dsimp [F]
        rw [hzero, htwo]
        ring
  simp_rw [hrad]
  simp
  field_simp [ha.ne']
  ring

theorem gap6 (a : ℝ) (ha : 0 < a) :
    surfaceArea a =
      2 * Real.pi * a ^ 2 / 3 * (2 * Real.sqrt 2 - 1) := by
  rw [gap4 a ha, gap5 a ha]

end

end ProofGap.Exercise4036
