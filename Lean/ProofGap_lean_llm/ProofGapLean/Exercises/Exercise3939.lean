import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3939

noncomputable section

open MeasureTheory
open scoped Interval

def annulus (a b : ℝ) : Set (ℝ × ℝ) :=
  {p | a ^ 2 ≤ p.1 ^ 2 + p.2 ^ 2 ∧
    p.1 ^ 2 + p.2 ^ 2 ≤ b ^ 2}

def polarPoint (r φ : ℝ) : ℝ × ℝ :=
  (r * Real.cos φ, r * Real.sin φ)

def annulusIntegral (a b : ℝ) (f : ℝ → ℝ → ℝ) : ℝ :=
  ∫ p in annulus a b, f p.1 p.2

private theorem ae_real_ne (u : ℝ) :
    ∀ᵐ x : ℝ ∂(volume : Measure ℝ), x ≠ u := by
  rw [ae_iff]
  simpa using measure_singleton u

theorem gap1 (a b φ r : ℝ)
    (hφ₀ : 0 ≤ φ) (hφ₂π : φ ≤ 2 * Real.pi)
    (hr : 0 ≤ r) (hp : polarPoint r φ ∈ annulus a b) :
    |a| ≤ r := by
  rcases hp with ⟨hp₁, hp₂⟩
  simp only [polarPoint] at hp₁ hp₂ ⊢
  rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one] at hp₁
  nlinarith [sq_abs a, abs_nonneg a]

theorem gap2 (a b φ r : ℝ)
    (hφ₀ : 0 ≤ φ) (hφ₂π : φ ≤ 2 * Real.pi)
    (hr : 0 ≤ r) (hp : polarPoint r φ ∈ annulus a b) :
    r ≤ |b| := by
  rcases hp with ⟨hp₁, hp₂⟩
  simp only [polarPoint] at hp₁ hp₂ ⊢
  rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one] at hp₂
  nlinarith [sq_abs b, abs_nonneg b]

theorem gap3 (a b : ℝ) (hΩ : (annulus a b).Nonempty) :
    |a| ≤ |b| := by
  rcases hΩ with ⟨⟨x, y⟩, hxy⟩
  simp only [annulus, Set.mem_setOf_eq] at hxy
  rcases hxy with ⟨hlo, hhi⟩
  nlinarith [sq_abs a, sq_abs b, abs_nonneg a, abs_nonneg b]

theorem gap4 (a b : ℝ) (f : ℝ → ℝ → ℝ)
    (hab : |a| ≤ |b|)
    (hf : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2) (annulus a b)) :
    annulusIntegral a b f =
      ∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in |a|..|b|,
          f (r * Real.cos φ) (r * Real.sin φ) * r := by
  let g : ℝ × ℝ → ℝ := fun p => f p.1 p.2
  let rect : Set (ℝ × ℝ) :=
    Set.Ioc |a| |b| ×ˢ Set.Ioo (-Real.pi) Real.pi
  let radial : ℝ × ℝ → ℝ := fun p =>
    f (p.1 * Real.cos p.2) (p.1 * Real.sin p.2) * p.1
  have hannulus_meas : MeasurableSet (annulus a b) := by
    exact
      (measurableSet_le measurable_const
        ((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2))).inter
      (measurableSet_le
        ((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2))
        measurable_const)
  have hg_annulus : IntegrableOn g (annulus a b) := by
    simpa only [g] using hf
  have hg_ind : Integrable ((annulus a b).indicator g) :=
    (integrable_indicator_iff hannulus_meas).2 hg_annulus
  have hrect_meas : MeasurableSet rect :=
    measurableSet_Ioc.prod measurableSet_Ioo
  have hpolar_point (p : ℝ × ℝ) (hpA : p.1 ≠ |a|) :
      polarCoord.target.indicator
          (fun q => q.1 * (annulus a b).indicator g (polarCoord.symm q)) p =
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
      have hmem :
          polarCoord.symm p ∈ annulus a b ↔
            |a| ≤ p.1 ∧ p.1 ≤ |b| := by
        change
          a ^ 2 ≤
                (polarCoord.symm p).1 ^ 2 +
                  (polarCoord.symm p).2 ^ 2 ∧
              (polarCoord.symm p).1 ^ 2 +
                  (polarCoord.symm p).2 ^ 2 ≤ b ^ 2 ↔
            |a| ≤ p.1 ∧ p.1 ≤ |b|
        rw [hnorm]
        constructor
        · rintro ⟨ha, hb⟩
          exact
            ⟨by nlinarith [sq_abs a, abs_nonneg a],
              by nlinarith [sq_abs b, abs_nonneg b]⟩
        · rintro ⟨ha, hb⟩
          constructor
          · nlinarith [sq_abs a, abs_nonneg a]
          · nlinarith [sq_abs b, abs_nonneg b]
      by_cases hrange : |a| ≤ p.1 ∧ p.1 ≤ |b|
      · have hd : polarCoord.symm p ∈ annulus a b := hmem.mpr hrange
        have hp_rect : p ∈ rect :=
          ⟨⟨lt_of_le_of_ne hrange.1 (Ne.symm hpA), hrange.2⟩, hang⟩
        rw [Set.indicator_of_mem ht, Set.indicator_of_mem hp_rect,
          Set.indicator_of_mem hd]
        simp only [g, radial, polarCoord_symm_apply]
        ring
      · have hd : polarCoord.symm p ∉ annulus a b :=
          fun hd => hrange (hmem.mp hd)
        have hp_rect : p ∉ rect :=
          fun hp => hrange ⟨hp.1.1.le, hp.1.2⟩
        rw [Set.indicator_of_mem ht, Set.indicator_of_notMem hd,
          Set.indicator_of_notMem hp_rect]
        simp
    · have hp_rect : p ∉ rect := by
        intro hp
        apply ht
        exact ⟨lt_of_le_of_lt (abs_nonneg a) hp.1.1, hp.2⟩
      rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem hp_rect]
  have hae_fst :
      ∀ᵐ p : ℝ × ℝ ∂((volume : Measure ℝ).prod volume),
        p.1 ≠ |a| := by
    change
      ∀ᵐ p : ℝ × ℝ ∂((volume : Measure ℝ).prod volume),
        p.1 ∈ ({|a|} : Set ℝ)ᶜ
    rw [MeasureTheory.Measure.ae_prod_iff_ae_ae
      (measurable_fst (measurableSet_singleton |a|).compl)]
    filter_upwards [ae_real_ne |a|] with r hr
    exact Filter.Eventually.of_forall fun _phi => by simpa using hr
  have hweighted_on :
      IntegrableOn
        (fun p : ℝ × ℝ =>
          |(fderivPolarCoordSymm p).det| •
            (annulus a b).indicator g (polarCoord.symm p))
        polarCoord.target := by
    have hsource :
        IntegrableOn ((annulus a b).indicator g) polarCoord.source :=
      hg_ind.integrableOn
    have hchange :=
      (MeasureTheory.integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
        (μ := volume) polarCoord.open_target.measurableSet
        (fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)
        polarCoord.symm.injOn ((annulus a b).indicator g))
    rw [polarCoord.symm_image_target_eq_source] at hchange
    exact hchange.mp hsource
  have hweighted_on' :
      IntegrableOn
        (fun p : ℝ × ℝ =>
          p.1 * (annulus a b).indicator g (polarCoord.symm p))
        polarCoord.target := by
    refine hweighted_on.congr_fun (fun p hp => ?_)
      polarCoord.open_target.measurableSet
    rw [det_fderivPolarCoordSymm, abs_of_pos hp.1]
    rfl
  have htarget_ind :
      Integrable
        (polarCoord.target.indicator
          (fun p : ℝ × ℝ =>
            p.1 * (annulus a b).indicator g (polarCoord.symm p))) :=
    (integrable_indicator_iff polarCoord.open_target.measurableSet).2
      hweighted_on'
  have hrect_integrable : Integrable (rect.indicator radial) := by
    refine htarget_ind.congr ?_
    filter_upwards [hae_fst] with p hpA
    exact hpolar_point p hpA
  have hpolar :
      annulusIntegral a b f =
        ∫ p : ℝ × ℝ, rect.indicator radial p := by
    have hp :=
      integral_comp_polarCoord_symm ((annulus a b).indicator g)
    calc
      annulusIntegral a b f =
          ∫ p : ℝ × ℝ, (annulus a b).indicator g p := by
        rw [integral_indicator hannulus_meas]
        rfl
      _ =
          ∫ p in polarCoord.target,
            p.1 * (annulus a b).indicator g (polarCoord.symm p) := by
        simpa only [smul_eq_mul] using hp.symm
      _ =
          ∫ p : ℝ × ℝ, rect.indicator radial p := by
        rw [← integral_indicator polarCoord.open_target.measurableSet]
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hae_fst] with p hpA
        exact hpolar_point p hpA
  have hrect_on : IntegrableOn radial rect :=
    (integrable_indicator_iff hrect_meas).mp hrect_integrable
  have hrect_eval :
      (∫ p : ℝ × ℝ, rect.indicator radial p) =
        ∫ phi in -Real.pi..Real.pi,
          ∫ r in |a|..|b|,
            f (r * Real.cos phi) (r * Real.sin phi) * r := by
    calc
      (∫ p : ℝ × ℝ, rect.indicator radial p) =
          ∫ p in rect, radial p := by
        rw [integral_indicator hrect_meas]
      _ =
          ∫ q in
              Set.Ioo (-Real.pi) Real.pi ×ˢ Set.Ioc |a| |b|,
            (radial ∘ Prod.swap) q := by
        exact
          (MeasureTheory.setIntegral_prod_swap
            (Set.Ioc |a| |b|) (Set.Ioo (-Real.pi) Real.pi) radial).symm
      _ =
          ∫ phi in Set.Ioo (-Real.pi) Real.pi,
            ∫ r in Set.Ioc |a| |b|, radial (r, phi) := by
        simpa only [Function.comp_apply] using
          (MeasureTheory.setIntegral_prod
            (μ := volume) (ν := volume)
            (radial ∘ Prod.swap) hrect_on.swap)
      _ =
          ∫ phi in -Real.pi..Real.pi,
            ∫ r in |a|..|b|,
              f (r * Real.cos phi) (r * Real.sin phi) * r := by
        rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo]
        rw [← intervalIntegral.integral_of_le
          (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
        apply intervalIntegral.integral_congr
        intro phi hphi
        change
          (∫ r in Set.Ioc |a| |b|, radial (r, phi)) =
            ∫ r in |a|..|b|,
              f (r * Real.cos phi) (r * Real.sin phi) * r
        rw [← intervalIntegral.integral_of_le hab]
  let H : ℝ → ℝ := fun phi =>
    ∫ r in |a|..|b|,
      f (r * Real.cos phi) (r * Real.sin phi) * r
  have hperiod : Function.Periodic H (2 * Real.pi) := by
    intro phi
    dsimp only [H]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [Real.cos_add_two_pi, Real.sin_add_two_pi]
  have hshift :
      (∫ phi in -Real.pi..Real.pi, H phi) =
        ∫ phi in (0 : ℝ)..2 * Real.pi, H phi := by
    have h := hperiod.intervalIntegral_add_eq (-Real.pi) 0
    convert h using 1 <;> ring
  rw [hpolar, hrect_eval]
  exact hshift

end

end ProofGap.Exercise3939
