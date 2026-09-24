import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
namespace ProofGap.Exercise4197

noncomputable section

open MeasureTheory Set
open scoped ENNReal

private theorem inner_polar
    (f : ℝ → ℝ≥0∞) (x : ℝ) :
    (∫⁻ yz : ℝ × ℝ,
        f (x ^ 2 + yz.1 ^ 2 + yz.2 ^ 2)) =
      ∫⁻ p : ℝ × ℝ in polarCoord.target,
        ENNReal.ofReal p.1 *
          f (x ^ 2 + p.1 ^ 2) := by
  rw [← lintegral_comp_polarCoord_symm]
  refine setLIntegral_congr_fun
    polarCoord.open_target.measurableSet ?_
  intro p hp
  simp only [polarCoord_symm_apply,
    smul_eq_mul]
  congr 1
  congr 1
  nlinarith [Real.sin_sq_add_cos_sq p.2]

private theorem inner_polar_angle
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) (x : ℝ) :
    (∫⁻ yz : ℝ × ℝ,
        f (x ^ 2 + yz.1 ^ 2 + yz.2 ^ 2)) =
      ENNReal.ofReal (2 * Real.pi) *
        ∫⁻ r : ℝ in Ioi 0,
          ENNReal.ofReal r *
            f (x ^ 2 + r ^ 2) := by
  rw [inner_polar, polarCoord_target,
    Measure.volume_eq_prod,
    setLIntegral_prod]
  · simp only [lintegral_const, Measure.restrict_apply_univ,
      Real.volume_Ioo]
    simp only [sub_neg_eq_add]
    rw [← lintegral_const_mul]
    · apply lintegral_congr
      intro r
      rw [ENNReal.ofReal_mul (by positivity),
        show ENNReal.ofReal (Real.pi + Real.pi) =
            ENNReal.ofReal 2 * ENNReal.ofReal Real.pi by
          rw [← two_mul, ENNReal.ofReal_mul]
          norm_num]
      ac_rfl
    · measurability
  · measurability

private theorem polar_symm_mem_upper
    (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
    polarCoord.symm p ∈ univ ×ˢ Ioi (0 : ℝ) ↔
      p.2 ∈ Ioo 0 Real.pi := by
  rw [polarCoord_target] at hp
  simp only [polarCoord_symm_apply,
    prodMk_mem_set_prod_eq, mem_univ, mem_Ioi,
    true_and, mem_Ioo]
  constructor
  · intro h
    have hs : 0 < Real.sin p.2 :=
      (mul_pos_iff_of_pos_left hp.1).mp h
    exact ⟨by
      by_contra hθ
      have hnonpos : Real.sin p.2 ≤ 0 :=
        Real.sin_nonpos_of_nonpos_of_neg_pi_le
          (le_of_not_gt hθ) hp.2.1.le
      linarith, hp.2.2⟩
  · intro h
    exact mul_pos hp.1
      (Real.sin_pos_of_pos_of_lt_pi h.1 h.2)

private theorem lintegral_sin_Ioo :
    (∫⁻ θ : ℝ in Ioo 0 Real.pi,
        ENNReal.ofReal (Real.sin θ)) = 2 := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le
        Real.pi_nonneg,
      integral_sin]
    simp
    norm_num
  · exact
      (integrableOn_Icc_iff_integrableOn_Ioo).mp
        Real.continuous_sin.integrableOn_Icc
  · filter_upwards [
        ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact
      (Real.sin_pos_of_pos_of_lt_pi
        hθ.1 hθ.2).le

private theorem halfplane_polar
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z : ℝ × ℝ in univ ×ˢ Ioi 0,
        ENNReal.ofReal z.2 *
          f (z.1 ^ 2 + z.2 ^ 2)) =
      2 * ∫⁻ r : ℝ in Ioi 0,
        ENNReal.ofReal (r ^ 2) *
          f (r ^ 2) := by
  let g : ℝ × ℝ → ℝ≥0∞ := fun z =>
    (univ ×ˢ Ioi (0 : ℝ)).indicator
      (fun z =>
        ENNReal.ofReal z.2 *
          f (z.1 ^ 2 + z.2 ^ 2)) z
  rw [← lintegral_indicator
    (MeasurableSet.univ.prod measurableSet_Ioi)]
  change (∫⁻ z : ℝ × ℝ, g z) = _
  rw [← lintegral_comp_polarCoord_symm]
  calc
    (∫⁻ p : ℝ × ℝ in polarCoord.target,
        ENNReal.ofReal p.1 •
          g (polarCoord.symm p)) =
        ∫⁻ p : ℝ × ℝ in
            Ioi (0 : ℝ) ×ˢ Ioo 0 Real.pi,
          ENNReal.ofReal (p.1 ^ 2) *
            f (p.1 ^ 2) *
              ENNReal.ofReal (Real.sin p.2) := by
      rw [← lintegral_indicator
          polarCoord.open_target.measurableSet,
        ← lintegral_indicator
          (measurableSet_Ioi.prod measurableSet_Ioo)]
      apply lintegral_congr
      intro p
      by_cases hp : p ∈ polarCoord.target
      · rw [indicator_of_mem hp]
        rw [polarCoord_target] at hp
        by_cases hθ : p.2 ∈ Ioo 0 Real.pi
        · have hsub :
              p ∈ Ioi (0 : ℝ) ×ˢ
                Ioo 0 Real.pi :=
            ⟨hp.1, hθ⟩
          rw [indicator_of_mem hsub]
          have hupper :
              polarCoord.symm p ∈
                univ ×ˢ Ioi (0 : ℝ) :=
            (polar_symm_mem_upper p
              (by simpa [polarCoord_target] using hp)).2 hθ
          change ENNReal.ofReal p.1 *
              (univ ×ˢ Ioi (0 : ℝ)).indicator
                (fun z =>
                  ENNReal.ofReal z.2 *
                    f (z.1 ^ 2 + z.2 ^ 2))
                (polarCoord.symm p) = _
          rw [indicator_of_mem hupper]
          simp only [polarCoord_symm_apply]
          have hs :
              0 ≤ Real.sin p.2 :=
            (Real.sin_pos_of_pos_of_lt_pi
              hθ.1 hθ.2).le
          have hsq :
              (p.1 * Real.cos p.2) ^ 2 +
                  (p.1 * Real.sin p.2) ^ 2 =
                p.1 ^ 2 := by
            nlinarith [
              Real.sin_sq_add_cos_sq p.2]
          rw [hsq,
            ENNReal.ofReal_mul hp.1.le,
            show ENNReal.ofReal (p.1 ^ 2) =
                ENNReal.ofReal p.1 *
                  ENNReal.ofReal p.1 by
              rw [pow_two,
                ENNReal.ofReal_mul hp.1.le]]
          ac_rfl
        · have hnsub :
              p ∉ Ioi (0 : ℝ) ×ˢ
                Ioo 0 Real.pi := by
            exact fun h => hθ h.2
          rw [indicator_of_notMem hnsub]
          have hnupper :
              polarCoord.symm p ∉
                univ ×ˢ Ioi (0 : ℝ) := by
            intro h
            exact hθ
              ((polar_symm_mem_upper p
                (by simpa [polarCoord_target] using hp)).1 h)
          change ENNReal.ofReal p.1 *
              (univ ×ˢ Ioi (0 : ℝ)).indicator
                (fun z =>
                  ENNReal.ofReal z.2 *
                    f (z.1 ^ 2 + z.2 ^ 2))
                (polarCoord.symm p) = 0
          rw [indicator_of_notMem hnupper]
          simp
      · rw [indicator_of_notMem hp]
        have hnsub :
            p ∉ Ioi (0 : ℝ) ×ˢ
              Ioo 0 Real.pi := by
          intro h
          apply hp
          rw [polarCoord_target]
          exact ⟨h.1,
            ⟨(neg_lt_zero.mpr Real.pi_pos).trans
                h.2.1,
              h.2.2⟩⟩
        rw [indicator_of_notMem hnsub]
    _ = 2 * ∫⁻ r : ℝ in Ioi 0,
          ENNReal.ofReal (r ^ 2) *
            f (r ^ 2) := by
      rw [Measure.volume_eq_prod,
        setLIntegral_prod]
      · have hinner (r : ℝ) :
            (∫⁻ θ : ℝ in Ioo 0 Real.pi,
                (ENNReal.ofReal (r ^ 2) *
                    f (r ^ 2)) *
                  ENNReal.ofReal
                    (Real.sin θ)) =
              (ENNReal.ofReal (r ^ 2) *
                  f (r ^ 2)) * 2 := by
            change
              (∫⁻ θ : ℝ,
                (ENNReal.ofReal (r ^ 2) *
                    f (r ^ 2)) *
                  (ENNReal.ofReal ∘
                    Real.sin) θ
                ∂volume.restrict
                  (Ioo 0 Real.pi)) = _
            rw [lintegral_const_mul _
              (ENNReal.measurable_ofReal.comp
                Real.measurable_sin)]
            have hsine :
                (∫⁻ θ : ℝ in Ioo 0 Real.pi,
                    (ENNReal.ofReal ∘
                      Real.sin) θ) = 2 := by
              simpa only [Function.comp_apply] using
                lintegral_sin_Ioo
            rw [hsine]
        change
          (∫⁻ r : ℝ in Ioi 0,
            ∫⁻ θ : ℝ in Ioo 0 Real.pi,
              (ENNReal.ofReal (r ^ 2) *
                  f (r ^ 2)) *
                ENNReal.ofReal
                  (Real.sin θ)) = _
        rw [show
          (∫⁻ r : ℝ in Ioi 0,
            ∫⁻ θ : ℝ in Ioo 0 Real.pi,
              (ENNReal.ofReal (r ^ 2) *
                  f (r ^ 2)) *
                ENNReal.ofReal
                  (Real.sin θ)) =
            ∫⁻ r : ℝ in Ioi 0,
              (ENNReal.ofReal (r ^ 2) *
                f (r ^ 2)) * 2 by
              apply lintegral_congr
              intro r
              exact hinner r]
        rw [← lintegral_const_mul]
        · apply lintegral_congr
          intro r
          ac_rfl
        · exact
            (ENNReal.measurable_ofReal.comp
              (measurable_id.pow_const 2)).mul
                (hf.comp
                  (measurable_id.pow_const 2))
      · measurability

private theorem lintegral_radial
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ q : ℝ × ℝ × ℝ,
        f (q.1 ^ 2 + q.2.1 ^ 2 +
          q.2.2 ^ 2)) =
      ENNReal.ofReal (4 * Real.pi) *
        ∫⁻ r : ℝ in Ioi 0,
          ENNReal.ofReal (r ^ 2) *
            f (r ^ 2) := by
  rw [Measure.volume_eq_prod,
    lintegral_prod _ (by measurability)]
  simp_rw [inner_polar_angle f hf]
  rw [lintegral_const_mul'
    (ENNReal.ofReal (2 * Real.pi)) _
    ENNReal.ofReal_ne_top]
  have hprod :
      (∫⁻ x : ℝ,
          ∫⁻ r : ℝ in Ioi 0,
            ENNReal.ofReal r *
              f (x ^ 2 + r ^ 2)) =
        ∫⁻ z : ℝ × ℝ in
            univ ×ˢ Ioi 0,
          ENNReal.ofReal z.2 *
            f (z.1 ^ 2 + z.2 ^ 2) := by
    rw [Measure.volume_eq_prod,
      setLIntegral_prod]
    · simp only [setLIntegral_univ]
    · measurability
  rw [hprod, halfplane_polar f hf]
  rw [← mul_assoc]
  congr 1
  rw [show ENNReal.ofReal (4 * Real.pi) =
      ENNReal.ofReal (2 * Real.pi) * 2 by
    rw [show (4 : ℝ) * Real.pi =
        (2 * Real.pi) * 2 by ring,
      ENNReal.ofReal_mul (by positivity)]
    norm_num]

private def exteriorProfile (s : ℝ) : ℝ≥0∞ :=
  if 1 < s then
    ENNReal.ofReal (1 / s ^ 3)
  else 0

private theorem measurable_exteriorProfile :
    Measurable exteriorProfile := by
  unfold exteriorProfile
  exact Measurable.ite
    (measurableSet_lt measurable_const
      measurable_id)
    (ENNReal.measurable_ofReal.comp
      (measurable_const.div
        (measurable_id.pow_const 3)))
    measurable_const

private theorem exterior_radial_tail :
    (∫⁻ r : ℝ in Ioi 0,
        ENNReal.ofReal (r ^ 2) *
          exteriorProfile (r ^ 2)) =
      ∫⁻ r : ℝ in Ioi 1,
        ENNReal.ofReal (r ^ (-4 : ℝ)) := by
  rw [← lintegral_indicator measurableSet_Ioi,
    ← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro r
  by_cases hr : r ∈ Ioi (1 : ℝ)
  · change 1 < r at hr
    have hr0 : r ∈ Ioi (0 : ℝ) := by
      exact zero_lt_one.trans hr
    rw [indicator_of_mem hr0,
      indicator_of_mem
        (show r ∈ Ioi (1 : ℝ) from hr)]
    have hrsq : 1 < r ^ 2 := by
      nlinarith [sq_nonneg (r - 1)]
    simp only [exteriorProfile, hrsq, if_true]
    rw [← ENNReal.ofReal_mul
      (sq_nonneg r)]
    congr 1
    rw [Real.rpow_neg hr0.le]
    field_simp
    exact Real.rpow_natCast r 4
  · rw [indicator_of_notMem hr]
    by_cases hr0 : r ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hr0]
      have hrsq : ¬ 1 < r ^ 2 := by
        intro h
        apply hr
        change 1 < r
        change 0 < r at hr0
        nlinarith [sq_nonneg (r - 1)]
      simp [exteriorProfile, hrsq]
    · rw [indicator_of_notMem hr0]

private theorem exterior_radial_value :
    (∫⁻ r : ℝ in Ioi 0,
        ENNReal.ofReal (r ^ 2) *
          exteriorProfile (r ^ 2)) =
      ENNReal.ofReal (1 / 3 : ℝ) := by
  rw [exterior_radial_tail,
    ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_Ioi_rpow_of_lt
      (a := (-4 : ℝ)) (by norm_num)
      zero_lt_one]
    norm_num
  · exact integrableOn_Ioi_rpow_of_lt
      (a := (-4 : ℝ)) (by norm_num)
      zero_lt_one
  · filter_upwards [
        ae_restrict_mem measurableSet_Ioi] with r hr
    exact Real.rpow_nonneg
      (zero_le_one.trans hr.le) _

private abbrev Point3 := ℝ × ℝ × ℝ

def exterior : Set (ℝ × ℝ × ℝ) :=
  {z | 1 < z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2}

def integrand (z : ℝ × ℝ × ℝ) : ℝ :=
  1 / (z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2) ^ 3

def integralValue : ℝ :=
  ∫ z in exterior, integrand z

def sphericalIntegral : ℝ :=
  ∫ azimuth in (0 : ℝ)..2 * Real.pi,
    ∫ latitude in (-Real.pi / 2)..Real.pi / 2,
      (∫ radius in Set.Ici (1 : ℝ), 1 / radius ^ 4) *
        Real.cos latitude

private def radiusSq (q : Point3) : ℝ :=
  q.1 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2

private theorem measurable_radiusSq :
    Measurable radiusSq := by
  unfold radiusSq
  fun_prop

private theorem measurableSet_exterior :
    MeasurableSet exterior := by
  exact measurableSet_lt measurable_const
    measurable_radiusSq

private theorem measurable_integrand :
    Measurable integrand := by
  unfold integrand
  fun_prop

private theorem integrand_nonneg
    (q : Point3) :
    0 ≤ integrand q := by
  unfold integrand
  positivity

private theorem exterior_profile_indicator :
    exterior.indicator
        (fun q => ENNReal.ofReal
          (integrand q)) =
      fun q => exteriorProfile
        (radiusSq q) := by
  funext q
  by_cases hq : q ∈ exterior
  · rw [indicator_of_mem hq]
    change 1 < radiusSq q at hq
    have hraw :
        1 < q.1 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2 := by
      simpa [radiusSq] using hq
    simp [exteriorProfile, integrand, radiusSq, hraw]
  · rw [indicator_of_notMem hq]
    have hq' : ¬ 1 < radiusSq q := by
      simpa only [exterior, radiusSq, mem_setOf_eq] using hq
    simp [exteriorProfile, hq']

private theorem exterior_setLIntegral :
    (∫⁻ q : Point3 in exterior,
        ENNReal.ofReal (integrand q)) =
      ENNReal.ofReal
        (4 * Real.pi / 3) := by
  rw [← lintegral_indicator
      measurableSet_exterior,
    exterior_profile_indicator]
  change
    (∫⁻ q : ℝ × ℝ × ℝ,
      exteriorProfile
        (q.1 ^ 2 + q.2.1 ^ 2 +
          q.2.2 ^ 2)) =
      ENNReal.ofReal
        (4 * Real.pi / 3)
  rw [lintegral_radial exteriorProfile
      measurable_exteriorProfile,
    exterior_radial_value,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

private theorem integrableOn_integrand :
    IntegrableOn integrand exterior
      MeasureTheory.volume := by
  constructor
  · exact measurable_integrand.aestronglyMeasurable
  · rw [hasFiniteIntegral_iff_enorm,
      lintegral_enorm_of_nonneg
        integrand_nonneg,
      exterior_setLIntegral]
    exact ENNReal.ofReal_lt_top

private theorem integralValue_value :
    integralValue = 4 * Real.pi / 3 := by
  unfold integralValue
  have hnonneg :
      0 ≤ᵐ[volume.restrict exterior]
        integrand :=
    Filter.Eventually.of_forall
      integrand_nonneg
  have hofReal :
      ENNReal.ofReal
          (∫ q : Point3 in exterior,
            integrand q) =
        ENNReal.ofReal
          (4 * Real.pi / 3) := by
    rw [ofReal_integral_eq_lintegral_ofReal
      integrableOn_integrand hnonneg]
    exact exterior_setLIntegral
  exact (ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg integrand_nonneg)
    (by positivity)).mp hofReal

private theorem radialIntegral_value :
    (∫ radius in Set.Ici (1 : ℝ), 1 / radius ^ 4) =
      (1 / 3 : ℝ) := by
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  have heq : Set.EqOn
      (fun radius : ℝ => 1 / radius ^ 4)
      (fun radius : ℝ => radius ^ (-4 : ℝ))
      (Set.Ioi 1) := by
    intro radius hr
    change 1 / radius ^ (4 : ℕ) = Real.rpow radius (-4)
    have hneg :
        Real.rpow radius (-4) = (Real.rpow radius 4)⁻¹ := by
      change radius ^ (-4 : ℝ) = (radius ^ (4 : ℝ))⁻¹
      exact Real.rpow_neg (zero_le_one.trans hr.le) 4
    have hnat :
        Real.rpow radius 4 = radius ^ (4 : ℕ) := by
      change radius ^ (4 : ℝ) = radius ^ (4 : ℕ)
      exact Real.rpow_natCast radius 4
    rw [hneg, hnat]
    simp only [one_div]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi heq]
  rw [integral_Ioi_rpow_of_lt (a := (-4 : ℝ))
    (by norm_num) zero_lt_one]
  norm_num

private theorem latitudeIntegral_value :
    (∫ latitude in (-Real.pi / 2)..Real.pi / 2,
      (1 / 3 : ℝ) * Real.cos latitude) =
      2 * (1 / 3 : ℝ) := by
  rw [intervalIntegral.integral_const_mul, integral_cos]
  rw [Real.sin_pi_div_two,
    show -Real.pi / 2 = -(Real.pi / 2) by ring,
    Real.sin_neg, Real.sin_pi_div_two]
  norm_num

theorem gap1 :
    integralValue = sphericalIntegral := by
  rw [integralValue_value]
  unfold sphericalIntegral
  rw [radialIntegral_value]
  rw [show
      (fun _ : ℝ =>
        ∫ latitude in (-Real.pi / 2)..Real.pi / 2,
          (1 / 3 : ℝ) * Real.cos latitude) =
        fun _ : ℝ => 2 * (1 / 3 : ℝ) by
    funext azimuth
    exact latitudeIntegral_value]
  rw [intervalIntegral.integral_const]
  simp
  ring

theorem gap2 :
    sphericalIntegral =
      2 * Real.pi * 2 * (1 / 3 : ℝ) := by
  unfold sphericalIntegral
  rw [radialIntegral_value]
  rw [show
      (fun _ : ℝ =>
        ∫ latitude in (-Real.pi / 2)..Real.pi / 2,
          (1 / 3 : ℝ) * Real.cos latitude) =
        fun _ : ℝ => 2 * (1 / 3 : ℝ) by
    funext azimuth
    exact latitudeIntegral_value]
  rw [intervalIntegral.integral_const]
  simp
  ring

theorem gap3 :
    2 * Real.pi * 2 * (1 / 3 : ℝ) =
      4 * Real.pi / 3 := by
  ring

theorem gap4 :
    integralValue = 4 * Real.pi / 3 := by
  rw [gap1, gap2, gap3]

end

end ProofGap.Exercise4197
