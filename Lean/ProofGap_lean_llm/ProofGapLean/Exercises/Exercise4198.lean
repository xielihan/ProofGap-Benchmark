import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4198

noncomputable section

open MeasureTheory Set
open scoped ENNReal Interval

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
                ENNReal.ofReal_mul hp.1.le] ]
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

private def betaFn (x y : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    Real.rpow (1 - t) (x - 1) *
      Real.rpow t (y - 1)

private theorem beta_intervalIntegrable (m q : ℝ)
    (hm : -1 < m) (hq : -1 < q) :
    IntervalIntegrable
      (fun t : ℝ =>
        Real.rpow t m *
          Real.rpow (1 - t) q)
      MeasureTheory.volume 0 1 := by
  have hmLeft :
      IntervalIntegrable
        (fun t : ℝ => Real.rpow t m)
        MeasureTheory.volume 0 (1 / 2 : ℝ) :=
    intervalIntegral.intervalIntegrable_rpow' hm
  have hqContLeft :
      ContinuousOn
        (fun t : ℝ => Real.rpow (1 - t) q)
        [[(0 : ℝ), 1 / 2]] := by
    apply continuousOn_of_forall_continuousAt
    intro t ht
    norm_num [Set.uIcc] at ht
    have hbase : 1 - t ≠ 0 := by
      linarith
    simpa [Function.comp_def] using
      (Real.continuousAt_rpow_const
        (1 - t) q (Or.inl hbase)).comp
        (continuous_const.sub
          continuous_id).continuousAt
  have hleft :
      IntervalIntegrable
        (fun t : ℝ =>
          Real.rpow t m *
            Real.rpow (1 - t) q)
        MeasureTheory.volume 0 (1 / 2 : ℝ) :=
    hmLeft.mul_continuousOn hqContLeft
  have hqRight :
      IntervalIntegrable
        (fun t : ℝ =>
          Real.rpow (1 - t) q)
        MeasureTheory.volume (1 / 2 : ℝ) 1 := by
    have h :=
      (intervalIntegral.intervalIntegrable_rpow'
        (a := (0 : ℝ)) (b := 1 / 2) hq).comp_sub_left 1
    convert h.symm using 1 <;> norm_num
  have hmContRight :
      ContinuousOn (fun t : ℝ => Real.rpow t m)
        [[(1 / 2 : ℝ), 1]] := by
    apply continuousOn_of_forall_continuousAt
    intro t ht
    norm_num [Set.uIcc] at ht
    exact Real.continuousAt_rpow_const t m
      (Or.inl (by linarith))
  have hright :
      IntervalIntegrable
        (fun t : ℝ =>
          Real.rpow t m *
            Real.rpow (1 - t) q)
        MeasureTheory.volume (1 / 2 : ℝ) 1 :=
    hqRight.continuousOn_mul hmContRight
  exact hleft.trans hright

private theorem betaFn_eq_Gamma_mul_div
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    betaFn x y =
      Real.Gamma x * Real.Gamma y /
        Real.Gamma (x + y) := by
  unfold betaFn
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  calc
    (∫ t in (0 : ℝ)..1,
        ((Real.rpow (1 - t) (x - 1) *
          Real.rpow t (y - 1) : ℝ) : ℂ)) =
        Complex.betaIntegral (y : ℂ) (x : ℂ) := by
      rw [Complex.betaIntegral]
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      change
        ((Real.rpow (1 - t) (x - 1) *
          Real.rpow t (y - 1) : ℝ) : ℂ) =
          (t : ℂ) ^ ((y : ℂ) - 1) *
            (1 - (t : ℂ)) ^ ((x : ℂ) - 1)
      have hpow1 :=
        Complex.ofReal_cpow
          (sub_nonneg.mpr ht.2) (x - 1)
      have hpow2 :=
        Complex.ofReal_cpow ht.1 (y - 1)
      rw [Real.rpow_eq_pow, Real.rpow_eq_pow,
        Complex.ofReal_mul, hpow1, hpow2]
      push_cast
      ring
    _ = Complex.Gamma (y : ℂ) *
          Complex.Gamma (x : ℂ) /
          Complex.Gamma ((y : ℂ) + (x : ℂ)) :=
      Complex.betaIntegral_eq_Gamma_mul_div
        (y : ℂ) (x : ℂ)
          (by simpa) (by simpa)
    _ = ((Real.Gamma x * Real.Gamma y /
          Real.Gamma (x + y) : ℝ) : ℂ) := by
      rw [Complex.Gamma_ofReal,
        Complex.Gamma_ofReal,
        ← Complex.ofReal_add,
        Complex.Gamma_ofReal]
      push_cast
      ring

private def betaKernel (p t : ℝ) : ℝ :=
  Real.rpow t (1 / 2 : ℝ) *
    Real.rpow (1 - t) (-p)

private theorem betaKernel_nonneg
    (p t : ℝ) (ht : t ∈ Ioc 0 1) :
    0 ≤ betaKernel p t := by
  unfold betaKernel
  exact mul_nonneg
    (Real.rpow_nonneg ht.1.le _)
    (Real.rpow_nonneg
      (sub_nonneg.mpr ht.2) _)

private theorem betaKernel_integrableOn_iff
    (p : ℝ) :
    IntegrableOn (betaKernel p)
        (Ioc (0 : ℝ) 1) volume ↔
      p < 1 := by
  constructor
  · intro h
    have hrest :
        IntegrableOn (betaKernel p)
          (Ioo (1 / 2 : ℝ) 1) volume :=
      h.mono_set (by
        intro x hx
        exact ⟨(by
          have hhalf :
              (0 : ℝ) < 1 / 2 := by
            norm_num
          exact hhalf.trans hx.1), hx.2.le⟩)
    have hmeas :
        AEStronglyMeasurable
          (fun x : ℝ =>
            Real.rpow (1 - x) (-p))
          (volume.restrict
            (Ioo (1 / 2 : ℝ) 1)) := by
      have hcont :
          ContinuousOn
            (fun x : ℝ =>
              Real.rpow (1 - x) (-p))
            (Ioo (1 / 2 : ℝ) 1) := by
        apply continuousOn_of_forall_continuousAt
        intro x hx
        exact
          (Real.continuousAt_rpow_const
            (1 - x) (-p)
            (Or.inl (sub_pos.mpr hx.2).ne')).comp
            (continuous_const.sub
              continuous_id).continuousAt
      exact hcont.aestronglyMeasurable
        measurableSet_Ioo
    have hpow :
        IntegrableOn
          (fun x : ℝ =>
            Real.rpow (1 - x) (-p))
          (Ioo (1 / 2 : ℝ) 1) volume := by
      apply (hrest.const_mul 2).mono'
        hmeas
      filter_upwards [
        ae_restrict_mem measurableSet_Ioo] with x hx
      have hxIoc : x ∈ Ioc (0 : ℝ) 1 :=
        ⟨(by
          have hhalf :
              (0 : ℝ) < 1 / 2 := by
            norm_num
          exact hhalf.trans hx.1), hx.2.le⟩
      have hg :
          0 ≤ Real.rpow (1 - x) (-p) :=
        Real.rpow_nonneg
          (sub_nonneg.mpr hx.2.le) _
      have hk : 0 ≤ betaKernel p x :=
        betaKernel_nonneg p x hxIoc
      have hsqrt_sq :
          Real.sqrt x ^ 2 = x :=
        Real.sq_sqrt hxIoc.1.le
      have hsqrt_nonneg :
          0 ≤ Real.sqrt x :=
        Real.sqrt_nonneg x
      have hsqrt_le_one :
          Real.sqrt x ≤ 1 :=
        Real.sqrt_le_one.mpr hx.2.le
      have hfac :
          1 ≤ 2 * Real.sqrt x := by
        have hxle : x ≤ Real.sqrt x := by
          nlinarith
        rw [show (1 : ℝ) = 2 * (1 / 2 : ℝ) by
          norm_num]
        exact mul_le_mul_of_nonneg_left
          (le_trans hx.1.le hxle) (by norm_num)
      unfold betaKernel
      rw [Real.norm_of_nonneg hg]
      have hrpow :
          Real.rpow x (1 / 2 : ℝ) =
            Real.sqrt x :=
        (Real.sqrt_eq_rpow x).symm
      rw [hrpow]
      calc
        Real.rpow (1 - x) (-p) =
            1 * Real.rpow (1 - x) (-p) := by
              ring
        _ ≤ (2 * Real.sqrt x) *
              Real.rpow (1 - x) (-p) :=
            mul_le_mul_of_nonneg_right hfac hg
        _ = 2 * (Real.sqrt x *
              Real.rpow (1 - x) (-p)) := by
            ring
    have hi :
        IntervalIntegrable
          (fun x : ℝ =>
            Real.rpow (1 - x) (-p))
          volume (1 / 2 : ℝ) 1 :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le
        (by norm_num)).2 hpow
    have hcomp := hi.comp_sub_left 1
    have huInterval :
        IntervalIntegrable
          (fun x : ℝ => Real.rpow x (-p))
          volume 0 (1 / 2 : ℝ) := by
      convert hcomp.symm using 1 <;>
        norm_num
    have hu :
        IntegrableOn
          (fun x : ℝ => Real.rpow x (-p))
          (Ioo 0 (1 / 2 : ℝ)) volume :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le
        (by norm_num)).1 huInterval
    have hexp :
        -1 < -p :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff
        (by norm_num : (0 : ℝ) < 1 / 2)).1 hu
    linarith
  · intro hp
    have hinterval :=
      beta_intervalIntegrable
        (1 / 2 : ℝ) (-p)
        (by norm_num) (by linarith)
    exact
      (intervalIntegrable_iff_integrableOn_Ioc_of_le
        zero_le_one).1
        (by simpa only [betaKernel] using hinterval)

private theorem betaKernel_integral
    (p : ℝ) (hp : p < 1) :
    (∫ t : ℝ in Ioc 0 1,
        betaKernel p t) =
      Real.Gamma (3 / 2 : ℝ) *
          Real.Gamma (1 - p) /
        Real.Gamma ((3 / 2 : ℝ) + (1 - p)) := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  have hbeta :
      (∫ t : ℝ in (0 : ℝ)..1,
          betaKernel p t) =
        betaFn (1 - p) (3 / 2 : ℝ) := by
    unfold betaFn betaKernel
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  rw [hbeta,
    betaFn_eq_Gamma_mul_div
      (1 - p) (3 / 2 : ℝ)
      (by linarith) (by norm_num)]
  ring

private def ballProfile
    (p s : ℝ) : ℝ≥0∞ :=
  if s ≤ 1 then
    ENNReal.ofReal
      (Real.rpow (1 - s) (-p))
  else 0

private theorem measurable_ballProfile
    (p : ℝ) :
    Measurable (ballProfile p) := by
  unfold ballProfile
  exact Measurable.ite
    (measurableSet_le measurable_id
      measurable_const)
    (by measurability)
    measurable_const

private theorem square_image_Ioc :
    (fun r : ℝ => r ^ 2) ''
        Ioc (0 : ℝ) 1 =
      Ioc (0 : ℝ) 1 := by
  ext t
  constructor
  · rintro ⟨r, hr, rfl⟩
    constructor
    · exact sq_pos_of_pos hr.1
    · exact (sq_le_one_iff₀ hr.1.le).2 hr.2
  · intro ht
    refine ⟨Real.sqrt t, ?_, ?_⟩
    · exact ⟨Real.sqrt_pos.2 ht.1,
        Real.sqrt_le_one.mpr ht.2⟩
    · exact Real.sq_sqrt ht.1.le

private theorem ball_radial_support
    (p : ℝ) :
    (∫⁻ r : ℝ in Ioi 0,
        ENNReal.ofReal (r ^ 2) *
          ballProfile p (r ^ 2)) =
      ∫⁻ r : ℝ in Ioc 0 1,
        ENNReal.ofReal (r ^ 2) *
          ENNReal.ofReal
            (Real.rpow (1 - r ^ 2) (-p)) := by
  rw [← lintegral_indicator measurableSet_Ioi,
    ← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr
  intro r
  by_cases hr : r ∈ Ioc (0 : ℝ) 1
  · have hr0 : r ∈ Ioi (0 : ℝ) := hr.1
    rw [indicator_of_mem hr,
      indicator_of_mem hr0]
    have hrsq : r ^ 2 ≤ 1 := by
      exact (sq_le_one_iff₀ hr.1.le).2 hr.2
    simp [ballProfile, hrsq]
  · rw [indicator_of_notMem hr]
    by_cases hr0 : r ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hr0]
      have hr1 : 1 < r := by
        have hnot : ¬ r ≤ 1 := by
          intro hle
          exact hr ⟨hr0, hle⟩
        exact lt_of_not_ge hnot
      have hrsq : ¬ r ^ 2 ≤ 1 := by
        nlinarith [sq_nonneg (r - 1)]
      simp [ballProfile, hrsq]
    · rw [indicator_of_notMem hr0]

private theorem beta_lintegral_eq_two_mul_radial
    (p : ℝ) :
    (∫⁻ t : ℝ in Ioc 0 1,
        ENNReal.ofReal (betaKernel p t)) =
      2 * ∫⁻ r : ℝ in Ioi 0,
        ENNReal.ofReal (r ^ 2) *
          ballProfile p (r ^ 2) := by
  rw [ball_radial_support]
  calc
    (∫⁻ t : ℝ in Ioc 0 1,
        ENNReal.ofReal (betaKernel p t)) =
        ∫⁻ t : ℝ in
            (fun r : ℝ => r ^ 2) ''
              Ioc (0 : ℝ) 1,
          ENNReal.ofReal (betaKernel p t) := by
      rw [square_image_Ioc]
    _ = ∫⁻ r : ℝ in Ioc (0 : ℝ) 1,
          ENNReal.ofReal (2 * r) *
            ENNReal.ofReal
              (betaKernel p (r ^ 2)) := by
      exact
        lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn
          measurableSet_Ioc
          (fun r hr => by
            convert
              ((hasDerivAt_id r).pow 2).hasDerivWithinAt
                using 1
            all_goals simp [id])
          (by
            intro a ha b hb hab
            nlinarith [
              mul_nonneg
                (sub_nonneg.mpr hab)
                (add_nonneg ha.1.le hb.1.le)])
          (fun t : ℝ =>
            ENNReal.ofReal (betaKernel p t))
    _ = 2 * ∫⁻ r : ℝ in Ioc (0 : ℝ) 1,
          ENNReal.ofReal (r ^ 2) *
            ENNReal.ofReal
              (Real.rpow (1 - r ^ 2) (-p)) := by
      rw [← lintegral_const_mul]
      · apply setLIntegral_congr_fun
          measurableSet_Ioc
        intro r hr
        have hr0 : 0 ≤ r := hr.1.le
        have hrsq0 : 0 ≤ r ^ 2 :=
          sq_nonneg r
        have hsub :
            0 ≤ 1 - r ^ 2 := by
          exact sub_nonneg.mpr
            ((sq_le_one_iff₀ hr0).2 hr.2)
        have hrpow :
            Real.rpow (r ^ 2) (1 / 2 : ℝ) =
              r := by
          calc
            Real.rpow (r ^ 2) (1 / 2 : ℝ) =
                Real.sqrt (r ^ 2) :=
              (Real.sqrt_eq_rpow (r ^ 2)).symm
            _ = |r| := Real.sqrt_sq_eq_abs r
            _ = r := abs_of_nonneg hr0
        have hsqOfReal :
            ENNReal.ofReal (r ^ 2) =
              ENNReal.ofReal r *
                ENNReal.ofReal r := by
          rw [pow_two,
            ENNReal.ofReal_mul hr0]
        unfold betaKernel
        simp only
        rw [hrpow,
          ENNReal.ofReal_mul hr0,
          ENNReal.ofReal_mul (by norm_num :
            (0 : ℝ) ≤ 2),
          hsqOfReal]
        norm_num
        ac_rfl
      · measurability

private theorem beta_lintegral_ne_top_iff
    (p : ℝ) :
    (∫⁻ t : ℝ in Ioc 0 1,
        ENNReal.ofReal (betaKernel p t)) ≠ ∞ ↔
      p < 1 := by
  have hmeas :
      AEStronglyMeasurable
        (betaKernel p)
        (volume.restrict
          (Ioc (0 : ℝ) 1)) := by
    rw [← Measure.restrict_congr_set
      (Ioo_ae_eq_Ioc :
        Ioo (0 : ℝ) 1 =ᵐ[volume]
          Ioc (0 : ℝ) 1)]
    have hcont :
        ContinuousOn (betaKernel p)
          (Ioo (0 : ℝ) 1) := by
      apply continuousOn_of_forall_continuousAt
      intro t ht
      unfold betaKernel
      exact
        (Real.continuousAt_rpow_const
          t (1 / 2 : ℝ)
          (Or.inl ht.1.ne')).mul
        ((Real.continuousAt_rpow_const
          (1 - t) (-p)
          (Or.inl
            (sub_pos.mpr ht.2).ne')).comp
          (continuous_const.sub
            continuous_id).continuousAt)
    exact hcont.aestronglyMeasurable
      measurableSet_Ioo
  have hnonneg :
      0 ≤ᵐ[volume.restrict
        (Ioc (0 : ℝ) 1)]
        betaKernel p := by
    filter_upwards [
      ae_restrict_mem measurableSet_Ioc] with t ht
    exact betaKernel_nonneg p t ht
  rw [lintegral_ofReal_ne_top_iff_integrable
    hmeas hnonneg]
  exact betaKernel_integrableOn_iff p

private theorem beta_lintegral_value
    (p : ℝ) (hp : p < 1) :
    (∫⁻ t : ℝ in Ioc 0 1,
        ENNReal.ofReal (betaKernel p t)) =
      ENNReal.ofReal
        (Real.Gamma (3 / 2 : ℝ) *
            Real.Gamma (1 - p) /
          Real.Gamma
            ((3 / 2 : ℝ) + (1 - p))) := by
  have hint :
      IntegrableOn (betaKernel p)
        (Ioc (0 : ℝ) 1) volume :=
    (betaKernel_integrableOn_iff p).2 hp
  have hnonneg :
      0 ≤ᵐ[volume.restrict
        (Ioc (0 : ℝ) 1)]
        betaKernel p := by
    filter_upwards [
      ae_restrict_mem measurableSet_Ioc] with t ht
    exact betaKernel_nonneg p t ht
  rw [← ofReal_integral_eq_lintegral_ofReal
      hint hnonneg,
    betaKernel_integral p hp]

private theorem ball_radial_ne_top_iff
    (p : ℝ) :
    (∫⁻ r : ℝ in Ioi 0,
      ENNReal.ofReal (r ^ 2) *
          ballProfile p (r ^ 2)) ≠ ∞ ↔
      p < 1 := by
  constructor
  · intro hradial
    apply (beta_lintegral_ne_top_iff p).1
    rw [beta_lintegral_eq_two_mul_radial p]
    exact ENNReal.mul_ne_top
      (by norm_num) hradial
  · intro hp htop
    have hfinite :=
      (beta_lintegral_ne_top_iff p).2 hp
    rw [beta_lintegral_eq_two_mul_radial p,
      htop] at hfinite
    norm_num at hfinite

private theorem ball_radial_value
    (p : ℝ) (hp : p < 1) :
    (∫⁻ r : ℝ in Ioi 0,
        ENNReal.ofReal (r ^ 2) *
          ballProfile p (r ^ 2)) =
      ENNReal.ofReal
        ((1 / 2 : ℝ) *
          (Real.Gamma (3 / 2 : ℝ) *
              Real.Gamma (1 - p) /
            Real.Gamma
              ((3 / 2 : ℝ) + (1 - p)))) := by
  let R : ℝ≥0∞ :=
    ∫⁻ r : ℝ in Ioi 0,
      ENNReal.ofReal (r ^ 2) *
        ballProfile p (r ^ 2)
  let B : ℝ :=
    Real.Gamma (3 / 2 : ℝ) *
        Real.Gamma (1 - p) /
      Real.Gamma
        ((3 / 2 : ℝ) + (1 - p))
  have htwo :
      (2 : ℝ≥0∞) * R =
        ENNReal.ofReal B := by
    dsimp only [R, B]
    rw [← beta_lintegral_eq_two_mul_radial p,
      beta_lintegral_value p hp]
  change R =
    ENNReal.ofReal ((1 / 2 : ℝ) * B)
  calc
    R = (2 : ℝ≥0∞)⁻¹ * (2 * R) :=
      (ENNReal.inv_mul_cancel_left
        (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).symm
    _ = (2 : ℝ≥0∞)⁻¹ *
          ENNReal.ofReal B := by
      rw [htwo]
    _ = ENNReal.ofReal
          ((1 / 2 : ℝ) * B) := by
      rw [ENNReal.ofReal_mul
        (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      have hinv :
          (2 : ℝ≥0∞)⁻¹ =
            ENNReal.ofReal (1 / 2 : ℝ) := by
        rw [show (1 / 2 : ℝ) =
            (2 : ℝ)⁻¹ by norm_num,
          ENNReal.ofReal_inv_of_pos
            (by norm_num : (0 : ℝ) < 2)]
        norm_num
      rw [hinv]

private abbrev Point3 := ℝ × ℝ × ℝ

private def closedSquaredRadius (q : Point3) : ℝ :=
  q.1 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2

private def closedBall : Set Point3 :=
  {q | closedSquaredRadius q ≤ 1}

private def closedIntegrand (p : ℝ) (q : Point3) : ℝ :=
  1 / Real.rpow
    (1 - closedSquaredRadius q) p

private def closedBetaReal (u v : ℝ) : ℝ :=
  Real.Gamma u * Real.Gamma v / Real.Gamma (u + v)

private def closedIntegral (p : ℝ) : ℝ :=
  ∫ q in closedBall, closedIntegrand p q
    ∂MeasureTheory.volume

private theorem measurable_squaredRadius :
    Measurable closedSquaredRadius := by
  unfold closedSquaredRadius
  fun_prop

private theorem measurableSet_ball :
    MeasurableSet closedBall := by
  exact measurableSet_le
    measurable_squaredRadius measurable_const

private theorem integrand_nonneg
    (p : ℝ) (q : Point3)
    (hq : q ∈ closedBall) :
    0 ≤ closedIntegrand p q := by
  have hbase :
      0 ≤ 1 - closedSquaredRadius q :=
    sub_nonneg.mpr hq
  unfold closedIntegrand
  exact one_div_nonneg.mpr
    (Real.rpow_nonneg hbase p)

private theorem integrand_eq_profile_toReal
    (p : ℝ) (q : Point3)
    (hq : q ∈ closedBall) :
    closedIntegrand p q =
      (ballProfile p
        (closedSquaredRadius q)).toReal := by
  have hs :
      closedSquaredRadius q ≤ 1 := hq
  have hbase :
      0 ≤ 1 - closedSquaredRadius q :=
    sub_nonneg.mpr hs
  unfold ballProfile
  rw [if_pos hs]
  unfold closedIntegrand
  calc
    1 / Real.rpow
          (1 - closedSquaredRadius q) p =
        (Real.rpow
          (1 - closedSquaredRadius q) p)⁻¹ := by
      rw [one_div]
    _ = Real.rpow
          (1 - closedSquaredRadius q) (-p) :=
      (Real.rpow_neg hbase p).symm
    _ = (ENNReal.ofReal
          (Real.rpow
            (1 - closedSquaredRadius q)
              (-p))).toReal :=
      (ENNReal.toReal_ofReal
        (Real.rpow_nonneg hbase (-p))).symm

private theorem integrand_aestronglyMeasurable
    (p : ℝ) :
    AEStronglyMeasurable
      (closedIntegrand p)
      (volume.restrict closedBall) := by
  have hprofile :
      AEStronglyMeasurable
        (fun q : Point3 =>
          (ballProfile p
            (closedSquaredRadius q)).toReal)
        (volume.restrict closedBall) :=
    (((measurable_ballProfile p).comp
      measurable_squaredRadius).ennreal_toReal
        ).aestronglyMeasurable
  apply hprofile.congr
  filter_upwards [
    ae_restrict_mem measurableSet_ball] with q hq
  exact (integrand_eq_profile_toReal
    p q hq).symm

private theorem ball_profile_indicator
    (p : ℝ) :
    closedBall.indicator
        (fun q : Point3 =>
          ENNReal.ofReal (closedIntegrand p q)) =
      fun q =>
        ballProfile p (closedSquaredRadius q) := by
  funext q
  by_cases hq : q ∈ closedBall
  · rw [indicator_of_mem hq]
    have hs :
        closedSquaredRadius q ≤ 1 := hq
    have hbase :
        0 ≤ 1 - closedSquaredRadius q :=
      sub_nonneg.mpr hs
    have hint :
        closedIntegrand p q =
          Real.rpow
            (1 - closedSquaredRadius q) (-p) := by
      unfold closedIntegrand
      calc
        1 / Real.rpow
              (1 - closedSquaredRadius q) p =
            (Real.rpow
              (1 - closedSquaredRadius q) p)⁻¹ := by
          rw [one_div]
        _ = Real.rpow
              (1 - closedSquaredRadius q) (-p) :=
          (Real.rpow_neg hbase p).symm
    rw [hint]
    simp [ballProfile, hs]
  · rw [indicator_of_notMem hq]
    have hs :
        ¬ closedSquaredRadius q ≤ 1 := by
      simpa only [closedBall, mem_setOf_eq]
        using hq
    simp [ballProfile, hs]

private theorem ball_setLIntegral
    (p : ℝ) :
    (∫⁻ q : Point3 in closedBall,
        ENNReal.ofReal (closedIntegrand p q)) =
      ENNReal.ofReal (4 * Real.pi) *
        ∫⁻ r : ℝ in Ioi 0,
          ENNReal.ofReal (r ^ 2) *
            ballProfile p (r ^ 2) := by
  rw [← lintegral_indicator
      measurableSet_ball,
    ball_profile_indicator p]
  change
    (∫⁻ q : ℝ × ℝ × ℝ,
      ballProfile p
        (q.1 ^ 2 + q.2.1 ^ 2 +
          q.2.2 ^ 2)) = _
  exact lintegral_radial
    (ballProfile p)
    (measurable_ballProfile p)

private theorem integrand_nonneg_ae
    (p : ℝ) :
    0 ≤ᵐ[volume.restrict closedBall]
      closedIntegrand p := by
  filter_upwards [
    ae_restrict_mem measurableSet_ball] with q hq
  exact integrand_nonneg p q hq

private theorem integrableOn_integrand_iff
    (p : ℝ) :
    IntegrableOn (closedIntegrand p) closedBall
        MeasureTheory.volume ↔
      p < 1 := by
  change
    (AEStronglyMeasurable
        (closedIntegrand p)
        (volume.restrict closedBall) ∧
      HasFiniteIntegral
        (closedIntegrand p)
        (volume.restrict closedBall)) ↔
      p < 1
  rw [and_iff_right
      (integrand_aestronglyMeasurable p),
    hasFiniteIntegral_iff_enorm,
    lintegral_enorm_of_ae_nonneg
      (integrand_nonneg_ae p),
    ball_setLIntegral p,
    ENNReal.mul_lt_top_iff]
  have hcoeffTop :
      ENNReal.ofReal (4 * Real.pi) < ∞ :=
    (ENNReal.ofReal_ne_top).lt_top
  have hcoeffZero :
      ENNReal.ofReal (4 * Real.pi) ≠ 0 := by
    exact ne_of_gt
      (ENNReal.ofReal_pos.2 (by positivity))
  simp only [hcoeffTop, hcoeffZero,
    true_and, false_or]
  rw [or_iff_left_of_imp (fun h => by
    rw [h]
    exact ENNReal.zero_lt_top)]
  rw [lt_top_iff_ne_top]
  exact ball_radial_ne_top_iff p

private theorem ball_setLIntegral_value
    (p : ℝ) (hp : p < 1) :
    (∫⁻ q : Point3 in closedBall,
        ENNReal.ofReal (closedIntegrand p q)) =
      ENNReal.ofReal
        (2 * Real.pi *
          closedBetaReal (3 / 2 : ℝ) (1 - p)) := by
  rw [ball_setLIntegral p,
    ball_radial_value p hp,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  unfold closedBetaReal
  ring

/-! Exercise 4198. -/

private theorem closedProblem (p : ℝ) :
    (IntegrableOn (closedIntegrand p) closedBall MeasureTheory.volume ↔ p < 1) ∧
    (p < 1 → closedIntegral p = 2 * Real.pi * closedBetaReal (3 / 2) (1 - p)) := by
  refine ⟨integrableOn_integrand_iff p, ?_⟩
  intro hp
  have hint :
      IntegrableOn (closedIntegrand p) closedBall
        MeasureTheory.volume :=
    (integrableOn_integrand_iff p).2 hp
  have hnonneg :=
    integrand_nonneg_ae p
  have hofReal :
      ENNReal.ofReal (closedIntegral p) =
        ENNReal.ofReal
          (2 * Real.pi *
            closedBetaReal (3 / 2 : ℝ)
              (1 - p)) := by
    unfold closedIntegral
    rw [ofReal_integral_eq_lintegral_ofReal
      hint hnonneg]
    exact ball_setLIntegral_value p hp
  have hintegral :
      0 ≤ closedIntegral p := by
    unfold closedIntegral
    exact integral_nonneg_of_ae hnonneg
  have hgamma1 :
      0 < Real.Gamma (3 / 2 : ℝ) :=
    Real.Gamma_pos_of_pos (by norm_num)
  have hgamma2 :
      0 < Real.Gamma (1 - p) :=
    Real.Gamma_pos_of_pos (by linarith)
  have hgammaSum :
      0 <
        Real.Gamma
          ((3 / 2 : ℝ) + (1 - p)) :=
    Real.Gamma_pos_of_pos (by linarith)
  have hbeta :
      0 < closedBetaReal (3 / 2 : ℝ)
          (1 - p) := by
    unfold closedBetaReal
    exact div_pos
      (mul_pos hgamma1 hgamma2)
      hgammaSum
  exact (ENNReal.ofReal_eq_ofReal_iff
    hintegral (by positivity)).mp hofReal

def unitBall : Set (ℝ × ℝ × ℝ) :=
  {z | z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 < 1}

def boundaryDistance (z : ℝ × ℝ × ℝ) : ℝ :=
  1 - z.1 ^ 2 - z.2.1 ^ 2 - z.2.2 ^ 2

def weight (p : ℝ) (z : ℝ × ℝ × ℝ) : ℝ :=
  Real.rpow (boundaryDistance z) (-p)

def volumeIntegral (p : ℝ) : ℝ :=
  ∫ z in unitBall, weight p z

def radialIntegral (p : ℝ) : ℝ :=
  ∫ r in Set.Ioc (0 : ℝ) 1,
    r ^ 2 * Real.rpow (1 - r ^ 2) (-p)

def sphericalIntegral (p : ℝ) : ℝ :=
  ∫ azimuth in (0 : ℝ)..2 * Real.pi,
    ∫ latitude in (-Real.pi / 2)..Real.pi / 2,
      ∫ r in (0 : ℝ)..1,
        Real.rpow (1 - r ^ 2) (-p) * r ^ 2 * Real.cos latitude

def betaIntegral (p : ℝ) : ℝ :=
  ∫ t in Set.Ioc (0 : ℝ) 1,
    Real.rpow t (1 / 2 : ℝ) * Real.rpow (1 - t) (-p)

def betaValue (p : ℝ) : ℝ :=
  Real.Gamma (3 / 2 : ℝ) * Real.Gamma (1 - p) /
    Real.Gamma (5 / 2 - p)

private def sphereBoundary : Set (ℝ × ℝ × ℝ) :=
  {z | z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1}

private theorem measurableSet_sphereBoundary :
    MeasurableSet sphereBoundary := by
  unfold sphereBoundary
  measurability

private theorem vertical_fiber_finite (x y : ℝ) :
    {z : ℝ | x ^ 2 + y ^ 2 + z ^ 2 = 1}.Finite := by
  by_cases hc : 0 ≤ 1 - x ^ 2 - y ^ 2
  · let s := Real.sqrt (1 - x ^ 2 - y ^ 2)
    have hs : s ^ 2 = 1 - x ^ 2 - y ^ 2 := by
      dsimp [s]
      exact Real.sq_sqrt hc
    refine ((Set.finite_singleton (-s)).insert s).subset ?_
    intro z hz
    change x ^ 2 + y ^ 2 + z ^ 2 = 1 at hz
    have hzsq : z ^ 2 = s ^ 2 := by
      nlinarith
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hzsq) with h | h
    · simp [h]
    · simp [h]
  · have hempty :
        {z : ℝ | x ^ 2 + y ^ 2 + z ^ 2 = 1} = ∅ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
      constructor
      · intro hz
        have : 0 ≤ 1 - x ^ 2 - y ^ 2 := by
          nlinarith [sq_nonneg z]
        exact (hc this).elim
      · intro h
        exact h.elim
    rw [hempty]
    exact Set.finite_empty

private theorem sphereBoundary_measure_zero :
    volume sphereBoundary = 0 := by
  rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), Measure.volume_eq_prod ℝ ℝ]
  apply Measure.measure_prod_null_of_ae_null measurableSet_sphereBoundary
  refine Filter.Eventually.of_forall fun x => ?_
  apply Measure.measure_prod_null_of_ae_null
    (measurableSet_sphereBoundary.preimage measurable_prodMk_left)
  refine Filter.Eventually.of_forall fun y => ?_
  have hfinite :
      (Prod.mk y ⁻¹' (Prod.mk x ⁻¹' sphereBoundary)).Finite := by
    simpa [sphereBoundary] using vertical_fiber_finite x y
  exact hfinite.measure_zero volume

private theorem closedBall_ae_eq_unitBall :
    closedBall =ᵐ[volume] unitBall := by
  rw [MeasureTheory.ae_eq_set]
  constructor
  · apply measure_mono_null (t := sphereBoundary) _ sphereBoundary_measure_zero
    intro z hz
    rcases hz with ⟨hclosed, hopen⟩
    change
      z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 ≤ 1 at hclosed
    change ¬z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 < 1 at hopen
    change z ∈ sphereBoundary
    change z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1
    linarith
  · have hsubset : unitBall ⊆ closedBall := by
      intro z hz
      change
        z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 < 1 at hz
      change
        z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 ≤ 1
      exact hz.le
    have hempty : unitBall \ closedBall = ∅ :=
      Set.diff_eq_empty.mpr hsubset
    rw [hempty]
    exact measure_empty

private theorem restricted_ball_eq :
    volume.restrict unitBall = volume.restrict closedBall := by
  exact Measure.restrict_congr_set closedBall_ae_eq_unitBall.symm

private theorem weight_eq_closedIntegrand
    (p : ℝ) :
    Set.EqOn (weight p) (closedIntegrand p) closedBall := by
  intro z hz
  have hbase :
      0 ≤ 1 - (z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2) :=
    sub_nonneg.mpr hz
  unfold weight boundaryDistance closedIntegrand closedSquaredRadius
  have hdist :
      1 - z.1 ^ 2 - z.2.1 ^ 2 - z.2.2 ^ 2 =
        1 - (z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2) := by
    ring
  rw [hdist]
  have hneg :
      Real.rpow
          (1 - (z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2)) (-p) =
        (Real.rpow
          (1 - (z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2)) p)⁻¹ := by
    change
      (1 - (z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2)) ^ (-p) =
        ((1 - (z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2)) ^ p)⁻¹
    exact Real.rpow_neg hbase p
  rw [hneg]
  simp only [one_div]

private theorem volumeIntegral_eq_closedIntegral (p : ℝ) :
    volumeIntegral p = closedIntegral p := by
  unfold volumeIntegral closedIntegral
  change
    (∫ z, weight p z ∂volume.restrict unitBall) =
      ∫ z, closedIntegrand p z ∂volume.restrict closedBall
  rw [restricted_ball_eq]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  exact weight_eq_closedIntegrand p hz

private theorem weight_integrable_iff (p : ℝ) :
    IntegrableOn (weight p) unitBall ↔ p < 1 := by
  change Integrable (weight p) (volume.restrict unitBall) ↔ p < 1
  rw [restricted_ball_eq]
  rw [← integrableOn_integrand_iff p]
  change Integrable (weight p) (volume.restrict closedBall) ↔
    Integrable (closedIntegrand p) (volume.restrict closedBall)
  constructor
  · intro h
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact weight_eq_closedIntegrand p hz
  · intro h
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact (weight_eq_closedIntegrand p hz).symm

private theorem volumeIntegral_value (p : ℝ) (hp : p < 1) :
    volumeIntegral p = 2 * Real.pi * betaValue p := by
  rw [volumeIntegral_eq_closedIntegral]
  have h := (closedProblem p).2 hp
  rw [h]
  unfold betaValue closedBetaReal
  congr 2
  ring

private theorem betaIntegral_value (p : ℝ) (hp : p < 1) :
    betaIntegral p = betaValue p := by
  unfold betaIntegral betaValue
  rw [show
      (fun t : ℝ =>
        Real.rpow t (1 / 2 : ℝ) *
          Real.rpow (1 - t) (-p)) =
        betaKernel p by rfl]
  rw [betaKernel_integral p hp]
  congr 2
  ring

private def radialKernel (p r : ℝ) : ℝ :=
  r ^ 2 * Real.rpow (1 - r ^ 2) (-p)

private theorem radialKernel_nonneg_ae (p : ℝ) :
    0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] radialKernel p := by
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  unfold radialKernel
  exact mul_nonneg (sq_nonneg r)
    (Real.rpow_nonneg (sub_nonneg.mpr
      ((sq_le_one_iff₀ hr.1.le).2 hr.2)) _)

private theorem radialKernel_setLIntegral_value
    (p : ℝ) (hp : p < 1) :
    (∫⁻ r : ℝ in Ioc 0 1,
      ENNReal.ofReal (radialKernel p r)) =
      ENNReal.ofReal ((1 / 2 : ℝ) * betaValue p) := by
  have h := ball_radial_value p hp
  rw [ball_radial_support] at h
  calc
    (∫⁻ r : ℝ in Ioc 0 1,
      ENNReal.ofReal (radialKernel p r)) =
        ∫⁻ r : ℝ in Ioc 0 1,
          ENNReal.ofReal (r ^ 2) *
            ENNReal.ofReal
              (Real.rpow (1 - r ^ 2) (-p)) := by
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro r hr
      unfold radialKernel
      change
        ENNReal.ofReal
            (r ^ 2 * Real.rpow (1 - r ^ 2) (-p)) =
          ENNReal.ofReal (r ^ 2) *
            ENNReal.ofReal (Real.rpow (1 - r ^ 2) (-p))
      rw [ENNReal.ofReal_mul (sq_nonneg r)]
    _ = ENNReal.ofReal
        ((1 / 2 : ℝ) *
          (Real.Gamma (3 / 2 : ℝ) *
              Real.Gamma (1 - p) /
            Real.Gamma ((3 / 2 : ℝ) + (1 - p)))) := h
    _ = ENNReal.ofReal ((1 / 2 : ℝ) * betaValue p) := by
      congr 2
      unfold betaValue
      congr 2
      ring

private theorem radialKernel_integrable
    (p : ℝ) (hp : p < 1) :
    IntegrableOn (radialKernel p) (Ioc (0 : ℝ) 1) := by
  constructor
  · have hm : Measurable (radialKernel p) := by
      unfold radialKernel
      measurability
    exact hm.aestronglyMeasurable
  · rw [hasFiniteIntegral_iff_enorm,
      lintegral_enorm_of_ae_nonneg (radialKernel_nonneg_ae p),
      radialKernel_setLIntegral_value p hp]
    exact ENNReal.ofReal_lt_top

private theorem radialIntegral_value
    (p : ℝ) (hp : p < 1) :
    radialIntegral p = (1 / 2 : ℝ) * betaValue p := by
  unfold radialIntegral
  change
    (∫ r in Ioc (0 : ℝ) 1, radialKernel p r) =
      (1 / 2 : ℝ) * betaValue p
  have hnonneg := radialKernel_nonneg_ae p
  have hof :
      ENNReal.ofReal
          (∫ r in Ioc (0 : ℝ) 1, radialKernel p r) =
        ENNReal.ofReal ((1 / 2 : ℝ) * betaValue p) := by
    rw [ofReal_integral_eq_lintegral_ofReal
      (radialKernel_integrable p hp) hnonneg]
    exact radialKernel_setLIntegral_value p hp
  have hleft :
      0 ≤ ∫ r in Ioc (0 : ℝ) 1, radialKernel p r :=
    integral_nonneg_of_ae hnonneg
  have hright : 0 ≤ (1 / 2 : ℝ) * betaValue p := by
    unfold betaValue
    have h1 : 0 < Real.Gamma (3 / 2 : ℝ) :=
      Real.Gamma_pos_of_pos (by norm_num)
    have h2 : 0 < Real.Gamma (1 - p) :=
      Real.Gamma_pos_of_pos (by linarith)
    have h3 : 0 < Real.Gamma (5 / 2 - p) :=
      Real.Gamma_pos_of_pos (by linarith)
    exact mul_nonneg (by norm_num)
      (div_nonneg (mul_nonneg h1.le h2.le) h3.le)
  exact (ENNReal.ofReal_eq_ofReal_iff hleft hright).mp hof

private theorem spherical_factor
    (p : ℝ) :
    sphericalIntegral p = 4 * Real.pi * radialIntegral p := by
  unfold sphericalIntegral
  have hradial :
      (∫ r in (0 : ℝ)..1,
        Real.rpow (1 - r ^ 2) (-p) * r ^ 2) =
        radialIntegral p := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    unfold radialIntegral
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    ring
  have hinner (latitude : ℝ) :
      (∫ r in (0 : ℝ)..1,
          Real.rpow (1 - r ^ 2) (-p) * r ^ 2 *
            Real.cos latitude) =
        radialIntegral p * Real.cos latitude := by
    calc
      (∫ r in (0 : ℝ)..1,
          Real.rpow (1 - r ^ 2) (-p) * r ^ 2 *
            Real.cos latitude) =
          (∫ r in (0 : ℝ)..1,
            Real.rpow (1 - r ^ 2) (-p) * r ^ 2) *
              Real.cos latitude :=
        intervalIntegral.integral_mul_const _ _
      _ = radialIntegral p * Real.cos latitude := by
        rw [hradial]
  have hlatitude :
      (∫ latitude in (-Real.pi / 2)..Real.pi / 2,
          radialIntegral p * Real.cos latitude) =
        2 * radialIntegral p := by
    rw [intervalIntegral.integral_const_mul, integral_cos]
    rw [Real.sin_pi_div_two,
      show -Real.pi / 2 = -(Real.pi / 2) by ring,
      Real.sin_neg, Real.sin_pi_div_two]
    ring
  rw [show
      (fun _azimuth : ℝ =>
        ∫ latitude in (-Real.pi / 2)..Real.pi / 2,
          ∫ r in (0 : ℝ)..1,
            Real.rpow (1 - r ^ 2) (-p) * r ^ 2 *
              Real.cos latitude) =
        fun _ : ℝ => 2 * radialIntegral p by
    funext azimuth
    simp_rw [hinner]
    exact hlatitude]
  rw [intervalIntegral.integral_const]
  simp
  ring

theorem gap1 (p : ℝ) (hp : p < 1) :
    volumeIntegral p = sphericalIntegral p := by
  rw [volumeIntegral_value p hp, spherical_factor p,
    radialIntegral_value p hp]
  ring

theorem gap2 (p : ℝ) (hp : p < 1) :
    sphericalIntegral p = 4 * Real.pi * radialIntegral p := by
  exact spherical_factor p

theorem gap3 (p : ℝ) (hp : p < 1) :
    volumeIntegral p = 4 * Real.pi * radialIntegral p := by
  rw [volumeIntegral_value p hp, radialIntegral_value p hp]
  ring

theorem gap4 (p : ℝ) (hp : p < 1) :
    radialIntegral p = (1 / 2 : ℝ) * betaIntegral p := by
  rw [radialIntegral_value p hp, betaIntegral_value p hp]

theorem gap5 (p : ℝ) (hp : p < 1) :
    betaIntegral p = betaValue p := by
  exact betaIntegral_value p hp

theorem gap6 (p : ℝ) (hp : p < 1) :
    radialIntegral p = (1 / 2 : ℝ) * betaValue p := by
  exact radialIntegral_value p hp

theorem gap7 (p : ℝ) (hp : p < 1) :
    volumeIntegral p = 2 * Real.pi * betaValue p := by
  exact volumeIntegral_value p hp

theorem gap8 (p : ℝ) (hp : 1 ≤ p) :
    ¬ IntegrableOn
      (fun t : ℝ =>
        Real.rpow t (1 / 2 : ℝ) * Real.rpow (1 - t) (-p))
      (Set.Ioc (0 : ℝ) 1) := by
  change ¬ IntegrableOn (betaKernel p) (Ioc (0 : ℝ) 1)
  rw [betaKernel_integrableOn_iff]
  linarith

theorem gap9 (p : ℝ) (hp : 1 ≤ p) :
    ¬ IntegrableOn (weight p) unitBall := by
  rw [weight_integrable_iff]
  linarith

end

end ProofGap.Exercise4198
