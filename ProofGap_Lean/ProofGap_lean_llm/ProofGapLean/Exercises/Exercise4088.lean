import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4088

noncomputable section

open MeasureTheory
open scoped Interval

def sphericalDomain : Set (ℝ × ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ Real.pi / 2 ∧
    Real.pi / 4 ≤ p.2.1 ∧ p.2.1 ≤ Real.pi / 2 ∧
    0 ≤ p.2.2 ∧ p.2.2 ≤ Real.sqrt 2}

def cartesianIntegral : ℝ :=
  ∫ x in (0 : ℝ)..1,
    ∫ y in (0 : ℝ)..Real.sqrt (1 - x ^ 2),
      ∫ z in Real.sqrt (x ^ 2 + y ^ 2)..
          Real.sqrt (2 - x ^ 2 - y ^ 2),
        z ^ 2

def endpointPrimitive (psi : ℝ) : ℝ :=
  Real.pi / 5 * (2 * Real.sqrt 2) * (1 / 3) * Real.sin psi ^ 3

private theorem sqrt_two_sq :
    Real.sqrt 2 ^ 2 = 2 := by
  rw [Real.sq_sqrt]
  norm_num

private theorem sqrt_two_pos :
    0 < Real.sqrt 2 := by
  positivity

private theorem radial_four_integral :
    (∫ r in (0 : ℝ)..Real.sqrt 2, r ^ 4) =
      4 * Real.sqrt 2 / 5 := by
  rw [integral_pow]
  norm_num
  have hs := sqrt_two_sq
  rw [show Real.sqrt 2 ^ 5 =
    (Real.sqrt 2 ^ 2) ^ 2 * Real.sqrt 2 by ring, hs]
  ring

private theorem psi_integral :
    (∫ psi in Real.pi / 4..Real.pi / 2,
      Real.cos psi * Real.sin psi ^ 2) =
      (4 - Real.sqrt 2) / 12 := by
  rw [show (fun psi : ℝ =>
      Real.cos psi * Real.sin psi ^ 2) =
      fun psi => Real.sin psi ^ 2 * Real.cos psi by
    funext psi
    ring]
  rw [integral_sin_sq_mul_cos, Real.sin_pi_div_two,
    Real.sin_pi_div_four]
  have hs := sqrt_two_sq
  rw [show (Real.sqrt 2 / 2) ^ 3 =
    Real.sqrt 2 ^ 2 * Real.sqrt 2 / 8 by ring, hs]
  ring

private theorem spherical_triple_value :
    (∫ phi in (0 : ℝ)..Real.pi / 2,
      ∫ psi in Real.pi / 4..Real.pi / 2,
        ∫ r in (0 : ℝ)..Real.sqrt 2,
          r ^ 2 * Real.cos psi * r ^ 2 * Real.sin psi ^ 2) =
      Real.pi / 15 * (2 * Real.sqrt 2 - 1) := by
  have hr (psi : ℝ) :
      (∫ r in (0 : ℝ)..Real.sqrt 2,
        r ^ 2 * Real.cos psi * r ^ 2 * Real.sin psi ^ 2) =
        (4 * Real.sqrt 2 / 5) *
          (Real.cos psi * Real.sin psi ^ 2) := by
    rw [show (fun r : ℝ =>
        r ^ 2 * Real.cos psi * r ^ 2 * Real.sin psi ^ 2) =
      fun r =>
        (Real.cos psi * Real.sin psi ^ 2) * r ^ 4 by
      funext r
      ring]
    rw [intervalIntegral.integral_const_mul, radial_four_integral]
    ring
  simp_rw [hr]
  rw [intervalIntegral.integral_const_mul, psi_integral]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  have hs := sqrt_two_sq
  ring_nf
  rw [hs]
  ring

private theorem endpoint_difference_value :
    endpointPrimitive (Real.pi / 2) -
        endpointPrimitive (Real.pi / 4) =
      Real.pi / 15 * (2 * Real.sqrt 2 - 1) := by
  unfold endpointPrimitive
  rw [Real.sin_pi_div_two, Real.sin_pi_div_four]
  have hs := sqrt_two_sq
  ring_nf
  rw [show Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 by ring, hs]
  ring

private def quarterDisk : Set (ℝ × ℝ) :=
  {q | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 ^ 2 + q.2 ^ 2 ≤ 1}

private def afterZ (q : ℝ × ℝ) : ℝ :=
  ((Real.sqrt (2 - q.1 ^ 2 - q.2 ^ 2)) ^ 3 -
    (Real.sqrt (q.1 ^ 2 + q.2 ^ 2)) ^ 3) / 3

private theorem quarterDisk_closed : IsClosed quarterDisk := by
  have hx : Continuous (fun q : ℝ × ℝ => q.1) := continuous_fst
  have hy : Continuous (fun q : ℝ × ℝ => q.2) := continuous_snd
  have hzero : Continuous (fun _q : ℝ × ℝ => (0 : ℝ)) :=
    continuous_const
  have hone : Continuous (fun _q : ℝ × ℝ => (1 : ℝ)) :=
    continuous_const
  simpa only [quarterDisk, Set.setOf_and] using
    (isClosed_le hzero hx).inter
      ((isClosed_le hzero hy).inter
        (isClosed_le ((hx.pow 2).add (hy.pow 2)) hone))

private theorem quarterDisk_compact : IsCompact quarterDisk := by
  apply (isCompact_Icc :
    IsCompact (Set.Icc ((0 : ℝ), (0 : ℝ))
      ((1 : ℝ), (1 : ℝ)))).of_isClosed_subset quarterDisk_closed
  intro q hq
  change 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 ^ 2 + q.2 ^ 2 ≤ 1 at hq
  have hx : q.1 ^ 2 ≤ 1 := by nlinarith [sq_nonneg q.2]
  have hy : q.2 ^ 2 ≤ 1 := by nlinarith [sq_nonneg q.1]
  exact ⟨⟨hq.1, hq.2.1⟩,
    ⟨by nlinarith [sq_nonneg (q.1 - 1)],
      by nlinarith [sq_nonneg (q.2 - 1)]⟩⟩

private theorem afterZ_continuous : Continuous afterZ := by
  have hx : Continuous (fun q : ℝ × ℝ => q.1) := continuous_fst
  have hy : Continuous (fun q : ℝ × ℝ => q.2) := continuous_snd
  have hfirst : Continuous
      (fun q : ℝ × ℝ => 2 - q.1 ^ 2 - q.2 ^ 2) :=
    (continuous_const.sub (hx.pow 2)).sub (hy.pow 2)
  have hsecond : Continuous
      (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2) :=
    (hx.pow 2).add (hy.pow 2)
  exact (((Real.continuous_sqrt.comp hfirst).pow 3).sub
    ((Real.continuous_sqrt.comp hsecond).pow 3)).div_const 3

private theorem inner_z_value (x y : ℝ) :
    (∫ z in Real.sqrt (x ^ 2 + y ^ 2)..
        Real.sqrt (2 - x ^ 2 - y ^ 2), z ^ 2) =
      afterZ (x, y) := by
  rw [integral_pow]
  norm_num
  rfl

private theorem cartesian_quarter_integral :
    cartesianIntegral = ∫ q in quarterDisk, afterZ q := by
  unfold cartesianIntegral
  simp_rw [inner_z_value]
  have hInt : Integrable (quarterDisk.indicator afterZ) := by
    rw [integrable_indicator_iff quarterDisk_closed.measurableSet]
    exact afterZ_continuous.continuousOn.integrableOn_compact
      quarterDisk_compact
  have hfub :
      (∫ q : ℝ × ℝ, quarterDisk.indicator afterZ q) =
        ∫ x : ℝ, ∫ y : ℝ,
          quarterDisk.indicator afterZ (x, y) := by
    exact MeasureTheory.integral_prod
      (quarterDisk.indicator afterZ) hInt
  rw [← integral_indicator quarterDisk_closed.measurableSet, hfub]
  have hsection (x : ℝ) :
      (∫ y : ℝ, quarterDisk.indicator afterZ (x, y)) =
        (Set.Icc (0 : ℝ) 1).indicator
          (fun x =>
            ∫ y in (0 : ℝ)..Real.sqrt (1 - x ^ 2),
              afterZ (x, y)) x := by
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
    · rw [Set.indicator_of_mem hx]
      have hx2 : x ^ 2 ≤ 1 := by
        have hprod : 0 ≤ (1 - x) * (1 + x) :=
          mul_nonneg (sub_nonneg.mpr hx.2) (by linarith [hx.1])
        nlinarith
      have hbase : 0 ≤ 1 - x ^ 2 := sub_nonneg.mpr hx2
      have hsqrt : 0 ≤ Real.sqrt (1 - x ^ 2) :=
        Real.sqrt_nonneg _
      have hsq : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
        Real.sq_sqrt hbase
      rw [intervalIntegral.integral_of_le hsqrt]
      rw [← integral_Icc_eq_integral_Ioc]
      rw [← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards [] with y
      have hmem :
          (x, y) ∈ quarterDisk ↔
            y ∈ Set.Icc (0 : ℝ) (Real.sqrt (1 - x ^ 2)) := by
        constructor
        · intro hq
          have hy2 : y ^ 2 ≤ 1 - x ^ 2 := by nlinarith [hq.2.2]
          have hyle :
              y ≤ Real.sqrt (1 - x ^ 2) := by
            apply (sq_le_sq₀ hq.2.1 hsqrt).mp
            rw [hsq]
            exact hy2
          exact ⟨hq.2.1, hyle⟩
        · intro hy
          have hy2 : y ^ 2 ≤ 1 - x ^ 2 := by
            have := (sq_le_sq₀ hy.1 hsqrt).mpr hy.2
            rwa [hsq] at this
          exact ⟨hx.1, hy.1, by nlinarith⟩
      by_cases hy :
          y ∈ Set.Icc (0 : ℝ) (Real.sqrt (1 - x ^ 2))
      · rw [Set.indicator_of_mem hy,
          Set.indicator_of_mem (hmem.mpr hy)]
      · have hq : (x, y) ∉ quarterDisk := by
          intro h
          exact hy (hmem.mp h)
        rw [Set.indicator_of_notMem hy,
          Set.indicator_of_notMem hq]
    · rw [Set.indicator_of_notMem hx]
      apply integral_eq_zero_of_ae
      filter_upwards [] with y
      have hq : (x, y) ∉ quarterDisk := by
        intro h
        have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
          have hx2 : x ^ 2 ≤ 1 := by
            nlinarith [h.2.2, sq_nonneg y]
          exact ⟨h.1,
            by nlinarith [sq_nonneg (x - 1)]⟩
        exact hx hx'
      rw [Set.indicator_of_notMem hq]
      simp
  simp_rw [hsection]
  rw [integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le zero_le_one]

private def radialAfter (r : ℝ) : ℝ :=
  ((Real.sqrt (2 - r ^ 2)) ^ 3 - r ^ 3) / 3

private theorem nonneg_trig_iff_quarter
    {theta : ℝ} (htheta : theta ∈ Set.Ioo (-Real.pi) Real.pi) :
    0 ≤ Real.cos theta ∧ 0 ≤ Real.sin theta ↔
      theta ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
  constructor
  · rintro ⟨hcos, hsin⟩
    constructor
    · by_contra h
      have htneg : theta < 0 := lt_of_not_ge h
      have hsneg : Real.sin theta < 0 :=
        Real.sin_neg_of_neg_of_neg_pi_lt htneg htheta.1
      linarith
    · by_contra h
      have htlarge : Real.pi / 2 < theta := lt_of_not_ge h
      have htupper : theta < Real.pi + Real.pi / 2 := by
        linarith [htheta.2, Real.pi_pos]
      have hcneg : Real.cos theta < 0 :=
        Real.cos_neg_of_pi_div_two_lt_of_lt htlarge htupper
      linarith
  · intro htheta'
    exact ⟨Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [htheta'.1, Real.pi_pos], htheta'.2⟩,
      Real.sin_nonneg_of_nonneg_of_le_pi htheta'.1
        (by linarith [htheta'.2, Real.pi_pos])⟩

private theorem quarter_polar_pointwise
    (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
    p.1 • quarterDisk.indicator afterZ (polarCoord.symm p) =
      (Set.Iic (1 : ℝ)).indicator
          (fun r => r * radialAfter r) p.1 *
        (Set.Icc (0 : ℝ) (Real.pi / 2)).indicator
          (fun _theta => (1 : ℝ)) p.2 := by
  rcases p with ⟨r, theta⟩
  have hr : 0 < r := hp.1
  have htheta : theta ∈ Set.Ioo (-Real.pi) Real.pi := hp.2
  have htrig : (r * Real.cos theta) ^ 2 +
      (r * Real.sin theta) ^ 2 = r ^ 2 := by
    calc
      _ = r ^ 2 * (Real.cos theta ^ 2 + Real.sin theta ^ 2) := by ring
      _ = r ^ 2 := by rw [Real.cos_sq_add_sin_sq]; ring
  have hunit : r ^ 2 ≤ 1 ↔ r ≤ 1 := by
    constructor
    · intro h
      nlinarith [sq_nonneg (r - 1)]
    · intro h
      nlinarith [mul_nonneg hr.le (sub_nonneg.mpr h)]
  have hmem :
      polarCoord.symm (r, theta) ∈ quarterDisk ↔
        r ≤ 1 ∧ theta ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    rw [polarCoord_symm_apply]
    simp only [quarterDisk, Set.mem_setOf_eq]
    rw [htrig]
    constructor
    · rintro ⟨hx, hy, hsquare⟩
      have hcos : 0 ≤ Real.cos theta :=
        (mul_nonneg_iff_of_pos_left hr).mp hx
      have hsin : 0 ≤ Real.sin theta :=
        (mul_nonneg_iff_of_pos_left hr).mp hy
      exact ⟨hunit.mp hsquare,
        (nonneg_trig_iff_quarter htheta).mp ⟨hcos, hsin⟩⟩
    · rintro ⟨hr1, ht⟩
      have htrig_nonneg :=
        (nonneg_trig_iff_quarter htheta).mpr ht
      exact ⟨mul_nonneg hr.le htrig_nonneg.1,
        mul_nonneg hr.le htrig_nonneg.2, hunit.mpr hr1⟩
  simp only [Set.indicator, hmem, Set.mem_Iic, Set.mem_Icc,
    smul_eq_mul]
  by_cases hr1 : r ≤ 1
  · by_cases ht : 0 ≤ theta ∧ theta ≤ Real.pi / 2
    · simp only [hr1, ht, and_self, if_true, mul_one]
      rw [polarCoord_symm_apply]
      simp only
      unfold afterZ radialAfter
      rw [show 2 - (r * Real.cos theta) ^ 2 -
          (r * Real.sin theta) ^ 2 = 2 - r ^ 2 by
            linarith [htrig],
        htrig, Real.sqrt_sq_eq_abs,
        abs_of_pos hr]
    · simp [hr1, ht]
  · simp [hr1]

private theorem angular_quarter :
    (∫ theta in Set.Ioo (-Real.pi) Real.pi,
        (Set.Icc (0 : ℝ) (Real.pi / 2)).indicator
          (fun _theta => (1 : ℝ)) theta) =
      Real.pi / 2 := by
  rw [setIntegral_indicator measurableSet_Icc]
  have hinter :
      Set.Ioo (-Real.pi) Real.pi ∩
          Set.Icc (0 : ℝ) (Real.pi / 2) =
        Set.Icc (0 : ℝ) (Real.pi / 2) := by
    apply Set.inter_eq_right.mpr
    intro theta htheta
    exact ⟨by linarith [htheta.1, Real.pi_pos],
      by linarith [htheta.2, Real.pi_pos]⟩
  rw [hinter, integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le
    (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

private theorem quarter_polar :
    (∫ q in quarterDisk, afterZ q) =
      (∫ r in (0 : ℝ)..1, r * radialAfter r) *
        (Real.pi / 2) := by
  have hp := integral_comp_polarCoord_symm
    (quarterDisk.indicator afterZ)
  rw [integral_indicator quarterDisk_closed.measurableSet] at hp
  have hprod :
      (∫ p in polarCoord.target,
          p.1 • quarterDisk.indicator afterZ (polarCoord.symm p)) =
        (∫ r in Set.Ioi (0 : ℝ),
            (Set.Iic (1 : ℝ)).indicator
              (fun r => r * radialAfter r) r) *
          ∫ theta in Set.Ioo (-Real.pi) Real.pi,
            (Set.Icc (0 : ℝ) (Real.pi / 2)).indicator
              (fun _theta => (1 : ℝ)) theta := by
    rw [polarCoord_target]
    calc
      _ = ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          (Set.Iic (1 : ℝ)).indicator
              (fun r => r * radialAfter r) p.1 *
            (Set.Icc (0 : ℝ) (Real.pi / 2)).indicator
              (fun _theta => (1 : ℝ)) p.2 := by
        apply setIntegral_congr_fun
          (measurableSet_Ioi.prod measurableSet_Ioo)
        intro p hp'
        exact quarter_polar_pointwise p hp'
      _ = _ := by
        exact setIntegral_prod_mul
          (fun r : ℝ =>
            (Set.Iic (1 : ℝ)).indicator
              (fun r => r * radialAfter r) r)
          (fun theta : ℝ =>
            (Set.Icc (0 : ℝ) (Real.pi / 2)).indicator
              (fun _theta => (1 : ℝ)) theta)
          (Set.Ioi (0 : ℝ)) (Set.Ioo (-Real.pi) Real.pi)
  have hrad :
      (∫ r in Set.Ioi (0 : ℝ),
          (Set.Iic (1 : ℝ)).indicator
            (fun r => r * radialAfter r) r) =
        ∫ r in (0 : ℝ)..1, r * radialAfter r := by
    rw [setIntegral_indicator measurableSet_Iic]
    have hinter :
        Set.Ioi (0 : ℝ) ∩ Set.Iic 1 = Set.Ioc (0 : ℝ) 1 := by
      ext r
      simp
    rw [hinter, intervalIntegral.integral_of_le zero_le_one]
  rw [hprod, hrad, angular_quarter] at hp
  exact hp.symm

private theorem radial_after_integral :
    (∫ r in (0 : ℝ)..1, r * radialAfter r) =
      2 / 15 * (2 * Real.sqrt 2 - 1) := by
  let F : ℝ → ℝ := fun r =>
    -(1 / 15 : ℝ) * (2 - r ^ 2) ^ 2 *
        Real.sqrt (2 - r ^ 2) -
      r ^ 5 / 15
  have hcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
    exact (by fun_prop : Continuous F).continuousOn
  have hd : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt F (r * radialAfter r) r := by
    intro r hr
    have hprod : 0 < (1 - r) * (1 + r) :=
      mul_pos (sub_pos.mpr hr.2) (by linarith [hr.1])
    have hpos : 0 < 2 - r ^ 2 := by
      nlinarith
    have hinner :
        HasDerivAt (fun x : ℝ => 2 - x ^ 2) (-2 * r) r := by
      convert (hasDerivAt_const r 2).sub
        ((hasDerivAt_id r).pow 2) using 1 <;>
        simp only [id_eq] <;> ring
    have hpow :
        HasDerivAt (fun x : ℝ => (2 - x ^ 2) ^ 2)
          (2 * (2 - r ^ 2) * (-2 * r)) r := by
      convert hinner.pow 2 using 1 <;> ring
    have hsqrt :
        HasDerivAt (fun x : ℝ => Real.sqrt (2 - x ^ 2))
          (1 / (2 * Real.sqrt (2 - r ^ 2)) * (-2 * r)) r := by
      simpa only [Function.comp_apply] using
        (Real.hasDerivAt_sqrt hpos.ne').comp r hinner
    have hsquare :
        Real.sqrt (2 - r ^ 2) ^ 2 = 2 - r ^ 2 :=
      Real.sq_sqrt hpos.le
    have hfour :
        Real.sqrt (2 - r ^ 2) ^ 4 = (2 - r ^ 2) ^ 2 := by
      calc
        _ = (Real.sqrt (2 - r ^ 2) ^ 2) ^ 2 := by ring
        _ = _ := by rw [hsquare]
    dsimp [F, radialAfter]
    convert
      ((hpow.mul hsqrt).const_mul (-(1 / 15 : ℝ))).sub
        (((hasDerivAt_id r).pow 5).div_const 15) using 1
    · funext x
      simp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, id_eq]
      ring
    · simp only [id_eq]
      norm_num
      field_simp [Real.sqrt_ne_zero'.mpr hpos]
      ring_nf
      rw [hfour, hsquare]
      ring
  have hi : IntervalIntegrable
      (fun r : ℝ => r * radialAfter r)
      MeasureTheory.volume 0 1 :=
    (by
      unfold radialAfter
      fun_prop : Continuous
        (fun r : ℝ => r * radialAfter r)).intervalIntegrable _ _
  have hFTC :
      (∫ r in (0 : ℝ)..1, r * radialAfter r) =
        F 1 - F 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      zero_le_one hcont hd hi
  rw [hFTC]
  dsimp [F, radialAfter]
  norm_num
  ring

private theorem cartesianIntegral_value :
    cartesianIntegral =
      Real.pi / 15 * (2 * Real.sqrt 2 - 1) := by
  rw [cartesian_quarter_integral, quarter_polar,
    radial_after_integral]
  ring

theorem gap1 :
    sphericalDomain =
      {p | 0 ≤ p.1 ∧ p.1 ≤ Real.pi / 2 ∧
        Real.pi / 4 ≤ p.2.1 ∧ p.2.1 ≤ Real.pi / 2 ∧
        0 ≤ p.2.2 ∧ p.2.2 ≤ Real.sqrt 2} := by
  rfl

theorem gap2 :
    cartesianIntegral =
      ∫ phi in (0 : ℝ)..Real.pi / 2,
        ∫ psi in Real.pi / 4..Real.pi / 2,
          ∫ r in (0 : ℝ)..Real.sqrt 2,
            r ^ 2 * Real.cos psi * r ^ 2 * Real.sin psi ^ 2 := by
  rw [cartesianIntegral_value, spherical_triple_value]

theorem gap3 :
    (∫ phi in (0 : ℝ)..Real.pi / 2,
        ∫ psi in Real.pi / 4..Real.pi / 2,
          ∫ r in (0 : ℝ)..Real.sqrt 2,
            r ^ 2 * Real.cos psi * r ^ 2 * Real.sin psi ^ 2) =
      1 / 5 * (4 * Real.sqrt 2) * (Real.pi / 2) *
        ∫ psi in Real.pi / 4..Real.pi / 2,
          Real.cos psi * Real.sin psi ^ 2 := by
  rw [spherical_triple_value, psi_integral]
  have hs := sqrt_two_sq
  ring_nf
  rw [hs]
  ring

theorem gap4 :
    cartesianIntegral =
      1 / 5 * (4 * Real.sqrt 2) * (Real.pi / 2) *
        ∫ psi in Real.pi / 4..Real.pi / 2,
          Real.cos psi * Real.sin psi ^ 2 := by
  rw [cartesianIntegral_value, psi_integral]
  have hs := sqrt_two_sq
  ring_nf
  rw [hs]
  ring

theorem gap5 :
    cartesianIntegral =
      endpointPrimitive (Real.pi / 2) -
        endpointPrimitive (Real.pi / 4) := by
  rw [cartesianIntegral_value, endpoint_difference_value]

theorem gap6 :
    endpointPrimitive (Real.pi / 2) -
        endpointPrimitive (Real.pi / 4) =
      Real.pi / 15 * (2 * Real.sqrt 2 - 1) :=
  endpoint_difference_value

theorem gap7 :
    cartesianIntegral =
      Real.pi / 15 * (2 * Real.sqrt 2 - 1) :=
  cartesianIntegral_value

end

end ProofGap.Exercise4088
