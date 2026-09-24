import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4091

noncomputable section

open MeasureTheory
open scoped Interval

def solid : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2.1 ^ 2 ≤ 2 * p.2.2 ∧ p.2.2 ≤ 2}

def cylindricalMap (r phi z : ℝ) : ℝ × ℝ × ℝ :=
  (r * Real.cos phi, r * Real.sin phi, z)

def cylindricalDomain : Set (ℝ × ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ 2 * Real.pi ∧
    0 ≤ p.2.1 ∧ p.2.1 ≤ 2 ∧
    p.2.1 ^ 2 / 2 ≤ p.2.2 ∧ p.2.2 ≤ 2}

def cylindricalJacobianAbs (r : ℝ) : ℝ :=
  |r|

def momentIntegral : ℝ :=
  ∫ p in solid, p.1 ^ 2 + p.2.1 ^ 2

private def diskTwo : Set (ℝ × ℝ) :=
  {q | q.1 ^ 2 + q.2 ^ 2 ≤ 4}

private def radialMoment (q : ℝ × ℝ) : ℝ :=
  (q.1 ^ 2 + q.2 ^ 2) *
    (2 - (q.1 ^ 2 + q.2 ^ 2) / 2)

private theorem solid_closed : IsClosed solid := by
  have hxy : Continuous (fun p : ℝ × ℝ × ℝ =>
      p.1 ^ 2 + p.2.1 ^ 2) :=
    (continuous_fst.pow 2).add
      ((continuous_fst.comp continuous_snd).pow 2)
  have hz : Continuous (fun p : ℝ × ℝ × ℝ => p.2.2) :=
    continuous_snd.comp continuous_snd
  exact (isClosed_le hxy (continuous_const.mul hz)).inter
    (isClosed_le hz continuous_const)

private theorem solid_measurable : MeasurableSet solid :=
  solid_closed.measurableSet

private theorem solid_compact : IsCompact solid := by
  have hclosed : IsClosed solid := solid_closed
  have hsub : solid ⊆
      Set.Icc ((-2 : ℝ), ((-2 : ℝ), (0 : ℝ)))
        ((2 : ℝ), ((2 : ℝ), (2 : ℝ))) := by
    intro p hp
    have hxy := hp.1
    have hz2 := hp.2
    have hz0 : 0 ≤ p.2.2 := by
      nlinarith [sq_nonneg p.1, sq_nonneg p.2.1]
    have hx4 : p.1 ^ 2 ≤ 4 := by
      nlinarith [sq_nonneg p.2.1]
    have hy4 : p.2.1 ^ 2 ≤ 4 := by
      nlinarith [sq_nonneg p.1]
    have hxlo : -2 ≤ p.1 := by nlinarith [sq_nonneg (p.1 + 2)]
    have hxhi : p.1 ≤ 2 := by nlinarith [sq_nonneg (p.1 - 2)]
    have hylo : -2 ≤ p.2.1 := by nlinarith [sq_nonneg (p.2.1 + 2)]
    have hyhi : p.2.1 ≤ 2 := by nlinarith [sq_nonneg (p.2.1 - 2)]
    exact ⟨⟨hxlo, ⟨hylo, hz0⟩⟩, ⟨hxhi, ⟨hyhi, hz2⟩⟩⟩
  exact isCompact_Icc.of_isClosed_subset hclosed hsub

private theorem solid_indicator_integrable :
    Integrable (solid.indicator
      (fun p : ℝ × ℝ × ℝ => p.1 ^ 2 + p.2.1 ^ 2)) := by
  have hf : Continuous (fun p : ℝ × ℝ × ℝ =>
      p.1 ^ 2 + p.2.1 ^ 2) :=
    (continuous_fst.pow 2).add
      ((continuous_fst.comp continuous_snd).pow 2)
  rw [integrable_indicator_iff solid_measurable]
  exact hf.continuousOn.integrableOn_compact solid_compact

private theorem momentIntegral_disk :
    momentIntegral = ∫ q in diskTwo, radialMoment q := by
  let f : ℝ × ℝ × ℝ → ℝ := fun p => p.1 ^ 2 + p.2.1 ^ 2
  let e :=
    (MeasurableEquiv.prodAssoc :
      ((ℝ × ℝ) × ℝ) ≃ᵐ (ℝ × (ℝ × ℝ)))
  have hfi : Integrable (solid.indicator f) :=
    solid_indicator_integrable
  have hfi' : Integrable
      (fun q : (ℝ × ℝ) × ℝ => solid.indicator f (e q)) := by
    simpa only [Function.comp_apply] using
      (volume_preserving_prodAssoc.integrable_comp_emb
        e.measurableEmbedding).2 hfi
  have hreassoc :
      (∫ q : (ℝ × ℝ) × ℝ, solid.indicator f (e q)) =
        ∫ p : ℝ × (ℝ × ℝ), solid.indicator f p := by
    exact volume_preserving_prodAssoc.integral_comp' (solid.indicator f)
  unfold momentIntegral
  rw [← integral_indicator solid_measurable]
  change (∫ p : ℝ × (ℝ × ℝ), solid.indicator f p) = _
  rw [← hreassoc]
  have hFubini :
      (∫ q : (ℝ × ℝ) × ℝ, solid.indicator f (e q)) =
        ∫ q : ℝ × ℝ, ∫ z : ℝ,
          solid.indicator f (e (q, z)) := by
    exact MeasureTheory.integral_prod
      (fun q : (ℝ × ℝ) × ℝ => solid.indicator f (e q)) hfi'
  rw [hFubini]
  change
    (∫ q : ℝ × ℝ, ∫ z : ℝ,
      solid.indicator f (q.1, (q.2, z))) =
      ∫ q in diskTwo, radialMoment q
  have hsection (q : ℝ × ℝ) :
      (∫ z : ℝ, solid.indicator f (q.1, (q.2, z))) =
        diskTwo.indicator radialMoment q := by
    let rho : ℝ := q.1 ^ 2 + q.2 ^ 2
    by_cases hq : rho ≤ 4
    · have hlow : rho / 2 ≤ 2 := by linarith
      have hfun :
          (fun z : ℝ => solid.indicator f (q.1, (q.2, z))) =
            (Set.Icc (rho / 2) 2).indicator (fun _ => rho) := by
        funext z
        have hmem :
            (q.1, (q.2, z)) ∈ solid ↔ z ∈ Set.Icc (rho / 2) 2 := by
          simp only [solid, Set.mem_setOf_eq, Set.mem_Icc, rho]
          constructor
          · rintro ⟨h1, h2⟩
            constructor
            · linarith
            · exact h2
          · rintro ⟨h1, h2⟩
            constructor
            · linarith
            · exact h2
        simp only [Set.indicator, hmem, f, rho]
      rw [hfun, integral_indicator measurableSet_Icc]
      rw [integral_Icc_eq_integral_Ioc]
      rw [← intervalIntegral.integral_of_le hlow]
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      have hmemq : q ∈ diskTwo := by
        simpa [diskTwo, rho] using hq
      rw [Set.indicator_of_mem hmemq]
      simp only [radialMoment, rho]
      ring
    · have hzero :
          (fun z : ℝ => solid.indicator f (q.1, (q.2, z))) =
            fun _ => 0 := by
        funext z
        have hnot : (q.1, (q.2, z)) ∉ solid := by
          intro hs
          apply hq
          change rho ≤ 4
          have h1 := hs.1
          have h2 := hs.2
          dsimp [rho]
          nlinarith
        simp [Set.indicator, hnot]
      rw [hzero]
      have hnotmem : q ∉ diskTwo := by
        simpa [diskTwo, rho] using hq
      simp [Set.indicator, hnotmem]
  simp_rw [hsection]
  rw [integral_indicator]
  exact (isClosed_le
    ((continuous_fst.pow 2).add (continuous_snd.pow 2))
    continuous_const).measurableSet

private theorem polar_diskTwo_pointwise (p : ℝ × ℝ)
    (hp : p ∈ polarCoord.target) :
    p.1 • diskTwo.indicator radialMoment (polarCoord.symm p) =
      (Set.Iic (2 : ℝ)).indicator
          (fun r => r ^ 3 * (2 - r ^ 2 / 2)) p.1 *
        (1 : ℝ) := by
  rcases p with ⟨r, theta⟩
  have hr : 0 < r := hp.1
  have htrig : (r * Real.cos theta) ^ 2 + (r * Real.sin theta) ^ 2 = r ^ 2 := by
    calc
      _ = r ^ 2 * (Real.cos theta ^ 2 + Real.sin theta ^ 2) := by ring
      _ = r ^ 2 := by rw [Real.cos_sq_add_sin_sq]; ring
  have hmem :
      polarCoord.symm (r, theta) ∈ diskTwo ↔ r ≤ 2 := by
    rw [polarCoord_symm_apply]
    simp only [diskTwo, Set.mem_setOf_eq, htrig]
    constructor
    · intro h
      nlinarith [sq_nonneg (r - 2)]
    · intro h
      nlinarith [mul_nonneg hr.le (sub_nonneg.mpr h)]
  simp only [Set.indicator, hmem, Set.mem_Iic, smul_eq_mul]
  split_ifs with h
  · rw [polarCoord_symm_apply]
    simp only [radialMoment]
    rw [htrig]
    ring
  · simp

private theorem angular_integral_one :
    (∫ theta in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ)) =
      2 * Real.pi := by
  calc
    _ = ∫ theta in Set.Ioc (-Real.pi) Real.pi, (1 : ℝ) :=
      (integral_Ioc_eq_integral_Ioo
        (f := fun _ : ℝ => (1 : ℝ))).symm
    _ = ∫ theta in -Real.pi..Real.pi, (1 : ℝ) := by
      rw [intervalIntegral.integral_of_le]
      exact neg_le_self Real.pi_nonneg
    _ = 2 * Real.pi := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      ring

private theorem radial_set_integral :
    (∫ r in Set.Ioi (0 : ℝ),
        (Set.Iic (2 : ℝ)).indicator
          (fun r => r ^ 3 * (2 - r ^ 2 / 2)) r) =
      ∫ r in (0 : ℝ)..2, r ^ 3 * (2 - r ^ 2 / 2) := by
  rw [setIntegral_indicator measurableSet_Iic]
  have hinter :
      Set.Ioi (0 : ℝ) ∩ Set.Iic 2 = Set.Ioc (0 : ℝ) 2 := by
    ext r
    simp
  rw [hinter, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]

private theorem disk_moment_value :
    (∫ q in diskTwo, radialMoment q) = 16 * Real.pi / 3 := by
  have hdisk : MeasurableSet diskTwo :=
    (isClosed_le
      ((continuous_fst.pow 2).add (continuous_snd.pow 2))
      continuous_const).measurableSet
  have hpolar := integral_comp_polarCoord_symm
    (diskTwo.indicator radialMoment)
  rw [integral_indicator hdisk] at hpolar
  have hprod :
      (∫ p in polarCoord.target,
          p.1 • diskTwo.indicator radialMoment (polarCoord.symm p)) =
        (∫ r in Set.Ioi (0 : ℝ),
            (Set.Iic (2 : ℝ)).indicator
              (fun r => r ^ 3 * (2 - r ^ 2 / 2)) r) *
          ∫ theta in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
    rw [polarCoord_target]
    calc
      _ = ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          (Set.Iic (2 : ℝ)).indicator
              (fun r => r ^ 3 * (2 - r ^ 2 / 2)) p.1 * (1 : ℝ) := by
        apply setIntegral_congr_fun
          (measurableSet_Ioi.prod measurableSet_Ioo)
        intro p hp
        exact polar_diskTwo_pointwise p hp
      _ = _ := by
        exact setIntegral_prod_mul
          (fun r : ℝ =>
            (Set.Iic (2 : ℝ)).indicator
              (fun r => r ^ 3 * (2 - r ^ 2 / 2)) r)
          (fun _ : ℝ => (1 : ℝ))
          (Set.Ioi (0 : ℝ)) (Set.Ioo (-Real.pi) Real.pi)
  rw [hprod, radial_set_integral, angular_integral_one] at hpolar
  rw [← hpolar]
  have hr :
      (∫ r in (0 : ℝ)..2, r ^ 3 * (2 - r ^ 2 / 2)) =
        8 / 3 := by
    rw [show (fun r : ℝ => r ^ 3 * (2 - r ^ 2 / 2)) =
        fun r => 2 * r ^ 3 - (1 / 2 : ℝ) * r ^ 5 by
      funext r
      ring]
    have hc3 : Continuous (fun r : ℝ => 2 * r ^ 3) :=
      continuous_const.mul (continuous_id.pow 3)
    have hc5 : Continuous (fun r : ℝ => (1 / 2 : ℝ) * r ^ 5) :=
      continuous_const.mul (continuous_id.pow 5)
    rw [intervalIntegral.integral_sub
      (hc3.intervalIntegrable (μ := volume) 0 2)
      (hc5.intervalIntegrable (μ := volume) 0 2)]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_pow, integral_pow]
    norm_num
  rw [hr]
  ring

private theorem momentIntegral_value :
    momentIntegral = 16 * Real.pi / 3 := by
  rw [momentIntegral_disk, disk_moment_value]

theorem gap1 (r phi z : ℝ) :
    let p := cylindricalMap r phi z
    p.1 ^ 2 + p.2.1 ^ 2 = 2 * p.2.2 ↔
      r ^ 2 = 2 * z := by
  dsimp [cylindricalMap]
  rw [show
    (r * Real.cos phi) ^ 2 + (r * Real.sin phi) ^ 2 = r ^ 2 by
      calc
        _ = r ^ 2 * (Real.cos phi ^ 2 + Real.sin phi ^ 2) := by ring
        _ = r ^ 2 := by rw [Real.cos_sq_add_sin_sq]; ring]

theorem gap2 :
    cylindricalDomain =
      {p | 0 ≤ p.1 ∧ p.1 ≤ 2 * Real.pi ∧
        0 ≤ p.2.1 ∧ p.2.1 ≤ 2 ∧
        p.2.1 ^ 2 / 2 ≤ p.2.2 ∧ p.2.2 ≤ 2} := by
  rfl

theorem gap3 (r : ℝ) (hr : 0 ≤ r) :
    cylindricalJacobianAbs r = r := by
  exact abs_of_nonneg hr

theorem gap4 :
    momentIntegral =
      ∫ phi in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..2,
          ∫ z in r ^ 2 / 2..2, r ^ 2 * r := by
  rw [momentIntegral_value]
  have hz (r : ℝ) :
      (∫ z in r ^ 2 / 2..2, r ^ 2 * r) =
        r ^ 3 * (2 - r ^ 2 / 2) := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  simp_rw [hz]
  have hr :
      (∫ r in (0 : ℝ)..2, r ^ 3 * (2 - r ^ 2 / 2)) = 8 / 3 := by
    rw [show (fun r : ℝ => r ^ 3 * (2 - r ^ 2 / 2)) =
        fun r => 2 * r ^ 3 - (1 / 2 : ℝ) * r ^ 5 by
      funext r
      ring]
    have hc3 : Continuous (fun r : ℝ => 2 * r ^ 3) :=
      continuous_const.mul (continuous_id.pow 3)
    have hc5 : Continuous (fun r : ℝ => (1 / 2 : ℝ) * r ^ 5) :=
      continuous_const.mul (continuous_id.pow 5)
    rw [intervalIntegral.integral_sub
      (hc3.intervalIntegrable (μ := volume) 0 2)
      (hc5.intervalIntegrable (μ := volume) 0 2)]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_pow, integral_pow]
    norm_num
  rw [hr, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem gap5 :
    (∫ phi in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..2,
          ∫ z in r ^ 2 / 2..2, r ^ 2 * r) =
      16 * Real.pi / 3 := by
  rw [← gap4, momentIntegral_value]

theorem gap6 :
    momentIntegral = 16 * Real.pi / 3 := by
  exact momentIntegral_value

end

end ProofGap.Exercise4091
