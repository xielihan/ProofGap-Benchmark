import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4104

noncomputable section

open MeasureTheory
open scoped Interval

def region (a : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2.1 ^ 2 ≤ a * p.2.2 ∧
    p.2.2 ≤ Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2)}

def cylindricalMap (r phi z : ℝ) : ℝ × ℝ × ℝ :=
  (r * Real.cos phi, r * Real.sin phi, z)

def parameterDomain (a : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ 2 * Real.pi ∧
    0 ≤ p.2.1 ∧ p.2.1 ≤ a ∧
    p.2.1 ^ 2 / a ≤ p.2.2 ∧ p.2.2 ≤ p.2.1}

def volume (a : ℝ) : ℝ :=
  ∫ _ in region a, (1 : ℝ)

private theorem exists_polar_angle (x y : ℝ) :
    ∃ phi : ℝ,
      0 ≤ phi ∧ phi ≤ 2 * Real.pi ∧
      Real.sqrt (x ^ 2 + y ^ 2) * Real.cos phi = x ∧
      Real.sqrt (x ^ 2 + y ^ 2) * Real.sin phi = y := by
  let z : ℂ := x + y * Complex.I
  let theta : ℝ := Complex.arg z
  let phi : ℝ := if 0 ≤ theta then theta else theta + 2 * Real.pi
  have hnorm :
      ‖z‖ = Real.sqrt (x ^ 2 + y ^ 2) := by
    rw [Complex.norm_def]
    simp [z, Complex.normSq_add_mul_I]
  have hcos :
      Real.sqrt (x ^ 2 + y ^ 2) * Real.cos theta = x := by
    rw [← hnorm]
    simpa [z, theta] using Complex.norm_mul_cos_arg z
  have hsin :
      Real.sqrt (x ^ 2 + y ^ 2) * Real.sin theta = y := by
    rw [← hnorm]
    simpa [z, theta] using Complex.norm_mul_sin_arg z
  refine ⟨phi, ?_⟩
  by_cases htheta : 0 ≤ theta
  · have hthetaUpper : theta ≤ 2 * Real.pi :=
      (Complex.arg_le_pi z).trans (by linarith [Real.pi_pos])
    simpa [phi, htheta] using
      (show
        0 ≤ theta ∧ theta ≤ 2 * Real.pi ∧
          Real.sqrt (x ^ 2 + y ^ 2) * Real.cos theta = x ∧
          Real.sqrt (x ^ 2 + y ^ 2) * Real.sin theta = y
        from ⟨htheta, hthetaUpper, hcos, hsin⟩)
  · have hthetaNeg : theta < 0 := lt_of_not_ge htheta
    have hphi0 : 0 ≤ theta + 2 * Real.pi := by
      linarith [Complex.neg_pi_lt_arg z, Real.pi_pos]
    have hphi1 : theta + 2 * Real.pi ≤ 2 * Real.pi := by
      linarith
    simp only [phi, if_neg htheta]
    rw [Real.cos_add_two_pi, Real.sin_add_two_pi]
    exact ⟨hphi0, hphi1, hcos, hsin⟩

private theorem region_measurable (a : ℝ) :
    MeasurableSet (region a) := by
  unfold region
  measurability

private theorem region_subset_box (a : ℝ) (ha : 0 < a) :
    region a ⊆
      Set.Icc (-a) a ×ˢ
        (Set.Icc (-a) a ×ˢ Set.Icc (0 : ℝ) a) := by
  rintro ⟨x, y, z⟩ ⟨hparaboloid, hcone⟩
  have hs0 : 0 ≤ x ^ 2 + y ^ 2 := by positivity
  let r : ℝ := Real.sqrt (x ^ 2 + y ^ 2)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = x ^ 2 + y ^ 2 :=
    Real.sq_sqrt hs0
  have hz0 : 0 ≤ z := by
    have : 0 ≤ a * z := le_trans hs0 hparaboloid
    nlinarith
  have hzle : z ≤ r := by simpa [r] using hcone
  have hra : r ≤ a := by
    by_cases hrzero : r = 0
    · simpa [hrzero] using ha.le
    · have hrpos : 0 < r :=
        lt_of_le_of_ne hr0 (Ne.symm hrzero)
      have hr2az : r ^ 2 ≤ a * z := by
        simpa [hrsq] using hparaboloid
      nlinarith
  have hx2 : x ^ 2 ≤ a ^ 2 := by
    nlinarith [sq_nonneg y, hrsq]
  have hy2 : y ^ 2 ≤ a ^ 2 := by
    nlinarith [sq_nonneg x, hrsq]
  exact
    ⟨⟨by nlinarith, by nlinarith⟩,
      ⟨⟨by nlinarith, by nlinarith⟩, hz0, hzle.trans hra⟩⟩

private theorem region_indicator_integrable (a : ℝ) (ha : 0 < a) :
    Integrable
      ((region a).indicator (fun _p : ℝ × ℝ × ℝ => (1 : ℝ)))
      MeasureTheory.volume := by
  have hbox :
      IntegrableOn (fun _p : ℝ × ℝ × ℝ => (1 : ℝ))
        (Set.Icc (-a) a ×ˢ
          (Set.Icc (-a) a ×ˢ Set.Icc (0 : ℝ) a))
        MeasureTheory.volume :=
    ((continuous_const :
      Continuous (fun _p : ℝ × ℝ × ℝ => (1 : ℝ))).continuousOn).integrableOn_compact
        (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  exact
    (integrable_indicator_iff (region_measurable a)).2
      (hbox.mono_set (region_subset_box a ha))

private def verticalSection (a : ℝ) (q : ℝ × ℝ) : Set ℝ :=
  Set.Icc ((q.1 ^ 2 + q.2 ^ 2) / a)
    (Real.sqrt (q.1 ^ 2 + q.2 ^ 2))

private theorem volume_eq_integral_sections (a : ℝ) (ha : 0 < a) :
    volume a =
      ∫ q : ℝ × ℝ,
        ∫ _z in verticalSection a q, (1 : ℝ) := by
  classical
  let g : (ℝ × ℝ × ℝ) → ℝ :=
    (region a).indicator (fun _p => (1 : ℝ))
  have hg : Integrable g MeasureTheory.volume := by
    exact region_indicator_integrable a ha
  have hp :
      MeasurePreserving
        (MeasurableEquiv.prodAssoc :
          (ℝ × ℝ) × ℝ ≃ᵐ ℝ × ℝ × ℝ) :=
    MeasureTheory.volume_preserving_prodAssoc
  have hgassoc :
      Integrable
        (fun p : (ℝ × ℝ) × ℝ =>
          g (p.1.1, p.1.2, p.2))
        MeasureTheory.volume := by
    simpa [Function.comp_def] using
      hp.integrable_comp_of_integrable hg
  have hfubini :
      (∫ p : (ℝ × ℝ) × ℝ,
          g (p.1.1, p.1.2, p.2)) =
        ∫ q : ℝ × ℝ, ∫ z : ℝ,
          g (q.1, q.2, z) := by
    change
      (∫ p : (ℝ × ℝ) × ℝ,
          g (p.1.1, p.1.2, p.2)
            ∂(MeasureTheory.volume : Measure (ℝ × ℝ)).prod
              MeasureTheory.volume) =
        ∫ q : ℝ × ℝ, ∫ z : ℝ,
          g (q.1, q.2, z)
    rw [MeasureTheory.integral_prod _ hgassoc]
  calc
    volume a =
        ∫ p : ℝ × ℝ × ℝ, g p := by
      rw [volume, MeasureTheory.integral_indicator
        (region_measurable a)]
    _ = ∫ p : (ℝ × ℝ) × ℝ,
          g (p.1.1, p.1.2, p.2) := by
      symm
      simpa [Function.comp_def] using hp.integral_comp' g
    _ = ∫ q : ℝ × ℝ, ∫ z : ℝ,
          g (q.1, q.2, z) := hfubini
    _ = ∫ q : ℝ × ℝ,
          ∫ _z in verticalSection a q, (1 : ℝ) := by
      apply integral_congr_ae
      filter_upwards with q
      rw [verticalSection,
        ← MeasureTheory.integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards with z
      have hmem :
          (q.1, q.2, z) ∈ region a ↔
            z ∈ verticalSection a q := by
        constructor
        · rintro ⟨hlo, hhi⟩
          exact ⟨(div_le_iff₀ ha).2 (by simpa [mul_comm] using hlo),
            hhi⟩
        · rintro ⟨hlo, hhi⟩
          exact ⟨by
            have := (div_le_iff₀ ha).1 hlo
            simpa [mul_comm] using this, hhi⟩
      simp only [g]
      change
        (if (q.1, q.2, z) ∈ region a then 1 else 0) =
          if z ∈ verticalSection a q then 1 else 0
      rw [hmem]

theorem gap1 (a : ℝ) (ha : 0 < a) :
    (fun p => cylindricalMap p.2.1 p.1 p.2.2) ''
        parameterDomain a =
      region a := by
  ext q
  constructor
  · rintro ⟨⟨phi, r, z⟩, hp, rfl⟩
    rcases hp with ⟨hphi0, hphi1, hr0, hra, hz0, hz1⟩
    have hrad :
        (r * Real.cos phi) ^ 2 + (r * Real.sin phi) ^ 2 =
          r ^ 2 := by
      nlinarith [Real.cos_sq_add_sin_sq phi]
    change
      (r * Real.cos phi) ^ 2 + (r * Real.sin phi) ^ 2 ≤
          a * z ∧
        z ≤ Real.sqrt
          ((r * Real.cos phi) ^ 2 + (r * Real.sin phi) ^ 2)
    rw [hrad, Real.sqrt_sq hr0]
    exact ⟨by
      have := (div_le_iff₀ ha).1 hz0
      nlinarith, hz1⟩
  · rintro ⟨hball, hcone⟩
    rcases q with ⟨x, y, z⟩
    let r : ℝ := Real.sqrt (x ^ 2 + y ^ 2)
    have hsnonneg : 0 ≤ x ^ 2 + y ^ 2 := by positivity
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hrsq : r ^ 2 = x ^ 2 + y ^ 2 := by
      exact Real.sq_sqrt hsnonneg
    have hzle : z ≤ r := by simpa [r] using hcone
    have hr2az : r ^ 2 ≤ a * z := by simpa [hrsq] using hball
    have hra : r ≤ a := by
      by_cases hrzero : r = 0
      · simpa [hrzero] using ha.le
      · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrzero)
        nlinarith
    have hzlower : r ^ 2 / a ≤ z := by
      apply (div_le_iff₀ ha).2
      nlinarith
    obtain ⟨phi, hphi0, hphi1, hx, hy⟩ :=
      exists_polar_angle x y
    refine ⟨(phi, r, z), ?_, ?_⟩
    · exact ⟨hphi0, hphi1, hr0, hra, hzlower, hzle⟩
    · ext <;> simp [cylindricalMap, r, hx, hy]

theorem gap2 (r : ℝ) (hr : 0 ≤ r) :
    |r| = r := by
  exact abs_of_nonneg hr

theorem gap3 (a : ℝ) (ha : 0 < a) :
    volume a =
      ∫ phi in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..a,
          ∫ z in r ^ 2 / a..r, r := by
  have hpolar :
      (∫ q : ℝ × ℝ,
          ∫ _z in verticalSection a q, (1 : ℝ)) =
        (∫ r in Set.Ioi (0 : ℝ),
            r * ∫ _z in Set.Icc (r ^ 2 / a) r, (1 : ℝ)) *
          ∫ _phi in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
    rw [← integral_comp_polarCoord_symm, polarCoord_target]
    rw [← setIntegral_prod_mul]
    apply setIntegral_congr_fun
      (measurableSet_Ioi.prod measurableSet_Ioo)
    rintro ⟨r, phi⟩ ⟨hr, _hphi⟩
    have hrad :
        (r * Real.cos phi) ^ 2 + (r * Real.sin phi) ^ 2 =
          r ^ 2 := by
      nlinarith [Real.cos_sq_add_sin_sq phi]
    simp only [polarCoord_symm_apply, smul_eq_mul, mul_one,
      verticalSection]
    rw [hrad, Real.sqrt_sq hr.le]
  have hradial :
      (∫ r in Set.Ioi (0 : ℝ),
          r * ∫ _z in Set.Icc (r ^ 2 / a) r, (1 : ℝ)) =
        ∫ r in (0 : ℝ)..a,
          ∫ _z in r ^ 2 / a..r, r := by
    calc
      (∫ r in Set.Ioi (0 : ℝ),
          r * ∫ _z in Set.Icc (r ^ 2 / a) r, (1 : ℝ)) =
          ∫ r in Set.Ioc (0 : ℝ) a,
            r * ∫ _z in Set.Icc (r ^ 2 / a) r, (1 : ℝ) := by
        apply setIntegral_eq_of_subset_of_forall_diff_eq_zero
          measurableSet_Ioi Set.Ioc_subset_Ioi_self
        rintro r ⟨hr0, hra⟩
        have hrpos : 0 < r := by simpa using hr0
        have har : a < r := by
          simp only [Set.mem_Ioc, hrpos, true_and] at hra
          exact lt_of_not_ge hra
        have hrlower : r < r ^ 2 / a := by
          apply (lt_div_iff₀ ha).2
          nlinarith
        rw [Set.Icc_eq_empty (by linarith)]
        simp
      _ = ∫ r in Set.Ioc (0 : ℝ) a,
            ∫ _z in r ^ 2 / a..r, r := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro r hr
        have hr0 : 0 < r := hr.1
        have hra : r ≤ a := hr.2
        have hlower : r ^ 2 / a ≤ r := by
          apply (div_le_iff₀ ha).2
          nlinarith
        change
          r * (∫ _z in Set.Icc (r ^ 2 / a) r, (1 : ℝ)) =
            ∫ _z in r ^ 2 / a..r, r
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
          intervalIntegral.integral_of_le hlower,
          ← MeasureTheory.integral_const_mul]
        simp
      _ = ∫ r in (0 : ℝ)..a,
            ∫ _z in r ^ 2 / a..r, r := by
        rw [intervalIntegral.integral_of_le ha.le]
  have hangle :
      (∫ _phi in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ)) =
        2 * Real.pi := by
    simp only [integral_const, MeasurableSet.univ,
      measureReal_restrict_apply, Set.univ_inter,
      smul_eq_mul, mul_one]
    rw [Real.volume_real_Ioo_of_le
      (by linarith [Real.pi_nonneg])]
    ring
  rw [volume_eq_integral_sections a ha, hpolar, hradial, hangle]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem gap4 (a : ℝ) (ha : 0 < a) :
    (∫ phi in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..a,
          ∫ z in r ^ 2 / a..r, r) =
      2 * Real.pi *
        ∫ r in (0 : ℝ)..a, r ^ 2 - r ^ 3 / a := by
  have ha0 : a ≠ 0 := ha.ne'
  have hpoint (r : ℝ) :
      (∫ _z in r ^ 2 / a..r, r) =
        r ^ 2 - r ^ 3 / a := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    field_simp [ha0]
  simp_rw [hpoint]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem gap5 (a : ℝ) (ha : 0 < a) :
    2 * Real.pi *
        (∫ r in (0 : ℝ)..a, r ^ 2 - r ^ 3 / a) =
      Real.pi * a ^ 3 / 6 := by
  have ha0 : a ≠ 0 := ha.ne'
  rw [intervalIntegral.integral_sub]
  · rw [integral_pow,
      intervalIntegral.integral_div,
      integral_pow]
    norm_num
    field_simp [ha0]
    ring
  · exact (continuous_pow 2).intervalIntegrable 0 a
  · exact (continuous_pow 3).intervalIntegrable 0 a |>.div_const a

theorem gap6 (a : ℝ) (ha : 0 < a) :
    volume a = Real.pi * a ^ 3 / 6 := by
  rw [gap3 a ha, gap4 a ha, gap5 a ha]

end

end ProofGap.Exercise4104
