import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4107

noncomputable section

open MeasureTheory
open scoped Interval

def solid (a : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≤ 2 * a * p.2.2 ∧
    p.1 ^ 2 + p.2.1 ^ 2 ≤ p.2.2 ^ 2}

def cylindricalMap (r phi z : ℝ) : ℝ × ℝ × ℝ :=
  (r * Real.cos phi, r * Real.sin phi, z)

def parameterDomain (a : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ 2 * Real.pi ∧
    0 ≤ p.2.1 ∧ p.2.1 ≤ a ∧
    p.2.1 ≤ p.2.2 ∧
    p.2.2 ≤ a + Real.sqrt (a ^ 2 - p.2.1 ^ 2)}

def volume (a : ℝ) : ℝ :=
  ∫ _ in solid a, (1 : ℝ)

def endpointPrimitive (a r : ℝ) : ℝ :=
  2 * Real.pi *
    (a * r ^ 2 / 2 -
      Real.sqrt (a ^ 2 - r ^ 2) ^ 3 / 3 -
      r ^ 3 / 3)

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

theorem gap1 (a r z : ℝ) :
    r ^ 2 + z ^ 2 = 2 * a * z ↔
      (z - a) ^ 2 = a ^ 2 - r ^ 2 := by
  constructor <;> intro h <;> nlinarith

theorem gap2 (a r z : ℝ)
    (hr : 0 ≤ r) (hz : r ≤ z) :
    r ^ 2 ≤ z ^ 2 := by
  nlinarith

theorem gap3 (a : ℝ) (ha : 0 < a) :
    (fun p => cylindricalMap p.2.1 p.1 p.2.2) ''
        parameterDomain a =
      solid a := by
  ext q
  constructor
  · rintro ⟨⟨phi, r, z⟩, hp, rfl⟩
    rcases hp with ⟨_hphi0, _hphi1, hr0, hra, hzlower, hzupper⟩
    have hrad :
        (r * Real.cos phi) ^ 2 + (r * Real.sin phi) ^ 2 =
          r ^ 2 := by
      nlinarith [Real.cos_sq_add_sin_sq phi]
    have ht : 0 ≤ a ^ 2 - r ^ 2 := by nlinarith
    have hsqrt0 : 0 ≤ Real.sqrt (a ^ 2 - r ^ 2) :=
      Real.sqrt_nonneg _
    have hsqrtsq :
        Real.sqrt (a ^ 2 - r ^ 2) ^ 2 = a ^ 2 - r ^ 2 :=
      Real.sq_sqrt ht
    have hlowerRoot :
        a - Real.sqrt (a ^ 2 - r ^ 2) ≤ r := by
      nlinarith
    have hzlo :
        -Real.sqrt (a ^ 2 - r ^ 2) ≤ z - a := by
      linarith
    have hzhi :
        z - a ≤ Real.sqrt (a ^ 2 - r ^ 2) := by
      linarith
    have hzsquare :
        (z - a) ^ 2 ≤
          Real.sqrt (a ^ 2 - r ^ 2) ^ 2 :=
      sq_le_sq' hzlo hzhi
    change
      (r * Real.cos phi) ^ 2 + (r * Real.sin phi) ^ 2 +
            z ^ 2 ≤ 2 * a * z ∧
        (r * Real.cos phi) ^ 2 + (r * Real.sin phi) ^ 2 ≤ z ^ 2
    rw [hrad]
    exact ⟨by nlinarith, gap2 a r z hr0 hzlower⟩
  · rintro ⟨hsphere, hcone⟩
    rcases q with ⟨x, y, z⟩
    let r : ℝ := Real.sqrt (x ^ 2 + y ^ 2)
    have hxy0 : 0 ≤ x ^ 2 + y ^ 2 := by positivity
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hrsq : r ^ 2 = x ^ 2 + y ^ 2 :=
      Real.sq_sqrt hxy0
    have hsphere' : r ^ 2 + z ^ 2 ≤ 2 * a * z := by
      simpa [hrsq] using hsphere
    have hz0 : 0 ≤ z := by
      have hleft : 0 ≤ r ^ 2 + z ^ 2 := by positivity
      nlinarith
    have hrzsq : r ^ 2 ≤ z ^ 2 := by
      simpa [hrsq] using hcone
    have hrz : r ≤ z := by
      exact (sq_le_sq₀ hr0 hz0).1 hrzsq
    have hshift :
        (z - a) ^ 2 ≤ a ^ 2 - r ^ 2 := by
      nlinarith
    have hradicand : 0 ≤ a ^ 2 - r ^ 2 := by
      nlinarith [sq_nonneg (z - a)]
    have hrsqrt :
        r ≤ a := by
      nlinarith [sq_nonneg r, sq_nonneg a]
    have hzupper :
        z ≤ a + Real.sqrt (a ^ 2 - r ^ 2) := by
      have hsqrt0 := Real.sqrt_nonneg (a ^ 2 - r ^ 2)
      have hsqrtsq := Real.sq_sqrt hradicand
      nlinarith
    obtain ⟨phi, hphi0, hphi1, hx, hy⟩ :=
      exists_polar_angle x y
    refine ⟨(phi, r, z), ?_, ?_⟩
    · exact ⟨hphi0, hphi1, hr0, hrsqrt, hrz, hzupper⟩
    · ext <;> simp [cylindricalMap, r, hx, hy]

private def verticalSection (a : ℝ) (q : ℝ × ℝ) : Set ℝ :=
  let r := Real.sqrt (q.1 ^ 2 + q.2 ^ 2)
  if r ≤ a then
    Set.Icc r (a + Real.sqrt (a ^ 2 - r ^ 2))
  else ∅

private theorem mem_verticalSection_iff (a : ℝ) (ha : 0 < a)
    (q : ℝ × ℝ) (z : ℝ) :
    z ∈ verticalSection a q ↔
      q.1 ^ 2 + q.2 ^ 2 + z ^ 2 ≤ 2 * a * z ∧
        q.1 ^ 2 + q.2 ^ 2 ≤ z ^ 2 := by
  let r : ℝ := Real.sqrt (q.1 ^ 2 + q.2 ^ 2)
  have hxy0 : 0 ≤ q.1 ^ 2 + q.2 ^ 2 := by positivity
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = q.1 ^ 2 + q.2 ^ 2 :=
    Real.sq_sqrt hxy0
  by_cases hra : r ≤ a
  · have ht : 0 ≤ a ^ 2 - r ^ 2 := by nlinarith
    have hsqrt0 : 0 ≤ Real.sqrt (a ^ 2 - r ^ 2) :=
      Real.sqrt_nonneg _
    have hsqrtsq :
        Real.sqrt (a ^ 2 - r ^ 2) ^ 2 = a ^ 2 - r ^ 2 :=
      Real.sq_sqrt ht
    simp only [verticalSection, r, if_pos hra, Set.mem_Icc]
    constructor
    · rintro ⟨hzlower, hzupper⟩
      have hlowerRoot :
          a - Real.sqrt (a ^ 2 - r ^ 2) ≤ r := by
        nlinarith
      have hzlo :
          -Real.sqrt (a ^ 2 - r ^ 2) ≤ z - a := by
        linarith
      have hzhi :
          z - a ≤ Real.sqrt (a ^ 2 - r ^ 2) := by
        linarith
      have hzsquare :
          (z - a) ^ 2 ≤
            Real.sqrt (a ^ 2 - r ^ 2) ^ 2 :=
        sq_le_sq' hzlo hzhi
      have hz0 : 0 ≤ z := hr0.trans hzlower
      exact ⟨by nlinarith [hrsq], by
        have := gap2 a r z hr0 hzlower
        nlinarith [hrsq]⟩
    · rintro ⟨hsphere, hcone⟩
      have hsphere' : r ^ 2 + z ^ 2 ≤ 2 * a * z := by
        nlinarith [hrsq]
      have hz0 : 0 ≤ z := by
        have hleft : 0 ≤ r ^ 2 + z ^ 2 := by positivity
        nlinarith
      have hrzsq : r ^ 2 ≤ z ^ 2 := by nlinarith [hrsq]
      have hrz : r ≤ z := (sq_le_sq₀ hr0 hz0).1 hrzsq
      have hshift :
          (z - a) ^ 2 ≤ a ^ 2 - r ^ 2 := by
        nlinarith
      have hzupper :
          z ≤ a + Real.sqrt (a ^ 2 - r ^ 2) := by
        nlinarith
      exact ⟨hrz, hzupper⟩
  · have hra' : a < r := lt_of_not_ge hra
    simp only [verticalSection, r, if_neg hra, Set.mem_empty_iff_false]
    constructor
    · intro h
      contradiction
    · rintro ⟨hsphere, _hcone⟩
      have hsphere' : r ^ 2 + z ^ 2 ≤ 2 * a * z := by
        nlinarith [hrsq]
      have hshift :
          (z - a) ^ 2 + r ^ 2 ≤ a ^ 2 := by
        nlinarith
      nlinarith [sq_nonneg (z - a)]

private theorem solid_measurable (a : ℝ) :
    MeasurableSet (solid a) := by
  unfold solid
  measurability

private theorem solid_subset_box (a : ℝ) (ha : 0 < a) :
    solid a ⊆
      Set.Icc (-a) a ×ˢ
        (Set.Icc (-a) a ×ˢ Set.Icc (0 : ℝ) (2 * a)) := by
  rintro ⟨x, y, z⟩ ⟨hsphere, _hcone⟩
  have hxy0 : 0 ≤ x ^ 2 + y ^ 2 := by positivity
  have hz0 : 0 ≤ z := by
    nlinarith
  have hshift :
      x ^ 2 + y ^ 2 + (z - a) ^ 2 ≤ a ^ 2 := by
    nlinarith
  have hx2 : x ^ 2 ≤ a ^ 2 := by
    nlinarith [sq_nonneg y, sq_nonneg (z - a)]
  have hy2 : y ^ 2 ≤ a ^ 2 := by
    nlinarith [sq_nonneg x, sq_nonneg (z - a)]
  exact
    ⟨⟨by nlinarith, by nlinarith⟩,
      ⟨⟨by nlinarith, by nlinarith⟩,
        ⟨hz0, by nlinarith [sq_nonneg (z - a)]⟩⟩⟩

private theorem solid_indicator_integrable (a : ℝ) (ha : 0 < a) :
    Integrable
      ((solid a).indicator
        (fun _p : ℝ × ℝ × ℝ => (1 : ℝ)))
      MeasureTheory.volume := by
  have hbox :
      IntegrableOn (fun _p : ℝ × ℝ × ℝ => (1 : ℝ))
        (Set.Icc (-a) a ×ˢ
          (Set.Icc (-a) a ×ˢ Set.Icc (0 : ℝ) (2 * a)))
        MeasureTheory.volume :=
    ((continuous_const :
      Continuous (fun _p : ℝ × ℝ × ℝ => (1 : ℝ))).continuousOn).integrableOn_compact
        (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  exact
    (integrable_indicator_iff (solid_measurable a)).2
      (hbox.mono_set (solid_subset_box a ha))

private theorem volume_eq_integral_sections (a : ℝ) (ha : 0 < a) :
    volume a =
      ∫ q : ℝ × ℝ,
        ∫ _z in verticalSection a q, (1 : ℝ) := by
  classical
  let g : (ℝ × ℝ × ℝ) → ℝ :=
    (solid a).indicator (fun _p => (1 : ℝ))
  have hg : Integrable g MeasureTheory.volume :=
    solid_indicator_integrable a ha
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
        (solid_measurable a)]
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
      rw [← MeasureTheory.integral_indicator]
      · apply integral_congr_ae
        filter_upwards with z
        simp only [g]
        change
          (if (q.1, q.2, z) ∈ solid a then 1 else 0) =
            if z ∈ verticalSection a q then 1 else 0
        have hmem :
            (q.1, q.2, z) ∈ solid a ↔
              z ∈ verticalSection a q := by
          rw [mem_verticalSection_iff a ha q z]
          rfl
        rw [hmem]
      · unfold verticalSection
        dsimp only
        split_ifs <;> measurability

theorem gap4 (a : ℝ) (ha : 0 < a) :
    volume a =
      ∫ phi in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..a,
          ∫ z in r..a + Real.sqrt (a ^ 2 - r ^ 2), r := by
  have hpolar :
      (∫ q : ℝ × ℝ,
          ∫ _z in verticalSection a q, (1 : ℝ)) =
        (∫ r in Set.Ioi (0 : ℝ),
            r *
              ∫ _z in
                (if r ≤ a then
                  Set.Icc r (a + Real.sqrt (a ^ 2 - r ^ 2))
                else ∅),
                (1 : ℝ)) *
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
    simp only [polarCoord_symm_apply, smul_eq_mul, mul_one]
    unfold verticalSection
    dsimp only
    rw [hrad, Real.sqrt_sq hr.le]
  have hradial :
      (∫ r in Set.Ioi (0 : ℝ),
          r *
            ∫ _z in
              (if r ≤ a then
                Set.Icc r (a + Real.sqrt (a ^ 2 - r ^ 2))
              else ∅),
              (1 : ℝ)) =
        ∫ r in (0 : ℝ)..a,
          ∫ _z in r..a + Real.sqrt (a ^ 2 - r ^ 2), r := by
    calc
      (∫ r in Set.Ioi (0 : ℝ),
          r *
            ∫ _z in
              (if r ≤ a then
                Set.Icc r (a + Real.sqrt (a ^ 2 - r ^ 2))
              else ∅),
              (1 : ℝ)) =
          ∫ r in Set.Ioc (0 : ℝ) a,
            r *
              ∫ _z in
                (if r ≤ a then
                  Set.Icc r (a + Real.sqrt (a ^ 2 - r ^ 2))
                else ∅),
                (1 : ℝ) := by
        apply setIntegral_eq_of_subset_of_forall_diff_eq_zero
          measurableSet_Ioi Set.Ioc_subset_Ioi_self
        rintro r ⟨hr0, hrnot⟩
        have hrpos : 0 < r := by simpa using hr0
        have hra : ¬r ≤ a := by
          simpa only [Set.mem_Ioc, hrpos, true_and] using hrnot
        simp [hra]
      _ = ∫ r in Set.Ioc (0 : ℝ) a,
            ∫ _z in r..a + Real.sqrt (a ^ 2 - r ^ 2), r := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro r hr
        have hr0 : 0 < r := hr.1
        have hra : r ≤ a := hr.2
        have ht : 0 ≤ a ^ 2 - r ^ 2 := by nlinarith
        have hsqrt0 : 0 ≤ Real.sqrt (a ^ 2 - r ^ 2) :=
          Real.sqrt_nonneg _
        have hlower :
            r ≤ a + Real.sqrt (a ^ 2 - r ^ 2) := by
          nlinarith
        simp only [if_pos hra]
        change
          r *
              (∫ _z in
                Set.Icc r (a + Real.sqrt (a ^ 2 - r ^ 2)),
                (1 : ℝ)) =
            ∫ _z in r..a + Real.sqrt (a ^ 2 - r ^ 2), r
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
          intervalIntegral.integral_of_le hlower,
          ← MeasureTheory.integral_const_mul]
        simp
      _ = ∫ r in (0 : ℝ)..a,
            ∫ _z in r..a + Real.sqrt (a ^ 2 - r ^ 2), r := by
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

theorem gap5 (a : ℝ) (ha : 0 < a) :
    volume a =
      2 * Real.pi *
        ∫ r in (0 : ℝ)..a,
          r * (a + Real.sqrt (a ^ 2 - r ^ 2) - r) := by
  rw [gap4 a ha]
  have hinner (r : ℝ) :
      (∫ _z in r..a + Real.sqrt (a ^ 2 - r ^ 2), r) =
        r * (a + Real.sqrt (a ^ 2 - r ^ 2) - r) := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  simp_rw [hinner]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem gap6 (a : ℝ) (ha : 0 < a) :
    2 * Real.pi *
        (∫ r in (0 : ℝ)..a,
          r * (a + Real.sqrt (a ^ 2 - r ^ 2) - r)) =
      endpointPrimitive a a - endpointPrimitive a 0 := by
  let F : ℝ → ℝ :=
    fun r =>
      2 * Real.pi *
        (a * r ^ 2 / 2 -
          Real.rpow (a ^ 2 - r ^ 2) (3 / 2 : ℝ) / 3 -
          r ^ 3 / 3)
  have hFcont : ContinuousOn F (Set.Icc (0 : ℝ) a) := by
    apply Continuous.continuousOn
    have hbasecont :
        Continuous (fun r : ℝ => a ^ 2 - r ^ 2) :=
      continuous_const.sub (continuous_id.pow 2)
    have hrpowcont :
        Continuous
          (fun r : ℝ =>
            Real.rpow (a ^ 2 - r ^ 2) (3 / 2 : ℝ)) :=
      hbasecont.rpow_const
        (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 3 / 2))
    exact continuous_const.mul
      ((((continuous_const.mul (continuous_id.pow 2)).div_const 2).sub
        (hrpowcont.div_const 3)).sub
        ((continuous_id.pow 3).div_const 3))
  have hFderiv :
      ∀ r ∈ Set.Ioo (0 : ℝ) a,
        HasDerivAt F
          (2 * Real.pi *
            (r * (a + Real.sqrt (a ^ 2 - r ^ 2) - r))) r := by
    intro r _hr
    have hbase :
        HasDerivAt (fun x : ℝ => a ^ 2 - x ^ 2) (-2 * r) r := by
      convert (hasDerivAt_const r (a ^ 2)).sub
        ((hasDerivAt_id r).pow 2) using 1 <;> simp <;> ring
    have hrpow :=
      hbase.rpow_const (p := (3 / 2 : ℝ))
        (Or.inr (by norm_num : (1 : ℝ) ≤ 3 / 2))
    have hpoly :
        HasDerivAt
          (fun x : ℝ =>
            a * x ^ 2 / 2 -
              Real.rpow (a ^ 2 - x ^ 2) (3 / 2 : ℝ) / 3 -
              x ^ 3 / 3)
          (r * (a + Real.sqrt (a ^ 2 - r ^ 2) - r)) r := by
      convert
        (((hasDerivAt_id r).pow 2).const_mul a |>.div_const 2).sub
          (hrpow.div_const 3) |>.sub
          (((hasDerivAt_id r).pow 3).div_const 3) using 1 <;>
        norm_num [Real.sqrt_eq_rpow] <;> ring
    simpa [F] using hpoly.const_mul (2 * Real.pi)
  have hint :
      IntervalIntegrable
        (fun r : ℝ =>
          2 * Real.pi *
            (r * (a + Real.sqrt (a ^ 2 - r ^ 2) - r)))
        MeasureTheory.volume 0 a := by
    exact
      (continuous_const.mul
        (continuous_id.mul
          ((continuous_const.add
            (Real.continuous_sqrt.comp
              (continuous_const.sub (continuous_id.pow 2)))).sub
            continuous_id))).intervalIntegrable 0 a
  have hFTC :
      (∫ r in (0 : ℝ)..a,
          2 * Real.pi *
            (r * (a + Real.sqrt (a ^ 2 - r ^ 2) - r))) =
        F a - F 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      ha.le hFcont hFderiv hint
  rw [← intervalIntegral.integral_const_mul, hFTC]
  have hpow (r : ℝ) (hr : 0 ≤ a ^ 2 - r ^ 2) :
      Real.rpow (a ^ 2 - r ^ 2) (3 / 2 : ℝ) =
        Real.sqrt (a ^ 2 - r ^ 2) ^ 3 := by
    rw [Real.sqrt_eq_rpow]
    calc
      Real.rpow (a ^ 2 - r ^ 2) (3 / 2 : ℝ) =
          Real.rpow (a ^ 2 - r ^ 2) ((1 / 2 : ℝ) * 3) := by
            norm_num
      _ = Real.rpow (Real.rpow (a ^ 2 - r ^ 2) (1 / 2 : ℝ))
          (3 : ℝ) := Real.rpow_mul hr _ _
      _ = Real.rpow (a ^ 2 - r ^ 2) (1 / 2 : ℝ) ^ 3 := by
        exact Real.rpow_natCast _ 3
  have haa : 0 ≤ a ^ 2 - a ^ 2 := by norm_num
  have ha0 : 0 ≤ a ^ 2 - (0 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg a]
  have hFa : F a = endpointPrimitive a a := by
    simp only [F, endpointPrimitive]
    rw [hpow a haa]
  have hF0 : F 0 = endpointPrimitive a 0 := by
    simp only [F, endpointPrimitive]
    rw [hpow 0 ha0]
  rw [hFa, hF0]

theorem gap7 (a : ℝ) (ha : 0 < a) :
    endpointPrimitive a a - endpointPrimitive a 0 =
      Real.pi * a ^ 3 := by
  have ha0 : 0 ≤ a := ha.le
  simp only [endpointPrimitive]
  rw [show a ^ 2 - a ^ 2 = 0 by ring,
    Real.sqrt_zero, show a ^ 2 - (0 : ℝ) ^ 2 = a ^ 2 by ring,
    Real.sqrt_sq ha0]
  ring

theorem gap8 (a : ℝ) (ha : 0 < a) :
    volume a = Real.pi * a ^ 3 := by
  rw [gap5 a ha, gap6 a ha, gap7 a ha]

end

end ProofGap.Exercise4107
