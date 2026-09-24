import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4113

noncomputable section

open MeasureTheory
open scoped Interval

def region (a b c : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 ^ 2 / a ^ 2 + p.2.1 ^ 2 / b ^ 2 +
      p.2.2 ^ 2 / c ^ 2 ≤ 1 ∧
    p.1 ^ 2 / a ^ 2 + p.2.1 ^ 2 / b ^ 2 ≤ p.2.2 / c}

def radialLimit : ℝ :=
  Real.sqrt ((Real.sqrt 5 - 1) / 2)

def volume (a b c : ℝ) : ℝ :=
  ∫ _ in region a b c, (1 : ℝ)

def endpointPrimitive (a b c r : ℝ) : ℝ :=
  2 * Real.pi * a * b * c *
    (-(Real.sqrt (1 - r ^ 2) ^ 3 / 3) - r ^ 4 / 4)

theorem gap1 (r : ℝ) :
    r ^ 2 = Real.sqrt (1 - r ^ 2) ↔
      r ^ 4 + r ^ 2 - 1 = 0 := by
  constructor
  · intro h
    have hrad : 0 ≤ 1 - r ^ 2 := by
      by_contra hn
      have hsqrt : Real.sqrt (1 - r ^ 2) = 0 :=
        Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hn)
      rw [hsqrt] at h
      nlinarith [sq_nonneg r]
    have hsquare :
        Real.sqrt (1 - r ^ 2) ^ 2 = 1 - r ^ 2 :=
      Real.sq_sqrt hrad
    nlinarith
  · intro h
    have hrad :
        1 - r ^ 2 = (r ^ 2) ^ 2 := by
      nlinarith
    rw [hrad, Real.sqrt_sq (sq_nonneg r)]

theorem gap2 (r : ℝ) (hr : 0 ≤ r)
    (heq : r ^ 4 + r ^ 2 - 1 = 0) :
    r = radialLimit := by
  have hfive : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt5 : 0 ≤ Real.sqrt 5 :=
    Real.sqrt_nonneg _
  have hlinear :
      2 * r ^ 2 + 1 = Real.sqrt 5 := by
    have hsq :
        (2 * r ^ 2 + 1) ^ 2 = (Real.sqrt 5) ^ 2 := by
      nlinarith
    nlinarith [sq_nonneg r]
  have hr2 :
      r ^ 2 = (Real.sqrt 5 - 1) / 2 := by
    linarith
  calc
    r = Real.sqrt (r ^ 2) := by
      rw [Real.sqrt_sq hr]
    _ = radialLimit := by
      rw [hr2]
      rfl

private def normalizedRadius (a b : ℝ) (q : ℝ × ℝ) : ℝ :=
  q.1 ^ 2 / a ^ 2 + q.2 ^ 2 / b ^ 2

private def verticalSection (a b c : ℝ) (q : ℝ × ℝ) : Set ℝ :=
  if normalizedRadius a b q ≤ 1 then
    Set.Icc
      (c * normalizedRadius a b q)
      (c * Real.sqrt (1 - normalizedRadius a b q))
  else ∅

private def planarScale (a b : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (a * p.1, b * p.2)

private def planarScaleFDeriv (a b : ℝ) :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![a, 0; 0, b]).toContinuousLinearMap

private theorem hasFDerivAt_planarScale (a b : ℝ) (p : ℝ × ℝ) :
    HasFDerivAt (planarScale a b) (planarScaleFDeriv a b) p := by
  unfold planarScaleFDeriv planarScale
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  convert HasFDerivAt.prodMk
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).const_mul a)
    ((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).const_mul b) using 1 <;>
    ext <;> simp

private theorem det_planarScaleFDeriv (a b : ℝ) :
    (planarScaleFDeriv a b).det = a * b := by
  unfold planarScaleFDeriv
  simp only [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of]
  ring

private theorem planarScale_injective (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    Function.Injective (planarScale a b) := by
  rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
  simp only [planarScale, Prod.mk.injEq] at h
  exact Prod.ext (mul_left_cancel₀ ha h.1) (mul_left_cancel₀ hb h.2)

private theorem planarScale_surjective (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    Function.Surjective (planarScale a b) := by
  rintro ⟨x, y⟩
  refine ⟨(x / a, y / b), ?_⟩
  apply Prod.ext
  · dsimp [planarScale]
    field_simp
  · dsimp [planarScale]
    field_simp

private theorem square_le_iff_mem (c t z : ℝ)
    (hc : 0 < c) (ht : 0 ≤ t) :
    z ^ 2 / c ^ 2 ≤ t ↔
      -c * Real.sqrt t ≤ z ∧ z ≤ c * Real.sqrt t := by
  have hs0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
  have hcs0 : 0 ≤ c * Real.sqrt t :=
    mul_nonneg hc.le hs0
  have hs2 : Real.sqrt t ^ 2 = t :=
    Real.sq_sqrt ht
  have hmul :
      t * c ^ 2 = (c * Real.sqrt t) ^ 2 := by
    nlinarith
  have hscale :
      z ^ 2 / c ^ 2 ≤ t ↔
        z ^ 2 ≤ (c * Real.sqrt t) ^ 2 := by
    constructor
    · intro h
      have h' : z ^ 2 ≤ t * c ^ 2 :=
        (div_le_iff₀ (sq_pos_of_pos hc)).1 h
      exact h'.trans_eq hmul
    · intro h
      apply (div_le_iff₀ (sq_pos_of_pos hc)).2
      exact h.trans_eq hmul.symm
  rw [hscale]
  have habspow : |z| ^ 2 = z ^ 2 := by
    rw [← abs_pow, abs_of_nonneg (sq_nonneg z)]
  rw [← habspow,
    pow_le_pow_iff_left₀ (abs_nonneg z) hcs0
      (by norm_num : (2 : ℕ) ≠ 0)]
  simpa [neg_mul] using
    (abs_le : |z| ≤ c * Real.sqrt t ↔
      -(c * Real.sqrt t) ≤ z ∧ z ≤ c * Real.sqrt t)

private theorem normalizedRadius_nonneg (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (q : ℝ × ℝ) :
    0 ≤ normalizedRadius a b q := by
  unfold normalizedRadius
  positivity

private theorem mem_verticalSection_iff (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (q : ℝ × ℝ) (z : ℝ) :
    z ∈ verticalSection a b c q ↔
      normalizedRadius a b q + z ^ 2 / c ^ 2 ≤ 1 ∧
        normalizedRadius a b q ≤ z / c := by
  have hs0 := normalizedRadius_nonneg a b ha hb q
  by_cases hs1 : normalizedRadius a b q ≤ 1
  · have ht : 0 ≤ 1 - normalizedRadius a b q :=
      sub_nonneg.2 hs1
    simp only [verticalSection, if_pos hs1, Set.mem_Icc]
    constructor
    · rintro ⟨hlower, hupper⟩
      have hz0 : 0 ≤ z := by
        exact (mul_nonneg hc.le hs0).trans hlower
      have hnegative :
          -c * Real.sqrt (1 - normalizedRadius a b q) ≤ z := by
        have : 0 ≤ c * Real.sqrt (1 - normalizedRadius a b q) :=
          mul_nonneg hc.le (Real.sqrt_nonneg _)
        linarith
      have hzsq :
          z ^ 2 / c ^ 2 ≤
            1 - normalizedRadius a b q :=
        (square_le_iff_mem c
          (1 - normalizedRadius a b q) z hc ht).2
          ⟨hnegative, hupper⟩
      have hsecond :
          normalizedRadius a b q ≤ z / c := by
        apply (le_div_iff₀ hc).2
        simpa [mul_comm] using hlower
      exact ⟨by linarith, hsecond⟩
    · rintro ⟨hball, hcone⟩
      have hzsq :
          z ^ 2 / c ^ 2 ≤
            1 - normalizedRadius a b q := by
        linarith
      have hbnds :=
        (square_le_iff_mem c
          (1 - normalizedRadius a b q) z hc ht).1 hzsq
      have hlower := (le_div_iff₀ hc).1 hcone
      exact ⟨by simpa [mul_comm] using hlower, hbnds.2⟩
  · have hs1' : 1 < normalizedRadius a b q :=
      lt_of_not_ge hs1
    simp only [verticalSection, if_neg hs1,
      Set.mem_empty_iff_false, false_iff]
    rintro ⟨hball, _hcone⟩
    have hzsq : 0 ≤ z ^ 2 / c ^ 2 := by positivity
    linarith

private theorem region_measurable (a b c : ℝ) :
    MeasurableSet (region a b c) := by
  unfold region
  measurability

private theorem region_subset_box (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    region a b c ⊆
      Set.Icc (-a) a ×ˢ
        (Set.Icc (-b) b ×ˢ Set.Icc (-c) c) := by
  rintro ⟨x, y, z⟩ ⟨hball, _hcone⟩
  change
    x ^ 2 / a ^ 2 + y ^ 2 / b ^ 2 +
      z ^ 2 / c ^ 2 ≤ 1 at hball
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have hxnonneg : 0 ≤ x ^ 2 / a ^ 2 := by positivity
  have hynonneg : 0 ≤ y ^ 2 / b ^ 2 := by positivity
  have hznonneg : 0 ≤ z ^ 2 / c ^ 2 := by positivity
  have hxdiv : x ^ 2 / a ^ 2 ≤ 1 := by linarith
  have hydiv : y ^ 2 / b ^ 2 ≤ 1 := by linarith
  have hzdiv : z ^ 2 / c ^ 2 ≤ 1 := by linarith
  have hx2 : x ^ 2 ≤ a ^ 2 := (div_le_one ha2).1 hxdiv
  have hy2 : y ^ 2 ≤ b ^ 2 := (div_le_one hb2).1 hydiv
  have hz2 : z ^ 2 ≤ c ^ 2 := (div_le_one hc2).1 hzdiv
  exact
    ⟨⟨by nlinarith, by nlinarith⟩,
      ⟨⟨by nlinarith, by nlinarith⟩,
        ⟨by nlinarith, by nlinarith⟩⟩⟩

private theorem region_indicator_integrable (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Integrable
      ((region a b c).indicator
        (fun _p : ℝ × ℝ × ℝ => (1 : ℝ)))
      MeasureTheory.volume := by
  have hbox :
      IntegrableOn (fun _p : ℝ × ℝ × ℝ => (1 : ℝ))
        (Set.Icc (-a) a ×ˢ
          (Set.Icc (-b) b ×ˢ Set.Icc (-c) c))
        MeasureTheory.volume :=
    ((continuous_const :
      Continuous (fun _p : ℝ × ℝ × ℝ => (1 : ℝ))).continuousOn).integrableOn_compact
        (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  exact
    (integrable_indicator_iff (region_measurable a b c)).2
      (hbox.mono_set (region_subset_box a b c ha hb hc))

private theorem volume_eq_integral_sections (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      ∫ q : ℝ × ℝ,
        ∫ _z in verticalSection a b c q, (1 : ℝ) := by
  classical
  let g : (ℝ × ℝ × ℝ) → ℝ :=
    (region a b c).indicator (fun _p => (1 : ℝ))
  have hg : Integrable g MeasureTheory.volume :=
    region_indicator_integrable a b c ha hb hc
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
    volume a b c =
        ∫ p : ℝ × ℝ × ℝ, g p := by
      rw [volume, MeasureTheory.integral_indicator
        (region_measurable a b c)]
    _ = ∫ p : (ℝ × ℝ) × ℝ,
          g (p.1.1, p.1.2, p.2) := by
      symm
      simpa [Function.comp_def] using hp.integral_comp' g
    _ = ∫ q : ℝ × ℝ, ∫ z : ℝ,
          g (q.1, q.2, z) := hfubini
    _ = ∫ q : ℝ × ℝ,
          ∫ _z in verticalSection a b c q, (1 : ℝ) := by
      apply integral_congr_ae
      filter_upwards with q
      rw [← MeasureTheory.integral_indicator]
      · apply integral_congr_ae
        filter_upwards with z
        have hmem :
            (q.1, q.2, z) ∈ region a b c ↔
              z ∈ verticalSection a b c q := by
          rw [mem_verticalSection_iff a b c ha hb hc q z]
          rfl
        simp only [g, Set.indicator_apply, hmem]
      · unfold verticalSection
        split_ifs <;> measurability

private theorem integral_scale_plane (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (f : ℝ × ℝ → ℝ) :
    (∫ q : ℝ × ℝ, f q) =
      a * b * ∫ p : ℝ × ℝ, f (planarScale a b p) := by
  have himage :
      planarScale a b '' (Set.univ : Set (ℝ × ℝ)) = Set.univ := by
    exact Set.image_univ.trans
      (Set.range_eq_univ.mpr
        (planarScale_surjective a b ha.ne' hb.ne'))
  have hchange :=
    integral_image_eq_integral_abs_det_fderiv_smul
      (μ := (MeasureTheory.volume : Measure (ℝ × ℝ)))
      (f := planarScale a b)
      (f' := fun _ => planarScaleFDeriv a b)
      MeasurableSet.univ
      (fun p _ => (hasFDerivAt_planarScale a b p).hasFDerivWithinAt)
      (planarScale_injective a b ha.ne' hb.ne').injOn f
  rw [himage] at hchange
  have hchange' :
      (∫ q : ℝ × ℝ, f q) =
        ∫ p : ℝ × ℝ,
          |(planarScaleFDeriv a b).det| •
            f (planarScale a b p) := by
    simpa using hchange
  rw [det_planarScaleFDeriv,
    abs_of_pos (mul_pos ha hb)] at hchange'
  simp only [smul_eq_mul,
    MeasureTheory.integral_const_mul] at hchange'
  exact hchange'

private theorem radialLimit_pos : 0 < radialLimit := by
  have hfive : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt5 : 0 ≤ Real.sqrt 5 :=
    Real.sqrt_nonneg _
  have ht : 0 < (Real.sqrt 5 - 1) / 2 := by
    nlinarith
  exact Real.sqrt_pos.2 ht

private theorem radialLimit_poly :
    radialLimit ^ 4 + radialLimit ^ 2 - 1 = 0 := by
  have hfive : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt5 : 0 ≤ Real.sqrt 5 :=
    Real.sqrt_nonneg _
  have ht : 0 ≤ (Real.sqrt 5 - 1) / 2 := by
    nlinarith
  have hsq :
      radialLimit ^ 2 = (Real.sqrt 5 - 1) / 2 := by
    exact Real.sq_sqrt ht
  rw [show radialLimit ^ 4 = (radialLimit ^ 2) ^ 2 by ring,
    hsq]
  nlinarith

private theorem radialLimit_le_one :
    radialLimit ≤ 1 := by
  have hnonneg : 0 ≤ radialLimit := radialLimit_pos.le
  have hp := radialLimit_poly
  nlinarith [sq_nonneg radialLimit]

theorem gap3 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      ∫ phi in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..radialLimit,
          ∫ z in c * r ^ 2..c * Real.sqrt (1 - r ^ 2),
            a * b * r := by
  have hnorm (r phi : ℝ) :
      normalizedRadius a b
          (planarScale a b (polarCoord.symm (r, phi))) =
        r ^ 2 := by
    have hx :
        (a * (r * Real.cos phi)) ^ 2 / a ^ 2 =
          (r * Real.cos phi) ^ 2 := by
      field_simp [ha.ne']
    have hy :
        (b * (r * Real.sin phi)) ^ 2 / b ^ 2 =
          (r * Real.sin phi) ^ 2 := by
      field_simp [hb.ne']
    simp only [normalizedRadius, planarScale, polarCoord_symm_apply]
    rw [hx, hy]
    nlinarith [Real.cos_sq_add_sin_sq phi]
  have hpolar :
      (∫ p : ℝ × ℝ,
          ∫ _z in verticalSection a b c
            (planarScale a b p), (1 : ℝ)) =
        (∫ r in Set.Ioi (0 : ℝ),
            r *
              ∫ _z in
                (if r ^ 2 ≤ 1 then
                  Set.Icc
                    (c * r ^ 2)
                    (c * Real.sqrt (1 - r ^ 2))
                else ∅),
                (1 : ℝ)) *
          ∫ _phi in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
    rw [← integral_comp_polarCoord_symm, polarCoord_target]
    rw [← setIntegral_prod_mul]
    apply setIntegral_congr_fun
      (measurableSet_Ioi.prod measurableSet_Ioo)
    rintro ⟨r, phi⟩ ⟨_hr, _hphi⟩
    simp only [polarCoord_symm_apply, smul_eq_mul, mul_one]
    have hn := hnorm r phi
    simp only [polarCoord_symm_apply] at hn
    have hsection :
        verticalSection a b c
            (planarScale a b
              (r * Real.cos phi, r * Real.sin phi)) =
          if r ^ 2 ≤ 1 then
            Set.Icc
              (c * r ^ 2)
              (c * Real.sqrt (1 - r ^ 2))
          else ∅ := by
      unfold verticalSection
      rw [hn]
    rw [hsection]
  have hradial :
      (∫ r in Set.Ioi (0 : ℝ),
          r *
            ∫ _z in
              (if r ^ 2 ≤ 1 then
                Set.Icc
                  (c * r ^ 2)
                  (c * Real.sqrt (1 - r ^ 2))
              else ∅),
              (1 : ℝ)) =
        ∫ r in (0 : ℝ)..radialLimit,
          ∫ _z in
            c * r ^ 2..c * Real.sqrt (1 - r ^ 2),
            r := by
    calc
      (∫ r in Set.Ioi (0 : ℝ),
          r *
            ∫ _z in
              (if r ^ 2 ≤ 1 then
                Set.Icc
                  (c * r ^ 2)
                  (c * Real.sqrt (1 - r ^ 2))
              else ∅),
              (1 : ℝ)) =
          ∫ r in Set.Ioc (0 : ℝ) radialLimit,
            r *
              ∫ _z in
                (if r ^ 2 ≤ 1 then
                  Set.Icc
                    (c * r ^ 2)
                    (c * Real.sqrt (1 - r ^ 2))
                else ∅),
                (1 : ℝ) := by
        apply setIntegral_eq_of_subset_of_forall_diff_eq_zero
          measurableSet_Ioi Set.Ioc_subset_Ioi_self
        rintro r ⟨hr0, hrnot⟩
        have hrpos : 0 < r := by simpa using hr0
        have hLr : radialLimit < r := by
          simp only [Set.mem_Ioc, hrpos, true_and] at hrnot
          exact lt_of_not_ge hrnot
        by_cases hrsq : r ^ 2 ≤ 1
        · have hL2r2 : radialLimit ^ 2 < r ^ 2 :=
            (sq_lt_sq₀ radialLimit_pos.le hrpos.le).2 hLr
          have hL4r4 : radialLimit ^ 4 < r ^ 4 := by
            rw [show radialLimit ^ 4 =
                (radialLimit ^ 2) ^ 2 by ring,
              show r ^ 4 = (r ^ 2) ^ 2 by ring]
            exact
              (sq_lt_sq₀ (sq_nonneg radialLimit)
                (sq_nonneg r)).2 hL2r2
          have hpoly :
              1 < r ^ 4 + r ^ 2 := by
            nlinarith [radialLimit_poly]
          have hrad : 0 ≤ 1 - r ^ 2 :=
            sub_nonneg.2 hrsq
          have hsquare :
              Real.sqrt (1 - r ^ 2) ^ 2 =
                1 - r ^ 2 :=
            Real.sq_sqrt hrad
          have hslt :
              Real.sqrt (1 - r ^ 2) < r ^ 2 := by
            nlinarith [Real.sqrt_nonneg (1 - r ^ 2)]
          have hempty :
              c * Real.sqrt (1 - r ^ 2) < c * r ^ 2 :=
            mul_lt_mul_of_pos_left hslt hc
          rw [if_pos hrsq,
            Set.Icc_eq_empty (not_le_of_gt hempty)]
          simp
        · simp [hrsq]
      _ = ∫ r in Set.Ioc (0 : ℝ) radialLimit,
            ∫ _z in
              c * r ^ 2..c * Real.sqrt (1 - r ^ 2),
              r := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro r hr
        have hr0 : 0 < r := hr.1
        have hrL : r ≤ radialLimit := hr.2
        have hr2L2 :
            r ^ 2 ≤ radialLimit ^ 2 :=
          (sq_le_sq₀ hr0.le radialLimit_pos.le).2 hrL
        have hr1 : r ≤ 1 :=
          hrL.trans radialLimit_le_one
        have hrsq : r ^ 2 ≤ 1 := by
          nlinarith
        have hr4L4 : r ^ 4 ≤ radialLimit ^ 4 := by
          rw [show r ^ 4 = (r ^ 2) ^ 2 by ring,
            show radialLimit ^ 4 =
              (radialLimit ^ 2) ^ 2 by ring]
          exact
            (sq_le_sq₀ (sq_nonneg r)
              (sq_nonneg radialLimit)).2 hr2L2
        have hpoly :
            r ^ 4 + r ^ 2 ≤ 1 := by
          nlinarith [radialLimit_poly]
        have hrad : 0 ≤ 1 - r ^ 2 :=
          sub_nonneg.2 hrsq
        have hsquare :
            Real.sqrt (1 - r ^ 2) ^ 2 =
              1 - r ^ 2 :=
          Real.sq_sqrt hrad
        have hsle :
            r ^ 2 ≤ Real.sqrt (1 - r ^ 2) := by
          nlinarith [Real.sqrt_nonneg (1 - r ^ 2)]
        have hlower :
            c * r ^ 2 ≤
              c * Real.sqrt (1 - r ^ 2) :=
          mul_le_mul_of_nonneg_left hsle hc.le
        simp only [if_pos hrsq]
        change
          r *
              (∫ _z in
                Set.Icc
                  (c * r ^ 2)
                  (c * Real.sqrt (1 - r ^ 2)),
                (1 : ℝ)) =
            ∫ _z in
              c * r ^ 2..c * Real.sqrt (1 - r ^ 2),
              r
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
          intervalIntegral.integral_of_le hlower,
          ← MeasureTheory.integral_const_mul]
        simp
      _ = ∫ r in (0 : ℝ)..radialLimit,
            ∫ _z in
              c * r ^ 2..c * Real.sqrt (1 - r ^ 2),
              r := by
        rw [intervalIntegral.integral_of_le radialLimit_pos.le]
  have hangle :
      (∫ _phi in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ)) =
        2 * Real.pi := by
    simp only [integral_const, MeasurableSet.univ,
      measureReal_restrict_apply, Set.univ_inter,
      smul_eq_mul, mul_one]
    rw [Real.volume_real_Ioo_of_le
      (by linarith [Real.pi_nonneg])]
    ring
  rw [volume_eq_integral_sections a b c ha hb hc,
    integral_scale_plane a b ha hb, hpolar, hradial, hangle]
  have hinner (r : ℝ) :
      (∫ _z in
          c * r ^ 2..c * Real.sqrt (1 - r ^ 2),
          a * b * r) =
        a * b *
          ∫ _z in
            c * r ^ 2..c * Real.sqrt (1 - r ^ 2),
            r := by
    rw [intervalIntegral.integral_const_mul]
  simp_rw [hinner]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem gap4 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      2 * Real.pi * a * b * c *
        ∫ r in (0 : ℝ)..radialLimit,
          r * (Real.sqrt (1 - r ^ 2) - r ^ 2) := by
  rw [gap3 a b c ha hb hc]
  have hinner (r : ℝ) :
      (∫ _z in
          c * r ^ 2..c * Real.sqrt (1 - r ^ 2),
          a * b * r) =
        a * b * c *
          (r * (Real.sqrt (1 - r ^ 2) - r ^ 2)) := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  simp_rw [hinner]
  rw [intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul]
  simp only [smul_eq_mul]
  ring

theorem gap5 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      endpointPrimitive a b c radialLimit -
        endpointPrimitive a b c 0 := by
  let F : ℝ → ℝ :=
    fun r =>
      -(Real.sqrt (1 - r ^ 2) ^ 3 / 3) -
        r ^ 4 / 4
  have hLlt : radialLimit < 1 := by
    apply lt_of_le_of_ne radialLimit_le_one
    intro h
    have h' : radialLimit = 1 := by linarith
    have hp := radialLimit_poly
    rw [h'] at hp
    norm_num at hp
  have hcont :
      ContinuousOn F (Set.Icc (0 : ℝ) radialLimit) := by
    exact (by fun_prop : Continuous F).continuousOn
  have hderiv :
      ∀ r ∈ Set.Ioo (0 : ℝ) radialLimit,
        HasDerivAt F
          (r * (Real.sqrt (1 - r ^ 2) - r ^ 2)) r := by
    intro r hr
    have hr1 : r < 1 := hr.2.trans hLlt
    have hpos : 0 < 1 - r ^ 2 := by
      have hr2 : r ^ 2 < (1 : ℝ) ^ 2 :=
        (sq_lt_sq₀ hr.1.le (by norm_num)).2 hr1
      nlinarith
    have hinner :
        HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * r) r := by
      convert
        (hasDerivAt_const r 1).sub
          ((hasDerivAt_id r).pow 2) using 1 <;>
        simp only [id_eq] <;> ring
    have hsqrt :
        HasDerivAt
          (fun x : ℝ => Real.sqrt (1 - x ^ 2))
          (1 / (2 * Real.sqrt (1 - r ^ 2)) *
            (-2 * r)) r := by
      simpa only [Function.comp_apply] using
        (Real.hasDerivAt_sqrt hpos.ne').comp r hinner
    have hsquare :
        Real.sqrt (1 - r ^ 2) ^ 2 =
          1 - r ^ 2 :=
      Real.sq_sqrt hpos.le
    have hraw :
        HasDerivAt F
          (-(3 * Real.sqrt (1 - r ^ 2) ^ 2 *
                (1 / (2 * Real.sqrt (1 - r ^ 2)) *
                  (-2 * r)) / 3) -
            4 * r ^ 3 / 4) r := by
      dsimp [F]
      convert
        ((hsqrt.pow 3).div_const 3).neg.sub
          (((hasDerivAt_id r).pow 4).div_const 4) using 1 <;>
        simp only [id_eq] <;> ring
    apply hraw.congr_deriv
    field_simp [Real.sqrt_ne_zero'.mpr hpos]
  have hint :
      IntervalIntegrable
        (fun r : ℝ =>
          r * (Real.sqrt (1 - r ^ 2) - r ^ 2))
        MeasureTheory.volume 0 radialLimit :=
    (by fun_prop : Continuous
      (fun r : ℝ =>
        r * (Real.sqrt (1 - r ^ 2) - r ^ 2))).intervalIntegrable _ _
  have hFTC :
      (∫ r in (0 : ℝ)..radialLimit,
          r * (Real.sqrt (1 - r ^ 2) - r ^ 2)) =
        F radialLimit - F 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      radialLimit_pos.le hcont hderiv hint
  rw [gap4 a b c ha hb hc, hFTC]
  simp only [endpointPrimitive, F]
  ring

theorem gap6 (a b c : ℝ) :
    endpointPrimitive a b c radialLimit -
        endpointPrimitive a b c 0 =
      5 * Real.pi * a * b * c * (3 - Real.sqrt 5) / 12 := by
  have hroot :
      radialLimit ^ 2 =
        Real.sqrt (1 - radialLimit ^ 2) :=
    (gap1 radialLimit).2 radialLimit_poly
  have hfive :
      Real.sqrt 5 ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt5 : 0 ≤ Real.sqrt 5 :=
    Real.sqrt_nonneg _
  have ht : 0 ≤ (Real.sqrt 5 - 1) / 2 := by
    nlinarith
  have hLsq :
      radialLimit ^ 2 =
        (Real.sqrt 5 - 1) / 2 := by
    exact Real.sq_sqrt ht
  have hfive3 :
      Real.sqrt 5 ^ 3 = 5 * Real.sqrt 5 := by
    calc
      Real.sqrt 5 ^ 3 =
          Real.sqrt 5 ^ 2 * Real.sqrt 5 := by ring
      _ = 5 * Real.sqrt 5 := by rw [hfive]
  unfold endpointPrimitive
  rw [← hroot]
  rw [show radialLimit ^ 4 =
      (radialLimit ^ 2) ^ 2 by ring, hLsq]
  norm_num
  ring_nf
  rw [hfive, hfive3]
  ring

theorem gap7 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      5 * Real.pi * a * b * c * (3 - Real.sqrt 5) / 12 := by
  rw [gap5 a b c ha hb hc, gap6]

end

end ProofGap.Exercise4113
