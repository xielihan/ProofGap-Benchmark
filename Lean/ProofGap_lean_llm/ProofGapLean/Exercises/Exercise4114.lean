import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4114

noncomputable section

open MeasureTheory
open scoped Interval

def region (a b c : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 ^ 2 / a ^ 2 + p.2.1 ^ 2 / b ^ 2 +
      p.2.2 ^ 4 / c ^ 4 ≤ 1}

def ellipticPolarMap (a b r phi z : ℝ) : ℝ × ℝ × ℝ :=
  (a * r * Real.cos phi, b * r * Real.sin phi, z)

def quarterPower (t : ℝ) : ℝ :=
  Real.rpow t (1 / 4 : ℝ)

def fiveQuarterPower (t : ℝ) : ℝ :=
  Real.rpow t (5 / 4 : ℝ)

def volume (a b c : ℝ) : ℝ :=
  ∫ _ in region a b c, (1 : ℝ)

def endpointPrimitive (a b c r : ℝ) : ℝ :=
  4 * Real.pi * a * b * c * (-(2 / 5 : ℝ)) *
    fiveQuarterPower (1 - r ^ 2)

private def normalizedRadius (a b : ℝ) (q : ℝ × ℝ) : ℝ :=
  q.1 ^ 2 / a ^ 2 + q.2 ^ 2 / b ^ 2

private def verticalSection (a b c : ℝ) (q : ℝ × ℝ) : Set ℝ :=
  if normalizedRadius a b q ≤ 1 then
    Set.Icc
      (-c * quarterPower (1 - normalizedRadius a b q))
      (c * quarterPower (1 - normalizedRadius a b q))
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

private theorem quarterPower_four {t : ℝ} (ht : 0 ≤ t) :
    quarterPower t ^ 4 = t := by
  have h :=
    Real.rpow_inv_natCast_pow ht (n := 4) (by norm_num)
  simpa [quarterPower] using h

private theorem fourth_le_iff_mem (c t z : ℝ)
    (hc : 0 < c) (ht : 0 ≤ t) :
    z ^ 4 / c ^ 4 ≤ t ↔
      -c * quarterPower t ≤ z ∧ z ≤ c * quarterPower t := by
  have hq0 : 0 ≤ quarterPower t :=
    Real.rpow_nonneg ht _
  have hcq0 : 0 ≤ c * quarterPower t :=
    mul_nonneg hc.le hq0
  have hq4 : quarterPower t ^ 4 = t :=
    quarterPower_four ht
  have hmul :
      t * c ^ 4 = (c * quarterPower t) ^ 4 := by
    calc
      t * c ^ 4 = quarterPower t ^ 4 * c ^ 4 := by rw [hq4]
      _ = (c * quarterPower t) ^ 4 := by ring
  have hscale :
      z ^ 4 / c ^ 4 ≤ t ↔
        z ^ 4 ≤ (c * quarterPower t) ^ 4 := by
    constructor
    · intro h
      have h' : z ^ 4 ≤ t * c ^ 4 :=
        (div_le_iff₀ (pow_pos hc 4)).1 h
      calc
        z ^ 4 ≤ t * c ^ 4 := h'
        _ = (c * quarterPower t) ^ 4 := hmul
    · intro h
      apply (div_le_iff₀ (pow_pos hc 4)).2
      calc
        z ^ 4 ≤ (c * quarterPower t) ^ 4 := h
        _ = t * c ^ 4 := hmul.symm
  rw [hscale]
  have habspow : |z| ^ 4 = z ^ 4 := by
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ z ^ 4)]
  rw [← habspow,
    pow_le_pow_iff_left₀ (abs_nonneg z) hcq0 (by norm_num : (4 : ℕ) ≠ 0)]
  simpa [neg_mul] using
    (abs_le : |z| ≤ c * quarterPower t ↔
      -(c * quarterPower t) ≤ z ∧ z ≤ c * quarterPower t)

private theorem mem_verticalSection_iff (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (q : ℝ × ℝ) (z : ℝ) :
    z ∈ verticalSection a b c q ↔
      normalizedRadius a b q + z ^ 4 / c ^ 4 ≤ 1 := by
  by_cases hrad : normalizedRadius a b q ≤ 1
  · have ht : 0 ≤ 1 - normalizedRadius a b q := sub_nonneg.2 hrad
    simp only [verticalSection, if_pos hrad, Set.mem_Icc]
    rw [← fourth_le_iff_mem c
      (1 - normalizedRadius a b q) z hc ht]
    constructor <;> intro h <;> linarith
  · have hrad' : 1 < normalizedRadius a b q := lt_of_not_ge hrad
    have hznonneg : 0 ≤ z ^ 4 / c ^ 4 := by positivity
    simp only [verticalSection, if_neg hrad, Set.mem_empty_iff_false]
    constructor
    · intro h
      contradiction
    · intro h
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
  rintro ⟨x, y, z⟩ h
  change
    x ^ 2 / a ^ 2 + y ^ 2 / b ^ 2 + z ^ 4 / c ^ 4 ≤ 1 at h
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
  have hc4 : 0 < c ^ 4 := pow_pos hc 4
  have hxnonneg : 0 ≤ x ^ 2 / a ^ 2 := by positivity
  have hynonneg : 0 ≤ y ^ 2 / b ^ 2 := by positivity
  have hznonneg : 0 ≤ z ^ 4 / c ^ 4 := by positivity
  have hxdiv : x ^ 2 / a ^ 2 ≤ 1 := by linarith
  have hydiv : y ^ 2 / b ^ 2 ≤ 1 := by linarith
  have hzdiv : z ^ 4 / c ^ 4 ≤ 1 := by linarith
  have hx2 : x ^ 2 ≤ a ^ 2 := (div_le_one ha2).1 hxdiv
  have hy2 : y ^ 2 ≤ b ^ 2 := (div_le_one hb2).1 hydiv
  have hz4 : z ^ 4 ≤ c ^ 4 := (div_le_one hc4).1 hzdiv
  have hz2 : z ^ 2 ≤ c ^ 2 := by
    have hzsq : (z ^ 2) ^ 2 ≤ (c ^ 2) ^ 2 := by
      calc
        (z ^ 2) ^ 2 = z ^ 4 := by ring
        _ ≤ c ^ 4 := hz4
        _ = (c ^ 2) ^ 2 := by ring
    exact (sq_le_sq₀ (sq_nonneg z) (sq_nonneg c)).1 hzsq
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
        simp only [g]
        change
          (if (q.1, q.2, z) ∈ region a b c then 1 else 0) =
            if z ∈ verticalSection a b c q then 1 else 0
        have hmem :
            (q.1, q.2, z) ∈ region a b c ↔
              z ∈ verticalSection a b c q := by
          rw [mem_verticalSection_iff a b c ha hb hc q z]
          rfl
        rw [hmem]
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

theorem gap1 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      ∫ phi in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..1,
          ∫ z in
              -c * quarterPower (1 - r ^ 2)..
                c * quarterPower (1 - r ^ 2),
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
                    (-c * quarterPower (1 - r ^ 2))
                    (c * quarterPower (1 - r ^ 2))
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
            (planarScale a b (r * Real.cos phi, r * Real.sin phi)) =
          if r ^ 2 ≤ 1 then
            Set.Icc
              (-c * quarterPower (1 - r ^ 2))
              (c * quarterPower (1 - r ^ 2))
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
                  (-c * quarterPower (1 - r ^ 2))
                  (c * quarterPower (1 - r ^ 2))
              else ∅),
              (1 : ℝ)) =
        ∫ r in (0 : ℝ)..1,
          ∫ _z in
            -c * quarterPower (1 - r ^ 2)..
              c * quarterPower (1 - r ^ 2),
            r := by
    calc
      (∫ r in Set.Ioi (0 : ℝ),
          r *
            ∫ _z in
              (if r ^ 2 ≤ 1 then
                Set.Icc
                  (-c * quarterPower (1 - r ^ 2))
                  (c * quarterPower (1 - r ^ 2))
              else ∅),
              (1 : ℝ)) =
          ∫ r in Set.Ioc (0 : ℝ) 1,
            r *
              ∫ _z in
                (if r ^ 2 ≤ 1 then
                  Set.Icc
                    (-c * quarterPower (1 - r ^ 2))
                    (c * quarterPower (1 - r ^ 2))
                else ∅),
                (1 : ℝ) := by
        apply setIntegral_eq_of_subset_of_forall_diff_eq_zero
          measurableSet_Ioi Set.Ioc_subset_Ioi_self
        rintro r ⟨hr0, hrnot⟩
        have hrpos : 0 < r := by simpa using hr0
        have hrone : 1 < r := by
          simp only [Set.mem_Ioc, hrpos, true_and] at hrnot
          exact lt_of_not_ge hrnot
        have hrsq : ¬r ^ 2 ≤ 1 := by nlinarith
        simp [hrsq]
      _ = ∫ r in Set.Ioc (0 : ℝ) 1,
            ∫ _z in
              -c * quarterPower (1 - r ^ 2)..
                c * quarterPower (1 - r ^ 2),
              r := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro r hr
        have hr0 : 0 < r := hr.1
        have hr1 : r ≤ 1 := hr.2
        have hrsq : r ^ 2 ≤ 1 := by nlinarith
        have ht : 0 ≤ 1 - r ^ 2 := sub_nonneg.2 hrsq
        have hq0 : 0 ≤ quarterPower (1 - r ^ 2) :=
          Real.rpow_nonneg ht _
        have hlower :
            -c * quarterPower (1 - r ^ 2) ≤
              c * quarterPower (1 - r ^ 2) := by
          nlinarith
        simp only [if_pos hrsq]
        change
          r *
              (∫ _z in
                Set.Icc
                  (-c * quarterPower (1 - r ^ 2))
                  (c * quarterPower (1 - r ^ 2)),
                (1 : ℝ)) =
            ∫ _z in
              -c * quarterPower (1 - r ^ 2)..
                c * quarterPower (1 - r ^ 2),
              r
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
          intervalIntegral.integral_of_le hlower,
          ← MeasureTheory.integral_const_mul]
        simp
      _ = ∫ r in (0 : ℝ)..1,
            ∫ _z in
              -c * quarterPower (1 - r ^ 2)..
                c * quarterPower (1 - r ^ 2),
              r := by
        rw [intervalIntegral.integral_of_le (by norm_num)]
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
          -c * quarterPower (1 - r ^ 2)..
            c * quarterPower (1 - r ^ 2),
          a * b * r) =
        a * b *
          ∫ _z in
            -c * quarterPower (1 - r ^ 2)..
              c * quarterPower (1 - r ^ 2),
            r := by
    rw [intervalIntegral.integral_const_mul]
  simp_rw [hinner]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem gap2 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      4 * Real.pi * a * b * c *
        ∫ r in (0 : ℝ)..1,
          r * quarterPower (1 - r ^ 2) := by
  rw [gap1 a b c ha hb hc]
  have hinner (r : ℝ) :
      (∫ _z in
          -c * quarterPower (1 - r ^ 2)..
            c * quarterPower (1 - r ^ 2),
          a * b * r) =
        2 * c * a * b *
          (r * quarterPower (1 - r ^ 2)) := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  simp_rw [hinner]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  rw [intervalIntegral.integral_const_mul]
  ring

theorem gap3 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    4 * Real.pi * a * b * c *
        (∫ r in (0 : ℝ)..1,
          r * quarterPower (1 - r ^ 2)) =
      endpointPrimitive a b c 1 - endpointPrimitive a b c 0 := by
  let F : ℝ → ℝ :=
    fun r => -(2 / 5 : ℝ) * fiveQuarterPower (1 - r ^ 2)
  have hFcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
    apply Continuous.continuousOn
    exact continuous_const.mul
      ((continuous_const.sub (continuous_id.pow 2)).rpow_const
        (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 5 / 4)))
  have hFderiv :
      ∀ r ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt F (r * quarterPower (1 - r ^ 2)) r := by
    intro r _hr
    have hbase :
        HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * r) r := by
      convert (hasDerivAt_const r (1 : ℝ)).sub
        ((hasDerivAt_id r).pow 2) using 1 <;> simp <;> ring
    have hrpow :=
      hbase.rpow_const (p := (5 / 4 : ℝ))
        (Or.inr (by norm_num : (1 : ℝ) ≤ 5 / 4))
    have hmul := hrpow.const_mul (-(2 / 5 : ℝ))
    convert hmul using 1 <;>
      norm_num [F, fiveQuarterPower, quarterPower] <;> ring
  have hint :
      IntervalIntegrable
        (fun r : ℝ => r * quarterPower (1 - r ^ 2))
        MeasureTheory.volume 0 1 := by
    exact
      (continuous_id.mul
        ((continuous_const.sub (continuous_id.pow 2)).rpow_const
          (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 4)))).intervalIntegrable 0 1
  have hFTC :
      (∫ r in (0 : ℝ)..1,
          r * quarterPower (1 - r ^ 2)) =
        F 1 - F 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (by norm_num) hFcont hFderiv hint
  rw [hFTC]
  simp only [endpointPrimitive, F]
  ring

theorem gap4 (a b c : ℝ) :
    endpointPrimitive a b c 1 - endpointPrimitive a b c 0 =
      (8 / 5 : ℝ) * Real.pi * a * b * c := by
  norm_num [endpointPrimitive, fiveQuarterPower, Real.zero_rpow]
  ring

theorem gap5 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      (8 / 5 : ℝ) * Real.pi * a * b * c := by
  rw [gap2 a b c ha hb hc, gap3 a b c ha hb hc, gap4]

end

end ProofGap.Exercise4114
