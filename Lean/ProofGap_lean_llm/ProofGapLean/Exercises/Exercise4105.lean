import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4105

noncomputable section

open MeasureTheory
open scoped Interval

def capRegion (a : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2.1 ^ 2 ≤ a ^ 2 ∧
    0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧
    p.2.2 ≤ (a ^ 2 - p.1 ^ 2 - p.2.1 ^ 2) / a}

def tetraRegion (a : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 + p.2.1 ≤ a ∧ 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧
    0 ≤ p.2.2 ∧ p.2.2 ≤ a - p.1 - p.2.1}

def region (a : ℝ) : Set (ℝ × ℝ × ℝ) :=
  capRegion a \ tetraRegion a

def volume (s : Set (ℝ × ℝ × ℝ)) : ℝ :=
  ∫ _ in s, (1 : ℝ)

private theorem capRegion_measurable_early (a : ℝ) :
    MeasurableSet (capRegion a) := by
  unfold capRegion
  measurability

private theorem capRegion_subset_box_early (a : ℝ) (ha : 0 < a) :
    capRegion a ⊆
      Set.Icc (0 : ℝ) a ×ˢ
        (Set.Icc (0 : ℝ) a ×ˢ Set.Icc (0 : ℝ) a) := by
  rintro ⟨x, y, z⟩ ⟨hxy, hx0, hy0, hz0, hzupper⟩
  have hx2 : x ^ 2 ≤ a ^ 2 := by
    nlinarith [sq_nonneg y]
  have hy2 : y ^ 2 ≤ a ^ 2 := by
    nlinarith [sq_nonneg x]
  have hza : z ≤ a := by
    have hnum : a ^ 2 - x ^ 2 - y ^ 2 ≤ a ^ 2 := by
      nlinarith [sq_nonneg x, sq_nonneg y]
    have hdiv :
        (a ^ 2 - x ^ 2 - y ^ 2) / a ≤ a := by
      apply (div_le_iff₀ ha).2
      nlinarith
    exact hzupper.trans hdiv
  exact
    ⟨⟨hx0, by nlinarith⟩,
      ⟨⟨hy0, by nlinarith⟩, hz0, hza⟩⟩

private theorem capRegion_const_integrableOn_early
    (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun _p : ℝ × ℝ × ℝ => (1 : ℝ))
      (capRegion a) MeasureTheory.volume := by
  have hbox :
      IntegrableOn (fun _p : ℝ × ℝ × ℝ => (1 : ℝ))
        (Set.Icc (0 : ℝ) a ×ˢ
          (Set.Icc (0 : ℝ) a ×ˢ Set.Icc (0 : ℝ) a))
        MeasureTheory.volume :=
    ((continuous_const :
      Continuous (fun _p : ℝ × ℝ × ℝ => (1 : ℝ))).continuousOn).integrableOn_compact
        (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  exact hbox.mono_set (capRegion_subset_box_early a ha)

private def capVerticalSection (a : ℝ) (q : ℝ × ℝ) : Set ℝ :=
  if q.1 ^ 2 + q.2 ^ 2 ≤ a ^ 2 ∧ 0 ≤ q.1 ∧ 0 ≤ q.2 then
    Set.Icc (0 : ℝ) ((a ^ 2 - q.1 ^ 2 - q.2 ^ 2) / a)
  else ∅

private theorem cap_volume_eq_integral_sections
    (a : ℝ) (ha : 0 < a) :
    volume (capRegion a) =
      ∫ q : ℝ × ℝ,
        ∫ _z in capVerticalSection a q, (1 : ℝ) := by
  classical
  let g : (ℝ × ℝ × ℝ) → ℝ :=
    (capRegion a).indicator (fun _p => (1 : ℝ))
  have hg : Integrable g MeasureTheory.volume := by
    exact
      (integrable_indicator_iff (capRegion_measurable_early a)).2
        (capRegion_const_integrableOn_early a ha)
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
    volume (capRegion a) =
        ∫ p : ℝ × ℝ × ℝ, g p := by
      rw [volume, MeasureTheory.integral_indicator
        (capRegion_measurable_early a)]
    _ = ∫ p : (ℝ × ℝ) × ℝ,
          g (p.1.1, p.1.2, p.2) := by
      symm
      simpa [Function.comp_def] using hp.integral_comp' g
    _ = ∫ q : ℝ × ℝ, ∫ z : ℝ,
          g (q.1, q.2, z) := hfubini
    _ = ∫ q : ℝ × ℝ,
          ∫ _z in capVerticalSection a q, (1 : ℝ) := by
      apply integral_congr_ae
      filter_upwards with q
      have hsection :
          MeasurableSet (capVerticalSection a q) := by
        unfold capVerticalSection
        split_ifs <;> measurability
      rw [← MeasureTheory.integral_indicator hsection]
      apply integral_congr_ae
      filter_upwards with z
      have hmem :
          (q.1, q.2, z) ∈ capRegion a ↔
            z ∈ capVerticalSection a q := by
        by_cases hq :
            q.1 ^ 2 + q.2 ^ 2 ≤ a ^ 2 ∧
              0 ≤ q.1 ∧ 0 ≤ q.2
        · simp only [capVerticalSection, if_pos hq, Set.mem_Icc]
          constructor
          · rintro ⟨_hrad, _hx, _hy, hz0, hz1⟩
            exact ⟨hz0, hz1⟩
          · rintro ⟨hz0, hz1⟩
            exact ⟨hq.1, hq.2.1, hq.2.2, hz0, hz1⟩
        · simp only [capVerticalSection, if_neg hq,
            Set.mem_empty_iff_false, iff_false]
          intro hz
          exact hq ⟨hz.1, hz.2.1, hz.2.2.1⟩
      simp only [g, Set.indicator_apply, hmem]

theorem gap1 (a : ℝ) (ha : 0 < a) :
    volume (capRegion a) =
      ∫ phi in (0 : ℝ)..Real.pi / 2,
        ∫ r in (0 : ℝ)..a, (a ^ 2 - r ^ 2) / a * r := by
  have hsection (r phi : ℝ) (hr : 0 < r)
      (hphi : phi ∈ Set.Ioo (-Real.pi) Real.pi) :
      capVerticalSection a (polarCoord.symm (r, phi)) =
        if r ≤ a ∧ 0 ≤ phi ∧ phi ≤ Real.pi / 2 then
          Set.Icc (0 : ℝ) ((a ^ 2 - r ^ 2) / a)
        else ∅ := by
    have hrad :
        (r * Real.cos phi) ^ 2 + (r * Real.sin phi) ^ 2 =
          r ^ 2 := by
      nlinarith [Real.cos_sq_add_sin_sq phi]
    have hcond :
        (r ^ 2 ≤ a ^ 2 ∧
            0 ≤ r * Real.cos phi ∧
            0 ≤ r * Real.sin phi) ↔
          r ≤ a ∧ 0 ≤ phi ∧ phi ≤ Real.pi / 2 := by
      constructor
      · rintro ⟨hra2, hx, hy⟩
        have hra : r ≤ a := by nlinarith
        have hcos : 0 ≤ Real.cos phi := by
          nlinarith
        have hsin : 0 ≤ Real.sin phi := by
          nlinarith
        have hphi0 : 0 ≤ phi := by
          by_contra hnot
          have hpneg : phi < 0 := lt_of_not_ge hnot
          have hsneg :
              Real.sin phi < 0 :=
            Real.sin_neg_of_neg_of_neg_pi_lt hpneg hphi.1
          linarith
        have hphile : phi ≤ Real.pi / 2 := by
          by_contra hnot
          have hpgt : Real.pi / 2 < phi := lt_of_not_ge hnot
          have hplt : phi < Real.pi + Real.pi / 2 := by
            exact hphi.2.trans
              (lt_add_of_pos_right Real.pi
                (half_pos Real.pi_pos))
          have hcneg :
              Real.cos phi < 0 :=
            Real.cos_neg_of_pi_div_two_lt_of_lt hpgt hplt
          linarith
        exact ⟨hra, hphi0, hphile⟩
      · rintro ⟨hra, hphi0, hphile⟩
        have hphiPi : phi ≤ Real.pi := by
          linarith [Real.pi_pos]
        have hsin :
            0 ≤ Real.sin phi :=
          Real.sin_nonneg_of_nonneg_of_le_pi hphi0 hphiPi
        have hcos :
            0 ≤ Real.cos phi :=
          Real.cos_nonneg_of_neg_pi_div_two_le_of_le
            (by linarith [Real.pi_pos]) hphile
        exact
          ⟨by nlinarith,
            mul_nonneg hr.le hcos,
            mul_nonneg hr.le hsin⟩
    have htop :
        a ^ 2 - (r * Real.cos phi) ^ 2 -
            (r * Real.sin phi) ^ 2 =
          a ^ 2 - r ^ 2 := by
      nlinarith [hrad]
    unfold capVerticalSection
    simp only [polarCoord_symm_apply]
    simp only [hrad, hcond, htop]
  have hsubset :
      Set.Ioc (0 : ℝ) a ×ˢ
          Set.Icc (0 : ℝ) (Real.pi / 2) ⊆
        Set.Ioi (0 : ℝ) ×ˢ
          Set.Ioo (-Real.pi) Real.pi := by
    rintro ⟨r, phi⟩ ⟨hr, hphi⟩
    change r ∈ Set.Ioc (0 : ℝ) a at hr
    change phi ∈ Set.Icc (0 : ℝ) (Real.pi / 2) at hphi
    exact
      ⟨hr.1,
        ⟨(neg_neg_of_pos Real.pi_pos).trans_le hphi.1,
          hphi.2.trans_lt (half_lt_self Real.pi_pos)⟩⟩
  have hpolar :
      (∫ q : ℝ × ℝ,
          ∫ _z in capVerticalSection a q, (1 : ℝ)) =
        (∫ r in Set.Ioc (0 : ℝ) a,
            (a ^ 2 - r ^ 2) / a * r) *
          ∫ _phi in Set.Icc (0 : ℝ) (Real.pi / 2), (1 : ℝ) := by
    rw [← integral_comp_polarCoord_symm, polarCoord_target]
    calc
      (∫ p in
          Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          p.1 •
            ∫ _z in capVerticalSection a
              (polarCoord.symm p), (1 : ℝ)) =
          ∫ p in
            Set.Ioc (0 : ℝ) a ×ˢ
              Set.Icc (0 : ℝ) (Real.pi / 2),
            p.1 •
              ∫ _z in capVerticalSection a
                (polarCoord.symm p), (1 : ℝ) := by
        apply setIntegral_eq_of_subset_of_forall_diff_eq_zero
          (measurableSet_Ioi.prod measurableSet_Ioo) hsubset
        rintro ⟨r, phi⟩ ⟨htarget, hnot⟩
        have hcondnot :
            ¬(r ≤ a ∧ 0 ≤ phi ∧ phi ≤ Real.pi / 2) := by
          intro hc
          apply hnot
          exact ⟨⟨htarget.1, hc.1⟩, hc.2⟩
        rw [hsection r phi htarget.1 htarget.2, if_neg hcondnot]
        simp
      _ = ∫ p in
            Set.Ioc (0 : ℝ) a ×ˢ
              Set.Icc (0 : ℝ) (Real.pi / 2),
            ((a ^ 2 - p.1 ^ 2) / a * p.1) * (1 : ℝ) := by
        apply setIntegral_congr_fun
          (measurableSet_Ioc.prod measurableSet_Icc)
        rintro ⟨r, phi⟩ ⟨hr, hphi⟩
        change r ∈ Set.Ioc (0 : ℝ) a at hr
        change phi ∈ Set.Icc (0 : ℝ) (Real.pi / 2) at hphi
        simp only
        have htarget :
            phi ∈ Set.Ioo (-Real.pi) Real.pi :=
          ⟨(neg_neg_of_pos Real.pi_pos).trans_le hphi.1,
            hphi.2.trans_lt (half_lt_self Real.pi_pos)⟩
        have hheight :
            0 ≤ (a ^ 2 - r ^ 2) / a := by
          apply div_nonneg
          · exact sub_nonneg.2
              ((sq_le_sq₀ hr.1.le ha.le).2 hr.2)
          · exact ha.le
        rw [hsection r phi hr.1 htarget,
          if_pos ⟨hr.2, hphi.1, hphi.2⟩]
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le hheight,
          intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
      _ = (∫ r in Set.Ioc (0 : ℝ) a,
              (a ^ 2 - r ^ 2) / a * r) *
            ∫ _phi in Set.Icc (0 : ℝ) (Real.pi / 2),
              (1 : ℝ) := by
        simpa only using
          (setIntegral_prod_mul
            (fun r : ℝ => (a ^ 2 - r ^ 2) / a * r)
            (fun _phi : ℝ => (1 : ℝ))
            (Set.Ioc (0 : ℝ) a)
            (Set.Icc (0 : ℝ) (Real.pi / 2)))
  rw [cap_volume_eq_integral_sections a ha, hpolar]
  rw [← intervalIntegral.integral_of_le ha.le]
  have hangle : (0 : ℝ) ≤ Real.pi / 2 := by
    linarith [Real.pi_pos]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hangle]
  let R : ℝ :=
    ∫ r in (0 : ℝ)..a, (a ^ 2 - r ^ 2) / a * r
  change
    R * (∫ _phi in (0 : ℝ)..Real.pi / 2, (1 : ℝ)) =
      ∫ _phi in (0 : ℝ)..Real.pi / 2, R
  simp only [intervalIntegral.integral_const, smul_eq_mul,
    sub_zero, mul_one]
  ring

theorem gap2 (a : ℝ) (ha : 0 < a) :
    (∫ phi in (0 : ℝ)..Real.pi / 2,
        ∫ r in (0 : ℝ)..a, (a ^ 2 - r ^ 2) / a * r) =
      Real.pi * a ^ 3 / 8 := by
  have ha0 : a ≠ 0 := ha.ne'
  have hpoint (r : ℝ) :
      (a ^ 2 - r ^ 2) / a * r =
        a * r - r ^ 3 / a := by
    field_simp [ha0]
  simp_rw [hpoint]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  rw [intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_const_mul,
      integral_id,
      intervalIntegral.integral_div,
      integral_pow]
    norm_num
    field_simp [ha0]
    ring
  · exact
      (continuous_const.mul continuous_id).intervalIntegrable 0 a
  · exact
      (continuous_pow 3).intervalIntegrable 0 a |>.div_const a

theorem gap3 (a : ℝ) (ha : 0 < a) :
    volume (capRegion a) = Real.pi * a ^ 3 / 8 := by
  rw [gap1 a ha, gap2 a ha]

theorem gap4 (a : ℝ) (ha : 0 < a) :
    volume (tetraRegion a) =
      ∫ x in (0 : ℝ)..a,
        ∫ y in (0 : ℝ)..a - x,
          ∫ z in (0 : ℝ)..a - x - y, (1 : ℝ) := by
  classical
  let g : (ℝ × ℝ × ℝ) → ℝ :=
    (tetraRegion a).indicator (fun _p => (1 : ℝ))
  have htmeas : MeasurableSet (tetraRegion a) := by
    unfold tetraRegion
    measurability
  have htsub :
      tetraRegion a ⊆
        Set.Icc (0 : ℝ) a ×ˢ
          (Set.Icc (0 : ℝ) a ×ˢ Set.Icc (0 : ℝ) a) := by
    rintro ⟨x, y, z⟩ ⟨hxy, hx0, hy0, hz0, hz1⟩
    exact
      ⟨⟨hx0, by linarith⟩,
        ⟨⟨hy0, by linarith⟩,
          ⟨hz0, by linarith⟩⟩⟩
  have hbox :
      IntegrableOn (fun _p : ℝ × ℝ × ℝ => (1 : ℝ))
        (Set.Icc (0 : ℝ) a ×ˢ
          (Set.Icc (0 : ℝ) a ×ˢ Set.Icc (0 : ℝ) a))
        MeasureTheory.volume :=
    ((continuous_const :
      Continuous (fun _p : ℝ × ℝ × ℝ => (1 : ℝ))).continuousOn).integrableOn_compact
        (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  have htconst :
      IntegrableOn (fun _p : ℝ × ℝ × ℝ => (1 : ℝ))
        (tetraRegion a) MeasureTheory.volume :=
    hbox.mono_set htsub
  have hg : Integrable g MeasureTheory.volume := by
    exact
      (integrable_indicator_iff htmeas).2 htconst
  have hfirst :
      (∫ p : ℝ × ℝ × ℝ, g p) =
        ∫ x : ℝ, ∫ q : ℝ × ℝ, g (x, q.1, q.2) := by
    change
      (∫ p : ℝ × (ℝ × ℝ), g p
        ∂(MeasureTheory.volume : Measure ℝ).prod
          (MeasureTheory.volume : Measure (ℝ × ℝ))) =
        ∫ x : ℝ, ∫ q : ℝ × ℝ, g (x, q.1, q.2)
    rw [MeasureTheory.integral_prod _ hg]
  have hsecond :
      (∫ x : ℝ, ∫ q : ℝ × ℝ, g (x, q.1, q.2)) =
        ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ, g (x, y, z) := by
    apply integral_congr_ae
    filter_upwards [hg.prod_right_ae] with x hx
    change
      (∫ q : ℝ × ℝ, g (x, q.1, q.2)
        ∂(MeasureTheory.volume : Measure ℝ).prod
          MeasureTheory.volume) =
        ∫ y : ℝ, ∫ z : ℝ, g (x, y, z)
    rw [MeasureTheory.integral_prod _ hx]
  let J : ℝ → ℝ → ℝ :=
    fun x y => ∫ z : ℝ, g (x, y, z)
  let K : ℝ → ℝ → ℝ :=
    fun x y => ∫ _z in (0 : ℝ)..a - x - y, (1 : ℝ)
  have hJ (x y : ℝ) :
      J x y =
        if hxy : 0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ a then
          ∫ _z in Set.Icc (0 : ℝ) (a - x - y), (1 : ℝ)
        else 0 := by
    by_cases hxy : 0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ a
    · simp only [J]
      rw [dif_pos hxy]
      rw [← MeasureTheory.integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards with z
      have hmem :
          (x, y, z) ∈ tetraRegion a ↔
            z ∈ Set.Icc (0 : ℝ) (a - x - y) := by
        constructor
        · rintro ⟨_hxy, _hx0, _hy0, hz0, hz1⟩
          exact ⟨hz0, hz1⟩
        · rintro ⟨hz0, hz1⟩
          exact ⟨hxy.2.2, hxy.1, hxy.2.1, hz0, hz1⟩
      simp only [g, Set.indicator_apply, hmem]
    · simp only [J]
      rw [dif_neg hxy]
      apply integral_eq_zero_of_ae
      filter_upwards with z
      change g (x, y, z) = (0 : ℝ)
      have hznot : (x, y, z) ∉ tetraRegion a := by
        intro hz
        exact hxy ⟨hz.2.1, hz.2.2.1, hz.1⟩
      simp only [g, Set.indicator_apply, hznot, ↓reduceIte]
  have hJ_on (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) a)
      (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) (a - x)) :
      J x y = K x y := by
    have hxy : 0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ a := by
      exact ⟨hx.1, hy.1, by linarith [hy.2]⟩
    rw [hJ, dif_pos hxy]
    have hupper : 0 ≤ a - x - y := by linarith
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hupper]
  have hJ_off_y (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) a)
      (y : ℝ) (hy : y ∉ Set.Icc (0 : ℝ) (a - x)) :
      J x y = 0 := by
    have hnot :
        ¬(0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ a) := by
      intro h
      apply hy
      exact ⟨h.2.1, by linarith [h.2.2]⟩
    rw [hJ, dif_neg hnot]
  have hinner (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) a) :
      (∫ y : ℝ, J x y) =
        ∫ y in (0 : ℝ)..a - x, K x y := by
    calc
      (∫ y : ℝ, J x y) =
          ∫ y in Set.Icc (0 : ℝ) (a - x), J x y := by
        symm
        apply setIntegral_eq_integral_of_ae_compl_eq_zero
        filter_upwards with y
        exact hJ_off_y x hx y
      _ = ∫ y in Set.Icc (0 : ℝ) (a - x), K x y := by
        apply setIntegral_congr_fun measurableSet_Icc
        exact hJ_on x hx
      _ = ∫ y in Set.Ioc (0 : ℝ) (a - x), K x y := by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      _ = ∫ y in (0 : ℝ)..a - x, K x y := by
        rw [intervalIntegral.integral_of_le (by linarith [hx.2])]
  have houter_off (x : ℝ) (hx : x ∉ Set.Icc (0 : ℝ) a) :
      (∫ y : ℝ, J x y) = 0 := by
    have hpoint (y : ℝ) : J x y = 0 := by
      have hnot :
          ¬(0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ a) := by
        intro h
        apply hx
        exact ⟨h.1, by linarith [h.2.1, h.2.2]⟩
      rw [hJ, dif_neg hnot]
    simp_rw [hpoint]
    simp
  calc
    volume (tetraRegion a) =
        ∫ p : ℝ × ℝ × ℝ, g p := by
      rw [volume, MeasureTheory.integral_indicator
        htmeas]
    _ = ∫ x : ℝ, ∫ y : ℝ, J x y := by
      rw [hfirst, hsecond]
    _ = ∫ x in Set.Icc (0 : ℝ) a,
          ∫ y : ℝ, J x y := by
      symm
      apply setIntegral_eq_integral_of_ae_compl_eq_zero
      filter_upwards with x
      exact houter_off x
    _ = ∫ x in Set.Icc (0 : ℝ) a,
          ∫ y in (0 : ℝ)..a - x, K x y := by
      apply setIntegral_congr_fun measurableSet_Icc
      exact hinner
    _ = ∫ x in Set.Ioc (0 : ℝ) a,
          ∫ y in (0 : ℝ)..a - x, K x y := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    _ = ∫ x in (0 : ℝ)..a,
          ∫ y in (0 : ℝ)..a - x,
            ∫ _z in (0 : ℝ)..a - x - y, (1 : ℝ) := by
      rw [intervalIntegral.integral_of_le ha.le]

theorem gap5 (a : ℝ) (ha : 0 < a) :
    (∫ x in (0 : ℝ)..a,
        ∫ y in (0 : ℝ)..a - x,
          ∫ z in (0 : ℝ)..a - x - y, (1 : ℝ)) =
      a ^ 3 / 6 := by
  have hz (x y : ℝ) :
      (∫ _z in (0 : ℝ)..a - x - y, (1 : ℝ)) =
        a - x - y := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul, mul_one, sub_zero]
  simp_rw [hz]
  have hy (x : ℝ) :
      (∫ y in (0 : ℝ)..a - x, a - x - y) =
        (a - x) ^ 2 / 2 := by
    rw [intervalIntegral.integral_sub]
    · rw [intervalIntegral.integral_const,
        integral_id]
      simp only [smul_eq_mul]
      ring
    · exact continuous_const.intervalIntegrable 0 (a - x)
    · exact continuous_id.intervalIntegrable 0 (a - x)
  simp_rw [hy]
  rw [show
    (fun x : ℝ => (a - x) ^ 2 / 2) =
      fun x => (a ^ 2 - 2 * a * x + x ^ 2) / 2 by
        funext x
        ring]
  rw [intervalIntegral.integral_div]
  have hconst :
      IntervalIntegrable (fun _x : ℝ => a ^ 2)
        MeasureTheory.volume 0 a :=
    continuous_const.intervalIntegrable 0 a
  have hlinear :
      IntervalIntegrable (fun x : ℝ => 2 * a * x)
        MeasureTheory.volume 0 a :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 a
  have hleft :
      IntervalIntegrable (fun x : ℝ => a ^ 2 - 2 * a * x)
        MeasureTheory.volume 0 a :=
    hconst.sub hlinear
  have hright :
      IntervalIntegrable (fun x : ℝ => x ^ 2)
        MeasureTheory.volume 0 a :=
    (continuous_pow 2).intervalIntegrable 0 a
  rw [intervalIntegral.integral_add hleft hright,
    intervalIntegral.integral_sub hconst hlinear]
  rw [intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul,
    integral_id, integral_pow]
  simp only [smul_eq_mul]
  norm_num
  ring

theorem gap6 (a : ℝ) (ha : 0 < a) :
    volume (tetraRegion a) = a ^ 3 / 6 := by
  rw [gap4 a ha, gap5 a ha]

private theorem capRegion_measurable (a : ℝ) :
    MeasurableSet (capRegion a) := by
  unfold capRegion
  measurability

private theorem tetraRegion_measurable (a : ℝ) :
    MeasurableSet (tetraRegion a) := by
  unfold tetraRegion
  measurability

private theorem tetraRegion_subset_capRegion (a : ℝ) (ha : 0 < a) :
    tetraRegion a ⊆ capRegion a := by
  rintro ⟨x, y, z⟩ ⟨hxy, hx0, hy0, hz0, hzupper⟩
  have hxa : x ≤ a := by linarith
  have hya : y ≤ a := by linarith
  have hsquares : x ^ 2 + y ^ 2 ≤ a ^ 2 := by
    nlinarith
  have hheight :
      a - x - y ≤ (a ^ 2 - x ^ 2 - y ^ 2) / a := by
    apply (le_div_iff₀ ha).2
    nlinarith
  exact
    ⟨hsquares, hx0, hy0, hz0, hzupper.trans hheight⟩

private theorem capRegion_subset_box (a : ℝ) (ha : 0 < a) :
    capRegion a ⊆
      Set.Icc (0 : ℝ) a ×ˢ
        (Set.Icc (0 : ℝ) a ×ˢ Set.Icc (0 : ℝ) a) := by
  rintro ⟨x, y, z⟩ ⟨hxy, hx0, hy0, hz0, hzupper⟩
  have hx2 : x ^ 2 ≤ a ^ 2 := by
    nlinarith [sq_nonneg y]
  have hy2 : y ^ 2 ≤ a ^ 2 := by
    nlinarith [sq_nonneg x]
  have hza : z ≤ a := by
    have hnum : a ^ 2 - x ^ 2 - y ^ 2 ≤ a ^ 2 := by
      nlinarith [sq_nonneg x, sq_nonneg y]
    have hdiv :
        (a ^ 2 - x ^ 2 - y ^ 2) / a ≤ a := by
      apply (div_le_iff₀ ha).2
      nlinarith
    exact hzupper.trans hdiv
  exact
    ⟨⟨hx0, by nlinarith⟩,
      ⟨⟨hy0, by nlinarith⟩, hz0, hza⟩⟩

private theorem capRegion_const_integrableOn (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun _p : ℝ × ℝ × ℝ => (1 : ℝ))
      (capRegion a) MeasureTheory.volume := by
  have hbox :
      IntegrableOn (fun _p : ℝ × ℝ × ℝ => (1 : ℝ))
        (Set.Icc (0 : ℝ) a ×ˢ
          (Set.Icc (0 : ℝ) a ×ˢ Set.Icc (0 : ℝ) a))
        MeasureTheory.volume :=
    ((continuous_const :
      Continuous (fun _p : ℝ × ℝ × ℝ => (1 : ℝ))).continuousOn).integrableOn_compact
        (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  exact hbox.mono_set (capRegion_subset_box a ha)

theorem gap7 (a : ℝ) (ha : 0 < a) :
    volume (region a) =
      volume (capRegion a) - volume (tetraRegion a) := by
  unfold volume region
  exact setIntegral_diff
    (tetraRegion_measurable a)
    (capRegion_const_integrableOn a ha)
    (tetraRegion_subset_capRegion a ha)

theorem gap8 (a : ℝ) :
    Real.pi * a ^ 3 / 8 - a ^ 3 / 6 =
      a ^ 3 / 24 * (3 * Real.pi - 4) := by
  ring

theorem gap9 (a : ℝ) (ha : 0 < a) :
    volume (region a) =
      a ^ 3 / 24 * (3 * Real.pi - 4) := by
  rw [gap7 a ha, gap3 a ha, gap6 a ha, gap8]

end

end ProofGap.Exercise4105
