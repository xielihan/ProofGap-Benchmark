import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise4101

noncomputable section

open MeasureTheory
open scoped Interval

def region : Set (ℝ × ℝ × ℝ) :=
  {p | p.2.2 ≥ p.1 ^ 2 + p.2.1 ^ 2 ∧
    p.2.2 ≤ 2 * p.1 ^ 2 + 2 * p.2.1 ^ 2 ∧
    p.2.1 ≥ p.1 ^ 2 ∧ p.2.1 ≤ p.1}

def volume : ℝ :=
  ∫ _ in region, (1 : ℝ)

def endpointPrimitive (x : ℝ) : ℝ :=
  1 / 3 * x ^ 4 - 1 / 5 * x ^ 5 - 1 / 21 * x ^ 7

theorem gap1 :
    region =
      {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧
        p.1 ^ 2 ≤ p.2.1 ∧ p.2.1 ≤ p.1 ∧
        p.1 ^ 2 + p.2.1 ^ 2 ≤ p.2.2 ∧
        p.2.2 ≤ 2 * p.1 ^ 2 + 2 * p.2.1 ^ 2} := by
  ext p
  simp only [region, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hzLower, hzUpper, hyLower, hyUpper⟩
    have hxNonneg : 0 ≤ p.1 := by
      nlinarith [sq_nonneg p.1]
    have hxUpper : p.1 ≤ 1 := by
      by_contra h
      have hxOne : 1 < p.1 := lt_of_not_ge h
      have hprod : 0 < p.1 * (p.1 - 1) :=
        mul_pos (lt_trans zero_lt_one hxOne) (sub_pos.mpr hxOne)
      nlinarith
    exact ⟨hxNonneg, hxUpper, hyLower, hyUpper, hzLower, hzUpper⟩
  · rintro ⟨hxNonneg, hxUpper, hyLower, hyUpper, hzLower, hzUpper⟩
    exact ⟨hzLower, hzUpper, hyLower, hyUpper⟩

theorem gap2 :
    volume =
      ∫ x in (0 : ℝ)..1,
        ∫ y in x ^ 2..x,
          ∫ z in x ^ 2 + y ^ 2..2 * x ^ 2 + 2 * y ^ 2,
            (1 : ℝ) := by
  classical
  have hs : MeasurableSet region := by
    unfold region
    measurability
  have hsubset :
      region ⊆
        Set.Icc (0 : ℝ) 1 ×ˢ
          (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 4) := by
    intro q hq
    have hq' :
        0 ≤ q.1 ∧ q.1 ≤ 1 ∧
          q.1 ^ 2 ≤ q.2.1 ∧ q.2.1 ≤ q.1 ∧
          q.1 ^ 2 + q.2.1 ^ 2 ≤ q.2.2 ∧
          q.2.2 ≤ 2 * q.1 ^ 2 + 2 * q.2.1 ^ 2 := by
      have hq'' := hq
      rw [gap1] at hq''
      exact hq''
    rcases hq' with
      ⟨hx0, hx1, hyLower, hyUpper, hzLower, hzUpper⟩
    have hy0 : 0 ≤ q.2.1 :=
      le_trans (sq_nonneg q.1) hyLower
    have hy1 : q.2.1 ≤ 1 :=
      le_trans hyUpper hx1
    have hxSq : q.1 ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
    have hySq : q.2.1 ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hy1)]
    have hz0 : 0 ≤ q.2.2 := by
      nlinarith [sq_nonneg q.1, sq_nonneg q.2.1]
    have hz4 : q.2.2 ≤ 4 := by
      nlinarith
    exact ⟨⟨hx0, hx1⟩, ⟨⟨hy0, hy1⟩, hz0, hz4⟩⟩
  have hbox :
      IntegrableOn (fun _q : ℝ × ℝ × ℝ => (1 : ℝ))
        (Set.Icc (0 : ℝ) 1 ×ˢ
          (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 4))
        MeasureTheory.volume :=
    ((continuous_const :
      Continuous (fun _q : ℝ × ℝ × ℝ => (1 : ℝ))).continuousOn).integrableOn_compact
        (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  have hri :
      IntegrableOn (fun _q : ℝ × ℝ × ℝ => (1 : ℝ))
        region MeasureTheory.volume :=
    hbox.mono_set hsubset
  have hind :
      Integrable (region.indicator (fun _q : ℝ × ℝ × ℝ => (1 : ℝ)))
        MeasureTheory.volume :=
    (integrable_indicator_iff hs).2 hri
  change
    Integrable (region.indicator (fun _q : ℝ × ℝ × ℝ => (1 : ℝ)))
      (MeasureTheory.volume.prod
        (MeasureTheory.volume.prod MeasureTheory.volume)) at hind
  have hprod :
      (∫ q : ℝ × ℝ × ℝ,
          region.indicator (fun _q => (1 : ℝ)) q
            ∂MeasureTheory.volume.prod
              (MeasureTheory.volume.prod MeasureTheory.volume)) =
        ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
          region.indicator (fun _q => (1 : ℝ)) (x, y, z) := by
    rw [MeasureTheory.integral_prod _ hind]
    apply integral_congr_ae
    filter_upwards [hind.prod_right_ae] with x hx
    change
      (∫ yz : ℝ × ℝ,
          region.indicator (fun _q => (1 : ℝ)) (x, yz)
            ∂MeasureTheory.volume.prod MeasureTheory.volume) =
        ∫ y : ℝ, ∫ z : ℝ,
          region.indicator (fun _q => (1 : ℝ)) (x, y, z)
    rw [MeasureTheory.integral_prod _ hx]
  have hsections :
      (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
          region.indicator (fun _q => (1 : ℝ)) (x, y, z)) =
        ∫ x in Set.Icc (0 : ℝ) 1,
          ∫ y in Set.Icc (x ^ 2) x,
            ∫ z in Set.Icc (x ^ 2 + y ^ 2)
              (2 * x ^ 2 + 2 * y ^ 2), (1 : ℝ) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
    · rw [Set.indicator_of_mem hx]
      rw [← MeasureTheory.integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards with y
      by_cases hy : y ∈ Set.Icc (x ^ 2) x
      · rw [Set.indicator_of_mem hy]
        rw [← MeasureTheory.integral_indicator measurableSet_Icc]
        apply integral_congr_ae
        filter_upwards with z
        by_cases hz :
            z ∈ Set.Icc (x ^ 2 + y ^ 2)
              (2 * x ^ 2 + 2 * y ^ 2)
        · have hr : (x, y, z) ∈ region := by
            exact ⟨hz.1, hz.2, hy.1, hy.2⟩
          simp only [Set.indicator_of_mem hz, Set.indicator_of_mem hr]
        · have hnr : (x, y, z) ∉ region := by
            intro hr
            exact hz ⟨hr.1, hr.2.1⟩
          simp [Set.indicator, hz, hnr]
      · have hyr :
            (Set.Icc (x ^ 2) x).indicator
              (fun y =>
                ∫ z in Set.Icc (x ^ 2 + y ^ 2)
                  (2 * x ^ 2 + 2 * y ^ 2), (1 : ℝ)) y = 0 := by
          simp [Set.indicator, hy]
        rw [hyr, ← integral_zero]
        apply integral_congr_ae
        filter_upwards with z
        have hnr : (x, y, z) ∉ region := by
          intro hr
          exact hy ⟨hr.2.2.1, hr.2.2.2⟩
        simp [Set.indicator, hnr]
    · have hxr :
          (Set.Icc (0 : ℝ) 1).indicator
            (fun x =>
              ∫ y in Set.Icc (x ^ 2) x,
                ∫ z in Set.Icc (x ^ 2 + y ^ 2)
                  (2 * x ^ 2 + 2 * y ^ 2), (1 : ℝ)) x = 0 := by
        simp [Set.indicator, hx]
      rw [hxr, ← integral_zero]
      apply integral_congr_ae
      filter_upwards with y
      rw [← integral_zero]
      apply integral_congr_ae
      filter_upwards with z
      have hnr : (x, y, z) ∉ region := by
        intro hr
        have hr' :
            0 ≤ x ∧ x ≤ 1 ∧
              x ^ 2 ≤ y ∧ y ≤ x ∧
              x ^ 2 + y ^ 2 ≤ z ∧
              z ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
          have hr'' := hr
          rw [gap1] at hr''
          exact hr''
        exact hx ⟨hr'.1, hr'.2.1⟩
      simp [Set.indicator, hnr]
  unfold volume
  calc
    (∫ _q in region, (1 : ℝ)) =
        ∫ q : ℝ × ℝ × ℝ,
          region.indicator (fun _q => (1 : ℝ)) q := by
            rw [MeasureTheory.integral_indicator hs]
    _ = ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
          region.indicator (fun _q => (1 : ℝ)) (x, y, z) := hprod
    _ = ∫ x in Set.Icc (0 : ℝ) 1,
          ∫ y in Set.Icc (x ^ 2) x,
            ∫ z in Set.Icc (x ^ 2 + y ^ 2)
              (2 * x ^ 2 + 2 * y ^ 2), (1 : ℝ) := hsections
    _ = ∫ x in (0 : ℝ)..1,
          ∫ y in x ^ 2..x,
            ∫ z in x ^ 2 + y ^ 2..2 * x ^ 2 + 2 * y ^ 2,
              (1 : ℝ) := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      dsimp only
      have hyorder : x ^ 2 ≤ x := by
        nlinarith [mul_nonneg hx.1.le (sub_nonneg.mpr hx.2)]
      rw [intervalIntegral.integral_of_le hyorder]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro y hy
      dsimp only
      have hzorder :
          x ^ 2 + y ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
        nlinarith [sq_nonneg x, sq_nonneg y]
      rw [intervalIntegral.integral_of_le hzorder]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]

theorem gap3 :
    (∫ x in (0 : ℝ)..1,
        ∫ y in x ^ 2..x,
          ∫ z in x ^ 2 + y ^ 2..2 * x ^ 2 + 2 * y ^ 2,
            (1 : ℝ)) =
      ∫ x in (0 : ℝ)..1,
        ∫ y in x ^ 2..x, x ^ 2 + y ^ 2 := by
  apply intervalIntegral.integral_congr
  intro x hx
  apply intervalIntegral.integral_congr
  intro y hy
  change (∫ z in x ^ 2 + y ^ 2..
    2 * x ^ 2 + 2 * y ^ 2, (1 : ℝ)) = x ^ 2 + y ^ 2
  rw [intervalIntegral.integral_const]
  simp
  ring

private theorem integral_id_zero_one :
    (∫ x in (0 : ℝ)..1, x) = 1 / 2 := by
  have hconst :
      IntervalIntegrable (fun _x : ℝ => (1 : ℝ))
        MeasureTheory.volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  have hid :
      IntervalIntegrable (fun x : ℝ => x)
        MeasureTheory.volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  have hreflect :
      (∫ x in (0 : ℝ)..1, (1 - x : ℝ)) =
        ∫ x in (0 : ℝ)..1, x := by
    simpa using
      (intervalIntegral.integral_comp_sub_left
        (f := fun x : ℝ => x) (a := (0 : ℝ)) (b := 1) 1)
  rw [intervalIntegral.integral_sub hconst hid,
    intervalIntegral.integral_const] at hreflect
  norm_num at hreflect ⊢
  linarith

private theorem integral_sq_zero_one :
    (∫ x in (0 : ℝ)..1, x ^ 2) = 1 / 3 := by
  have hp01 :
      IntervalIntegrable (fun x : ℝ => x ^ 2)
        MeasureTheory.volume 0 1 :=
    (continuous_id.pow 2).intervalIntegrable 0 1
  have hp12 :
      IntervalIntegrable (fun x : ℝ => x ^ 2)
        MeasureTheory.volume 1 2 :=
    (continuous_id.pow 2).intervalIntegrable 1 2
  have hscaled :
      (∫ x in (0 : ℝ)..1, (2 * x) ^ 2) =
        4 * ∫ x in (0 : ℝ)..1, x ^ 2 := by
    calc
      (∫ x in (0 : ℝ)..1, (2 * x) ^ 2) =
          ∫ x in (0 : ℝ)..1, 4 * x ^ 2 := by
            apply intervalIntegral.integral_congr
            intro x hx
            ring
      _ = 4 * ∫ x in (0 : ℝ)..1, x ^ 2 := by
        rw [intervalIntegral.integral_const_mul]
  have hscale :
      8 * (∫ x in (0 : ℝ)..1, x ^ 2) =
        ∫ x in (0 : ℝ)..2, x ^ 2 := by
    have h := intervalIntegral.smul_integral_comp_mul_left
      (fun x : ℝ => x ^ 2) (a := (0 : ℝ)) (b := 1) 2
    rw [hscaled] at h
    norm_num [smul_eq_mul] at h ⊢
    linarith
  have htranslated :
      (∫ x in (0 : ℝ)..1, (x + 1) ^ 2) =
        (∫ x in (0 : ℝ)..1, x ^ 2) + 2 := by
    have h2x :
        IntervalIntegrable (fun x : ℝ => 2 * x)
          MeasureTheory.volume 0 1 :=
      (continuous_const.mul continuous_id).intervalIntegrable 0 1
    have hone :
        IntervalIntegrable (fun _x : ℝ => (1 : ℝ))
          MeasureTheory.volume 0 1 :=
      continuous_const.intervalIntegrable 0 1
    calc
      (∫ x in (0 : ℝ)..1, (x + 1) ^ 2) =
          ∫ x in (0 : ℝ)..1, x ^ 2 + (2 * x + 1) := by
            apply intervalIntegral.integral_congr
            intro x hx
            ring
      _ = (∫ x in (0 : ℝ)..1, x ^ 2) +
          ∫ x in (0 : ℝ)..1, 2 * x + 1 := by
            rw [intervalIntegral.integral_add hp01 (h2x.add hone)]
      _ = (∫ x in (0 : ℝ)..1, x ^ 2) +
          ((∫ x in (0 : ℝ)..1, 2 * x) +
            ∫ _x in (0 : ℝ)..1, (1 : ℝ)) := by
              rw [intervalIntegral.integral_add h2x hone]
      _ = (∫ x in (0 : ℝ)..1, x ^ 2) + 2 := by
        rw [intervalIntegral.integral_const_mul, integral_id_zero_one,
          intervalIntegral.integral_const]
        norm_num
  have hsplit :
      (∫ x in (0 : ℝ)..2, x ^ 2) =
        (∫ x in (0 : ℝ)..1, x ^ 2) +
          ∫ x in (0 : ℝ)..1, (x + 1) ^ 2 := by
    calc
      (∫ x in (0 : ℝ)..2, x ^ 2) =
          (∫ x in (0 : ℝ)..1, x ^ 2) +
            ∫ x in (1 : ℝ)..2, x ^ 2 :=
        (intervalIntegral.integral_add_adjacent_intervals hp01 hp12).symm
      _ = (∫ x in (0 : ℝ)..1, x ^ 2) +
            ∫ x in (0 : ℝ)..1, (x + 1) ^ 2 := by
        congr 1
        symm
        convert
          (intervalIntegral.integral_comp_add_right
            (fun x : ℝ => x ^ 2) (a := (0 : ℝ)) (b := 1) 1) using 1 <;>
          norm_num
  rw [htranslated] at hsplit
  nlinarith [hscale, hsplit]

private theorem integral_cube_zero_one :
    (∫ x in (0 : ℝ)..1, x ^ 3) = 1 / 4 := by
  have hone :
      IntervalIntegrable (fun _x : ℝ => (1 : ℝ))
        MeasureTheory.volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  have h3x :
      IntervalIntegrable (fun x : ℝ => 3 * x)
        MeasureTheory.volume 0 1 :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 1
  have h3x2 :
      IntervalIntegrable (fun x : ℝ => 3 * x ^ 2)
        MeasureTheory.volume 0 1 :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 1
  have hx3 :
      IntervalIntegrable (fun x : ℝ => x ^ 3)
        MeasureTheory.volume 0 1 :=
    (continuous_id.pow 3).intervalIntegrable 0 1
  have hpoly :
      (∫ x in (0 : ℝ)..1, (1 - x) ^ 3) =
        1 / 2 - ∫ x in (0 : ℝ)..1, x ^ 3 := by
    calc
      (∫ x in (0 : ℝ)..1, (1 - x) ^ 3) =
          ∫ x in (0 : ℝ)..1, ((1 - 3 * x) + 3 * x ^ 2) - x ^ 3 := by
            apply intervalIntegral.integral_congr
            intro x hx
            ring
      _ = (((∫ _x in (0 : ℝ)..1, (1 : ℝ)) -
              ∫ x in (0 : ℝ)..1, 3 * x) +
            ∫ x in (0 : ℝ)..1, 3 * x ^ 2) -
          ∫ x in (0 : ℝ)..1, x ^ 3 := by
            rw [intervalIntegral.integral_sub ((hone.sub h3x).add h3x2) hx3,
              intervalIntegral.integral_add (hone.sub h3x) h3x2,
              intervalIntegral.integral_sub hone h3x]
      _ = 1 / 2 - ∫ x in (0 : ℝ)..1, x ^ 3 := by
        rw [intervalIntegral.integral_const,
          intervalIntegral.integral_const_mul, integral_id_zero_one,
          intervalIntegral.integral_const_mul, integral_sq_zero_one]
        norm_num
  have hreflect :
      (∫ x in (0 : ℝ)..1, (1 - x) ^ 3) =
        ∫ x in (0 : ℝ)..1, x ^ 3 := by
    simpa using
      (intervalIntegral.integral_comp_sub_left
        (f := fun x : ℝ => x ^ 3) (a := (0 : ℝ)) (b := 1) 1)
  linarith [hpoly, hreflect]

private theorem integral_fourth_zero_one :
    (∫ x in (0 : ℝ)..1, x ^ 4) = 1 / 5 := by
  have hp01 :
      IntervalIntegrable (fun x : ℝ => x ^ 4)
        MeasureTheory.volume 0 1 :=
    (continuous_id.pow 4).intervalIntegrable 0 1
  have hp12 :
      IntervalIntegrable (fun x : ℝ => x ^ 4)
        MeasureTheory.volume 1 2 :=
    (continuous_id.pow 4).intervalIntegrable 1 2
  have hscaled :
      (∫ x in (0 : ℝ)..1, (2 * x) ^ 4) =
        16 * ∫ x in (0 : ℝ)..1, x ^ 4 := by
    calc
      (∫ x in (0 : ℝ)..1, (2 * x) ^ 4) =
          ∫ x in (0 : ℝ)..1, 16 * x ^ 4 := by
            apply intervalIntegral.integral_congr
            intro x hx
            ring
      _ = 16 * ∫ x in (0 : ℝ)..1, x ^ 4 := by
        rw [intervalIntegral.integral_const_mul]
  have hscale :
      32 * (∫ x in (0 : ℝ)..1, x ^ 4) =
        ∫ x in (0 : ℝ)..2, x ^ 4 := by
    have h := intervalIntegral.smul_integral_comp_mul_left
      (fun x : ℝ => x ^ 4) (a := (0 : ℝ)) (b := 1) 2
    rw [hscaled] at h
    norm_num [smul_eq_mul] at h ⊢
    linarith
  have htranslated :
      (∫ x in (0 : ℝ)..1, (x + 1) ^ 4) =
        (∫ x in (0 : ℝ)..1, x ^ 4) + 6 := by
    have hx4 :
        IntervalIntegrable (fun x : ℝ => x ^ 4)
          MeasureTheory.volume 0 1 :=
      (continuous_id.pow 4).intervalIntegrable 0 1
    have h4x3 :
        IntervalIntegrable (fun x : ℝ => 4 * x ^ 3)
          MeasureTheory.volume 0 1 :=
      (continuous_const.mul (continuous_id.pow 3)).intervalIntegrable 0 1
    have h6x2 :
        IntervalIntegrable (fun x : ℝ => 6 * x ^ 2)
          MeasureTheory.volume 0 1 :=
      (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 1
    have h4x :
        IntervalIntegrable (fun x : ℝ => 4 * x)
          MeasureTheory.volume 0 1 :=
      (continuous_const.mul continuous_id).intervalIntegrable 0 1
    have hone :
        IntervalIntegrable (fun _x : ℝ => (1 : ℝ))
          MeasureTheory.volume 0 1 :=
      continuous_const.intervalIntegrable 0 1
    calc
      (∫ x in (0 : ℝ)..1, (x + 1) ^ 4) =
          ∫ x in (0 : ℝ)..1,
            (((x ^ 4 + 4 * x ^ 3) + 6 * x ^ 2) + 4 * x) + 1 := by
              apply intervalIntegral.integral_congr
              intro x hx
              ring
      _ = ((((∫ x in (0 : ℝ)..1, x ^ 4) +
              ∫ x in (0 : ℝ)..1, 4 * x ^ 3) +
            ∫ x in (0 : ℝ)..1, 6 * x ^ 2) +
          ∫ x in (0 : ℝ)..1, 4 * x) +
        ∫ _x in (0 : ℝ)..1, (1 : ℝ) := by
          rw [intervalIntegral.integral_add
              (((hx4.add h4x3).add h6x2).add h4x) hone,
            intervalIntegral.integral_add
              ((hx4.add h4x3).add h6x2) h4x,
            intervalIntegral.integral_add (hx4.add h4x3) h6x2,
            intervalIntegral.integral_add hx4 h4x3]
      _ = (∫ x in (0 : ℝ)..1, x ^ 4) + 6 := by
        rw [intervalIntegral.integral_const_mul, integral_cube_zero_one,
          intervalIntegral.integral_const_mul, integral_sq_zero_one,
          intervalIntegral.integral_const_mul, integral_id_zero_one,
          intervalIntegral.integral_const]
        norm_num
        ring
  have hsplit :
      (∫ x in (0 : ℝ)..2, x ^ 4) =
        (∫ x in (0 : ℝ)..1, x ^ 4) +
          ∫ x in (0 : ℝ)..1, (x + 1) ^ 4 := by
    calc
      (∫ x in (0 : ℝ)..2, x ^ 4) =
          (∫ x in (0 : ℝ)..1, x ^ 4) +
            ∫ x in (1 : ℝ)..2, x ^ 4 :=
        (intervalIntegral.integral_add_adjacent_intervals hp01 hp12).symm
      _ = (∫ x in (0 : ℝ)..1, x ^ 4) +
            ∫ x in (0 : ℝ)..1, (x + 1) ^ 4 := by
        congr 1
        symm
        convert
          (intervalIntegral.integral_comp_add_right
            (fun x : ℝ => x ^ 4) (a := (0 : ℝ)) (b := 1) 1) using 1 <;>
          norm_num
  rw [htranslated] at hsplit
  nlinarith [hscale, hsplit]

private theorem integral_fifth_zero_one :
    (∫ x in (0 : ℝ)..1, x ^ 5) = 1 / 6 := by
  have hone :
      IntervalIntegrable (fun _x : ℝ => (1 : ℝ))
        MeasureTheory.volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  have h5x :
      IntervalIntegrable (fun x : ℝ => 5 * x)
        MeasureTheory.volume 0 1 :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 1
  have h10x2 :
      IntervalIntegrable (fun x : ℝ => 10 * x ^ 2)
        MeasureTheory.volume 0 1 :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 1
  have h10x3 :
      IntervalIntegrable (fun x : ℝ => 10 * x ^ 3)
        MeasureTheory.volume 0 1 :=
    (continuous_const.mul (continuous_id.pow 3)).intervalIntegrable 0 1
  have h5x4 :
      IntervalIntegrable (fun x : ℝ => 5 * x ^ 4)
        MeasureTheory.volume 0 1 :=
    (continuous_const.mul (continuous_id.pow 4)).intervalIntegrable 0 1
  have hx5 :
      IntervalIntegrable (fun x : ℝ => x ^ 5)
        MeasureTheory.volume 0 1 :=
    (continuous_id.pow 5).intervalIntegrable 0 1
  have hpoly :
      (∫ x in (0 : ℝ)..1, (1 - x) ^ 5) =
        1 / 3 - ∫ x in (0 : ℝ)..1, x ^ 5 := by
    calc
      (∫ x in (0 : ℝ)..1, (1 - x) ^ 5) =
          ∫ x in (0 : ℝ)..1,
            ((((1 - 5 * x) + 10 * x ^ 2) - 10 * x ^ 3) +
              5 * x ^ 4) - x ^ 5 := by
                apply intervalIntegral.integral_congr
                intro x hx
                ring
      _ = (((((∫ _x in (0 : ℝ)..1, (1 : ℝ)) -
                ∫ x in (0 : ℝ)..1, 5 * x) +
              ∫ x in (0 : ℝ)..1, 10 * x ^ 2) -
            ∫ x in (0 : ℝ)..1, 10 * x ^ 3) +
          ∫ x in (0 : ℝ)..1, 5 * x ^ 4) -
        ∫ x in (0 : ℝ)..1, x ^ 5 := by
          rw [intervalIntegral.integral_sub
              ((((hone.sub h5x).add h10x2).sub h10x3).add h5x4) hx5,
            intervalIntegral.integral_add
              (((hone.sub h5x).add h10x2).sub h10x3) h5x4,
            intervalIntegral.integral_sub
              ((hone.sub h5x).add h10x2) h10x3,
            intervalIntegral.integral_add (hone.sub h5x) h10x2,
            intervalIntegral.integral_sub hone h5x]
      _ = 1 / 3 - ∫ x in (0 : ℝ)..1, x ^ 5 := by
        rw [intervalIntegral.integral_const,
          intervalIntegral.integral_const_mul, integral_id_zero_one,
          intervalIntegral.integral_const_mul, integral_sq_zero_one,
          intervalIntegral.integral_const_mul, integral_cube_zero_one,
          intervalIntegral.integral_const_mul, integral_fourth_zero_one]
        norm_num
  have hreflect :
      (∫ x in (0 : ℝ)..1, (1 - x) ^ 5) =
        ∫ x in (0 : ℝ)..1, x ^ 5 := by
    simpa using
      (intervalIntegral.integral_comp_sub_left
        (f := fun x : ℝ => x ^ 5) (a := (0 : ℝ)) (b := 1) 1)
  linarith [hpoly, hreflect]

private theorem integral_sixth_zero_one :
    (∫ x in (0 : ℝ)..1, x ^ 6) = 1 / 7 := by
  have hp01 :
      IntervalIntegrable (fun x : ℝ => x ^ 6)
        MeasureTheory.volume 0 1 :=
    (continuous_id.pow 6).intervalIntegrable 0 1
  have hp12 :
      IntervalIntegrable (fun x : ℝ => x ^ 6)
        MeasureTheory.volume 1 2 :=
    (continuous_id.pow 6).intervalIntegrable 1 2
  have hscaled :
      (∫ x in (0 : ℝ)..1, (2 * x) ^ 6) =
        64 * ∫ x in (0 : ℝ)..1, x ^ 6 := by
    calc
      (∫ x in (0 : ℝ)..1, (2 * x) ^ 6) =
          ∫ x in (0 : ℝ)..1, 64 * x ^ 6 := by
            apply intervalIntegral.integral_congr
            intro x hx
            ring
      _ = 64 * ∫ x in (0 : ℝ)..1, x ^ 6 := by
        rw [intervalIntegral.integral_const_mul]
  have hscale :
      128 * (∫ x in (0 : ℝ)..1, x ^ 6) =
        ∫ x in (0 : ℝ)..2, x ^ 6 := by
    have h := intervalIntegral.smul_integral_comp_mul_left
      (fun x : ℝ => x ^ 6) (a := (0 : ℝ)) (b := 1) 2
    rw [hscaled] at h
    norm_num [smul_eq_mul] at h ⊢
    linarith
  have htranslated :
      (∫ x in (0 : ℝ)..1, (x + 1) ^ 6) =
        (∫ x in (0 : ℝ)..1, x ^ 6) + 18 := by
    have hx6 :
        IntervalIntegrable (fun x : ℝ => x ^ 6)
          MeasureTheory.volume 0 1 :=
      (continuous_id.pow 6).intervalIntegrable 0 1
    have h6x5 :
        IntervalIntegrable (fun x : ℝ => 6 * x ^ 5)
          MeasureTheory.volume 0 1 :=
      (continuous_const.mul (continuous_id.pow 5)).intervalIntegrable 0 1
    have h15x4 :
        IntervalIntegrable (fun x : ℝ => 15 * x ^ 4)
          MeasureTheory.volume 0 1 :=
      (continuous_const.mul (continuous_id.pow 4)).intervalIntegrable 0 1
    have h20x3 :
        IntervalIntegrable (fun x : ℝ => 20 * x ^ 3)
          MeasureTheory.volume 0 1 :=
      (continuous_const.mul (continuous_id.pow 3)).intervalIntegrable 0 1
    have h15x2 :
        IntervalIntegrable (fun x : ℝ => 15 * x ^ 2)
          MeasureTheory.volume 0 1 :=
      (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 1
    have h6x :
        IntervalIntegrable (fun x : ℝ => 6 * x)
          MeasureTheory.volume 0 1 :=
      (continuous_const.mul continuous_id).intervalIntegrable 0 1
    have hone :
        IntervalIntegrable (fun _x : ℝ => (1 : ℝ))
          MeasureTheory.volume 0 1 :=
      continuous_const.intervalIntegrable 0 1
    calc
      (∫ x in (0 : ℝ)..1, (x + 1) ^ 6) =
          ∫ x in (0 : ℝ)..1,
            ((((((x ^ 6 + 6 * x ^ 5) + 15 * x ^ 4) + 20 * x ^ 3) +
              15 * x ^ 2) + 6 * x) + 1) := by
                apply intervalIntegral.integral_congr
                intro x hx
                ring
      _ = ((((((∫ x in (0 : ℝ)..1, x ^ 6) +
                  ∫ x in (0 : ℝ)..1, 6 * x ^ 5) +
                ∫ x in (0 : ℝ)..1, 15 * x ^ 4) +
              ∫ x in (0 : ℝ)..1, 20 * x ^ 3) +
            ∫ x in (0 : ℝ)..1, 15 * x ^ 2) +
          ∫ x in (0 : ℝ)..1, 6 * x) +
        ∫ _x in (0 : ℝ)..1, (1 : ℝ) := by
          rw [intervalIntegral.integral_add
              (((((hx6.add h6x5).add h15x4).add h20x3).add h15x2).add h6x)
              hone,
            intervalIntegral.integral_add
              ((((hx6.add h6x5).add h15x4).add h20x3).add h15x2) h6x,
            intervalIntegral.integral_add
              (((hx6.add h6x5).add h15x4).add h20x3) h15x2,
            intervalIntegral.integral_add
              ((hx6.add h6x5).add h15x4) h20x3,
            intervalIntegral.integral_add (hx6.add h6x5) h15x4,
            intervalIntegral.integral_add hx6 h6x5]
      _ = (∫ x in (0 : ℝ)..1, x ^ 6) + 18 := by
        rw [intervalIntegral.integral_const_mul, integral_fifth_zero_one,
          intervalIntegral.integral_const_mul, integral_fourth_zero_one,
          intervalIntegral.integral_const_mul, integral_cube_zero_one,
          intervalIntegral.integral_const_mul, integral_sq_zero_one,
          intervalIntegral.integral_const_mul, integral_id_zero_one,
          intervalIntegral.integral_const]
        norm_num
        ring
  have hsplit :
      (∫ x in (0 : ℝ)..2, x ^ 6) =
        (∫ x in (0 : ℝ)..1, x ^ 6) +
          ∫ x in (0 : ℝ)..1, (x + 1) ^ 6 := by
    calc
      (∫ x in (0 : ℝ)..2, x ^ 6) =
          (∫ x in (0 : ℝ)..1, x ^ 6) +
            ∫ x in (1 : ℝ)..2, x ^ 6 :=
        (intervalIntegral.integral_add_adjacent_intervals hp01 hp12).symm
      _ = (∫ x in (0 : ℝ)..1, x ^ 6) +
            ∫ x in (0 : ℝ)..1, (x + 1) ^ 6 := by
        congr 1
        symm
        convert
          (intervalIntegral.integral_comp_add_right
            (fun x : ℝ => x ^ 6) (a := (0 : ℝ)) (b := 1) 1) using 1 <;>
          norm_num
  rw [htranslated] at hsplit
  nlinarith [hscale, hsplit]

private theorem integral_sq_interval (a b : ℝ) :
    (∫ x in a..b, x ^ 2) = (b ^ 3 - a ^ 3) / 3 := by
  have hx2 :
      IntervalIntegrable (fun x : ℝ => (b - a) ^ 2 * x ^ 2)
        MeasureTheory.volume 0 1 :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 1
  have hx :
      IntervalIntegrable
        (fun x : ℝ => (2 * a * (b - a)) * x)
        MeasureTheory.volume 0 1 :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 1
  have hc :
      IntervalIntegrable (fun _x : ℝ => a ^ 2)
        MeasureTheory.volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  have haffine :
      (∫ x in (0 : ℝ)..1, ((b - a) * x + a) ^ 2) =
        (b - a) ^ 2 * (1 / 3) +
          (2 * a * (b - a)) * (1 / 2) + a ^ 2 := by
    calc
      (∫ x in (0 : ℝ)..1, ((b - a) * x + a) ^ 2) =
          ∫ x in (0 : ℝ)..1,
            ((b - a) ^ 2 * x ^ 2 +
              (2 * a * (b - a)) * x) + a ^ 2 := by
                apply intervalIntegral.integral_congr
                intro x hx
                ring
      _ = ((∫ x in (0 : ℝ)..1, (b - a) ^ 2 * x ^ 2) +
            ∫ x in (0 : ℝ)..1, (2 * a * (b - a)) * x) +
          ∫ _x in (0 : ℝ)..1, a ^ 2 := by
            rw [intervalIntegral.integral_add (hx2.add hx) hc,
              intervalIntegral.integral_add hx2 hx]
      _ = (b - a) ^ 2 * (1 / 3) +
          (2 * a * (b - a)) * (1 / 2) + a ^ 2 := by
            rw [intervalIntegral.integral_const_mul, integral_sq_zero_one,
              intervalIntegral.integral_const_mul, integral_id_zero_one,
              intervalIntegral.integral_const]
            norm_num
  have hchange :
      (b - a) * (∫ x in (0 : ℝ)..1, ((b - a) * x + a) ^ 2) =
        ∫ x in a..b, x ^ 2 := by
    convert
      (intervalIntegral.smul_integral_comp_mul_add
        (fun x : ℝ => x ^ 2) (a := (0 : ℝ)) (b := 1) (b - a) a) using 1 <;>
      simp [smul_eq_mul] <;> ring
  rw [haffine] at hchange
  rw [← hchange]
  ring

theorem gap4 :
    (∫ x in (0 : ℝ)..1,
        ∫ y in x ^ 2..x, x ^ 2 + y ^ 2) =
      ∫ x in (0 : ℝ)..1,
        (4 / 3 * x ^ 3 - x ^ 4 - 1 / 3 * x ^ 6) := by
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  have hc :
      IntervalIntegrable (fun _y : ℝ => x ^ 2)
        MeasureTheory.volume (x ^ 2) x :=
    continuous_const.intervalIntegrable (x ^ 2) x
  have hs :
      IntervalIntegrable (fun y : ℝ => y ^ 2)
        MeasureTheory.volume (x ^ 2) x :=
    (continuous_id.pow 2).intervalIntegrable (x ^ 2) x
  rw [intervalIntegral.integral_add hc hs,
    intervalIntegral.integral_const, integral_sq_interval]
  simp only [smul_eq_mul]
  ring

theorem gap5 :
    volume =
      ∫ x in (0 : ℝ)..1,
        (4 / 3 * x ^ 3 - x ^ 4 - 1 / 3 * x ^ 6) := by
  rw [gap2, gap3, gap4]

theorem gap6 :
    volume = endpointPrimitive 1 - endpointPrimitive 0 := by
  rw [gap5]
  have h3 :
      IntervalIntegrable (fun x : ℝ => 4 / 3 * x ^ 3)
        MeasureTheory.volume 0 1 :=
    (continuous_const.mul (continuous_id.pow 3)).intervalIntegrable 0 1
  have h4 :
      IntervalIntegrable (fun x : ℝ => x ^ 4)
        MeasureTheory.volume 0 1 :=
    (continuous_id.pow 4).intervalIntegrable 0 1
  have h6 :
      IntervalIntegrable (fun x : ℝ => 1 / 3 * x ^ 6)
        MeasureTheory.volume 0 1 :=
    (continuous_const.mul (continuous_id.pow 6)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_sub (h3.sub h4) h6,
    intervalIntegral.integral_sub h3 h4,
    intervalIntegral.integral_const_mul, integral_cube_zero_one,
    integral_fourth_zero_one,
    intervalIntegral.integral_const_mul, integral_sixth_zero_one]
  norm_num [endpointPrimitive]

theorem gap7 :
    endpointPrimitive 1 - endpointPrimitive 0 = 3 / 35 := by
  norm_num [endpointPrimitive]

theorem gap8 :
    volume = 3 / 35 := by
  rw [gap6, gap7]

end

end ProofGap.Exercise4101
