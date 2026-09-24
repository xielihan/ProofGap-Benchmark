import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise4102

noncomputable section

open MeasureTheory
open scoped Interval

def region : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 * p.2.1 ≤ p.2.2 ∧ p.2.2 ≤ p.1 + p.2.1 ∧
    p.1 + p.2.1 ≤ 1 ∧ 0 ≤ p.1 ∧ 0 ≤ p.2.1}

def volume : ℝ :=
  ∫ _ in region, (1 : ℝ)

theorem gap1 :
    region =
      {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧
        0 ≤ p.2.1 ∧ p.2.1 ≤ 1 - p.1 ∧
        p.1 * p.2.1 ≤ p.2.2 ∧ p.2.2 ≤ p.1 + p.2.1} := by
  ext p
  simp only [region, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hzLower, hzUpper, hxy, hx, hy⟩
    have hx1 : p.1 ≤ 1 := by linarith
    have hy1 : p.2.1 ≤ 1 - p.1 := by linarith
    exact ⟨hx, hx1, hy, hy1, hzLower, hzUpper⟩
  · rintro ⟨hx, hx1, hy, hy1, hzLower, hzUpper⟩
    exact ⟨hzLower, hzUpper, by linarith, hx, hy⟩

theorem gap2 :
    volume =
      ∫ x in (0 : ℝ)..1,
        ∫ y in (0 : ℝ)..1 - x,
          ∫ z in x * y..x + y, (1 : ℝ) := by
  classical
  have hs : MeasurableSet region := by
    unfold region
    measurability
  have hsubset :
      region ⊆
        Set.Icc (0 : ℝ) 1 ×ˢ
          (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro q hq
    have hq' :
        0 ≤ q.1 ∧ q.1 ≤ 1 ∧
          0 ≤ q.2.1 ∧ q.2.1 ≤ 1 - q.1 ∧
          q.1 * q.2.1 ≤ q.2.2 ∧
          q.2.2 ≤ q.1 + q.2.1 := by
      have hq'' := hq
      rw [gap1] at hq''
      exact hq''
    rcases hq' with
      ⟨hx0, hx1, hy0, hyUpper, hzLower, hzUpper⟩
    have hy1 : q.2.1 ≤ 1 := by linarith
    have hz0 : 0 ≤ q.2.2 := by
      nlinarith [mul_nonneg hx0 hy0]
    have hz1 : q.2.2 ≤ 1 := by linarith
    exact ⟨⟨hx0, hx1⟩, ⟨⟨hy0, hy1⟩, hz0, hz1⟩⟩
  have hbox :
      IntegrableOn (fun _q : ℝ × ℝ × ℝ => (1 : ℝ))
        (Set.Icc (0 : ℝ) 1 ×ˢ
          (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
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
          ∫ y in Set.Icc (0 : ℝ) (1 - x),
            ∫ z in Set.Icc (x * y) (x + y), (1 : ℝ) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
    · rw [Set.indicator_of_mem hx]
      rw [← MeasureTheory.integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards with y
      by_cases hy : y ∈ Set.Icc (0 : ℝ) (1 - x)
      · rw [Set.indicator_of_mem hy]
        rw [← MeasureTheory.integral_indicator measurableSet_Icc]
        apply integral_congr_ae
        filter_upwards with z
        by_cases hz : z ∈ Set.Icc (x * y) (x + y)
        · have hr : (x, y, z) ∈ region := by
            exact
              ⟨hz.1, hz.2, by linarith [hx.2, hy.2], hx.1, hy.1⟩
          simp only [Set.indicator_of_mem hz, Set.indicator_of_mem hr]
        · have hnr : (x, y, z) ∉ region := by
            intro hr
            exact hz ⟨hr.1, hr.2.1⟩
          simp [Set.indicator, hz, hnr]
      · have hyr :
            (Set.Icc (0 : ℝ) (1 - x)).indicator
              (fun y =>
                ∫ z in Set.Icc (x * y) (x + y), (1 : ℝ)) y = 0 := by
          simp [Set.indicator, hy]
        rw [hyr, ← integral_zero]
        apply integral_congr_ae
        filter_upwards with z
        have hnr : (x, y, z) ∉ region := by
          intro hr
          have hr' :
              0 ≤ x ∧ x ≤ 1 ∧
                0 ≤ y ∧ y ≤ 1 - x ∧
                x * y ≤ z ∧ z ≤ x + y := by
            have hr'' := hr
            rw [gap1] at hr''
            exact hr''
          exact hy ⟨hr'.2.2.1, hr'.2.2.2.1⟩
        simp [Set.indicator, hnr]
    · have hxr :
          (Set.Icc (0 : ℝ) 1).indicator
            (fun x =>
              ∫ y in Set.Icc (0 : ℝ) (1 - x),
                ∫ z in Set.Icc (x * y) (x + y), (1 : ℝ)) x = 0 := by
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
              0 ≤ y ∧ y ≤ 1 - x ∧
              x * y ≤ z ∧ z ≤ x + y := by
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
          ∫ y in Set.Icc (0 : ℝ) (1 - x),
            ∫ z in Set.Icc (x * y) (x + y), (1 : ℝ) := hsections
    _ = ∫ x in (0 : ℝ)..1,
          ∫ y in (0 : ℝ)..1 - x,
            ∫ z in x * y..x + y, (1 : ℝ) := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      dsimp only
      have hyorder : (0 : ℝ) ≤ 1 - x := by linarith [hx.2]
      rw [intervalIntegral.integral_of_le hyorder]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro y hy
      dsimp only
      have hy1 : y ≤ 1 := by linarith [hx.1, hy.2]
      have hzorder : x * y ≤ x + y := by
        have hxyx : x * y ≤ x :=
          (mul_le_iff_le_one_right hx.1).2 hy1
        linarith [hxyx, hy.1]
      rw [intervalIntegral.integral_of_le hzorder]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]

theorem gap3 :
    (∫ x in (0 : ℝ)..1,
        ∫ y in (0 : ℝ)..1 - x,
          ∫ z in x * y..x + y, (1 : ℝ)) =
      ∫ x in (0 : ℝ)..1,
        ∫ y in (0 : ℝ)..1 - x, x + y - x * y := by
  apply intervalIntegral.integral_congr
  intro x hx
  apply intervalIntegral.integral_congr
  intro y hy
  change (∫ z in x * y..x + y, (1 : ℝ)) = x + y - x * y
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul, mul_one]

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

private theorem integral_id_zero_right (b : ℝ) :
    (∫ x in (0 : ℝ)..b, x) = b ^ 2 / 2 := by
  have hscaled :
      (∫ x in (0 : ℝ)..1, b * x) =
        b * ∫ x in (0 : ℝ)..1, x := by
    rw [intervalIntegral.integral_const_mul]
  have hchange :
      b * (∫ x in (0 : ℝ)..1, b * x) =
        ∫ x in (0 : ℝ)..b, x := by
    convert
      (intervalIntegral.smul_integral_comp_mul_left
        (fun x : ℝ => x) (a := (0 : ℝ)) (b := 1) b) using 1 <;>
      simp [smul_eq_mul] <;> ring
  rw [hscaled, integral_id_zero_one] at hchange
  rw [← hchange]
  ring

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

theorem gap4 :
    (∫ x in (0 : ℝ)..1,
        ∫ y in (0 : ℝ)..1 - x, x + y - x * y) =
      ∫ x in (0 : ℝ)..1,
        x * (1 - x) + (1 - x) ^ 3 / 2 := by
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  have hc :
      IntervalIntegrable (fun _y : ℝ => x)
        MeasureTheory.volume 0 (1 - x) :=
    continuous_const.intervalIntegrable 0 (1 - x)
  have hl :
      IntervalIntegrable (fun y : ℝ => (1 - x) * y)
        MeasureTheory.volume 0 (1 - x) :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 (1 - x)
  calc
    (∫ y in (0 : ℝ)..1 - x, x + y - x * y) =
        ∫ y in (0 : ℝ)..1 - x, x + (1 - x) * y := by
          apply intervalIntegral.integral_congr
          intro y hy
          ring
    _ = (∫ _y in (0 : ℝ)..1 - x, x) +
        ∫ y in (0 : ℝ)..1 - x, (1 - x) * y := by
          rw [intervalIntegral.integral_add hc hl]
    _ = x * (1 - x) +
        (1 - x) * ((1 - x) ^ 2 / 2) := by
          rw [intervalIntegral.integral_const,
            intervalIntegral.integral_const_mul,
            integral_id_zero_right]
          simp only [smul_eq_mul]
          ring
    _ = x * (1 - x) + (1 - x) ^ 3 / 2 := by ring

theorem gap5 :
    (∫ x in (0 : ℝ)..1,
        x * (1 - x) + (1 - x) ^ 3 / 2) =
      7 / 24 := by
  have hid :
      IntervalIntegrable (fun x : ℝ => x)
        MeasureTheory.volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  have hsq :
      IntervalIntegrable (fun x : ℝ => x ^ 2)
        MeasureTheory.volume 0 1 :=
    (continuous_id.pow 2).intervalIntegrable 0 1
  have hcube :
      IntervalIntegrable (fun x : ℝ => (1 - x) ^ 3)
        MeasureTheory.volume 0 1 :=
    ((continuous_const.sub continuous_id).pow 3).intervalIntegrable 0 1
  have hscaled :
      IntervalIntegrable (fun x : ℝ => (1 / 2 : ℝ) * (1 - x) ^ 3)
        MeasureTheory.volume 0 1 :=
    (continuous_const.mul ((continuous_const.sub continuous_id).pow 3)).intervalIntegrable 0 1
  have hreflect :
      (∫ x in (0 : ℝ)..1, (1 - x) ^ 3) =
        ∫ x in (0 : ℝ)..1, x ^ 3 := by
    simpa using
      (intervalIntegral.integral_comp_sub_left
        (f := fun x : ℝ => x ^ 3) (a := (0 : ℝ)) (b := 1) 1)
  calc
    (∫ x in (0 : ℝ)..1,
        x * (1 - x) + (1 - x) ^ 3 / 2) =
      ∫ x in (0 : ℝ)..1,
        (x - x ^ 2) + (1 / 2 : ℝ) * (1 - x) ^ 3 := by
          apply intervalIntegral.integral_congr
          intro x hx
          ring
    _ = ((∫ x in (0 : ℝ)..1, x) -
          ∫ x in (0 : ℝ)..1, x ^ 2) +
        ∫ x in (0 : ℝ)..1, (1 / 2 : ℝ) * (1 - x) ^ 3 := by
          rw [intervalIntegral.integral_add (hid.sub hsq) hscaled,
            intervalIntegral.integral_sub hid hsq]
    _ = ((∫ x in (0 : ℝ)..1, x) -
          ∫ x in (0 : ℝ)..1, x ^ 2) +
        (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..1, (1 - x) ^ 3 := by
          rw [intervalIntegral.integral_const_mul]
    _ = (1 / 2 : ℝ) - 1 / 3 + (1 / 2 : ℝ) * (1 / 4) := by
          rw [integral_id_zero_one, integral_sq_zero_one,
            hreflect, integral_cube_zero_one]
    _ = 7 / 24 := by norm_num

theorem gap6 :
    volume = 7 / 24 := by
  rw [gap2, gap3, gap4, gap5]

end

end ProofGap.Exercise4102
