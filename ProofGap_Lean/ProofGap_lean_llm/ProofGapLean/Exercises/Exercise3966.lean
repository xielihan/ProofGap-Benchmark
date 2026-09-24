import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3966

noncomputable section

open MeasureTheory
open scoped Interval

def diamond : Set (ℝ × ℝ) :=
  {p | |p.1| + |p.2| ≤ 1}

def diamondNormIntegral : ℝ :=
  ∫ p in diamond, |p.1| + |p.2|

private theorem ae_real_ne (u : ℝ) :
    ∀ᵐ x : ℝ ∂(volume : Measure ℝ), x ≠ u := by
  rw [ae_iff]
  simpa using measure_singleton u

private theorem integral_indicator_Icc_eq_interval
    (u v : ℝ) (f : ℝ → ℝ) (huv : u ≤ v) :
    (∫ x : ℝ, (Set.Icc u v).indicator f x) = ∫ x in u..v, f x := by
  rw [intervalIntegral.integral_of_le huv]
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [ae_real_ne u] with x hx
  by_cases hxc : x ∈ Set.Icc u v
  · have hxo : x ∈ Set.Ioc u v :=
      ⟨lt_of_le_of_ne hxc.1 (Ne.symm hx), hxc.2⟩
    simp [hxc, hxo]
  · have hxo : x ∉ Set.Ioc u v := fun h => hxc ⟨h.1.le, h.2⟩
    simp [hxc, hxo]

private theorem integral_abs_symmetric (c : ℝ) (hc : 0 ≤ c) :
    (∫ y in -c..c, |y|) = c ^ 2 := by
  have habs_left :
      (∫ y in -c..(0 : ℝ), |y|) =
        ∫ y in -c..(0 : ℝ), -y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le (by linarith : -c ≤ (0 : ℝ))] at hy
    exact abs_of_nonpos hy.2
  have habs_right :
      (∫ y in (0 : ℝ)..c, |y|) =
        ∫ y in (0 : ℝ)..c, y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hc] at hy
    exact abs_of_nonneg hy.1
  have hint_left :
      IntervalIntegrable (fun y : ℝ => |y|) volume (-c) 0 :=
    continuous_abs.intervalIntegrable _ _
  have hint_right :
      IntervalIntegrable (fun y : ℝ => |y|) volume 0 c :=
    continuous_abs.intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    hint_left hint_right, habs_left, habs_right]
  rw [intervalIntegral.integral_neg, integral_id, integral_id]
  ring

private theorem diamondNormIntegral_eval :
    diamondNormIntegral = 4 / 3 := by
  let g : ℝ × ℝ → ℝ := fun p => |p.1| + |p.2|
  have hdiamond_closed : IsClosed diamond := by
    exact isClosed_le (continuous_fst.abs.add continuous_snd.abs)
      continuous_const
  have hdiamond_sub :
      diamond ⊆ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 := by
    intro p hp
    change |p.1| + |p.2| ≤ 1 at hp
    have hx : |p.1| ≤ 1 := by linarith [abs_nonneg p.2]
    have hy : |p.2| ≤ 1 := by linarith [abs_nonneg p.1]
    exact ⟨abs_le.1 hx, abs_le.1 hy⟩
  have hdiamond_compact : IsCompact diamond :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset
      hdiamond_closed hdiamond_sub
  have hg_cont : Continuous g := by
    dsimp [g]
    fun_prop
  have hg_diamond : IntegrableOn g diamond :=
    hg_cont.continuousOn.integrableOn_compact hdiamond_compact
  have hind : Integrable (diamond.indicator g) :=
    (integrable_indicator_iff hdiamond_closed.measurableSet).2 hg_diamond
  have hindicator (x y : ℝ) :
      diamond.indicator g (x, y) =
        (Set.Icc (-1 : ℝ) 1).indicator
          (fun x =>
            (Set.Icc (-(1 - |x|)) (1 - |x|)).indicator
              (fun y => |x| + |y|) y) x := by
    by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
    · have hxabs : |x| ≤ 1 := abs_le.2 hx
      by_cases hy : y ∈ Set.Icc (-(1 - |x|)) (1 - |x|)
      · have hyabs : |y| ≤ 1 - |x| := abs_le.2 hy
        have hxy : (x, y) ∈ diamond := by
          change |x| + |y| ≤ 1
          linarith
        rw [Set.indicator_of_mem hxy, Set.indicator_of_mem hx,
          Set.indicator_of_mem hy]
      · have hxy : (x, y) ∉ diamond := by
          intro hmem
          apply hy
          change |x| + |y| ≤ 1 at hmem
          exact abs_le.1 (by linarith)
        rw [Set.indicator_of_notMem hxy, Set.indicator_of_mem hx,
          Set.indicator_of_notMem hy]
    · have hxy : (x, y) ∉ diamond := by
        intro hmem
        apply hx
        change |x| + |y| ≤ 1 at hmem
        exact abs_le.1 (by linarith [abs_nonneg y])
      simp [hxy, hx]
  have hslice :
      diamondNormIntegral =
        ∫ x in (-1 : ℝ)..1,
          ∫ y in -(1 - |x|)..(1 - |x|), |x| + |y| := by
    unfold diamondNormIntegral
    change (∫ p in diamond, g p) = _
    rw [← integral_indicator hdiamond_closed.measurableSet]
    change
      (∫ p : ℝ × ℝ, diamond.indicator g p
        ∂((volume : Measure ℝ).prod volume)) = _
    change Integrable (diamond.indicator g)
      ((volume : Measure ℝ).prod volume) at hind
    rw [integral_prod _ hind]
    have hcollapse (x : ℝ) :
        (∫ y : ℝ,
          (Set.Icc (-1 : ℝ) 1).indicator
            (fun x =>
              (Set.Icc (-(1 - |x|)) (1 - |x|)).indicator
                (fun y => |x| + |y|) y) x) =
          (Set.Icc (-1 : ℝ) 1).indicator
            (fun x =>
              ∫ y : ℝ,
                (Set.Icc (-(1 - |x|)) (1 - |x|)).indicator
                  (fun y => |x| + |y|) y) x := by
      by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1 <;> simp [hx]
    simp_rw [hindicator, hcollapse]
    rw [integral_indicator_Icc_eq_interval (-1) 1 _
      (by norm_num : (-1 : ℝ) ≤ 1)]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    exact integral_indicator_Icc_eq_interval
      (-(1 - |x|)) (1 - |x|) _
      (by
        have : |x| ≤ 1 := abs_le.2 hx
        linarith)
  have hinner (x : ℝ) (hx : x ∈ Set.uIcc (-1 : ℝ) 1) :
      (∫ y in -(1 - |x|)..(1 - |x|), |x| + |y|) =
        1 - x ^ 2 := by
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    have hxabs : |x| ≤ 1 := abs_le.2 hx
    let c : ℝ := 1 - |x|
    have hc : 0 ≤ c := by
      dsimp [c]
      linarith
    have hconst :
        (∫ _y in -c..c, |x|) = 2 * c * |x| := by
      rw [intervalIntegral.integral_const]
      simp only [sub_neg_eq_add, smul_eq_mul]
      ring
    have hconst_int :
        IntervalIntegrable (fun _y : ℝ => |x|) volume (-c) c :=
      continuous_const.intervalIntegrable _ _
    have habs_int :
        IntervalIntegrable (fun y : ℝ => |y|) volume (-c) c :=
      continuous_abs.intervalIntegrable _ _
    change (∫ y in -c..c, |x| + |y|) = 1 - x ^ 2
    rw [intervalIntegral.integral_add hconst_int habs_int,
      hconst, integral_abs_symmetric c hc]
    dsimp [c]
    nlinarith [sq_abs x]
  rw [hslice]
  calc
    (∫ x in (-1 : ℝ)..1,
        ∫ y in -(1 - |x|)..(1 - |x|), |x| + |y|) =
        ∫ x in (-1 : ℝ)..1, 1 - x ^ 2 := by
      apply intervalIntegral.integral_congr
      exact hinner
    _ = 4 / 3 := by
      have hconst :
          IntervalIntegrable (fun _x : ℝ => (1 : ℝ)) volume (-1) 1 :=
        continuous_const.intervalIntegrable _ _
      have hpow :
          IntervalIntegrable (fun x : ℝ => x ^ 2) volume (-1) 1 :=
        (continuous_id.pow 2).intervalIntegrable _ _
      rw [intervalIntegral.integral_sub hconst hpow,
        intervalIntegral.integral_const, integral_pow]
      norm_num

private theorem triangle_iterated_eval :
    (∫ x in (0 : ℝ)..1,
        ∫ y in (0 : ℝ)..1 - x, x + y) =
      1 / 3 := by
  have hinner (x : ℝ) :
      (∫ y in (0 : ℝ)..1 - x, x + y) =
        x * (1 - x) + (1 - x) ^ 2 / 2 := by
    have hconst :
        IntervalIntegrable (fun _y : ℝ => x) volume 0 (1 - x) :=
      continuous_const.intervalIntegrable _ _
    have hid :
        IntervalIntegrable (fun y : ℝ => y) volume 0 (1 - x) :=
      continuous_id.intervalIntegrable _ _
    rw [intervalIntegral.integral_add hconst hid,
      intervalIntegral.integral_const, integral_id]
    norm_num
    ring
  simp_rw [hinner]
  have hpoly :
      (fun x : ℝ => x * (1 - x) + (1 - x) ^ 2 / 2) =
        fun x : ℝ => 1 / 2 - x ^ 2 / 2 := by
    funext x
    ring
  rw [hpoly]
  have hconst :
      IntervalIntegrable (fun _x : ℝ => (1 / 2 : ℝ)) volume 0 1 :=
    continuous_const.intervalIntegrable _ _
  have hpow :
      IntervalIntegrable (fun x : ℝ => x ^ 2 / 2) volume 0 1 :=
    ((continuous_id.pow 2).div_const 2).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hconst hpow,
    intervalIntegral.integral_const,
    intervalIntegral.integral_div, integral_pow]
  norm_num

theorem gap1 :
    diamondNormIntegral =
      4 * ∫ x in (0 : ℝ)..1,
        ∫ y in (0 : ℝ)..1 - x, x + y := by
  rw [diamondNormIntegral_eval, triangle_iterated_eval]
  ring

theorem gap2 :
    4 * (∫ x in (0 : ℝ)..1,
        ∫ y in (0 : ℝ)..1 - x, x + y) =
      4 / 3 := by
  rw [triangle_iterated_eval]
  ring

theorem gap3 :
    diamondNormIntegral = 4 / 3 := by
  exact diamondNormIntegral_eval

end

end ProofGap.Exercise3966
