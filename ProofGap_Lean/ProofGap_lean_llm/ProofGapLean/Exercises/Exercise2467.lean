import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped Interval

namespace ProofGap.Exercise2467

noncomputable section

def firstOctantSection (a b x : ℝ) : ℝ :=
  ∫ _y in 0..Real.sqrt (a * x - x ^ 2),
    Real.sqrt (b * (a - x))

def quarterVolume (a b : ℝ) : ℝ :=
  ∫ x in 0..a, firstOctantSection a b x

def totalVolume (a b : ℝ) : ℝ := 4 * quarterVolume a b

private theorem sqrt_weight_integral (a : ℝ) (ha : 0 ≤ a) :
    (∫ x in 0..a, Real.sqrt x * (a - x)) =
      4 / 15 * a ^ 2 * Real.sqrt a := by
  by_cases ha0 : a = 0
  · subst a
    simp
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    let F : ℝ → ℝ := fun x =>
      (2 * a / 3) * x ^ (3 / 2 : ℝ) -
        (2 / 5) * x ^ (5 / 2 : ℝ)
    have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) a,
        HasDerivAt F (Real.sqrt x * (a - x)) x := by
      intro x hx
      rw [Set.uIcc_of_le ha] at hx
      have hx0 : 0 ≤ x := hx.1
      have h3 : HasDerivAt (fun t : ℝ => t ^ (3 / 2 : ℝ))
          ((3 / 2 : ℝ) * x ^ ((3 / 2 : ℝ) - 1)) x :=
        Real.hasDerivAt_rpow_const (p := (3 / 2 : ℝ))
          (Or.inr (by norm_num))
      have h5 : HasDerivAt (fun t : ℝ => t ^ (5 / 2 : ℝ))
          ((5 / 2 : ℝ) * x ^ ((5 / 2 : ℝ) - 1)) x :=
        Real.hasDerivAt_rpow_const (p := (5 / 2 : ℝ))
          (Or.inr (by norm_num))
      have hd := (h3.const_mul (2 * a / 3)).sub
        (h5.const_mul (2 / 5))
      by_cases hxzero : x = 0
      · subst x
        have hsub3 : (3 / 2 : ℝ) - 1 = 1 / 2 := by norm_num
        have hsub5 : (5 / 2 : ℝ) - 1 = 3 / 2 := by norm_num
        have hzero3 : (0 : ℝ) ^ (1 / 2 : ℝ) = 0 := by norm_num
        have hzero5 : (0 : ℝ) ^ (3 / 2 : ℝ) = 0 := by norm_num
        simpa [F, hsub3, hsub5, hzero3, hzero5] using hd
      · have hx_pos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hxzero)
        have hpow3 : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
          rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
            Real.rpow_add hx_pos, Real.rpow_one, ← Real.sqrt_eq_rpow]
        have hcoef :
            (2 * a / 3) * ((3 / 2 : ℝ) * x ^ ((3 / 2 : ℝ) - 1)) -
                (2 / 5) * ((5 / 2 : ℝ) * x ^ ((5 / 2 : ℝ) - 1)) =
              Real.sqrt x * (a - x) := by
          rw [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num,
            show (5 / 2 : ℝ) - 1 = 3 / 2 by norm_num,
            ← Real.sqrt_eq_rpow, hpow3]
          ring
        simpa only [F, hcoef] using hd
    have hcont : Continuous (fun x : ℝ => Real.sqrt x * (a - x)) :=
      Real.continuous_sqrt.mul (continuous_const.sub continuous_id)
    have hint : IntervalIntegrable (fun x : ℝ => Real.sqrt x * (a - x))
        MeasureTheory.volume 0 a :=
      hcont.intervalIntegrable 0 a
    have hFTC :
        (∫ x in 0..a, Real.sqrt x * (a - x)) = F a - F 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    have hpow3a : a ^ (3 / 2 : ℝ) = a * Real.sqrt a := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
        Real.rpow_add ha_pos, Real.rpow_one, ← Real.sqrt_eq_rpow]
    have hpow5a : a ^ (5 / 2 : ℝ) = a * (a * Real.sqrt a) := by
      rw [show (5 / 2 : ℝ) = 1 + 3 / 2 by norm_num,
        Real.rpow_add ha_pos, Real.rpow_one, hpow3a]
    calc
      (∫ x in 0..a, Real.sqrt x * (a - x)) = F a - F 0 := hFTC
      _ = 4 / 15 * a ^ 2 * Real.sqrt a := by
        simp [F, hpow3a, hpow5a] <;> ring

theorem gap1 (a b x : ℝ) :
    firstOctantSection a b x =
      ∫ _y in 0..Real.sqrt (a * x - x ^ 2),
        Real.sqrt (b * (a - x)) := by
  rfl

theorem gap2 (a b x : ℝ) :
    firstOctantSection a b x =
      Real.sqrt (a * x - x ^ 2) * Real.sqrt (b * (a - x)) := by
  simp [firstOctantSection]

theorem gap3 (a b : ℝ) :
    quarterVolume a b = ∫ x in 0..a, firstOctantSection a b x := by
  rfl

theorem gap4 (a b : ℝ) :
    quarterVolume a b =
      ∫ x in 0..a,
        Real.sqrt (a * x - x ^ 2) * Real.sqrt (b * (a - x)) := by
  simp only [quarterVolume, gap2]

theorem gap5 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    quarterVolume a b =
      Real.sqrt b * ∫ x in 0..a, Real.sqrt x * (a - x) := by
  rw [gap4, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le ha] at hx
  have hx0 : 0 ≤ x := hx.1
  have hax : 0 ≤ a - x := sub_nonneg.mpr hx.2
  change Real.sqrt (a * x - x ^ 2) * Real.sqrt (b * (a - x)) =
    Real.sqrt b * (Real.sqrt x * (a - x))
  have hpoly : a * x - x ^ 2 = x * (a - x) := by ring
  rw [hpoly, Real.sqrt_mul hx0, Real.sqrt_mul hb]
  calc
    (Real.sqrt x * Real.sqrt (a - x)) *
        (Real.sqrt b * Real.sqrt (a - x)) =
        Real.sqrt b * Real.sqrt x * (Real.sqrt (a - x)) ^ 2 := by ring
    _ = Real.sqrt b * (Real.sqrt x * (a - x)) := by
      rw [Real.sq_sqrt hax]
      ring

theorem gap6 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt b * (∫ x in 0..a, Real.sqrt x * (a - x)) =
      4 / 15 * a ^ 2 * Real.sqrt (a * b) := by
  rw [sqrt_weight_integral a ha, Real.sqrt_mul ha]
  ring

theorem gap7 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    quarterVolume a b = 1 / 4 * totalVolume a b ∧
      quarterVolume a b = 4 / 15 * a ^ 2 * Real.sqrt (a * b) := by
  constructor
  · rw [totalVolume]
    ring
  · exact (gap5 a b ha hb).trans (gap6 a b ha hb)

theorem gap8 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    totalVolume a b = 16 / 15 * a ^ 2 * Real.sqrt (a * b) := by
  rw [totalVolume, (gap7 a b ha hb).2]
  ring

end

end ProofGap.Exercise2467
