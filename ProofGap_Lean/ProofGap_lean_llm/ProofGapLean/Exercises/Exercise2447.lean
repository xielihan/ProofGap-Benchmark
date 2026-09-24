import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Filter.Tendsto

open Filter
open scoped Interval

namespace ProofGap.Exercise2447

noncomputable section

def radius (a m φ : ℝ) : ℝ := a * Real.exp (m * φ)

def speed (a m φ : ℝ) : ℝ :=
  Real.sqrt (radius a m φ ^ 2 + (a * m * Real.exp (m * φ)) ^ 2)

theorem gap1 (a m φ : ℝ) (ha : 0 < a) :
    0 < radius a m φ := by
  unfold radius
  exact mul_pos ha (Real.exp_pos _)

theorem gap2 (a m φ : ℝ) (ha : 0 < a) (hm : 0 < m) (hφ : φ < 0) :
    radius a m φ < a := by
  unfold radius
  have harg : m * φ < 0 := mul_neg_of_pos_of_neg hm hφ
  have hexp : Real.exp (m * φ) < 1 := Real.exp_lt_one_iff.mpr harg
  calc
    a * Real.exp (m * φ) < a * 1 := mul_lt_mul_of_pos_left hexp ha
    _ = a := mul_one a

theorem gap3 (a m : ℝ) (ha : 0 < a) (hm : 0 < m) :
    Tendsto (radius a m) atBot (nhds 0) := by
  unfold radius
  have harg : Tendsto (fun φ : ℝ => m * φ) atBot atBot :=
    (tendsto_const_mul_atBot_of_pos hm).2 tendsto_id
  simpa only [mul_zero] using
    (Real.tendsto_exp_atBot.comp harg).const_mul a

theorem gap4 (a m φ : ℝ) (ha : 0 < a) (hm : 0 < m) :
    radius a m φ < a ↔ φ < 0 := by
  constructor
  · intro h
    unfold radius at h
    have hmul : a * Real.exp (m * φ) < a * 1 := by
      simpa only [mul_one] using h
    have hexp : Real.exp (m * φ) < 1 := by
      by_contra hn
      have hone : 1 ≤ Real.exp (m * φ) := le_of_not_gt hn
      have hle : a * 1 ≤ a * Real.exp (m * φ) :=
        mul_le_mul_of_nonneg_left hone (le_of_lt ha)
      exact (not_le_of_gt hmul) hle
    have harg : m * φ < 0 := Real.exp_lt_one_iff.mp hexp
    by_contra hn
    have hφ0 : 0 ≤ φ := le_of_not_gt hn
    have hprod : 0 ≤ m * φ := mul_nonneg (le_of_lt hm) hφ0
    exact (not_le_of_gt harg) hprod
  · intro hφ
    exact gap2 a m φ ha hm hφ

theorem gap5 (a m s : ℝ) (ha : 0 < a) (hm : 0 < m)
    (hs : Tendsto (fun A : ℝ => ∫ φ in A..0, speed a m φ) atBot (nhds s)) :
    Tendsto (fun A : ℝ =>
      ∫ φ in A..0,
        Real.sqrt
          (a ^ 2 * Real.exp (2 * m * φ) +
            a ^ 2 * m ^ 2 * Real.exp (2 * m * φ))) atBot (nhds s) := by
  have hspeed (φ : ℝ) :
      speed a m φ =
        Real.sqrt
          (a ^ 2 * Real.exp (2 * m * φ) +
            a ^ 2 * m ^ 2 * Real.exp (2 * m * φ)) := by
    unfold speed radius
    apply congrArg Real.sqrt
    rw [show 2 * m * φ = m * φ + m * φ by ring, Real.exp_add]
    ring
  simpa only [hspeed] using hs

theorem gap6 (a m φ : ℝ) (ha : 0 < a) :
    speed a m φ =
      a * Real.sqrt (m ^ 2 + 1) * Real.exp (m * φ) := by
  unfold speed radius
  have hae : 0 ≤ a * Real.exp (m * φ) :=
    mul_nonneg (le_of_lt ha) (le_of_lt (Real.exp_pos _))
  calc
    Real.sqrt
        ((a * Real.exp (m * φ)) ^ 2 +
          (a * m * Real.exp (m * φ)) ^ 2) =
        Real.sqrt
          ((a * Real.exp (m * φ)) ^ 2 * (m ^ 2 + 1)) := by
            congr 1
            ring
    _ = Real.sqrt ((a * Real.exp (m * φ)) ^ 2) *
          Real.sqrt (m ^ 2 + 1) := by
            rw [Real.sqrt_mul (sq_nonneg (a * Real.exp (m * φ)))]
    _ = a * Real.sqrt (m ^ 2 + 1) * Real.exp (m * φ) := by
            rw [Real.sqrt_sq hae]
            ring

theorem gap7 (a m s : ℝ) (ha : 0 < a) (hm : 0 < m)
    (hs : Tendsto (fun A : ℝ => ∫ φ in A..0, speed a m φ) atBot (nhds s)) :
    s = a * Real.sqrt (1 + m ^ 2) / m := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hderivint (A : ℝ) :
      (∫ φ in A..0, m * Real.exp (m * φ)) =
        1 - Real.exp (m * A) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := A) (b := 0)
      (f := fun φ : ℝ => Real.exp (m * φ))
      (f' := fun φ : ℝ => m * Real.exp (m * φ))
      (fun φ _ => by
        simpa [mul_comm] using
          (Real.hasDerivAt_exp (m * φ)).comp φ
            ((hasDerivAt_id φ).const_mul m))
    have hcont : Continuous (fun φ : ℝ => m * Real.exp (m * φ)) :=
      continuous_const.mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    have hint :
        IntervalIntegrable
          (fun φ : ℝ => m * Real.exp (m * φ))
          MeasureTheory.volume A 0 :=
      hcont.intervalIntegrable A 0
    simpa using (h hint)
  have hexp (A : ℝ) :
      (∫ φ in A..0, Real.exp (m * φ)) =
        (1 - Real.exp (m * A)) / m := by
    have hscaled := hderivint A
    rw [intervalIntegral.integral_const_mul] at hscaled
    apply (eq_div_iff hm0).2
    simpa [mul_comm] using hscaled
  have hformula (A : ℝ) :
      (∫ φ in A..0, speed a m φ) =
        (a * Real.sqrt (m ^ 2 + 1) / m) *
          (1 - Real.exp (m * A)) := by
    simp_rw [gap6 a m _ ha]
    rw [intervalIntegral.integral_const_mul, hexp]
    ring
  have hexp_lim :
      Tendsto (fun A : ℝ => Real.exp (m * A)) atBot (nhds 0) := by
    have h := gap3 1 m zero_lt_one hm
    change Tendsto (fun A : ℝ => 1 * Real.exp (m * A)) atBot (nhds 0) at h
    simpa only [one_mul] using h
  have hone :
      Tendsto (fun _ : ℝ => (1 : ℝ)) atBot (nhds 1) :=
    tendsto_const_nhds
  have hformula_lim :
      Tendsto
        (fun A : ℝ =>
          (a * Real.sqrt (m ^ 2 + 1) / m) *
            (1 - Real.exp (m * A)))
        atBot
        (nhds (a * Real.sqrt (m ^ 2 + 1) / m)) := by
    simpa using
      (hone.sub hexp_lim).const_mul (a * Real.sqrt (m ^ 2 + 1) / m)
  have hintegral_lim :
      Tendsto (fun A : ℝ => ∫ φ in A..0, speed a m φ) atBot
        (nhds (a * Real.sqrt (m ^ 2 + 1) / m)) := by
    simpa only [hformula] using hformula_lim
  have hs_value : s = a * Real.sqrt (m ^ 2 + 1) / m :=
    tendsto_nhds_unique hs hintegral_lim
  simpa [add_comm] using hs_value

end

end ProofGap.Exercise2447
