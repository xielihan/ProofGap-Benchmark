import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1046

noncomputable section

def xCoord (t : ℝ) : ℝ :=
  Real.arcsin (t / Real.sqrt (1 + t ^ 2))

def yCoord (t : ℝ) : ℝ :=
  Real.arccos (1 / Real.sqrt (1 + t ^ 2))

def yExpanded (t : ℝ) : ℝ :=
  -(1 / Real.sqrt (1 - 1 / (1 + t ^ 2))) *
    (-(t / Real.rpow (1 + t ^ 2) (3 / 2 : ℝ)))

def xExpanded (t : ℝ) : ℝ :=
  (1 / Real.sqrt (1 - t ^ 2 / (1 + t ^ 2))) *
    ((Real.sqrt (1 + t ^ 2) - t ^ 2 / Real.sqrt (1 + t ^ 2)) /
      (1 + t ^ 2))

def paramDerivative (t : ℝ) : ℝ := deriv yCoord t / deriv xCoord t

private theorem hasDerivAt_sqrt_one_add_sq (t : ℝ) :
    HasDerivAt (fun z : ℝ => Real.sqrt (1 + z ^ 2))
      (t / Real.sqrt (1 + t ^ 2)) t := by
  have hq : 0 < 1 + t ^ 2 := by
    nlinarith [sq_nonneg t]
  have hs : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.2 hq
  have hbase0 :=
    (hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).pow 2)
  have hbase :
      HasDerivAt (fun z : ℝ => 1 + z ^ 2) (2 * t) t := by
    convert hbase0 using 1 <;> norm_num
  have hcomp :
      HasDerivAt (fun z : ℝ => Real.sqrt (1 + z ^ 2))
        ((1 / (2 * Real.sqrt (1 + t ^ 2))) * (2 * t)) t := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_sqrt hq.ne').comp t hbase
  convert hcomp using 1
  field_simp [hs.ne'] <;> ring

theorem gap1 (t : ℝ) (ht : t ≠ 0) :
    deriv yCoord t = yExpanded t := by
  apply HasDerivAt.deriv
  unfold yCoord yExpanded
  have hq : 0 < 1 + t ^ 2 := by
    nlinarith [sq_nonneg t]
  have hs : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.2 hq
  have hsq : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 :=
    Real.sq_sqrt hq.le
  have hrpow :
      Real.rpow (1 + t ^ 2) (3 / 2 : ℝ) =
        (1 + t ^ 2) * Real.sqrt (1 + t ^ 2) := by
    change (1 + t ^ 2) ^ (3 / 2 : ℝ) =
      (1 + t ^ 2) * Real.sqrt (1 + t ^ 2)
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num]
    rw [Real.rpow_add hq, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hrecip0 :
      HasDerivAt
        (fun z : ℝ => 1 / Real.sqrt (1 + z ^ 2))
        ((0 * Real.sqrt (1 + t ^ 2) -
            1 * (t / Real.sqrt (1 + t ^ 2))) /
          Real.sqrt (1 + t ^ 2) ^ 2) t :=
    (hasDerivAt_const t 1).div (hasDerivAt_sqrt_one_add_sq t) hs.ne'
  have hcoef :
      (0 * Real.sqrt (1 + t ^ 2) -
          1 * (t / Real.sqrt (1 + t ^ 2))) /
          Real.sqrt (1 + t ^ 2) ^ 2 =
        -(t / Real.rpow (1 + t ^ 2) (3 / 2 : ℝ)) := by
    rw [hrpow, hsq]
    field_simp [hs.ne', hq.ne']
    ring
  have hrecip :
      HasDerivAt
        (fun z : ℝ => 1 / Real.sqrt (1 + z ^ 2))
        (-(t / Real.rpow (1 + t ^ 2) (3 / 2 : ℝ))) t := by
    rw [← hcoef]
    exact hrecip0
  have hsone : 1 < Real.sqrt (1 + t ^ 2) := by
    have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht
    nlinarith
  have hv :
      1 / Real.sqrt (1 + t ^ 2) ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · have hvpos : 0 < 1 / Real.sqrt (1 + t ^ 2) := one_div_pos.mpr hs
      linarith
    · apply (div_lt_iff₀ hs).2
      simpa using hsone
  have hinv_sq :
      (Real.sqrt (1 + t ^ 2))⁻¹ ^ 2 = (1 + t ^ 2)⁻¹ := by
    rw [inv_pow, hsq]
  simpa only [Function.comp_apply, hinv_sq, one_div] using
    (Real.hasDerivAt_arccos hv.1.ne' hv.2.ne).comp t hrecip

theorem gap2 (t : ℝ) (ht : t ≠ 0) :
    yExpanded t = Real.sign t / (1 + t ^ 2) := by
  unfold yExpanded
  have hq : 0 < 1 + t ^ 2 := by
    nlinarith [sq_nonneg t]
  have hs : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.2 hq
  have hi :
      1 - 1 / (1 + t ^ 2) = t ^ 2 / (1 + t ^ 2) := by
    field_simp [hq.ne'] <;> ring
  have hrpow :
      Real.rpow (1 + t ^ 2) (3 / 2 : ℝ) =
        (1 + t ^ 2) * Real.sqrt (1 + t ^ 2) := by
    change (1 + t ^ 2) ^ (3 / 2 : ℝ) =
      (1 + t ^ 2) * Real.sqrt (1 + t ^ 2)
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num]
    rw [Real.rpow_add hq, Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hi, Real.sqrt_div (sq_nonneg t), Real.sqrt_sq_eq_abs, hrpow]
  rcases lt_or_gt_of_ne ht with htneg | htpos
  · rw [Real.sign_of_neg htneg, abs_of_neg htneg]
    field_simp [hs.ne', hq.ne', htneg.ne] <;> ring
  · rw [Real.sign_of_pos htpos, abs_of_pos htpos]
    field_simp [hs.ne', hq.ne', htpos.ne'] <;> ring

theorem gap3 (t : ℝ) (ht : t ≠ 0) :
    deriv yCoord t = Real.sign t / (1 + t ^ 2) := by
  rw [gap1 t ht, gap2 t ht]

theorem gap4 (t : ℝ) :
    deriv xCoord t = xExpanded t := by
  apply HasDerivAt.deriv
  unfold xCoord xExpanded
  have hq : 0 < 1 + t ^ 2 := by
    nlinarith [sq_nonneg t]
  have hs : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.2 hq
  have hsq : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 :=
    Real.sq_sqrt hq.le
  have hfrac0 :
      HasDerivAt
        (fun z : ℝ => z / Real.sqrt (1 + z ^ 2))
        ((1 * Real.sqrt (1 + t ^ 2) -
            t * (t / Real.sqrt (1 + t ^ 2))) /
          Real.sqrt (1 + t ^ 2) ^ 2) t :=
    (hasDerivAt_id t).div (hasDerivAt_sqrt_one_add_sq t) hs.ne'
  have hcoef :
      (1 * Real.sqrt (1 + t ^ 2) -
          t * (t / Real.sqrt (1 + t ^ 2))) /
          Real.sqrt (1 + t ^ 2) ^ 2 =
        (Real.sqrt (1 + t ^ 2) -
            t ^ 2 / Real.sqrt (1 + t ^ 2)) / (1 + t ^ 2) := by
    rw [hsq]
    ring
  have hfrac :
      HasDerivAt
        (fun z : ℝ => z / Real.sqrt (1 + z ^ 2))
        ((Real.sqrt (1 + t ^ 2) -
            t ^ 2 / Real.sqrt (1 + t ^ 2)) / (1 + t ^ 2)) t := by
    rw [← hcoef]
    exact hfrac0
  have hut : t < Real.sqrt (1 + t ^ 2) := by
    nlinarith [sq_nonneg (t - Real.sqrt (1 + t ^ 2))]
  have hlu : -Real.sqrt (1 + t ^ 2) < t := by
    nlinarith [sq_nonneg (t + Real.sqrt (1 + t ^ 2))]
  have hu :
      t / Real.sqrt (1 + t ^ 2) ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · apply (lt_div_iff₀ hs).2
      simpa using hlu
    · exact (div_lt_one hs).2 hut
  have hfrac_sq :
      (t / Real.sqrt (1 + t ^ 2)) ^ 2 = t ^ 2 / (1 + t ^ 2) := by
    rw [div_pow, hsq]
  simpa only [Function.comp_apply, hfrac_sq, one_div] using
    (Real.hasDerivAt_arcsin hu.1.ne' hu.2.ne).comp t hfrac

theorem gap5 (t : ℝ) :
    xExpanded t = 1 / (1 + t ^ 2) := by
  unfold xExpanded
  have hq : 0 < 1 + t ^ 2 := by
    nlinarith [sq_nonneg t]
  have hs : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.2 hq
  have hsq : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 :=
    Real.sq_sqrt hq.le
  have hi :
      1 - t ^ 2 / (1 + t ^ 2) = 1 / (1 + t ^ 2) := by
    field_simp [hq.ne'] <;> ring
  rw [hi, Real.sqrt_div (by positivity), Real.sqrt_one]
  field_simp [hs.ne', hq.ne'] <;> nlinarith [hsq]

theorem gap6 (t : ℝ) :
    deriv xCoord t = 1 / (1 + t ^ 2) := by
  rw [gap4 t, gap5 t]

theorem gap7 (t : ℝ) (ht : t ≠ 0) :
    paramDerivative t =
      (Real.sign t / (1 + t ^ 2)) / (1 / (1 + t ^ 2)) := by
  unfold paramDerivative
  rw [gap3 t ht, gap6 t]

theorem gap8 (t : ℝ) :
    (Real.sign t / (1 + t ^ 2)) / (1 / (1 + t ^ 2)) =
      Real.sign t := by
  have hq : 1 + t ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg t]
  field_simp [hq]

theorem gap9 (t : ℝ) (ht : t ≠ 0) :
    paramDerivative t = Real.sign t := by
  rw [gap7 t ht, gap8 t]

end

end ProofGap.Exercise1046
