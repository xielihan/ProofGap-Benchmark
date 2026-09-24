import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3770

noncomputable section

open Set MeasureTheory
open scoped Interval

def singularKernel (α x : ℝ) : ℝ :=
  Real.sin (α * x) / Real.sqrt |x - α|

def leftKernel (α x : ℝ) : ℝ :=
  Real.sin (α * x) / Real.sqrt (α - x)

def rightKernel (α x : ℝ) : ℝ :=
  Real.sin (α * x) / Real.sqrt (x - α)

def leftMajorant (α x : ℝ) : ℝ :=
  1 / Real.sqrt (α - x)

def rightMajorant (α x : ℝ) : ℝ :=
  1 / Real.sqrt (x - α)

def LeftUniformlyConvergent : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ α ∈ Set.Icc (0 : ℝ) 1, ∀ η : ℝ,
        0 < η → η < δ → η ≤ α →
          |∫ x in α - η..α, leftKernel α x| < ε

def RightUniformlyConvergent : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ α ∈ Set.Icc (0 : ℝ) 1, ∀ η : ℝ,
        0 < η → η < δ → η ≤ 1 - α →
          |∫ x in α..α + η, rightKernel α x| < ε

def UniformlyConvergent : Prop :=
  LeftUniformlyConvergent ∧ RightUniformlyConvergent

private theorem one_div_sqrt_eq_rpow {t : ℝ} (ht : 0 ≤ t) :
    1 / Real.sqrt t = t ^ (-1 / 2 : ℝ) := by
  calc
    1 / Real.sqrt t = (t ^ (1 / 2 : ℝ))⁻¹ := by
      rw [Real.sqrt_eq_rpow]
      simp
    _ = t ^ (-(1 / 2 : ℝ)) :=
      (Real.rpow_neg ht (1 / 2 : ℝ)).symm
    _ = t ^ (-1 / 2 : ℝ) := by ring_nf

private theorem base_integral (d : ℝ) :
    (∫ t in (0 : ℝ)..d, t ^ (-1 / 2 : ℝ)) =
      2 * Real.sqrt d := by
  rw [integral_rpow (Or.inl (by norm_num))]
  rw [show (-1 / 2 : ℝ) + 1 = 1 / 2 by ring]
  rw [← Real.sqrt_eq_rpow]
  simp
  ring

private theorem leftMajorant_intervalIntegrable
    (α η : ℝ) (hη : 0 ≤ η) :
    IntervalIntegrable (leftMajorant α) volume (α - η) α := by
  have hp : IntervalIntegrable
      (fun t : ℝ => t ^ (-1 / 2 : ℝ)) volume 0 η :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hs : IntervalIntegrable
      (fun x : ℝ => (α - x) ^ (-1 / 2 : ℝ))
      volume (α - η) α := by
    simpa using (hp.comp_sub_left α).symm
  apply hs.congr
  intro x hx
  have hxI : x ∈ Icc (α - η) α := by
    simpa [uIcc, sub_le_self α hη] using uIoc_subset_uIcc hx
  unfold leftMajorant
  exact (one_div_sqrt_eq_rpow (sub_nonneg.mpr hxI.2)).symm

private theorem rightMajorant_intervalIntegrable
    (α η : ℝ) (hη : 0 ≤ η) :
    IntervalIntegrable (rightMajorant α) volume α (α + η) := by
  have hp : IntervalIntegrable
      (fun t : ℝ => t ^ (-1 / 2 : ℝ)) volume 0 η :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hs : IntervalIntegrable
      (fun x : ℝ => (x - α) ^ (-1 / 2 : ℝ))
      volume α (α + η) := by
    simpa [add_comm] using hp.comp_sub_right α
  apply hs.congr
  intro x hx
  have hxI : x ∈ Icc α (α + η) := by
    simpa [uIcc, le_add_of_nonneg_right hη] using uIoc_subset_uIcc hx
  unfold rightMajorant
  exact (one_div_sqrt_eq_rpow (sub_nonneg.mpr hxI.1)).symm

private theorem leftKernel_intervalIntegrable
    (α η : ℝ) (hη : 0 ≤ η) :
    IntervalIntegrable (leftKernel α) volume (α - η) α := by
  have hsin :
      ContinuousOn (fun x : ℝ => Real.sin (α * x))
        (uIcc (α - η) α) :=
    (Real.continuous_sin.comp
      (continuous_const.mul continuous_id)).continuousOn
  have h :=
    (leftMajorant_intervalIntegrable α η hη).mul_continuousOn hsin
  apply h.congr
  intro x _
  unfold leftMajorant leftKernel
  ring

private theorem rightKernel_intervalIntegrable
    (α η : ℝ) (hη : 0 ≤ η) :
    IntervalIntegrable (rightKernel α) volume α (α + η) := by
  have hsin :
      ContinuousOn (fun x : ℝ => Real.sin (α * x))
        (uIcc α (α + η)) :=
    (Real.continuous_sin.comp
      (continuous_const.mul continuous_id)).continuousOn
  have h :=
    (rightMajorant_intervalIntegrable α η hη).mul_continuousOn hsin
  apply h.congr
  intro x _
  unfold rightMajorant rightKernel
  ring

theorem gap1 (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x in (0 : ℝ)..1, singularKernel α x) =
      (∫ x in (0 : ℝ)..α, leftKernel α x) +
        ∫ x in α..1, rightKernel α x := by
  have hleft :
      IntervalIntegrable (leftKernel α) volume 0 α := by
    simpa using leftKernel_intervalIntegrable α α hα.1
  have hright :
      IntervalIntegrable (rightKernel α) volume α 1 := by
    simpa using rightKernel_intervalIntegrable α (1 - α)
      (sub_nonneg.mpr hα.2)
  have hsleft :
      IntervalIntegrable (singularKernel α) volume 0 α := by
    apply hleft.congr
    intro x hx
    have hxI : x ∈ Icc (0 : ℝ) α := by
      simpa [uIcc, hα.1] using uIoc_subset_uIcc hx
    have habs : |x - α| = α - x := by
      rw [abs_of_nonpos (sub_nonpos.mpr hxI.2)]
      ring
    simp [singularKernel, leftKernel, habs]
  have hsright :
      IntervalIntegrable (singularKernel α) volume α 1 := by
    apply hright.congr
    intro x hx
    have hxI : x ∈ Icc α 1 := by
      simpa [uIcc, hα.2] using uIoc_subset_uIcc hx
    have habs : |x - α| = x - α :=
      abs_of_nonneg (sub_nonneg.mpr hxI.1)
    simp [singularKernel, rightKernel, habs]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    hsleft hsright]
  congr 1
  · apply intervalIntegral.integral_congr
    intro x hx
    have hxI : x ∈ Icc (0 : ℝ) α := by
      simpa [uIcc, hα.1] using hx
    have habs : |x - α| = α - x := by
      rw [abs_of_nonpos (sub_nonpos.mpr hxI.2)]
      ring
    simp [singularKernel, leftKernel, habs]
  · apply intervalIntegral.integral_congr
    intro x hx
    have hxI : x ∈ Icc α 1 := by
      simpa [uIcc, hα.2] using hx
    have habs : |x - α| = x - α :=
      abs_of_nonneg (sub_nonneg.mpr hxI.1)
    simp [singularKernel, rightKernel, habs]

theorem gap2 (α η : ℝ) (hη : 0 ≤ η) :
    |∫ x in α - η..α, leftKernel α x| ≤
      ∫ x in α - η..α, leftMajorant α x := by
  rw [← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le
    (sub_le_self α hη)
  · filter_upwards [] with x hx
    rw [Real.norm_eq_abs, leftKernel, abs_div]
    have hsqrt : 0 ≤ Real.sqrt (α - x) := Real.sqrt_nonneg _
    rw [abs_of_nonneg hsqrt, leftMajorant]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) hsqrt
  · exact leftMajorant_intervalIntegrable α η hη

theorem gap3 (α η : ℝ) (hη : 0 ≤ η) :
    (∫ x in α - η..α, leftMajorant α x) =
      2 * Real.sqrt η := by
  calc
    (∫ x in α - η..α, leftMajorant α x) =
        ∫ x in α - η..α, (α - x) ^ (-1 / 2 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hxI : x ∈ Icc (α - η) α := by
        simpa [uIcc, sub_le_self α hη] using hx
      unfold leftMajorant
      exact one_div_sqrt_eq_rpow (sub_nonneg.mpr hxI.2)
    _ = ∫ t in (0 : ℝ)..η, t ^ (-1 / 2 : ℝ) := by
      simpa using intervalIntegral.integral_comp_sub_left
        (fun t : ℝ => t ^ (-1 / 2 : ℝ))
        (a := α - η) (b := α) α
    _ = 2 * Real.sqrt η := base_integral η

theorem gap4 (α η : ℝ) (hη : 0 ≤ η) :
    |∫ x in α - η..α, leftKernel α x| ≤
      2 * Real.sqrt η := by
  exact (gap2 α η hη).trans_eq (gap3 α η hη)

theorem gap5 (η α ε : ℝ) (hε : 0 < ε) (hη : 0 < η)
    (hηε : η < ε ^ 2 / 4) :
    |∫ x in α - η..α, leftKernel α x| < ε := by
  refine lt_of_le_of_lt (gap4 α η hη.le) ?_
  have hsqrt : Real.sqrt η < ε / 2 := by
    apply (Real.sqrt_lt' (by positivity)).2
    nlinarith
  nlinarith

theorem gap6 :
    LeftUniformlyConvergent := by
  intro ε hε
  refine ⟨ε ^ 2 / 4, by positivity, ?_⟩
  intro α hα η hη hηδ hηα
  exact gap5 η α ε hε hη hηδ

theorem gap7 (α η : ℝ) (hη : 0 ≤ η) :
    |∫ x in α..α + η, rightKernel α x| ≤
      ∫ x in α..α + η, rightMajorant α x := by
  rw [← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le
    (le_add_of_nonneg_right hη)
  · filter_upwards [] with x hx
    rw [Real.norm_eq_abs, rightKernel, abs_div]
    have hsqrt : 0 ≤ Real.sqrt (x - α) := Real.sqrt_nonneg _
    rw [abs_of_nonneg hsqrt, rightMajorant]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) hsqrt
  · exact rightMajorant_intervalIntegrable α η hη

theorem gap8 (α η : ℝ) (hη : 0 ≤ η) :
    (∫ x in α..α + η, rightMajorant α x) =
      2 * Real.sqrt η := by
  calc
    (∫ x in α..α + η, rightMajorant α x) =
        ∫ x in α..α + η, (x - α) ^ (-1 / 2 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hxI : x ∈ Icc α (α + η) := by
        simpa [uIcc, le_add_of_nonneg_right hη] using hx
      unfold rightMajorant
      exact one_div_sqrt_eq_rpow (sub_nonneg.mpr hxI.1)
    _ = ∫ t in (0 : ℝ)..η, t ^ (-1 / 2 : ℝ) := by
      simpa using intervalIntegral.integral_comp_sub_right
        (fun t : ℝ => t ^ (-1 / 2 : ℝ))
        (a := α) (b := α + η) α
    _ = 2 * Real.sqrt η := base_integral η

theorem gap9 (α η : ℝ) (hη : 0 ≤ η) :
    |∫ x in α..α + η, rightKernel α x| ≤
      2 * Real.sqrt η := by
  exact (gap7 α η hη).trans_eq (gap8 α η hη)

theorem gap10 (η α ε : ℝ) (hε : 0 < ε) (hη : 0 < η)
    (hηε : η < ε ^ 2 / 4) :
    |∫ x in α..α + η, rightKernel α x| < ε := by
  refine lt_of_le_of_lt (gap9 α η hη.le) ?_
  have hsqrt : Real.sqrt η < ε / 2 := by
    apply (Real.sqrt_lt' (by positivity)).2
    nlinarith
  nlinarith

theorem gap11 :
    RightUniformlyConvergent := by
  intro ε hε
  refine ⟨ε ^ 2 / 4, by positivity, ?_⟩
  intro α hα η hη hηδ hηα
  exact gap10 η α ε hε hη hηδ

theorem gap12 :
    UniformlyConvergent :=
  ⟨gap6, gap11⟩

theorem gap13 :
    UniformlyConvergent :=
  gap12

end

end ProofGap.Exercise3770
