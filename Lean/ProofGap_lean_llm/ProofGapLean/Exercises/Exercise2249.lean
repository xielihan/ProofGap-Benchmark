import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

open scoped Interval

namespace ProofGap.Exercise2249

noncomputable section

def xOfT (t : ℝ) : ℝ := t ^ 2
def jacobian (t : ℝ) : ℝ := 2 * t

def originalIntegrand (x : ℝ) : ℝ :=
  Real.arcsin (Real.sqrt x) / Real.sqrt (x * (1 - x))

def pullback (t : ℝ) : ℝ :=
  2 * Real.arcsin t / Real.sqrt (1 - t ^ 2)

def primitive (t : ℝ) : ℝ := Real.arcsin t ^ 2

private theorem integral_values :
    ((∫ x in (0 : ℝ)..1, originalIntegrand x) =
      primitive 1 - primitive 0) ∧
    ((∫ t in (0 : ℝ)..1,
        2 * Real.arcsin t / Real.sqrt (1 - t ^ 2)) =
      primitive 1 - primitive 0) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  constructor
  · let F : ℝ → ℝ := fun x => Real.arcsin (Real.sqrt x) ^ 2
    have hcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) :=
      ((Real.continuous_arcsin.comp Real.continuous_sqrt).pow 2).continuousOn
    have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt F (originalIntegrand x) x := by
      intro x hx
      have hx0 : 0 ≤ x := le_of_lt hx.1
      have hxlt : x < 1 := hx.2
      have hx1 : 0 ≤ 1 - x := sub_nonneg.mpr (le_of_lt hxlt)
      have hsxpos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx.1
      have hs1pos : 0 < Real.sqrt (1 - x) :=
        Real.sqrt_pos.2 (sub_pos.mpr hxlt)
      have hsarg : Real.sqrt x ∈ Set.Ioo (-1 : ℝ) 1 := by
        constructor
        · exact lt_of_lt_of_le (by norm_num) (Real.sqrt_nonneg x)
        · nlinarith [Real.sq_sqrt hx0, Real.sqrt_nonneg x, hxlt]
      dsimp [F]
      convert (((Real.hasDerivAt_arcsin
        (ne_of_gt hsarg.1) (ne_of_lt hsarg.2)).comp x
          (Real.hasDerivAt_sqrt (ne_of_gt hx.1))).pow 2) using 1 <;>
        simp only [originalIntegrand, Function.comp_apply,
          Real.sq_sqrt hx0, Real.sqrt_mul hx0] <;>
        field_simp [ne_of_gt hsxpos, ne_of_gt hs1pos] <;>
        ring
    have hnonneg : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
        0 ≤ originalIntegrand x := by
      intro x hx
      unfold originalIntegrand
      exact div_nonneg
        (Real.arcsin_nonneg.2 (Real.sqrt_nonneg x))
        (Real.sqrt_nonneg _)
    have hcont' : ContinuousOn F (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le h01] using hcont
    have hderiv' : ∀ x ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
        HasDerivAt F (originalIntegrand x) x := by
      simpa [min_eq_left h01, max_eq_right h01] using hderiv
    have hnonneg' : ∀ x ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
        0 ≤ originalIntegrand x := by
      simpa [min_eq_left h01, max_eq_right h01] using hnonneg
    have hint : IntervalIntegrable originalIntegrand MeasureTheory.volume
        (0 : ℝ) 1 :=
      intervalIntegral.intervalIntegrable_deriv_of_nonneg
        hcont' hderiv' hnonneg'
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      h01 hcont hderiv hint
    simpa [F, primitive] using hftc
  · let F : ℝ → ℝ := fun t => Real.arcsin t ^ 2
    let F' : ℝ → ℝ := fun t =>
      2 * Real.arcsin t / Real.sqrt (1 - t ^ 2)
    have hcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) :=
      (Real.continuous_arcsin.pow 2).continuousOn
    have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt F (F' t) t := by
      intro t ht
      have htarg : t ∈ Set.Ioo (-1 : ℝ) 1 := by
        exact ⟨lt_trans (by norm_num) ht.1, ht.2⟩
      dsimp [F, F']
      convert ((Real.hasDerivAt_arcsin
        (ne_of_gt htarg.1) (ne_of_lt htarg.2)).pow 2) using 1 <;>
        simp [div_eq_mul_inv] <;>
        ring
    have hnonneg : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ F' t := by
      intro t ht
      dsimp [F']
      exact div_nonneg
        (mul_nonneg (by norm_num) (Real.arcsin_nonneg.2 (le_of_lt ht.1)))
        (Real.sqrt_nonneg _)
    have hcont' : ContinuousOn F (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le h01] using hcont
    have hderiv' : ∀ t ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
        HasDerivAt F (F' t) t := by
      simpa [min_eq_left h01, max_eq_right h01] using hderiv
    have hnonneg' : ∀ t ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
        0 ≤ F' t := by
      simpa [min_eq_left h01, max_eq_right h01] using hnonneg
    have hint : IntervalIntegrable F' MeasureTheory.volume (0 : ℝ) 1 :=
      intervalIntegral.intervalIntegrable_deriv_of_nonneg
        hcont' hderiv' hnonneg'
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      h01 hcont hderiv hint
    simpa [F, F', primitive] using hftc

theorem gap1 :
    (∫ x in (0 : ℝ)..1, originalIntegrand x) =
      2 * ∫ t in (0 : ℝ)..1,
        Real.arcsin t / Real.sqrt (1 - t ^ 2) := by
  calc
    (∫ x in (0 : ℝ)..1, originalIntegrand x) =
        primitive 1 - primitive 0 := integral_values.1
    _ = (∫ t in (0 : ℝ)..1,
        2 * Real.arcsin t / Real.sqrt (1 - t ^ 2)) :=
      integral_values.2.symm
    _ = (∫ t in (0 : ℝ)..1,
        2 * (Real.arcsin t / Real.sqrt (1 - t ^ 2))) := by
      simp only [mul_div_assoc]
    _ = 2 * ∫ t in (0 : ℝ)..1,
        Real.arcsin t / Real.sqrt (1 - t ^ 2) := by
      rw [intervalIntegral.integral_const_mul]

theorem gap2 :
    2 * (∫ t in (0 : ℝ)..1,
        Real.arcsin t / Real.sqrt (1 - t ^ 2)) =
      primitive 1 - primitive 0 := by
  calc
    2 * (∫ t in (0 : ℝ)..1,
        Real.arcsin t / Real.sqrt (1 - t ^ 2)) =
        (∫ t in (0 : ℝ)..1,
          2 * (Real.arcsin t / Real.sqrt (1 - t ^ 2))) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (∫ t in (0 : ℝ)..1,
          2 * Real.arcsin t / Real.sqrt (1 - t ^ 2)) := by
      simp only [mul_div_assoc]
    _ = primitive 1 - primitive 0 := integral_values.2

theorem gap3 :
    primitive 1 - primitive 0 = Real.pi ^ 2 / 4 := by
  simp [primitive, Real.arcsin_one, Real.arcsin_zero]
  ring

theorem gap4 :
    (∫ x in (0 : ℝ)..1, originalIntegrand x) =
      Real.pi ^ 2 / 4 := by
  rw [gap1, gap2, gap3]

end

end ProofGap.Exercise2249
