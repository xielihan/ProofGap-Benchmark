import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp

open scoped Interval

namespace ProofGap.Exercise2254

noncomputable section

def xOfT (a b t : ℝ) : ℝ := a + (b - a) * t
def jacobian (a b : ℝ) : ℝ := b - a

theorem gap1 (a b t : ℝ) :
    deriv (xOfT a b) t = jacobian a b := by
  have hlinear :
      HasDerivAt (fun s : ℝ => (b - a) * s) (b - a) t := by
    simpa using (hasDerivAt_id t).const_mul (b - a)
  have h : HasDerivAt (xOfT a b) (b - a) t := by
    simpa [xOfT] using (hasDerivAt_const t a).add hlinear
  simpa [jacobian] using h.deriv

theorem gap2 (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) :
    (∫ x in a..b, f x) =
      (b - a) * ∫ t in (0 : ℝ)..1, f (xOfT a b t) := by
  by_cases h : b = a
  · subst b
    simp [xOfT]
  · have hc : b - a ≠ 0 := sub_ne_zero.mpr h
    have hchange :
        (∫ t in (0 : ℝ)..1, f (xOfT a b t)) =
          (b - a)⁻¹ * ∫ x in a..b, f x := by
      simpa [xOfT, add_comm] using
        (intervalIntegral.integral_comp_mul_add
          (f := f) (a := (0 : ℝ)) (b := 1)
          (c := b - a) (d := a) hc)
    rw [hchange]
    field_simp [hc]

theorem gap3 (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) :
    (∫ x in a..b, f x) =
      (b - a) * ∫ x in (0 : ℝ)..1, f (a + (b - a) * x) := by
  simpa [xOfT] using gap2 f hf a b

theorem gap4 (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) :
    (∫ x in a..b, f x) =
      (b - a) * ∫ x in (0 : ℝ)..1, f (a + (b - a) * x) := by
  exact gap3 f hf a b

end

end ProofGap.Exercise2254
