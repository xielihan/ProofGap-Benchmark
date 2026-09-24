import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1088

noncomputable section

def y (a x : ℝ) : ℝ := Real.log |x + Real.sqrt (x ^ 2 + a)|
def differentialAt (a x dx : ℝ) : ℝ := deriv (y a) x * dx

theorem gap1 (a x : ℝ) (ha : 0 < a) :
    HasDerivAt (y a) (1 / Real.sqrt (x ^ 2 + a)) x := by
  have harg_pos : ∀ t : ℝ, 0 < t + Real.sqrt (t ^ 2 + a) := by
    intro t
    have hu_t : 0 < t ^ 2 + a := by nlinarith [sq_nonneg t]
    have hs_t : 0 ≤ Real.sqrt (t ^ 2 + a) := Real.sqrt_nonneg _
    have hsq_t : (Real.sqrt (t ^ 2 + a)) ^ 2 = t ^ 2 + a :=
      Real.sq_sqrt (le_of_lt hu_t)
    by_contra h
    have hsum : Real.sqrt (t ^ 2 + a) + t ≤ 0 := by linarith
    have hdiff : 0 ≤ Real.sqrt (t ^ 2 + a) - t := by linarith
    have hmul :
        (Real.sqrt (t ^ 2 + a) + t) *
            (Real.sqrt (t ^ 2 + a) - t) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hsum hdiff
    nlinarith
  have hy : y a = fun t : ℝ => Real.log (t + Real.sqrt (t ^ 2 + a)) := by
    funext t
    simp [y, abs_of_pos (harg_pos t)]
  rw [hy]
  have hu : 0 < x ^ 2 + a := by nlinarith [sq_nonneg x]
  have hs : 0 < Real.sqrt (x ^ 2 + a) := Real.sqrt_pos.2 hu
  have hinner :
      HasDerivAt (fun t : ℝ => t ^ 2 + a) (2 * x) x := by
    simpa using ((hasDerivAt_id x).pow 2).add_const a
  have hsqrt :
      HasDerivAt (fun t : ℝ => Real.sqrt (t ^ 2 + a))
        (x / Real.sqrt (x ^ 2 + a)) x := by
    convert (Real.hasDerivAt_sqrt hu.ne').comp x hinner using 1 <;>
      field_simp [hs.ne'] <;> ring
  have hsum :
      HasDerivAt (fun t : ℝ => t + Real.sqrt (t ^ 2 + a))
        (1 + x / Real.sqrt (x ^ 2 + a)) x :=
    (hasDerivAt_id x).add hsqrt
  convert (Real.hasDerivAt_log (harg_pos x).ne').comp x hsum using 1 <;>
    field_simp [hs.ne', (harg_pos x).ne'] <;> ring

theorem gap2 (a x dx : ℝ) (ha : 0 < a) :
    differentialAt a x dx = dx / Real.sqrt (x ^ 2 + a) := by
  unfold differentialAt
  rw [(gap1 a x ha).deriv]
  ring

end

end ProofGap.Exercise1088
