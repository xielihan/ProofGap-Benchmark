import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace ProofGap.Exercise854

noncomputable section

def y (x : ℝ) : ℝ :=
  x * Real.sqrt (1 + x ^ 2)

theorem gap1 (x : ℝ) :
    HasDerivAt y
      (Real.sqrt (1 + x ^ 2) + x ^ 2 / Real.sqrt (1 + x ^ 2)) x := by
  unfold y
  have hpos : 0 < 1 + x ^ 2 := by positivity
  have hsqrt_ne : Real.sqrt (1 + x ^ 2) ≠ 0 := by positivity
  have hinner :
      HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * x) x := by
    convert
      HasDerivAt.add (hasDerivAt_const x (1 : ℝ))
        (HasDerivAt.pow (hasDerivAt_id x) 2) using 1 <;>
      simp [id_eq] <;> ring_nf
  have hroot :
      HasDerivAt (fun t : ℝ => Real.sqrt (1 + t ^ 2))
        (x / Real.sqrt (1 + x ^ 2)) x := by
    convert
      (Real.hasDerivAt_sqrt (ne_of_gt hpos)).comp x hinner using 1 <;>
      field_simp [hsqrt_ne] <;> ring_nf
  have hderiv := HasDerivAt.mul (hasDerivAt_id x) hroot
  convert hderiv using 1 <;>
    simp [id_eq] <;> field_simp [hsqrt_ne] <;> ring_nf

theorem gap2 (x : ℝ) :
    Real.sqrt (1 + x ^ 2) + x ^ 2 / Real.sqrt (1 + x ^ 2) =
      (1 + 2 * x ^ 2) / Real.sqrt (1 + x ^ 2) := by
  have hsqrt_ne : Real.sqrt (1 + x ^ 2) ≠ 0 := by
    positivity
  have hsquare : (Real.sqrt (1 + x ^ 2)) ^ 2 = 1 + x ^ 2 :=
    Real.sq_sqrt (by positivity)
  calc
    Real.sqrt (1 + x ^ 2) + x ^ 2 / Real.sqrt (1 + x ^ 2) =
        ((Real.sqrt (1 + x ^ 2)) ^ 2 + x ^ 2) /
          Real.sqrt (1 + x ^ 2) := by
            field_simp [hsqrt_ne]
    _ = (1 + 2 * x ^ 2) / Real.sqrt (1 + x ^ 2) := by
          rw [hsquare]
          ring

theorem gap3 (x : ℝ) :
    HasDerivAt y ((1 + 2 * x ^ 2) / Real.sqrt (1 + x ^ 2)) x := by
  simpa only [gap2 x] using gap1 x

end

end ProofGap.Exercise854
