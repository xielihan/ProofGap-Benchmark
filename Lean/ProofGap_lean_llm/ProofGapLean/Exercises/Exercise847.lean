import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise847

noncomputable section

def y (x : ℝ) : ℝ :=
  x / ((1 - x) ^ 2 * (1 + x) ^ 3)

/-- Exercise 847, gap 1; exclude both poles `x = ±1`. -/
theorem gap1 (x : ℝ) (hden : (1 - x) ^ 2 * (1 + x) ^ 3 ≠ 0) :
    HasDerivAt y
      (((1 - x) ^ 2 * (1 + x) ^ 3 -
          x * (3 * (1 + x) ^ 2 * (1 - x) ^ 2 -
            2 * (1 - x) * (1 + x) ^ 3)) /
        ((1 - x) ^ 4 * (1 + x) ^ 6)) x := by
  have hsub : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
    convert
      (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
        (hasDerivAt_id x) using 1 <;> ring
  have hadd : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by
    convert
      (hasDerivAt_const (x := x) (c := (1 : ℝ))).add
        (hasDerivAt_id x) using 1 <;> ring
  have hleft :
      HasDerivAt (fun t : ℝ => (1 - t) ^ 2) (-2 * (1 - x)) x := by
    convert hsub.mul hsub using 1 <;>
      (try funext t) <;> simp <;> ring
  have hright :
      HasDerivAt (fun t : ℝ => (1 + t) ^ 3) (3 * (1 + x) ^ 2) x := by
    convert hadd.mul (hadd.mul hadd) using 1 <;>
      (try funext t) <;> simp <;> ring
  have hproduct :
      HasDerivAt
        (fun t : ℝ => (1 - t) ^ 2 * (1 + t) ^ 3)
        (3 * (1 + x) ^ 2 * (1 - x) ^ 2 -
          2 * (1 - x) * (1 + x) ^ 3) x := by
    convert hleft.mul hright using 1 <;> ring
  have hquot :
      HasDerivAt y
        (((1 - x) ^ 2 * (1 + x) ^ 3 -
            x * (3 * (1 + x) ^ 2 * (1 - x) ^ 2 -
              2 * (1 - x) * (1 + x) ^ 3)) /
          (((1 - x) ^ 2 * (1 + x) ^ 3) ^ 2)) x := by
    simpa only [y, id_eq, one_mul] using
      (hasDerivAt_id x).div hproduct hden
  have hsq :
      ((1 - x) ^ 2 * (1 + x) ^ 3) ^ 2 =
        (1 - x) ^ 4 * (1 + x) ^ 6 := by
    ring
  rw [hsq] at hquot
  exact hquot

/-- Exercise 847, gap 2; exclude both poles `x = ±1`. -/
theorem gap2 (x : ℝ) (hden : (1 - x) ^ 2 * (1 + x) ^ 3 ≠ 0) :
    HasDerivAt y
      ((1 - x + 4 * x ^ 2) / ((1 - x) ^ 3 * (1 + x) ^ 4)) x := by
  have hminus : 1 - x ≠ 0 := by
    intro hx
    apply hden
    simp [hx]
  have hplus : 1 + x ≠ 0 := by
    intro hx
    apply hden
    simp [hx]
  convert gap1 x hden using 1
  field_simp [hminus, hplus] <;> ring

end

end ProofGap.Exercise847
