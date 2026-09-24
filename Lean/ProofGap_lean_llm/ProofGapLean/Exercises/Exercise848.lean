import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise848

noncomputable section

def y (x : ℝ) : ℝ :=
  ((2 - x ^ 2) * (3 - x ^ 3)) / (1 - x) ^ 2

/-- Exercise 848, gap 1; add the omitted pole exclusion
`x ≠ 1`. -/
theorem gap1 (x : ℝ) (hx : x ≠ 1) :
    HasDerivAt y
      (((1 - x) ^ 2 *
          (-2 * x * (3 - x ^ 3) - 3 * x ^ 2 * (2 - x ^ 2)) +
        2 * (1 - x) * (2 - x ^ 2) * (3 - x ^ 3)) /
        (1 - x) ^ 4) x := by
  unfold y
  have hbase : (1 - x) ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hid : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
  have hsq_raw : HasDerivAt (fun t : ℝ => t * t) (1 * x + x * 1) x :=
    hid.mul hid
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    convert hsq_raw using 1
    · funext t
      ring
    · ring
  have hcub_raw : HasDerivAt (fun t : ℝ => (t ^ 2) * t)
      ((2 * x) * x + x ^ 2 * 1) x :=
    hsq.mul hid
  have hcub : HasDerivAt (fun t : ℝ => t ^ 3) (3 * x ^ 2) x := by
    convert hcub_raw using 1 <;> ring
  have hleft : HasDerivAt (fun t : ℝ => 2 - t ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const x (2 : ℝ)).sub hsq using 1 <;> ring
  have hright : HasDerivAt (fun t : ℝ => 3 - t ^ 3) (-3 * x ^ 2) x := by
    convert (hasDerivAt_const x (3 : ℝ)).sub hcub using 1 <;> ring
  have hnum : HasDerivAt (fun t : ℝ => (2 - t ^ 2) * (3 - t ^ 3))
      (-2 * x * (3 - x ^ 3) - 3 * x ^ 2 * (2 - x ^ 2)) x := by
    convert hleft.mul hright using 1 <;> ring
  have hlin : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub hid using 1 <;> ring
  have hden_raw : HasDerivAt (fun t : ℝ => (1 - t) * (1 - t))
      ((-1) * (1 - x) + (1 - x) * (-1)) x :=
    hlin.mul hlin
  have hden : HasDerivAt (fun t : ℝ => (1 - t) ^ 2) (-2 * (1 - x)) x := by
    convert hden_raw using 1
    · funext t
      ring
    · ring
  convert hnum.div hden (pow_ne_zero 2 hbase) using 1
  field_simp [hbase]
  <;> ring

/-- Exercise 848, gap 2; add the omitted pole exclusion
`x ≠ 1`. -/
theorem gap2 (x : ℝ) (hx : x ≠ 1) :
    HasDerivAt y
      ((12 - 6 * x - 6 * x ^ 2 + 2 * x ^ 3 + 5 * x ^ 4 - 3 * x ^ 5) /
        (1 - x) ^ 3) x := by
  convert gap1 x hx using 1 <;>
    field_simp [sub_ne_zero.mpr (Ne.symm hx)] <;>
    ring

end

end ProofGap.Exercise848
