import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise844

noncomputable section

def mobius (a b c d x : ℝ) : ℝ :=
  (a * x + b) / (c * x + d)

def y (x : ℝ) : ℝ :=
  1 / x + 2 / x ^ 2 + 3 / x ^ 3

/-- Exercise 844, gap 1; make the implicit pole exclusion
explicit. -/
theorem gap1 (a b c d x : ℝ) (hden : c * x + d ≠ 0) :
    HasDerivAt (mobius a b c d)
      ((a * (c * x + d) - c * (a * x + b)) / (c * x + d) ^ 2) x := by
  have hid : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
  have hnum : HasDerivAt (fun t : ℝ => a * t + b) a x := by
    convert (hid.const_mul a).add_const b using 1 <;> ring
  have hden' : HasDerivAt (fun t : ℝ => c * t + d) c x := by
    convert (hid.const_mul c).add_const d using 1 <;> ring
  have hquot := hnum.div hden' hden
  unfold mobius
  convert hquot using 1 <;> ring

/-- Exercise 844, gap 2; retain the rational function's
implicit domain condition. -/
theorem gap2 (a b c d x : ℝ) (hden : c * x + d ≠ 0) :
    (a * (c * x + d) - c * (a * x + b)) / (c * x + d) ^ 2 =
      (a * d - b * c) / (c * x + d) ^ 2 := by
  ring

/-- Exercise 844, gap 3; make the implicit pole exclusion
explicit. -/
theorem gap3 (a b c d x : ℝ) (hden : c * x + d ≠ 0) :
    HasDerivAt (mobius a b c d)
      ((a * d - b * c) / (c * x + d) ^ 2) x := by
  rw [← gap2 a b c d x hden]
  exact gap1 a b c d x hden

/-- Exercise 844, gap 4; this is the determinant form of
the same formula, with the determinant expanded as `a*d-b*c`. -/
theorem gap4 (a b c d x : ℝ) (hden : c * x + d ≠ 0) :
    HasDerivAt (mobius a b c d)
      ((a * d - b * c) / (c * x + d) ^ 2) x := by
  exact gap3 a b c d x hden

/-- Exercise 844, gap 5; bind the previously free function
`y` and retain its natural domain. -/
theorem gap5 (x : ℝ) (hx : x ≠ 0) :
    y x = 1 / x + 2 / x ^ 2 + 3 / x ^ 3 := by
  rfl

/-- Exercise 844, gap 6; the derivative is asserted only
on the natural domain `x ≠ 0`. -/
theorem gap6 (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt y (-(1 / x ^ 2 + 4 / x ^ 3 + 9 / x ^ 4)) x := by
  have hid : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  have hx3 : x ^ 3 ≠ 0 := pow_ne_zero 3 hx
  have hpow2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    convert hid.mul hid using 1 <;> try ring
    funext t
    simp [pow_two]
  have hpow3 : HasDerivAt (fun t : ℝ => t ^ 3) (3 * x ^ 2) x := by
    convert hpow2.mul hid using 1 <;> ring
  have h1 : HasDerivAt (fun t : ℝ => 1 / t) (-1 / x ^ 2) x := by
    have hquot := (hasDerivAt_const x (1 : ℝ)).div hid hx
    convert hquot using 1 <;> field_simp [hx] <;> ring
  have h2 : HasDerivAt (fun t : ℝ => 2 / t ^ 2) (-4 / x ^ 3) x := by
    have hquot := (hasDerivAt_const x (2 : ℝ)).div hpow2 hx2
    convert hquot using 1 <;> field_simp [hx] <;> ring
  have h3 : HasDerivAt (fun t : ℝ => 3 / t ^ 3) (-9 / x ^ 4) x := by
    have hquot := (hasDerivAt_const x (3 : ℝ)).div hpow3 hx3
    convert hquot using 1 <;> field_simp [hx] <;> ring
  have hsum := (h1.add h2).add h3
  unfold y
  convert hsum using 1 <;> ring

/-- Exercise 844, gap 7; make the implicit pole exclusion
explicit. -/
theorem gap7 (a b c d x : ℝ) (hden : c * x + d ≠ 0) :
    HasDerivAt (mobius a b c d)
      ((a * d - b * c) / (c * x + d) ^ 2) x := by
  exact gap3 a b c d x hden

end

end ProofGap.Exercise844
