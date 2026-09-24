import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise928

noncomputable section

def u (x : ℝ) : ℝ :=
  (1 - x ^ 2) / (1 + x ^ 2)

def y (x : ℝ) : ℝ :=
  Real.arcsin (u x)

def expandedDerivative (x : ℝ) : ℝ :=
  1 / Real.sqrt (1 - u x ^ 2) *
    ((-2 * x * (1 + x ^ 2) - 2 * x * (1 - x ^ 2)) /
      (1 + x ^ 2) ^ 2)

def finalDerivative (x : ℝ) : ℝ :=
  -(2 * Real.sign x) / (1 + x ^ 2)

/-- Source: `proof_gap/exercise_928/1.txt`; exclude `x = 0`, where the
inverse-sine argument reaches `1` and the composition has a cusp. -/
theorem gap1 (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt y (expandedDerivative x) x := by
  have hx2pos : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hdenpos : 0 < 1 + x ^ 2 := by
    nlinarith [sq_nonneg x]
  have hden : 1 + x ^ 2 ≠ 0 := ne_of_gt hdenpos
  have hleft : u x ≠ -1 := by
    unfold u
    intro h
    field_simp [hden] at h
    nlinarith
  have hright : u x ≠ 1 := by
    unfold u
    intro h
    field_simp [hden] at h
    nlinarith
  have hnum_deriv :
      HasDerivAt (fun z : ℝ => 1 - z ^ 2) (-2 * x) x := by
    convert
      (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)
      using 1 <;> simp only [id_eq] <;> ring
  have hden_deriv :
      HasDerivAt (fun z : ℝ => 1 + z ^ 2) (2 * x) x := by
    convert
      (hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).pow 2)
      using 1 <;> simp only [id_eq] <;> ring
  have hu_deriv :
      HasDerivAt u
        ((-2 * x * (1 + x ^ 2) - 2 * x * (1 - x ^ 2)) /
          (1 + x ^ 2) ^ 2) x := by
    unfold u
    convert hnum_deriv.div hden_deriv hden using 1 <;> ring
  unfold y expandedDerivative
  simpa only [one_div] using
    (Real.hasDerivAt_arcsin hleft hright).comp x hu_deriv

/-- Source: `proof_gap/exercise_928/2.txt`; the nonzero hypothesis controls
the absolute value arising from the square root. -/
theorem gap2 (x : ℝ) (hx : x ≠ 0) :
    expandedDerivative x = finalDerivative x := by
  have hdenpos : 0 < 1 + x ^ 2 := by
    nlinarith [sq_nonneg x]
  have hden : 1 + x ^ 2 ≠ 0 := ne_of_gt hdenpos
  have hsqrt_arg :
      1 - u x ^ 2 = (2 * x / (1 + x ^ 2)) ^ 2 := by
    unfold u
    field_simp [hden] <;> ring
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have hfrac : 2 * x / (1 + x ^ 2) < 0 :=
      div_neg_of_neg_of_pos
        (mul_neg_of_pos_of_neg (by norm_num) hxneg) hdenpos
    unfold expandedDerivative finalDerivative
    rw [hsqrt_arg, Real.sqrt_sq_eq_abs, abs_of_neg hfrac,
      Real.sign_of_neg hxneg]
    field_simp [hden, hx] <;> ring
  · have hfrac : 0 < 2 * x / (1 + x ^ 2) :=
      div_pos (mul_pos (by norm_num) hxpos) hdenpos
    unfold expandedDerivative finalDerivative
    rw [hsqrt_arg, Real.sqrt_sq_eq_abs, abs_of_pos hfrac,
      Real.sign_of_pos hxpos]
    field_simp [hden, hx] <;> ring

/-- Source: `proof_gap/exercise_928/3.txt`; retain the two smooth components
of the source function's domain. -/
theorem gap3 (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt y (finalDerivative x) x := by
  rw [← gap2 x hx]
  exact gap1 x hx

end

end ProofGap.Exercise928
