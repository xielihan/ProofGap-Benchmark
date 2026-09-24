import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise921

noncomputable section

def y (x : ℝ) : ℝ :=
  Real.arcsin (Real.sin x)

def expandedDerivative (x : ℝ) : ℝ :=
  Real.cos x / Real.sqrt (1 - Real.sin x ^ 2)

def finalDerivative (x : ℝ) : ℝ :=
  Real.sign (Real.cos x)

/-- Exercise 921, gap 1; exclude the cusp points where
`sin x = ±1`, equivalently `cos x = 0`. -/
theorem gap1 (x : ℝ) (hx : Real.cos x ≠ 0) :
    HasDerivAt y (expandedDerivative x) x := by
  have hcos_sq : 0 < Real.cos x ^ 2 := sq_pos_of_ne_zero hx
  have hsin_mem : Real.sin x ∈ Set.Ioo (-1) 1 := by
    constructor
    · nlinarith [Real.neg_one_le_sin x, Real.sin_le_one x,
        Real.sin_sq_add_cos_sq x, hcos_sq]
    · nlinarith [Real.neg_one_le_sin x, Real.sin_le_one x,
        Real.sin_sq_add_cos_sq x, hcos_sq]
  have harcsin :
      HasDerivAt Real.arcsin
        (1 / Real.sqrt (1 - Real.sin x ^ 2)) (Real.sin x) := by
    apply Real.hasDerivAt_arcsin
    · exact ne_of_gt hsin_mem.1
    · exact ne_of_lt hsin_mem.2
  simpa [y, expandedDerivative, Function.comp_def, div_eq_mul_inv, mul_comm] using
    harcsin.comp x (Real.hasDerivAt_sin x)

/-- Exercise 921, gap 2; away from zeros of cosine,
`sqrt (cos² x) = |cos x|` yields the sign. -/
theorem gap2 (x : ℝ) (hx : Real.cos x ≠ 0) :
    expandedDerivative x = finalDerivative x := by
  unfold expandedDerivative finalDerivative
  have hsq : 1 - Real.sin x ^ 2 = Real.cos x ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [hsq, Real.sqrt_sq_eq_abs]
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · simp [abs_of_neg hneg, Real.sign, hneg, hx]
  · have hnotneg : ¬ Real.cos x < 0 :=
      not_lt_of_ge (le_of_lt hpos)
    simp [abs_of_pos hpos, Real.sign, hpos, hnotneg, hx]

/-- Exercise 921, gap 3; the composed function is not
differentiable at the omitted cusp points. -/
theorem gap3 (x : ℝ) (hx : Real.cos x ≠ 0) :
    HasDerivAt y (finalDerivative x) x := by
  simpa only [gap2 x hx] using (gap1 x hx)

end

end ProofGap.Exercise921
