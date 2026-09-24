import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise871

noncomputable section

def sec (x : ℝ) : ℝ := 1 / Real.cos x
def csc (x : ℝ) : ℝ := 1 / Real.sin x
def cot (x : ℝ) : ℝ := Real.cos x / Real.sin x
def half (x : ℝ) : ℝ := x / 2

def y (x : ℝ) : ℝ := Real.tan (half x) - cot (half x)

def expandedDerivative (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * sec (half x) ^ 2 +
    (1 / 2 : ℝ) * csc (half x) ^ 2

def finalDerivative (x : ℝ) : ℝ := 2 / Real.sin x ^ 2

/-- Exercise 871, gap 1; require both half-angle
denominators to be nonzero. -/
theorem gap1 (x : ℝ) (hcos : Real.cos (half x) ≠ 0)
    (hsin : Real.sin (half x) ≠ 0) :
    deriv y x = expandedDerivative x := by
  have hhalf : HasDerivAt half (1 / 2 : ℝ) x := by
    simpa [half] using (hasDerivAt_id x).div_const 2
  have hcos' :
      HasDerivAt (fun t => Real.cos (half t))
        (-Real.sin (half x) * (1 / 2 : ℝ)) x :=
    (Real.hasDerivAt_cos (half x)).comp x hhalf
  have hsin' :
      HasDerivAt (fun t => Real.sin (half t))
        (Real.cos (half x) * (1 / 2 : ℝ)) x :=
    (Real.hasDerivAt_sin (half x)).comp x hhalf
  have htanQuot :
      HasDerivAt
        (fun t => Real.sin (half t) / Real.cos (half t))
        (((Real.cos (half x) * (1 / 2 : ℝ)) * Real.cos (half x) -
            Real.sin (half x) * (-Real.sin (half x) * (1 / 2 : ℝ))) /
          Real.cos (half x) ^ 2) x :=
    hsin'.div hcos' hcos
  have htanNum :
      (Real.cos (half x) * (1 / 2 : ℝ)) * Real.cos (half x) -
          Real.sin (half x) * (-Real.sin (half x) * (1 / 2 : ℝ)) =
        (1 / 2 : ℝ) := by
    nlinarith [Real.sin_sq_add_cos_sq (half x)]
  have htan :
      HasDerivAt (fun t => Real.tan (half t))
        ((1 / 2 : ℝ) / Real.cos (half x) ^ 2) x := by
    rw [← htanNum]
    simpa only [Real.tan_eq_sin_div_cos] using htanQuot
  have hcotQuot :
      HasDerivAt
        (fun t => Real.cos (half t) / Real.sin (half t))
        (((-Real.sin (half x) * (1 / 2 : ℝ)) * Real.sin (half x) -
            Real.cos (half x) * (Real.cos (half x) * (1 / 2 : ℝ))) /
          Real.sin (half x) ^ 2) x :=
    hcos'.div hsin' hsin
  have hcotNum :
      (-Real.sin (half x) * (1 / 2 : ℝ)) * Real.sin (half x) -
          Real.cos (half x) * (Real.cos (half x) * (1 / 2 : ℝ)) =
        -(1 / 2 : ℝ) := by
    nlinarith [Real.sin_sq_add_cos_sq (half x)]
  have hcot :
      HasDerivAt
        (fun t => Real.cos (half t) / Real.sin (half t))
        (-(1 / 2 : ℝ) / Real.sin (half x) ^ 2) x := by
    rw [← hcotNum]
    exact hcotQuot
  have hdiff :
      HasDerivAt
        (fun t => Real.tan (half t) -
          Real.cos (half t) / Real.sin (half t))
        ((1 / 2 : ℝ) / Real.cos (half x) ^ 2 -
          (-(1 / 2 : ℝ) / Real.sin (half x) ^ 2)) x :=
    htan.sub hcot
  have hy :
      HasDerivAt y
        ((1 / 2 : ℝ) / Real.cos (half x) ^ 2 -
          (-(1 / 2 : ℝ) / Real.sin (half x) ^ 2)) x := by
    simpa only [y, cot] using hdiff
  rw [hy.deriv]
  unfold expandedDerivative sec csc
  field_simp [hcos, hsin] <;> ring

/-- Exercise 871, gap 2; retain the common domain of
`tan (x/2)` and `cot (x/2)`. -/
theorem gap2 (x : ℝ) (hcos : Real.cos (half x) ≠ 0)
    (hsin : Real.sin (half x) ≠ 0) :
    expandedDerivative x = finalDerivative x := by
  have hsq :
      Real.sin (half x) ^ 2 + Real.cos (half x) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq (half x)
  have hdouble :
      Real.sin x =
        2 * Real.sin (half x) * Real.cos (half x) := by
    calc
      Real.sin x = Real.sin (half x + half x) := by
        congr 1
        unfold half
        ring
      _ = 2 * Real.sin (half x) * Real.cos (half x) := by
        rw [Real.sin_add]
        ring
  calc
    expandedDerivative x =
        (1 / 2 : ℝ) *
          (Real.sin (half x) ^ 2 + Real.cos (half x) ^ 2) /
          (Real.sin (half x) ^ 2 * Real.cos (half x) ^ 2) := by
      unfold expandedDerivative sec csc
      field_simp [hcos, hsin] <;> ring
    _ = (1 / 2 : ℝ) /
          (Real.sin (half x) ^ 2 * Real.cos (half x) ^ 2) := by
      rw [hsq]
      ring
    _ = 2 /
          (2 * Real.sin (half x) * Real.cos (half x)) ^ 2 := by
      field_simp [hcos, hsin] <;> ring
    _ = finalDerivative x := by
      unfold finalDerivative
      rw [hdouble]

/-- Exercise 871, gap 3; restrict to the source function's
domain. -/
theorem gap3 (x : ℝ) (hcos : Real.cos (half x) ≠ 0)
    (hsin : Real.sin (half x) ≠ 0) :
    deriv y x = finalDerivative x := by
  calc
    deriv y x = expandedDerivative x := gap1 x hcos hsin
    _ = finalDerivative x := gap2 x hcos hsin

end

end ProofGap.Exercise871
