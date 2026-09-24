import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise936

noncomputable section

def A (x : ℝ) : ℝ :=
  x ^ 2 + x * Real.sqrt 2 + 1

def B (x : ℝ) : ℝ :=
  x ^ 2 - x * Real.sqrt 2 + 1

def y (x : ℝ) : ℝ :=
  1 / (4 * Real.sqrt 2) * Real.log (A x / B x) -
    1 / (2 * Real.sqrt 2) *
      Real.arctan (x * Real.sqrt 2 / (x ^ 2 - 1))

def expandedDerivative (x : ℝ) : ℝ :=
  1 / (4 * Real.sqrt 2) *
      ((2 * x + Real.sqrt 2) / A x -
        (2 * x - Real.sqrt 2) / B x) -
    1 / (2 * Real.sqrt 2) *
      (1 / (1 + (x * Real.sqrt 2 / (x ^ 2 - 1)) ^ 2)) *
      ((Real.sqrt 2 * (x ^ 2 - 1) - 2 * x ^ 2 * Real.sqrt 2) /
        (x ^ 2 - 1) ^ 2)

def finalDerivative (x : ℝ) : ℝ :=
  1 / (1 + x ^ 4)

/-- Source: `proof_gap/exercise_936/1.txt`; both logarithmic quadratics are
positive, while the arctangent quotient requires `x² ≠ 1`. -/
private theorem quadratics_pos (x : ℝ) : 0 < A x ∧ 0 < B x := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  constructor
  · unfold A
    nlinarith [sq_nonneg (x + Real.sqrt 2 / 2)]
  · unfold B
    nlinarith [sq_nonneg (x - Real.sqrt 2 / 2)]

theorem gap1 (x : ℝ) (hx : x ^ 2 ≠ 1) :
    HasDerivAt y (expandedDerivative x) x := by
  have hp := quadratics_pos x
  have hAne : A x ≠ 0 := ne_of_gt hp.1
  have hBne : B x ≠ 0 := ne_of_gt hp.2
  have hden : x ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hx
  have hsne : Real.sqrt 2 ≠ 0 := by positivity
  have hquotne : A x / B x ≠ 0 := div_ne_zero hAne hBne
  have hOne :
      1 + (x * Real.sqrt 2 / (x ^ 2 - 1)) ^ 2 ≠ 0 := by
    positivity
  have hsq : HasDerivAt (fun z : ℝ => z ^ 2) (2 * x) x := by
    simpa [pow_two, two_mul] using
      (hasDerivAt_id x).mul (hasDerivAt_id x)
  have hlinear :
      HasDerivAt (fun z : ℝ => z * Real.sqrt 2) (Real.sqrt 2) x := by
    simpa using
      (hasDerivAt_id x).mul (hasDerivAt_const x (Real.sqrt 2))
  have hA : HasDerivAt A (2 * x + Real.sqrt 2) x := by
    simpa [A] using
      (hsq.add hlinear).add (hasDerivAt_const x 1)
  have hB : HasDerivAt B (2 * x - Real.sqrt 2) x := by
    simpa [B] using
      (hsq.sub hlinear).add (hasDerivAt_const x 1)
  have hquot :
      HasDerivAt (fun z : ℝ => A z / B z)
        (((2 * x + Real.sqrt 2) * B x -
            A x * (2 * x - Real.sqrt 2)) / (B x) ^ 2) x :=
    hA.div hB hBne
  let logD : ℝ :=
    (A x / B x)⁻¹ *
      (((2 * x + Real.sqrt 2) * B x -
          A x * (2 * x - Real.sqrt 2)) / (B x) ^ 2)
  have hlog :
      HasDerivAt (fun z : ℝ => Real.log (A z / B z)) logD x := by
    dsimp [logD]
    simpa [one_div] using
      (Real.hasDerivAt_log hquotne).comp x hquot
  have hdenDeriv :
      HasDerivAt (fun z : ℝ => z ^ 2 - 1) (2 * x) x := by
    simpa only [Pi.sub_apply, sub_zero] using
      hsq.sub (hasDerivAt_const x 1)
  have harg :
      HasDerivAt
        (fun z : ℝ => z * Real.sqrt 2 / (z ^ 2 - 1))
        ((Real.sqrt 2 * (x ^ 2 - 1) -
            (x * Real.sqrt 2) * (2 * x)) / (x ^ 2 - 1) ^ 2) x :=
    hlinear.div hdenDeriv hden
  let atanD : ℝ :=
    (1 + (x * Real.sqrt 2 / (x ^ 2 - 1)) ^ 2)⁻¹ *
      ((Real.sqrt 2 * (x ^ 2 - 1) -
          (x * Real.sqrt 2) * (2 * x)) / (x ^ 2 - 1) ^ 2)
  have hatan :
      HasDerivAt
        (fun z : ℝ => Real.arctan
          (z * Real.sqrt 2 / (z ^ 2 - 1))) atanD x := by
    dsimp [atanD]
    simpa [one_div] using
      (Real.hasDerivAt_arctan
        (x * Real.sqrt 2 / (x ^ 2 - 1))).comp x harg
  have hraw :
      HasDerivAt y
        (1 / (4 * Real.sqrt 2) * logD -
          1 / (2 * Real.sqrt 2) * atanD) x := by
    change HasDerivAt
      (fun z : ℝ =>
        1 / (4 * Real.sqrt 2) * Real.log (A z / B z) -
          1 / (2 * Real.sqrt 2) *
            Real.arctan (z * Real.sqrt 2 / (z ^ 2 - 1)))
      (1 / (4 * Real.sqrt 2) * logD -
        1 / (2 * Real.sqrt 2) * atanD) x
    simpa only [Pi.mul_apply, Pi.sub_apply, zero_mul, zero_add] using
      ((hasDerivAt_const x (1 / (4 * Real.sqrt 2))).mul hlog).sub
        ((hasDerivAt_const x (1 / (2 * Real.sqrt 2))).mul hatan)
  have heq :
      1 / (4 * Real.sqrt 2) * logD -
          1 / (2 * Real.sqrt 2) * atanD = expandedDerivative x := by
    dsimp [logD, atanD]
    unfold expandedDerivative
    field_simp [hAne, hBne, hden, hsne, hOne, hquotne] <;> ring
  rw [← heq]
  exact hraw

/-- Source: `proof_gap/exercise_936/2.txt`; retain the nonzero quotient
denominator used in the rational simplification. -/
theorem gap2 (x : ℝ) (hx : x ^ 2 ≠ 1) :
    expandedDerivative x = finalDerivative x := by
  have hp := quadratics_pos x
  have hAne : A x ≠ 0 := ne_of_gt hp.1
  have hBne : B x ≠ 0 := ne_of_gt hp.2
  have hden : x ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hx
  have hsne : Real.sqrt 2 ≠ 0 := by positivity
  have hs : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hfinal : 1 + x ^ 4 ≠ 0 := by positivity
  have hOne :
      1 + (x * Real.sqrt 2 / (x ^ 2 - 1)) ^ 2 ≠ 0 := by
    positivity
  have hAB : A x * B x = 1 + x ^ 4 := by
    unfold A B
    calc
      (x ^ 2 + x * Real.sqrt 2 + 1) *
          (x ^ 2 - x * Real.sqrt 2 + 1) =
          (x ^ 2 + 1) ^ 2 - (x * Real.sqrt 2) ^ 2 := by ring
      _ = (x ^ 2 + 1) ^ 2 - x ^ 2 * (Real.sqrt 2) ^ 2 := by ring
      _ = 1 + x ^ 4 := by rw [hs]; ring
  have hnumLog :
      (2 * x + Real.sqrt 2) * B x -
          (2 * x - Real.sqrt 2) * A x =
        2 * Real.sqrt 2 * (1 - x ^ 2) := by
    unfold A B
    ring
  have hfrac :
      (2 * x + Real.sqrt 2) / A x -
          (2 * x - Real.sqrt 2) / B x =
        ((2 * x + Real.sqrt 2) * B x -
          (2 * x - Real.sqrt 2) * A x) / (A x * B x) := by
    field_simp [hAne, hBne] <;> ring
  have hlogPart :
      1 / (4 * Real.sqrt 2) *
          ((2 * x + Real.sqrt 2) / A x -
            (2 * x - Real.sqrt 2) / B x) =
        (1 - x ^ 2) / (2 * (1 + x ^ 4)) := by
    rw [hfrac, hnumLog, hAB]
    field_simp [hsne, hfinal] <;> ring
  have huDen :
      (x ^ 2 - 1) ^ 2 + (x * Real.sqrt 2) ^ 2 =
        1 + x ^ 4 := by
    calc
      (x ^ 2 - 1) ^ 2 + (x * Real.sqrt 2) ^ 2 =
          (x ^ 2 - 1) ^ 2 + x ^ 2 * (Real.sqrt 2) ^ 2 := by ring
      _ = 1 + x ^ 4 := by rw [hs]; ring
  have hsumne :
      (x ^ 2 - 1) ^ 2 + (x * Real.sqrt 2) ^ 2 ≠ 0 := by
    rw [huDen]
    exact hfinal
  have hfactor :
      1 / (1 + (x * Real.sqrt 2 / (x ^ 2 - 1)) ^ 2) =
        (x ^ 2 - 1) ^ 2 /
          ((x ^ 2 - 1) ^ 2 + (x * Real.sqrt 2) ^ 2) := by
    field_simp [hden, hOne, hsumne] <;> ring
  have hnumArg :
      Real.sqrt 2 * (x ^ 2 - 1) - 2 * x ^ 2 * Real.sqrt 2 =
        -(Real.sqrt 2) * (x ^ 2 + 1) := by
    ring
  have hatanPart :
      1 / (2 * Real.sqrt 2) *
          (1 / (1 + (x * Real.sqrt 2 / (x ^ 2 - 1)) ^ 2)) *
          ((Real.sqrt 2 * (x ^ 2 - 1) -
              2 * x ^ 2 * Real.sqrt 2) / (x ^ 2 - 1) ^ 2) =
        -(x ^ 2 + 1) / (2 * (1 + x ^ 4)) := by
    rw [hfactor, huDen, hnumArg]
    field_simp [hsne, hden, hfinal] <;> ring
  unfold expandedDerivative finalDerivative
  rw [hlogPart, hatanPart]
  field_simp [hfinal] <;> ring

/-- Source: `proof_gap/exercise_936/3.txt`; the displayed primitive has poles
at `x = ±1` even though the simplified rational expression is finite there. -/
theorem gap3 (x : ℝ) (hx : x ^ 2 ≠ 1) :
    HasDerivAt y (finalDerivative x) x := by
  rw [← gap2 x hx]
  exact gap1 x hx

end

end ProofGap.Exercise936
