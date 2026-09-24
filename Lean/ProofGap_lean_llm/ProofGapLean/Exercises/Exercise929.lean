import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise929

noncomputable section

def y (x : ℝ) : ℝ :=
  1 / Real.arccos (x ^ 2) ^ 2

def expandedDerivative (x : ℝ) : ℝ :=
  (-2 / Real.arccos (x ^ 2) ^ 3) *
    (-2 * x / Real.sqrt (1 - x ^ 4))

def finalDerivative (x : ℝ) : ℝ :=
  4 * x / (Real.sqrt (1 - x ^ 4) * Real.arccos (x ^ 2) ^ 3)

/-- Source: `proof_gap/exercise_929/1.txt`; `x² < 1` keeps the arccosine
argument in its strict interior and its value nonzero. -/
theorem gap1 (x : ℝ) (hx : x ^ 2 < 1) :
    HasDerivAt y (expandedDerivative x) x := by
  let sq : ℝ → ℝ := fun t => t ^ 2
  let inner : ℝ → ℝ := fun t => Real.arccos (sq t)
  have hsq : HasDerivAt sq (2 * x) x := by
    dsimp [sq]
    simpa using (hasDerivAt_id x).pow 2
  have hpow : (x ^ 2) ^ 2 = x ^ 4 := by
    ring
  have harccos :
      HasDerivAt Real.arccos
        (-(1 / Real.sqrt (1 - (sq x) ^ 2))) (sq x) := by
    exact Real.hasDerivAt_arccos
      (x := sq x)
      (by dsimp [sq]; nlinarith [sq_nonneg x])
      (by dsimp [sq]; nlinarith [sq_nonneg x])
  have hinnerRaw :
      HasDerivAt (Real.arccos ∘ sq)
        (-(1 / Real.sqrt (1 - (sq x) ^ 2)) * (2 * x)) x :=
    harccos.comp x hsq
  have hinner :
      HasDerivAt inner
        (-2 * x / Real.sqrt (1 - x ^ 4)) x := by
    convert hinnerRaw using 1 <;>
      simp only [inner, sq, hpow, div_eq_mul_inv] <;>
      ring
  have ha : inner x ≠ 0 := by
    dsimp [inner, sq]
    exact ne_of_gt (Real.arccos_pos.2 hx)
  have houter :
      HasDerivAt (fun t : ℝ => 1 / t ^ 2)
        (-2 / (inner x) ^ 3) (inner x) := by
    convert
      (hasDerivAt_const (inner x) (1 : ℝ)).div
        ((hasDerivAt_id (inner x)).pow 2)
        (pow_ne_zero 2 ha) using 1 <;>
      simp [id] <;>
      field_simp [ha] <;>
      ring_nf
  change
    HasDerivAt
      (fun t : ℝ => 1 / Real.arccos (t ^ 2) ^ 2)
      ((-2 / Real.arccos (x ^ 2) ^ 3) *
        (-2 * x / Real.sqrt (1 - x ^ 4))) x
  simpa only [Function.comp_apply, inner, sq] using
    houter.comp x hinner

/-- Source: `proof_gap/exercise_929/2.txt`; the strict-domain condition makes
both displayed denominator factors nonzero. -/
theorem gap2 (x : ℝ) (hx : x ^ 2 < 1) :
    expandedDerivative x = finalDerivative x := by
  have hrad : 0 < 1 - x ^ 4 := by
    calc
      0 < (1 - x ^ 2) * (1 + x ^ 2) :=
        mul_pos (sub_pos.mpr hx) (by nlinarith [sq_nonneg x])
      _ = 1 - x ^ 4 := by ring
  have hsqrt : Real.sqrt (1 - x ^ 4) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hrad)
  have ha : Real.arccos (x ^ 2) ≠ 0 :=
    ne_of_gt (Real.arccos_pos.2 hx)
  unfold expandedDerivative finalDerivative
  field_simp [hsqrt, ha] <;> ring

/-- Source: `proof_gap/exercise_929/3.txt`; retain the nonsingular reciprocal
arccosine domain. -/
theorem gap3 (x : ℝ) (hx : x ^ 2 < 1) :
    HasDerivAt y (finalDerivative x) x := by
  have h := gap1 x hx
  rw [gap2 x hx] at h
  exact h

end

end ProofGap.Exercise929
