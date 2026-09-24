import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise950

noncomputable section

def y (x : ℝ) : ℝ :=
  x * Real.arctan x - (1 / 2 : ℝ) * Real.log (1 + x ^ 2) -
    (1 / 2 : ℝ) * Real.arctan x ^ 2

def expandedDerivative (x : ℝ) : ℝ :=
  Real.arctan x + x / (1 + x ^ 2) - x / (1 + x ^ 2) -
    1 / (1 + x ^ 2) * Real.arctan x

def finalDerivative (x : ℝ) : ℝ :=
  x ^ 2 / (1 + x ^ 2) * Real.arctan x

theorem gap1 (x : ℝ) : HasDerivAt y (expandedDerivative x) x := by
  have hden : 1 + x ^ 2 ≠ 0 := by
    positivity
  have hidSq :
      HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    simpa [pow_two, two_mul] using
      ((hasDerivAt_id x).mul (hasDerivAt_id x))
  have hinner :
      HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * x) x :=
    hidSq.const_add (1 : ℝ)
  have hatan :
      HasDerivAt Real.arctan (1 / (1 + x ^ 2)) x := by
    simpa [pow_two] using Real.hasDerivAt_arctan x
  have hterm1 :
      HasDerivAt (fun t : ℝ => t * Real.arctan t)
        (Real.arctan x + x * (1 / (1 + x ^ 2))) x := by
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id x).mul hatan)
  have hlog :
      HasDerivAt (fun t : ℝ => Real.log (1 + t ^ 2))
        ((1 + x ^ 2)⁻¹ * (2 * x)) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_log hden).comp x hinner
  have hterm2 :
      HasDerivAt (fun t : ℝ => (1 / 2 : ℝ) * Real.log (1 + t ^ 2))
        ((1 / 2 : ℝ) * ((1 + x ^ 2)⁻¹ * (2 * x))) x := by
    simpa only using hlog.const_mul (1 / 2 : ℝ)
  have hatanSq :
      HasDerivAt (fun t : ℝ => Real.arctan t ^ 2)
        (1 / (1 + x ^ 2) * Real.arctan x +
          Real.arctan x * (1 / (1 + x ^ 2))) x := by
    simpa only [pow_two] using hatan.mul hatan
  have hterm3 :
      HasDerivAt (fun t : ℝ => (1 / 2 : ℝ) * Real.arctan t ^ 2)
        ((1 / 2 : ℝ) *
          (1 / (1 + x ^ 2) * Real.arctan x +
            Real.arctan x * (1 / (1 + x ^ 2)))) x := by
    simpa only using hatanSq.const_mul (1 / 2 : ℝ)
  have hmain := (hterm1.sub hterm2).sub hterm3
  have hcoeff :
      (Real.arctan x + x * (1 / (1 + x ^ 2)) -
          (1 / 2 : ℝ) * ((1 + x ^ 2)⁻¹ * (2 * x))) -
        (1 / 2 : ℝ) *
          (1 / (1 + x ^ 2) * Real.arctan x +
            Real.arctan x * (1 / (1 + x ^ 2))) =
        expandedDerivative x := by
    unfold expandedDerivative
    field_simp [hden]
    ring
  rw [hcoeff] at hmain
  simpa only [y] using hmain

theorem gap2 (x : ℝ) : expandedDerivative x = finalDerivative x := by
  unfold expandedDerivative finalDerivative
  have hden : 1 + x ^ 2 ≠ 0 := by
    positivity
  field_simp [hden] <;> ring

theorem gap3 (x : ℝ) : HasDerivAt y (finalDerivative x) x := by
  simpa only [gap2] using (gap1 x)

end

end ProofGap.Exercise950
