import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1181

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def y (C₁ C₂ x : ℝ) : ℝ := C₁ * Real.cos x + C₂ * Real.sin x

theorem gap1 (C₁ C₂ x : ℝ) :
    iterDeriv 1 (y C₁ C₂) x = -C₁ * Real.sin x + C₂ * Real.cos x := by
  change deriv (y C₁ C₂) x = _
  have h :
      HasDerivAt (y C₁ C₂) (C₁ * (-Real.sin x) + C₂ * Real.cos x) x := by
    unfold y
    exact
      ((Real.hasDerivAt_cos x).const_mul C₁).add
        ((Real.hasDerivAt_sin x).const_mul C₂)
  rw [h.deriv]
  ring

theorem gap2 (C₁ C₂ x : ℝ) :
    iterDeriv 2 (y C₁ C₂) x = -C₁ * Real.cos x - C₂ * Real.sin x := by
  change deriv (deriv (y C₁ C₂)) x = _
  have hfirst :
      deriv (y C₁ C₂) = fun t => -C₁ * Real.sin t + C₂ * Real.cos t := by
    funext t
    exact gap1 C₁ C₂ t
  rw [hfirst]
  have hderiv :
      deriv (fun t => -C₁ * Real.sin t + C₂ * Real.cos t) x =
        (-C₁) * Real.cos x + C₂ * (-Real.sin x) := by
    simpa using
      (((Real.hasDerivAt_sin x).const_mul (-C₁)).add
        ((Real.hasDerivAt_cos x).const_mul C₂)).deriv
  rw [hderiv]
  ring

theorem gap3 (C₁ C₂ x : ℝ) :
    -C₁ * Real.cos x - C₂ * Real.sin x = -y C₁ C₂ x := by
  unfold y
  ring

theorem gap4 (C₁ C₂ x : ℝ) :
    iterDeriv 2 (y C₁ C₂) x = -y C₁ C₂ x := by
  calc
    iterDeriv 2 (y C₁ C₂) x = -C₁ * Real.cos x - C₂ * Real.sin x := gap2 C₁ C₂ x
    _ = -y C₁ C₂ x := gap3 C₁ C₂ x

theorem gap5 (C₁ C₂ x : ℝ) :
    iterDeriv 2 (y C₁ C₂) x + y C₁ C₂ x = 0 := by
  rw [gap4]
  ring

theorem gap6 (C₁ C₂ x : ℝ) :
    iterDeriv 2 (y C₁ C₂) x + y C₁ C₂ x = 0 := by
  exact gap5 C₁ C₂ x

end

end ProofGap.Exercise1181
