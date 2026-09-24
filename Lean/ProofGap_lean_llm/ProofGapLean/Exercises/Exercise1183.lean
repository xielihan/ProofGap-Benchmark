import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1183

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def y (C₁ C₂ r₁ r₂ x : ℝ) : ℝ :=
  C₁ * Real.exp (r₁ * x) + C₂ * Real.exp (r₂ * x)

def expandedODE (C₁ C₂ r₁ r₂ x : ℝ) : ℝ :=
  C₁ * r₁ ^ 2 * Real.exp (r₁ * x) +
    C₂ * r₂ ^ 2 * Real.exp (r₂ * x) -
    C₁ * r₁ ^ 2 * Real.exp (r₁ * x) -
    C₁ * r₁ * r₂ * Real.exp (r₁ * x) -
    C₂ * r₂ ^ 2 * Real.exp (r₂ * x) -
    C₂ * r₁ * r₂ * Real.exp (r₂ * x) +
    C₁ * r₁ * r₂ * Real.exp (r₁ * x) +
    C₂ * r₁ * r₂ * Real.exp (r₂ * x)

theorem gap1 (C₁ C₂ r₁ r₂ x : ℝ) :
    iterDeriv 1 (y C₁ C₂ r₁ r₂) x =
      C₁ * r₁ * Real.exp (r₁ * x) + C₂ * r₂ * Real.exp (r₂ * x) := by
  unfold iterDeriv y
  change deriv (fun x : ℝ => C₁ * Real.exp (r₁ * x) + C₂ * Real.exp (r₂ * x)) x = _
  have hr₁ : HasDerivAt (fun t : ℝ => r₁ * t) r₁ x := by
    simpa using (hasDerivAt_id x).const_mul r₁
  have hr₂ : HasDerivAt (fun t : ℝ => r₂ * t) r₂ x := by
    simpa using (hasDerivAt_id x).const_mul r₂
  have h₁ : HasDerivAt (fun t : ℝ => C₁ * Real.exp (r₁ * t))
      (C₁ * (Real.exp (r₁ * x) * r₁)) x :=
    ((Real.hasDerivAt_exp (r₁ * x)).comp x hr₁).const_mul C₁
  have h₂ : HasDerivAt (fun t : ℝ => C₂ * Real.exp (r₂ * t))
      (C₂ * (Real.exp (r₂ * x) * r₂)) x :=
    ((Real.hasDerivAt_exp (r₂ * x)).comp x hr₂).const_mul C₂
  have hsum : HasDerivAt
      (fun t : ℝ => C₁ * Real.exp (r₁ * t) + C₂ * Real.exp (r₂ * t))
      (C₁ * (Real.exp (r₁ * x) * r₁) + C₂ * (Real.exp (r₂ * x) * r₂)) x :=
    h₁.add h₂
  calc
    deriv (fun t : ℝ => C₁ * Real.exp (r₁ * t) + C₂ * Real.exp (r₂ * t)) x =
        C₁ * (Real.exp (r₁ * x) * r₁) + C₂ * (Real.exp (r₂ * x) * r₂) := hsum.deriv
    _ = C₁ * r₁ * Real.exp (r₁ * x) + C₂ * r₂ * Real.exp (r₂ * x) := by ring

theorem gap2 (C₁ C₂ r₁ r₂ x : ℝ) :
    iterDeriv 2 (y C₁ C₂ r₁ r₂) x =
      C₁ * r₁ ^ 2 * Real.exp (r₁ * x) +
        C₂ * r₂ ^ 2 * Real.exp (r₂ * x) := by
  unfold iterDeriv
  change deriv (deriv (y C₁ C₂ r₁ r₂)) x = _
  have hfun : deriv (y C₁ C₂ r₁ r₂) =
      fun t : ℝ => C₁ * r₁ * Real.exp (r₁ * t) + C₂ * r₂ * Real.exp (r₂ * t) := by
    funext t
    exact gap1 C₁ C₂ r₁ r₂ t
  rw [hfun]
  have hr₁ : HasDerivAt (fun t : ℝ => r₁ * t) r₁ x := by
    simpa using (hasDerivAt_id x).const_mul r₁
  have hr₂ : HasDerivAt (fun t : ℝ => r₂ * t) r₂ x := by
    simpa using (hasDerivAt_id x).const_mul r₂
  have h₁ : HasDerivAt (fun t : ℝ => C₁ * r₁ * Real.exp (r₁ * t))
      ((C₁ * r₁) * (Real.exp (r₁ * x) * r₁)) x :=
    ((Real.hasDerivAt_exp (r₁ * x)).comp x hr₁).const_mul (C₁ * r₁)
  have h₂ : HasDerivAt (fun t : ℝ => C₂ * r₂ * Real.exp (r₂ * t))
      ((C₂ * r₂) * (Real.exp (r₂ * x) * r₂)) x :=
    ((Real.hasDerivAt_exp (r₂ * x)).comp x hr₂).const_mul (C₂ * r₂)
  have hsum : HasDerivAt
      (fun t : ℝ => C₁ * r₁ * Real.exp (r₁ * t) + C₂ * r₂ * Real.exp (r₂ * t))
      ((C₁ * r₁) * (Real.exp (r₁ * x) * r₁) +
        (C₂ * r₂) * (Real.exp (r₂ * x) * r₂)) x :=
    h₁.add h₂
  calc
    deriv (fun t : ℝ => C₁ * r₁ * Real.exp (r₁ * t) + C₂ * r₂ * Real.exp (r₂ * t)) x =
        (C₁ * r₁) * (Real.exp (r₁ * x) * r₁) +
          (C₂ * r₂) * (Real.exp (r₂ * x) * r₂) := hsum.deriv
    _ = C₁ * r₁ ^ 2 * Real.exp (r₁ * x) + C₂ * r₂ ^ 2 * Real.exp (r₂ * x) := by ring

theorem gap3 (C₁ C₂ r₁ r₂ x : ℝ) :
    iterDeriv 2 (y C₁ C₂ r₁ r₂) x -
        (r₁ + r₂) * iterDeriv 1 (y C₁ C₂ r₁ r₂) x +
        r₁ * r₂ * y C₁ C₂ r₁ r₂ x =
      expandedODE C₁ C₂ r₁ r₂ x := by
  rw [gap1, gap2]
  unfold y expandedODE
  ring

theorem gap4 (C₁ C₂ r₁ r₂ x : ℝ) :
    expandedODE C₁ C₂ r₁ r₂ x = 0 := by
  unfold expandedODE
  ring

theorem gap5 (C₁ C₂ r₁ r₂ x : ℝ) :
    iterDeriv 2 (y C₁ C₂ r₁ r₂) x -
        (r₁ + r₂) * iterDeriv 1 (y C₁ C₂ r₁ r₂) x +
        r₁ * r₂ * y C₁ C₂ r₁ r₂ x = 0 := by
  rw [gap3, gap4]

theorem gap6 (C₁ C₂ r₁ r₂ x : ℝ) :
    iterDeriv 2 (y C₁ C₂ r₁ r₂) x -
        (r₁ + r₂) * iterDeriv 1 (y C₁ C₂ r₁ r₂) x +
        r₁ * r₂ * y C₁ C₂ r₁ r₂ x = 0 := by
  exact gap5 C₁ C₂ r₁ r₂ x

end

end ProofGap.Exercise1183
