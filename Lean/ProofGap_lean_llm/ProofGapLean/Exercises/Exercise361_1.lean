import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise361_1

def f (a b x : ℝ) : ℝ := a * x + b

def IsCenter (g : ℝ → ℝ) (x₀ y₀ : ℝ) : Prop :=
  ∀ t, g (x₀ + t) + g (x₀ - t) = 2 * y₀

/-- Source: `proof_gap/exercise_361_1/1.txt`. -/
theorem gap1 (a b x₀ y₀ : ℝ) :
    IsCenter (f a b) x₀ y₀ ↔ y₀ = a * x₀ + b := by
  constructor
  · intro h
    have h0 := h 0
    simp [f] at h0
    linarith
  · intro h t
    simp only [f]
    rw [h]
    ring

/-- Source: `proof_gap/exercise_361_1/2.txt`. -/
theorem gap2 (a b x₀ y₀ : ℝ) (hpoint : y₀ = a * x₀ + b) :
    IsCenter (f a b) x₀ y₀ := by
  exact (gap1 a b x₀ y₀).2 hpoint

end ProofGap.Exercise361_1
