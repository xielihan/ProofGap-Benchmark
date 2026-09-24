import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise361_4

noncomputable section

def f (x : ℝ) : ℝ := 1 / (x - 1) + 1 / (x - 2) + 1 / (x - 3)
def domain : Set ℝ := {x | x ≠ 1 ∧ x ≠ 2 ∧ x ≠ 3}

def IsGraphCenter (g : ℝ → ℝ) (D : Set ℝ) (x₀ y₀ : ℝ) : Prop :=
  ∀ t, x₀ + t ∈ D → x₀ - t ∈ D →
    g (x₀ + t) + g (x₀ - t) = 2 * y₀

/-- Exercise 361_4, gap 1; exclude all poles of the two reflected inputs. -/
theorem gap1 : ∀ t, 2 + t ∈ domain → 2 - t ∈ domain →
    f (2 + t) + f (2 - t) = 0 := by
  intro t _ _
  have h1 : 2 + t - 1 = -(2 - t - 3) := by ring
  have h2 : 2 + t - 2 = -(2 - t - 2) := by ring
  have h3 : 2 + t - 3 = -(2 - t - 1) := by ring
  unfold f
  rw [h1, h2, h3]
  simp only [one_div, inv_neg]
  ring

/-- Exercise 361_4, gap 2; graph-center symmetry is restricted to the natural domain. -/
theorem gap2 : IsGraphCenter f domain 2 0 := by
  unfold IsGraphCenter
  intro t ht hmt
  simpa using gap1 t ht hmt

end

end ProofGap.Exercise361_4
