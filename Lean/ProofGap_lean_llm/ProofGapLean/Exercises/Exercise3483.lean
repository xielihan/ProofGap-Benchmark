import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3483

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

theorem gap1 (x y u U : ℝ → ℝ → ℝ) (r φ : ℝ)
    (hr : r ≠ 0)
    (hUx : partialX U (x r φ) (y r φ) =
      x r φ / r * partialX u r φ -
        y r φ / r ^ 2 * partialY u r φ)
    (hUy : partialY U (x r φ) (y r φ) =
      y r φ / r * partialX u r φ +
        x r φ / r ^ 2 * partialY u r φ) :
    partialX U (x r φ) (y r φ) ^ 2 +
        partialY U (x r φ) (y r φ) ^ 2 =
      (x r φ / r * partialX u r φ -
          y r φ / r ^ 2 * partialY u r φ) ^ 2 +
        (y r φ / r * partialX u r φ +
          x r φ / r ^ 2 * partialY u r φ) ^ 2 := by
  rw [hUx, hUy]

theorem gap2 (x y u : ℝ → ℝ → ℝ) (r φ : ℝ)
    (hr : r ≠ 0)
    (hRadius : x r φ ^ 2 + y r φ ^ 2 = r ^ 2) :
    (x r φ / r * partialX u r φ -
          y r φ / r ^ 2 * partialY u r φ) ^ 2 +
        (y r φ / r * partialX u r φ +
          x r φ / r ^ 2 * partialY u r φ) ^ 2 =
      partialX u r φ ^ 2 + 1 / r ^ 2 * partialY u r φ ^ 2 := by
  field_simp [hr]
  calc
    (x r φ * r * partialX u r φ - y r φ * partialY u r φ) ^ 2 +
          (r * partialX u r φ * y r φ +
            x r φ * partialY u r φ) ^ 2 =
        (x r φ ^ 2 + y r φ ^ 2) *
          (r ^ 2 * partialX u r φ ^ 2 + partialY u r φ ^ 2) := by
      ring
    _ = r ^ 2 *
          (r ^ 2 * partialX u r φ ^ 2 + partialY u r φ ^ 2) := by
      rw [hRadius]

theorem gap3 (x y u U : ℝ → ℝ → ℝ) (r φ : ℝ)
    (hExpanded :
      partialX U (x r φ) (y r φ) ^ 2 +
          partialY U (x r φ) (y r φ) ^ 2 =
        (x r φ / r * partialX u r φ -
            y r φ / r ^ 2 * partialY u r φ) ^ 2 +
          (y r φ / r * partialX u r φ +
            x r φ / r ^ 2 * partialY u r φ) ^ 2)
    (hSimplified :
      (x r φ / r * partialX u r φ -
            y r φ / r ^ 2 * partialY u r φ) ^ 2 +
          (y r φ / r * partialX u r φ +
            x r φ / r ^ 2 * partialY u r φ) ^ 2 =
        partialX u r φ ^ 2 + 1 / r ^ 2 * partialY u r φ ^ 2) :
    partialX U (x r φ) (y r φ) ^ 2 +
        partialY U (x r φ) (y r φ) ^ 2 =
      partialX u r φ ^ 2 + 1 / r ^ 2 * partialY u r φ ^ 2 := by
  exact hExpanded.trans hSimplified

end

end ProofGap.Exercise3483
