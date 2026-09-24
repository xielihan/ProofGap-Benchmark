import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3487

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def physicalJacobian (U V : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialX U x y * partialY V x y - partialY U x y * partialX V x y

def polarJacobian (u v : ℝ → ℝ → ℝ) (r φ : ℝ) : ℝ :=
  partialX u r φ * partialY v r φ - partialY u r φ * partialX v r φ

def expandedJacobian (x y u v : ℝ → ℝ → ℝ) (r φ : ℝ) : ℝ :=
  (x r φ / r * partialX u r φ - y r φ / r ^ 2 * partialY u r φ) *
      (y r φ / r * partialX v r φ + x r φ / r ^ 2 * partialY v r φ) -
    (y r φ / r * partialX u r φ + x r φ / r ^ 2 * partialY u r φ) *
      (x r φ / r * partialX v r φ - y r φ / r ^ 2 * partialY v r φ)

theorem gap1 (x y u v U V : ℝ → ℝ → ℝ) (r φ : ℝ)
    (hr : r ≠ 0)
    (hUx : partialX U (x r φ) (y r φ) =
      x r φ / r * partialX u r φ - y r φ / r ^ 2 * partialY u r φ)
    (hUy : partialY U (x r φ) (y r φ) =
      y r φ / r * partialX u r φ + x r φ / r ^ 2 * partialY u r φ)
    (hVx : partialX V (x r φ) (y r φ) =
      x r φ / r * partialX v r φ - y r φ / r ^ 2 * partialY v r φ)
    (hVy : partialY V (x r φ) (y r φ) =
      y r φ / r * partialX v r φ + x r φ / r ^ 2 * partialY v r φ) :
    physicalJacobian U V (x r φ) (y r φ) =
      expandedJacobian x y u v r φ := by
  unfold physicalJacobian expandedJacobian
  rw [hUx, hVy, hUy, hVx]

theorem gap2 (x y u v : ℝ → ℝ → ℝ) (r φ : ℝ)
    (hr : r ≠ 0)
    (hRadius : x r φ ^ 2 + y r φ ^ 2 = r ^ 2) :
    expandedJacobian x y u v r φ =
      1 / r * polarJacobian u v r φ := by
  calc
    expandedJacobian x y u v r φ =
        (x r φ ^ 2 + y r φ ^ 2) / r ^ 3 * polarJacobian u v r φ := by
      unfold expandedJacobian polarJacobian
      field_simp [hr]
      ring
    _ = 1 / r * polarJacobian u v r φ := by
      rw [hRadius]
      field_simp [hr]

theorem gap3 (x y u v U V : ℝ → ℝ → ℝ) (r φ : ℝ)
    (hExpanded :
      physicalJacobian U V (x r φ) (y r φ) =
        expandedJacobian x y u v r φ)
    (hSimplified :
      expandedJacobian x y u v r φ =
        1 / r * polarJacobian u v r φ) :
    physicalJacobian U V (x r φ) (y r φ) =
      1 / r * polarJacobian u v r φ := by
  exact hExpanded.trans hSimplified

end

end ProofGap.Exercise3487
