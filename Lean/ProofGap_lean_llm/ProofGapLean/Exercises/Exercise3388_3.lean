import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise3388_3

noncomputable section

def partialX (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => g t y) x

theorem gap1 (f : ℝ → ℝ → ℝ → ℝ) (z G : ℝ → ℝ → ℝ)
    (hG : ∀ x y, G x y = f x y (z x y)) :
    ∀ x y, G x y = f x y (z x y) := by
  exact hG

theorem gap2 (f : ℝ → ℝ → ℝ → ℝ) (y H : ℝ → ℝ → ℝ)
    (hH : ∀ x z, H x z = f x (y x z) z) :
    ∀ x z, H x z = f x (y x z) z := by
  exact hH

theorem gap3 (f : ℝ → ℝ → ℝ → ℝ)
    (z y G H : ℝ → ℝ → ℝ)
    (hG : ∀ x y₀, G x y₀ = f x y₀ (z x y₀))
    (hH : ∀ x z₀, H x z₀ = f x (y x z₀) z₀)
    (hGx : partialX G 1 1 = -2)
    (hHx : partialX H 1 1 = -1) :
    partialX G 1 1 ≠ partialX H 1 1 := by
  simpa [hGx, hHx]

theorem gap4 (G H : ℝ → ℝ → ℝ)
    (hDifferent : partialX G 1 1 ≠ partialX H 1 1) :
    partialX G 1 1 ≠ partialX H 1 1 := by
  exact hDifferent

end

end ProofGap.Exercise3388_3
