import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise4201

noncomputable section

open MeasureTheory
open scoped Interval

abbrev Kernel := ℕ → ℝ → ℝ → ℝ

def HasConvolutionLaw (K : Kernel) (a b : ℝ) : Prop :=
  ∀ n m x y,
    K (n + m + 1) x y =
      ∫ t in a..b, K n x t * K m t y

theorem gap1
    (K : Kernel) (a b : ℝ) (hK : HasConvolutionLaw K a b)
    (n m : ℕ) (x y : ℝ) :
    ∃ A B : ℝ → ℝ,
      K (n + m + 1) x y = ∫ t in a..b, A t * B t := by
  refine ⟨fun t => K n x t, fun t => K m t y, ?_⟩
  exact hK n m x y

theorem gap2 (K : Kernel) (n : ℕ) (x : ℝ) :
    ∃ A : ℝ → ℝ, ∀ t, A t = K n x t := by
  exact ⟨fun t => K n x t, fun t => rfl⟩

theorem gap3 (K : Kernel) (m : ℕ) (y : ℝ) :
    ∃ B : ℝ → ℝ, ∀ t, B t = K m t y := by
  exact ⟨fun t => K m t y, fun t => rfl⟩

theorem gap4
    (K : Kernel) (a b : ℝ) (hK : HasConvolutionLaw K a b)
    (n m : ℕ) (x y : ℝ) :
    K (n + m + 1) x y =
      ∫ t in a..b, K n x t * K m t y := by
  exact hK n m x y

theorem gap5
    (K : Kernel) (a b : ℝ) (hK : HasConvolutionLaw K a b)
    (n m : ℕ) (x y : ℝ) :
    K (n + m + 1) x y =
      ∫ t in a..b, K n x t * K m t y := by
  exact gap4 K a b hK n m x y

end

end ProofGap.Exercise4201
