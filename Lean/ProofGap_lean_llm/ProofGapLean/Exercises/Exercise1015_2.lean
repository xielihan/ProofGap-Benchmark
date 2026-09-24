import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace ProofGap.Exercise1015_2

noncomputable section

def f (x : ℝ) : ℝ := |x|
def g (x : ℝ) : ℝ := |x|
def F (x : ℝ) : ℝ := f x * g x

theorem gap1 : ¬ DifferentiableAt ℝ f 0 := by
  simpa [f] using not_differentiableAt_abs_zero

theorem gap2 : ¬ DifferentiableAt ℝ g 0 := by
  simpa [g] using not_differentiableAt_abs_zero

theorem gap3 (x : ℝ) : F x = f x * g x := by
  rfl

theorem gap4 (x : ℝ) : f x * g x = |x| ^ 2 := by
  simp [f, g, pow_two]

theorem gap5 (x : ℝ) : |x| ^ 2 = x ^ 2 := by
  exact sq_abs x

theorem gap6 (x : ℝ) : F x = x ^ 2 := by
  rw [gap3, gap4, gap5]

theorem gap7 : DifferentiableAt ℝ F 0 := by
  have hF : F = fun x : ℝ => x ^ 2 := funext gap6
  rw [hF]
  exact ((hasDerivAt_id (0 : ℝ)).pow 2).differentiableAt

theorem gap8 : HasDerivAt F 0 0 := by
  have hF : F = fun x : ℝ => x ^ 2 := funext gap6
  rw [hF]
  convert (hasDerivAt_id (0 : ℝ)).pow 2 using 1 <;> norm_num

theorem gap9 :
    ¬ DifferentiableAt ℝ f 0 ∧
      ¬ DifferentiableAt ℝ g 0 ∧
      (∀ x, F x = f x * g x) ∧
      DifferentiableAt ℝ F 0 := by
  exact ⟨gap1, gap2, gap3, gap7⟩

end

end ProofGap.Exercise1015_2
