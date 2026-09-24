import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Add

namespace ProofGap.Exercise1014_2

noncomputable section

def f (x : ℝ) : ℝ := (x + |x|) / 2
def g (x : ℝ) : ℝ := (x - |x|) / 2
def F (x : ℝ) : ℝ := f x + g x

theorem gap1 : ¬ DifferentiableAt ℝ f 0 := by
  intro hf
  apply not_differentiableAt_abs_zero
  have habs :
      DifferentiableAt ℝ (fun x : ℝ => 2 * f x - x) 0 :=
    (hf.const_mul 2).sub differentiableAt_id
  convert habs using 1
  funext x
  simp [f]
  ring

theorem gap2 : ¬ DifferentiableAt ℝ g 0 := by
  intro hg
  apply not_differentiableAt_abs_zero
  have habs :
      DifferentiableAt ℝ (fun x : ℝ => x - 2 * g x) 0 :=
    differentiableAt_id.sub (hg.const_mul 2)
  convert habs using 1
  funext x
  simp [g]
  ring

theorem gap3 (x : ℝ) : F x = f x + g x := by
  rfl

theorem gap4 (x : ℝ) : f x + g x = x := by
  unfold f g
  ring

theorem gap5 (x : ℝ) : F x = x := by
  rw [gap3, gap4]

theorem gap6 : DifferentiableAt ℝ F 0 := by
  have hF : F = id := funext gap5
  rw [hF]
  exact differentiableAt_id

theorem gap7 : HasDerivAt F 1 0 := by
  have hF : F = id := funext gap5
  rw [hF]
  exact hasDerivAt_id 0

theorem gap8 :
    ¬ DifferentiableAt ℝ f 0 ∧
      ¬ DifferentiableAt ℝ g 0 ∧
      (∀ x, F x = f x + g x) ∧
      DifferentiableAt ℝ F 0 := by
  exact ⟨gap1, gap2, gap3, gap6⟩

end

end ProofGap.Exercise1014_2
