import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2120
noncomputable section

def tanh (x : ℝ) := Real.sinh x / Real.cosh x
def quotient (x : ℝ) := Real.sinh x / Real.cosh x
def primitive (x : ℝ) := Real.log (Real.cosh x)

def Family (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x, HasDerivAt F (f x) x}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C : ℝ, ∀ x, F x = p x + C}

private theorem hasDerivAt_primitive (x : ℝ) :
    HasDerivAt primitive (quotient x) x := by
  unfold primitive quotient
  simpa [Function.comp_def, div_eq_mul_inv, mul_comm] using
    ((Real.hasDerivAt_log (ne_of_gt (Real.cosh_pos x))).comp x
      (Real.hasDerivAt_cosh x))

theorem gap1 : Family tanh = Family quotient := by
  rfl
theorem gap2 : Family quotient = Translates primitive := by
  ext F
  constructor
  · intro hF
    change ∀ x, HasDerivAt F (quotient x) x at hF
    change ∃ C : ℝ, ∀ x, F x = primitive x + C
    have hzero : ∀ x, HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x
      simpa using (hF x).sub (hasDerivAt_primitive x)
    have hdiff : Differentiable ℝ (fun y => F y - primitive y) :=
      fun x => (hzero x).differentiableAt
    have hderiv : ∀ x, deriv (fun y => F y - primitive y) x = 0 :=
      fun x => (hzero x).deriv
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have hc : F x - primitive x = F 0 - primitive 0 :=
      is_const_of_deriv_eq_zero hdiff hderiv x 0
    linarith
  · intro hF
    change ∃ C : ℝ, ∀ x, F x = primitive x + C at hF
    rcases hF with ⟨C, hC⟩
    change ∀ x, HasDerivAt F (quotient x) x
    have hEq : F = fun y => primitive y + C := funext hC
    intro x
    rw [hEq]
    exact (hasDerivAt_primitive x).add_const C
theorem gap3 : Family tanh = Translates primitive := by
  calc
    Family tanh = Family quotient := gap1
    _ = Translates primitive := gap2

end
end ProofGap.Exercise2120
