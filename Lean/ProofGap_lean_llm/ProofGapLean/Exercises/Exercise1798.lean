import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1798

noncomputable section

def integrand (x : ℝ) : ℝ := x * Real.cos x
def primitive (x : ℝ) : ℝ := x * Real.sin x + Real.cos x
def IsAntiderivative (F f : ℝ → ℝ) : Prop := ∀ x, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) : Set (ℝ → ℝ) := {F | IsAntiderivative F f}
def Translates (P : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x, F x = P x + C}

theorem gap1 (x : ℝ) :
    HasDerivAt Real.sin (Real.cos x) x := by
  simpa using Real.hasDerivAt_sin x

theorem gap2 (x : ℝ) :
    HasDerivAt (fun y => y * Real.sin y)
      (integrand x + Real.sin x) x := by
  simpa [integrand, add_comm, add_left_comm, add_assoc] using
    (hasDerivAt_id x).mul (gap1 x)

theorem gap3 (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  simpa [primitive, integrand] using
    (gap2 x).add (Real.hasDerivAt_cos x)

theorem gap4 :
    Family integrand = Translates primitive := by
  ext F
  constructor
  · intro hF
    have hzero : ∀ x, HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x
      simpa using (hF x).sub (gap3 x)
    have hdiff : Differentiable ℝ (fun y => F y - primitive y) := by
      intro x
      exact (hzero x).differentiableAt
    have hderiv : ∀ x, deriv (fun y => F y - primitive y) x = 0 := by
      intro x
      exact (hzero x).deriv
    have hconst : ∀ x, F x - primitive x = F 0 - primitive 0 := by
      intro x
      exact is_const_of_deriv_eq_zero hdiff hderiv x 0
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    linarith [hconst x]
  · rintro ⟨C, hC⟩
    intro x
    have hEq : F = fun y => primitive y + C := by
      funext y
      exact hC y
    rw [hEq]
    simpa using (gap3 x).const_add C

end

end ProofGap.Exercise1798
