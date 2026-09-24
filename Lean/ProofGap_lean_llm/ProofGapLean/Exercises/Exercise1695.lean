import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1695

noncomputable section

def branch : Set ℝ := Set.univ
def integrand (x : ℝ) := (Real.sin x) ^ 5 * Real.cos x
def substitutedIntegrand (x : ℝ) :=
  (Real.sin x) ^ 5 * deriv Real.sin x
def primitive (x : ℝ) := (1 / 6 : ℝ) * (Real.sin x) ^ 6
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private theorem deriv_sin_eq_cos (x : ℝ) :
    deriv Real.sin x = Real.cos x :=
  (Real.hasDerivAt_sin x).deriv

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (substitutedIntegrand x) x := by
  convert ((Real.hasDerivAt_sin x).pow 6).const_mul (1 / 6 : ℝ) using 1 <;>
    simp [substitutedIntegrand, deriv_sin_eq_cos] <;> ring

theorem gap1 :
    AntiderivativesOn integrand = AntiderivativesOn substitutedIntegrand := by
  simp [AntiderivativesOn, integrand, substitutedIntegrand,
    deriv_sin_eq_cos]
theorem gap2 :
    AntiderivativesOn substitutedIntegrand = PrimitiveFamily primitive := by
  ext F
  constructor
  · intro hF
    let g : ℝ → ℝ := fun x => F x - primitive x
    have hg : ∀ x : ℝ, HasDerivAt g 0 x := by
      intro x
      have hsub := (hF x (by simp [branch])).sub (primitive_hasDerivAt x)
      simpa [g] using hsub
    have hgdiff : Differentiable ℝ g :=
      fun x => (hg x).differentiableAt
    have hgderiv : ∀ x : ℝ, deriv g x = 0 :=
      fun x => (hg x).deriv
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have heq : g x = g 0 :=
      is_const_of_deriv_eq_zero hgdiff hgderiv x 0
    dsimp [g] at heq
    linarith
  · rintro ⟨C, hC⟩
    intro x hx
    have hEq : F = fun y => primitive y + C := by
      funext y
      exact hC y (by simp [branch])
    rw [hEq]
    simpa using (primitive_hasDerivAt x).add_const C
theorem gap3 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  exact gap1.trans gap2

end
end ProofGap.Exercise1695
