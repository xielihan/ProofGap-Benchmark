import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1706

noncomputable section

def branch : Set ℝ := Set.univ
def integrand (x : ℝ) := 1 / Real.cosh x
def exponentialIntegrand (x : ℝ) :=
  2 / (Real.exp x + Real.exp (-x))
def substitutedIntegrand (x : ℝ) :=
  2 * (deriv Real.exp x / (1 + (Real.exp x) ^ 2))
def primitive (x : ℝ) := 2 * Real.arctan (Real.exp x)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private theorem integrand_eq_exponentialIntegrand :
    integrand = exponentialIntegrand := by
  funext x
  have hden : Real.exp x + Real.exp (-x) ≠ 0 := by positivity
  unfold integrand exponentialIntegrand
  rw [Real.cosh_eq]
  field_simp [hden]

private theorem exponentialIntegrand_eq_substitutedIntegrand :
    exponentialIntegrand = substitutedIntegrand := by
  funext x
  have hexp : Real.exp x ≠ 0 := Real.exp_ne_zero x
  have hden : 1 + Real.exp x ^ 2 ≠ 0 := by positivity
  unfold exponentialIntegrand substitutedIntegrand
  rw [(Real.hasDerivAt_exp x).deriv, Real.exp_neg]
  field_simp [hexp, hden]
  ring

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (substitutedIntegrand x) x := by
  simpa [primitive, substitutedIntegrand, (Real.hasDerivAt_exp x).deriv,
    Function.comp_apply, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (((Real.hasDerivAt_arctan (Real.exp x)).comp x
      (Real.hasDerivAt_exp x)).const_mul 2)

private theorem functions_differ_by_constant
    {F p f : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F (f x) x)
    (hp : ∀ x, HasDerivAt p (f x) x) :
    ∃ C : ℝ, ∀ x, F x = p x + C := by
  let D : ℝ → ℝ := fun x => F x - p x
  have hD : ∀ x, HasDerivAt D 0 x := by
    intro x
    simpa [D] using (hF x).sub (hp x)
  have hDdiff : Differentiable ℝ D :=
    fun x => (hD x).differentiableAt
  have hDderiv : ∀ x, deriv D x = 0 :=
    fun x => (hD x).deriv
  have hconst := is_const_of_deriv_eq_zero hDdiff hDderiv
  refine ⟨F 0 - p 0, ?_⟩
  intro x
  have hx : F x - p x = F 0 - p 0 := by
    simpa [D] using hconst x 0
  calc
    F x = p x + (F x - p x) := by ring
    _ = p x + (F 0 - p 0) := by rw [hx]

theorem gap1 :
    AntiderivativesOn integrand = AntiderivativesOn exponentialIntegrand := by
  exact congrArg AntiderivativesOn integrand_eq_exponentialIntegrand
theorem gap2 :
    AntiderivativesOn exponentialIntegrand =
      AntiderivativesOn substitutedIntegrand := by
  exact congrArg AntiderivativesOn exponentialIntegrand_eq_substitutedIntegrand
theorem gap3 :
    AntiderivativesOn substitutedIntegrand = PrimitiveFamily primitive := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (substitutedIntegrand x) x) ↔
      (∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C)
  constructor
  · intro hF
    obtain ⟨C, hC⟩ := functions_differ_by_constant
      (fun x => hF x (by simp [branch])) primitive_hasDerivAt
    exact ⟨C, fun x _ => hC x⟩
  · rintro ⟨C, hC⟩
    have hfun : F = fun x => primitive x + C := by
      funext x
      exact hC x (by simp [branch])
    intro x _
    rw [hfun]
    exact (primitive_hasDerivAt x).add_const C
theorem gap4 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  calc
    AntiderivativesOn integrand = AntiderivativesOn exponentialIntegrand := gap1
    _ = AntiderivativesOn substitutedIntegrand := gap2
    _ = PrimitiveFamily primitive := gap3

end
end ProofGap.Exercise1706
