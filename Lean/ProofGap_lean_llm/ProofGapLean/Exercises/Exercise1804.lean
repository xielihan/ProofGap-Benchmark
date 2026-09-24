import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1804

noncomputable section

def branch : Set ℝ := Set.univ
def integrand (x : ℝ) := x * Real.arctan x
def scaledDerivativeIntegrand (x : ℝ) :=
  (1 / 2 : ℝ) * Real.arctan x * deriv (fun t : ℝ => t ^ 2) x
def residual (x : ℝ) := x ^ 2 / (1 + x ^ 2)
def rewrittenResidual (x : ℝ) := 1 - 1 / (1 + x ^ 2)
def boundary (x : ℝ) := (1 / 2 : ℝ) * x ^ 2 * Real.arctan x
def primitive (x : ℝ) :=
  (1 / 2 : ℝ) * x ^ 2 * Real.arctan x -
    x / 2 + (1 / 2 : ℝ) * Real.arctan x
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def ByPartsFamily (r : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn r, ∀ x ∈ branch, F x = boundary x - (1 / 2) * G x}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C}

private theorem derivative_square (x : ℝ) :
    deriv (fun t : ℝ => t ^ 2) x = 2 * x := by
  simpa using (((hasDerivAt_id x).pow 2).deriv)

private theorem scaledDerivativeIntegrand_eq_integrand (x : ℝ) :
    scaledDerivativeIntegrand x = integrand x := by
  simp [scaledDerivativeIntegrand, integrand, derivative_square]
  ring

private theorem hasDerivAt_boundary (x : ℝ) :
    HasDerivAt boundary
      (scaledDerivativeIntegrand x + (1 / 2 : ℝ) * residual x) x := by
  have h :=
    (((hasDerivAt_id x).pow 2).const_mul (1 / 2 : ℝ)).mul
      (Real.hasDerivAt_arctan x)
  convert h using 1 <;>
    simp [boundary, residual, scaledDerivativeIntegrand, derivative_square] <;> ring

private theorem residual_eq_rewrittenResidual (x : ℝ) :
    residual x = rewrittenResidual x := by
  have hne : 1 + x ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg x]
  unfold residual rewrittenResidual
  field_simp [hne] <;> ring

private theorem hasDerivAt_rewrittenResidualPrimitive (x : ℝ) :
    HasDerivAt (fun t : ℝ => t - Real.arctan t) (rewrittenResidual x) x := by
  convert (hasDerivAt_id x).sub (Real.hasDerivAt_arctan x) using 1 <;>
    simp [rewrittenResidual]

private theorem constant_of_hasDerivAt_zero (f : ℝ → ℝ)
    (h : ∀ x, HasDerivAt f 0 x) : ∀ x, f x = f 0 := by
  have hf : Differentiable ℝ f := fun x => (h x).differentiableAt
  have hd : ∀ x, deriv f x = 0 := fun x => (h x).deriv
  intro x
  exact is_const_of_deriv_eq_zero hf hd x 0

theorem gap1 :
    AntiderivativesOn integrand =
      AntiderivativesOn scaledDerivativeIntegrand := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
      ∀ x ∈ branch, HasDerivAt F (scaledDerivativeIntegrand x) x
  constructor
  · intro h x hx
    simpa only [scaledDerivativeIntegrand_eq_integrand] using h x hx
  · intro h x hx
    simpa only [scaledDerivativeIntegrand_eq_integrand] using h x hx
theorem gap2 :
    AntiderivativesOn scaledDerivativeIntegrand = ByPartsFamily residual := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (scaledDerivativeIntegrand x) x) ↔
      ∃ G, (∀ x ∈ branch, HasDerivAt G (residual x) x) ∧
        ∀ x ∈ branch, F x = boundary x - (1 / 2 : ℝ) * G x
  constructor
  · intro hF
    refine ⟨fun x => 2 * (boundary x - F x), ?_, ?_⟩
    · intro x hx
      convert ((hasDerivAt_boundary x).sub (hF x hx)).const_mul 2 using 1 <;> ring
    · intro x hx
      ring
  · rintro ⟨G, hG, hEq⟩
    intro x hx
    have hfun : F = fun t => boundary t - (1 / 2 : ℝ) * G t := by
      funext t
      exact hEq t (by simp [branch])
    rw [hfun]
    convert (hasDerivAt_boundary x).sub ((hG x hx).const_mul (1 / 2 : ℝ)) using 1 <;> ring
theorem gap3 :
    AntiderivativesOn integrand = ByPartsFamily residual := by
  exact gap1.trans gap2
theorem gap4 :
    AntiderivativesOn integrand = ByPartsFamily rewrittenResidual := by
  have hA : AntiderivativesOn residual = AntiderivativesOn rewrittenResidual := by
    ext G
    change
      (∀ x ∈ branch, HasDerivAt G (residual x) x) ↔
        ∀ x ∈ branch, HasDerivAt G (rewrittenResidual x) x
    constructor
    · intro h x hx
      simpa only [residual_eq_rewrittenResidual] using h x hx
    · intro h x hx
      simpa only [residual_eq_rewrittenResidual] using h x hx
  calc
    AntiderivativesOn integrand = ByPartsFamily residual := gap3
    _ = ByPartsFamily rewrittenResidual := by
      simp only [ByPartsFamily, hA]
theorem gap5 : ByPartsFamily rewrittenResidual = PrimitiveFamily := by
  ext F
  change
    (∃ G, (∀ x ∈ branch, HasDerivAt G (rewrittenResidual x) x) ∧
      ∀ x ∈ branch, F x = boundary x - (1 / 2 : ℝ) * G x) ↔
      ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C
  constructor
  · rintro ⟨G, hG, hEq⟩
    have hz : ∀ y : ℝ,
        HasDerivAt (fun t => G t - (t - Real.arctan t)) 0 y := by
      intro y
      convert (hG y (by simp [branch])).sub
        (hasDerivAt_rewrittenResidualPrimitive y) using 1 <;> ring
    refine ⟨-(1 / 2 : ℝ) * G 0, ?_⟩
    intro x hx
    have hc := constant_of_hasDerivAt_zero
      (fun t => G t - (t - Real.arctan t)) hz x
    have hc' : G x - (x - Real.arctan x) = G 0 := by
      simpa using hc
    have hgx : G x = x - Real.arctan x + G 0 := by
      linarith
    rw [hEq x hx, hgx]
    simp [primitive, boundary]
    ring
  · rintro ⟨C, hF⟩
    refine ⟨fun x => x - Real.arctan x - 2 * C, ?_, ?_⟩
    · intro x hx
      convert (hasDerivAt_rewrittenResidualPrimitive x).sub_const (2 * C) using 1 <;> ring
    · intro x hx
      rw [hF x hx]
      simp [primitive, boundary]
      ring
theorem gap6 : AntiderivativesOn integrand = PrimitiveFamily := by
  exact gap4.trans gap5

end
end ProofGap.Exercise1804
