import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1709

noncomputable section

def branch : Set ℝ := Set.univ
def integrand (x : ℝ) := Real.arctan x / (1 + x ^ 2)
def substitutedIntegrand (x : ℝ) :=
  Real.arctan x * deriv Real.arctan x
def primitive (x : ℝ) := (1 / 2 : ℝ) * (Real.arctan x) ^ 2
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

theorem gap1 :
    AntiderivativesOn integrand =
      AntiderivativesOn substitutedIntegrand := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor <;> intro h x hx
  · have hd : deriv Real.arctan x = 1 / (1 + x ^ 2) :=
      (Real.hasDerivAt_arctan x).deriv
    simpa only [integrand, substitutedIntegrand, hd, div_eq_mul_inv, one_mul]
      using h x hx
  · have hd : deriv Real.arctan x = 1 / (1 + x ^ 2) :=
      (Real.hasDerivAt_arctan x).deriv
    simpa only [integrand, substitutedIntegrand, hd, div_eq_mul_inv, one_mul]
      using h x hx
theorem gap2 :
    AntiderivativesOn substitutedIntegrand = PrimitiveFamily primitive := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  have hp : ∀ x : ℝ, HasDerivAt primitive (substitutedIntegrand x) x := by
    intro x
    have ha := Real.hasDerivAt_arctan x
    have hs : HasDerivAt
        (fun y => (1 / 2 : ℝ) * (Real.arctan y * Real.arctan y))
        ((1 / 2 : ℝ) *
          ((1 / (1 + x ^ 2)) * Real.arctan x +
            Real.arctan x * (1 / (1 + x ^ 2)))) x :=
      (ha.mul ha).const_mul (1 / 2 : ℝ)
    have hcoef :
        (1 / 2 : ℝ) *
            ((1 / (1 + x ^ 2)) * Real.arctan x +
              Real.arctan x * (1 / (1 + x ^ 2))) =
          Real.arctan x * deriv Real.arctan x := by
      rw [ha.deriv]
      ring
    rw [hcoef] at hs
    change HasDerivAt
      (fun y => (1 / 2 : ℝ) * (Real.arctan y) ^ 2)
      (Real.arctan x * deriv Real.arctan x) x
    simpa only [pow_two] using hs
  constructor
  · intro h
    let G : ℝ → ℝ := fun x => F x - primitive x
    have hG : ∀ x : ℝ, HasDerivAt G 0 x := by
      intro x
      simpa [G] using (h x (Set.mem_univ x)).sub (hp x)
    have hdiff : Differentiable ℝ G := fun x => (hG x).differentiableAt
    have hderiv : ∀ x : ℝ, deriv G x = 0 := fun x => (hG x).deriv
    refine ⟨G 0, ?_⟩
    intro x hx
    have hc : G x = G 0 :=
      is_const_of_deriv_eq_zero hdiff hderiv x 0
    dsimp [G] at hc ⊢
    linarith
  · rintro ⟨C, hC⟩ x hx
    have hEq : F = fun y => primitive y + C := by
      funext y
      exact hC y (Set.mem_univ y)
    rw [hEq]
    simpa using (hp x).const_add C
theorem gap3 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  rw [gap1, gap2]

end
end ProofGap.Exercise1709
