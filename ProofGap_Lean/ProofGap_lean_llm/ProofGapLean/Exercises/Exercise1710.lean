import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.OrderClosed

namespace ProofGap.Exercise1710

noncomputable section

def branch : Set ℝ := Set.Ioo 0 1
def integrand (x : ℝ) :=
  1 / ((Real.arcsin x) ^ 2 * Real.sqrt (1 - x ^ 2))
def substitutedIntegrand (x : ℝ) :=
  deriv Real.arcsin x / (Real.arcsin x) ^ 2
def primitive (x : ℝ) := -(1 / Real.arcsin x)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private lemma integrand_eq_substituted (x : ℝ) (hx : x ∈ branch) :
    integrand x = substitutedIntegrand x := by
  have hm1 : x ≠ (-1 : ℝ) := by
    linarith [hx.1]
  have hp1 : x ≠ (1 : ℝ) := by
    linarith [hx.2]
  have ha := Real.hasDerivAt_arcsin hm1 hp1
  have hapos : 0 < Real.arcsin x := Real.arcsin_pos.2 hx.1
  have hspos : 0 < Real.sqrt (1 - x ^ 2) := by
    apply Real.sqrt_pos.2
    nlinarith [hx.1, hx.2]
  rw [integrand, substitutedIntegrand, ha.deriv]
  field_simp [ne_of_gt hapos, ne_of_gt hspos]
  <;> ring

private lemma hasDerivAt_primitive (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (substitutedIntegrand x) x := by
  have hm1 : x ≠ (-1 : ℝ) := by
    linarith [hx.1]
  have hp1 : x ≠ (1 : ℝ) := by
    linarith [hx.2]
  have ha := Real.hasDerivAt_arcsin hm1 hp1
  have hne : Real.arcsin x ≠ 0 :=
    ne_of_gt (Real.arcsin_pos.2 hx.1)
  have hp : HasDerivAt (fun y : ℝ => -(Real.arcsin y)⁻¹)
      (substitutedIntegrand x) x := by
    simpa [substitutedIntegrand, ha.deriv, div_eq_mul_inv] using
      (ha.inv hne).neg
  have hfun : (fun y : ℝ => -(Real.arcsin y)⁻¹) = primitive := by
    funext y
    simp [primitive, one_div]
  rw [← hfun]
  exact hp

theorem gap1 :
    AntiderivativesOn integrand =
      AntiderivativesOn substitutedIntegrand := by
  apply Set.ext
  intro F
  constructor <;> intro hF x hx
  · simpa only [integrand_eq_substituted x hx] using hF x hx
  · simpa only [integrand_eq_substituted x hx] using hF x hx
theorem gap2 :
    AntiderivativesOn substitutedIntegrand = PrimitiveFamily primitive := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    have hz : ∀ x ∈ branch,
        HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      simpa using (hF x hx).sub (hasDerivAt_primitive x hx)
    have hdiff : DifferentiableOn ℝ (fun y => F y - primitive y) branch := by
      intro x hx
      exact (hz x hx).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ branch,
        deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      exact (hz x hx).deriv
    have hconst : ∀ x ∈ branch, ∀ y ∈ branch,
        F x - primitive x = F y - primitive y := by
      intro x hx y hy
      exact isOpen_Ioo.is_const_of_deriv_eq_zero
        isPreconnected_Ioo hdiff hderiv hx hy
    refine ⟨F (1 / 2) - primitive (1 / 2), ?_⟩
    intro x hx
    have hhalf : (1 / 2 : ℝ) ∈ branch := by
      norm_num [branch]
    have heq : F x - primitive x =
        F (1 / 2) - primitive (1 / 2) :=
      hconst x hx (1 / 2) hhalf
    linarith
  · rintro ⟨C, hC⟩
    intro x hx
    have hlocal : Filter.EventuallyEq (nhds x) F
        (fun y => primitive y + C) := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact hC y hy
    exact ((hasDerivAt_primitive x hx).add_const C).congr_of_eventuallyEq
      hlocal
theorem gap3 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  rw [gap1, gap2]

end
end ProofGap.Exercise1710
