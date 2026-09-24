import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2006
noncomputable section

def branch : Set ℝ := Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)
def integrand (x : ℝ) := Real.sin x ^ 4 / Real.cos x ^ 6
def transformed (x : ℝ) := Real.tan x ^ 4 * deriv Real.tan x
def primitive (x : ℝ) := (1 / 5 : ℝ) * Real.tan x ^ 5
def Family (f : ℝ → ℝ) := {F : ℝ → ℝ | ∀ x ∈ branch, HasDerivAt F (f x) x}
def Translates (p : ℝ → ℝ) := {F : ℝ → ℝ | ∃ C, ∀ x ∈ branch, F x = p x + C}

private lemma cos_ne_zero_of_mem_branch {x : ℝ} (hx : x ∈ branch) : Real.cos x ≠ 0 := by
  apply ne_of_gt
  apply Real.cos_pos_of_mem_Ioo
  simpa [branch] using hx

private lemma transformed_eq_integrand {x : ℝ} (hx : x ∈ branch) :
    transformed x = integrand x := by
  have hcos : Real.cos x ≠ 0 := cos_ne_zero_of_mem_branch hx
  have ht : HasDerivAt Real.tan (1 / Real.cos x ^ 2) x :=
    Real.hasDerivAt_tan hcos
  rw [transformed, integrand, ht.deriv, Real.tan_eq_sin_div_cos]
  field_simp [hcos] <;> ring

private lemma primitive_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (transformed x) x := by
  have hcos : Real.cos x ≠ 0 := cos_ne_zero_of_mem_branch hx
  have ht : HasDerivAt Real.tan (1 / Real.cos x ^ 2) x :=
    Real.hasDerivAt_tan hcos
  convert (ht.pow 5).const_mul (1 / 5 : ℝ) using 1 <;>
    simp [primitive, transformed] <;> ring

theorem gap1 : Family integrand = Family transformed := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
      ∀ x ∈ branch, HasDerivAt F (transformed x) x
  constructor
  · intro hF x hx
    rw [transformed_eq_integrand hx]
    exact hF x hx
  · intro hF x hx
    rw [← transformed_eq_integrand hx]
    exact hF x hx
theorem gap2 : Family transformed = Translates primitive := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (transformed x) x) ↔
      ∃ C, ∀ x ∈ branch, F x = primitive x + C
  constructor
  · intro hF
    have hdiff : DifferentiableOn ℝ (fun y => F y - primitive y) branch := by
      intro x hx
      exact
        ((hF x hx).sub (primitive_hasDerivAt x hx)).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ branch, deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      simpa using ((hF x hx).sub (primitive_hasDerivAt x hx)).deriv
    have h0 : (0 : ℝ) ∈ branch := by
      change -(Real.pi / 2) < 0 ∧ 0 < Real.pi / 2
      constructor <;> linarith [Real.pi_pos]
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have hc : F x - primitive x = F 0 - primitive 0 :=
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff hderiv hx h0
    linarith
  · rintro ⟨C, hF⟩ x hx
    have hbranch_nhds : branch ∈ nhds x := by
      exact isOpen_Ioo.mem_nhds hx
    have heq : F =ᶠ[nhds x] (fun y => primitive y + C) :=
      Filter.mem_of_superset hbranch_nhds (fun y hy => hF y hy)
    exact
      ((primitive_hasDerivAt x hx).add_const C).congr_of_eventuallyEq heq
theorem gap3 : Family integrand = Translates primitive := by
  exact gap1.trans gap2

end
end ProofGap.Exercise2006
