import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Ring
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1693

noncomputable section

def branch : Set ℝ := Set.Ioi 0
def integrand (x : ℝ) := (Real.log x) ^ 2 / x
def substitutedIntegrand (x : ℝ) :=
  (Real.log x) ^ 2 * deriv Real.log x
def primitive (x : ℝ) := (1 / 3 : ℝ) * (Real.log x) ^ 3
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private theorem primitive_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (substitutedIntegrand x) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hlog := Real.hasDerivAt_log hx0
  unfold primitive substitutedIntegrand
  convert (hlog.pow 3).const_mul (1 / 3 : ℝ) using 1
  rw [hlog.deriv]
  ring

theorem gap1 :
    AntiderivativesOn integrand = AntiderivativesOn substitutedIntegrand := by
  apply Set.ext
  intro F
  constructor
  · intro h x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hlog := Real.hasDerivAt_log hx0
    simpa [integrand, substitutedIntegrand, div_eq_mul_inv, hlog.deriv] using h x hx
  · intro h x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hlog := Real.hasDerivAt_log hx0
    simpa [integrand, substitutedIntegrand, div_eq_mul_inv, hlog.deriv] using h x hx
theorem gap2 :
    AntiderivativesOn substitutedIntegrand = PrimitiveFamily primitive := by
  apply Set.Subset.antisymm
  · intro F hF
    have hg : ∀ x ∈ branch,
        HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      simpa using (hF x hx).sub (primitive_hasDerivAt x hx)
    have hdiff : DifferentiableOn ℝ (fun y => F y - primitive y) branch := by
      intro x hx
      exact (hg x hx).differentiableAt.differentiableWithinAt
    have hpre : IsPreconnected branch := by
      simpa [branch] using isPreconnected_Ioi
    have hzero : ∀ x ∈ branch,
        deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      exact (hg x hx).deriv
    have h1 : (1 : ℝ) ∈ branch := by
      simpa [branch] using (zero_lt_one : (0 : ℝ) < 1)
    have hconst : ∀ x ∈ branch,
        F x - primitive x = F 1 - primitive 1 := by
      intro x hx
      exact (show IsOpen branch from isOpen_Ioi).is_const_of_deriv_eq_zero
        hpre hdiff hzero hx h1
    refine ⟨F 1 - primitive 1, ?_⟩
    intro x hx
    have h := hconst x hx
    calc
      F x = (F 1 - primitive 1) + primitive x := (sub_eq_iff_eq_add).mp h
      _ = primitive x + (F 1 - primitive 1) := add_comm _ _
  · intro F hF
    rcases hF with ⟨C, hC⟩
    intro x hx
    have hbranch : branch ∈ nhds x := by
      exact (show IsOpen branch from isOpen_Ioi).mem_nhds hx
    have heq : F =ᶠ[nhds x] (fun y => primitive y + C) := by
      filter_upwards [hbranch] with y hy
      exact hC y hy
    exact ((primitive_hasDerivAt x hx).add_const C).congr_of_eventuallyEq heq
theorem gap3 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  exact gap1.trans gap2

end
end ProofGap.Exercise1693
