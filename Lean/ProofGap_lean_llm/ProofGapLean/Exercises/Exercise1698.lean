import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1698

noncomputable section

def branch : Set ℝ := Set.Ioo 0 Real.pi
def cot (x : ℝ) := Real.cos x / Real.sin x
def integrand (x : ℝ) := cot x
def quotientIntegrand (x : ℝ) := Real.cos x / Real.sin x
def substitutedIntegrand (x : ℝ) := deriv Real.sin x / Real.sin x
def primitive (x : ℝ) := Real.log |Real.sin x|
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private theorem primitive_hasDerivAt {x : ℝ} (hx : x ∈ branch) :
    HasDerivAt primitive (substitutedIntegrand x) x := by
  have hsin_pos : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have hsin_ne : Real.sin x ≠ 0 := ne_of_gt hsin_pos
  have hlog : HasDerivAt (fun y => Real.log (Real.sin y))
      (Real.cos x / Real.sin x) x :=
    (Real.hasDerivAt_sin x).log hsin_ne
  have heq : primitive =ᶠ[nhds x] (fun y => Real.log (Real.sin y)) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    have hsy : 0 < Real.sin y :=
      Real.sin_pos_of_pos_of_lt_pi hy.1 hy.2
    simp [primitive, abs_of_pos hsy]
  have hp : HasDerivAt primitive (Real.cos x / Real.sin x) x :=
    hlog.congr_of_eventuallyEq heq
  simpa [substitutedIntegrand, Real.deriv_sin] using hp

theorem gap1 :
    AntiderivativesOn integrand = AntiderivativesOn quotientIntegrand := by
  rfl
theorem gap2 :
    AntiderivativesOn quotientIntegrand = AntiderivativesOn substitutedIntegrand := by
  ext F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor <;> intro h x hx
  · simpa [quotientIntegrand, substitutedIntegrand, Real.deriv_sin] using h x hx
  · simpa [quotientIntegrand, substitutedIntegrand, Real.deriv_sin] using h x hx
theorem gap3 :
    AntiderivativesOn substitutedIntegrand = PrimitiveFamily primitive := by
  ext F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    let m : ℝ := Real.pi / 2
    have hm : m ∈ branch := by
      dsimp [m, branch]
      constructor <;> linarith [Real.pi_pos]
    refine ⟨F m - primitive m, ?_⟩
    intro x hx
    have hdiff : ∀ y ∈ branch,
        HasDerivAt (fun z => F z - primitive z) 0 y := by
      intro y hy
      convert (hF y hy).sub (primitive_hasDerivAt hy) using 1 <;> simp
    have hdifferentiable :
        DifferentiableOn ℝ (fun z => F z - primitive z) branch := by
      intro y hy
      exact (hdiff y hy).differentiableAt.differentiableWithinAt
    have hderiv : ∀ y ∈ branch,
        deriv (fun z => F z - primitive z) y = 0 := by
      intro y hy
      exact (hdiff y hy).deriv
    have hopen : IsOpen branch := by
      simpa [branch] using
        (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) Real.pi))
    have hpre : IsPreconnected branch := by
      simpa [branch] using
        (isPreconnected_Ioo : IsPreconnected (Set.Ioo (0 : ℝ) Real.pi))
    have heq : F x - primitive x = F m - primitive m :=
      hopen.is_const_of_deriv_eq_zero hpre hdifferentiable hderiv hx hm
    linarith
  · rintro ⟨C, hC⟩ x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) Real.pi := by
      simpa [branch] using hx
    have hlocal : F =ᶠ[nhds x] (fun y => primitive y + C) := by
      filter_upwards [Ioo_mem_nhds hx'.1 hx'.2] with y hy
      exact hC y (by simpa [branch] using hy)
    have hsum : HasDerivAt (fun y => primitive y + C)
        (substitutedIntegrand x) x := by
      exact (primitive_hasDerivAt hx).add_const C
    exact hsum.congr_of_eventuallyEq hlocal
theorem gap4 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  calc
    AntiderivativesOn integrand = AntiderivativesOn quotientIntegrand := gap1
    _ = AntiderivativesOn substitutedIntegrand := gap2
    _ = PrimitiveFamily primitive := gap3

end
end ProofGap.Exercise1698
