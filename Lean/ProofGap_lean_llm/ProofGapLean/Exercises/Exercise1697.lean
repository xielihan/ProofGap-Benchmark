import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1697

noncomputable section

def branch : Set ℝ := Set.Ioo (-Real.pi / 2) (Real.pi / 2)
def integrand (x : ℝ) := Real.tan x
def quotientIntegrand (x : ℝ) := Real.sin x / Real.cos x
def substitutedIntegrand (x : ℝ) :=
  -(deriv Real.cos x / Real.cos x)
def primitive (x : ℝ) := -Real.log |Real.cos x|
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private lemma primitive_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (substitutedIntegrand x) x := by
  have hx' : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · linarith [hx.1]
    · exact hx.2
  have hcos : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo hx'
  have hbase :
      HasDerivAt (fun y : ℝ => -Real.log (Real.cos y))
        (Real.sin x / Real.cos x) x := by
    convert ((Real.hasDerivAt_log hcos.ne').comp x
      (Real.hasDerivAt_cos x)).neg using 1 <;> ring
  have hopen : IsOpen {y : ℝ | 0 < Real.cos y} :=
    isOpen_lt continuous_const Real.continuous_cos
  have hevent :
      primitive =ᶠ[nhds x] (fun y : ℝ => -Real.log (Real.cos y)) := by
    apply Filter.Eventually.mono (hopen.mem_nhds hcos)
    intro y hy
    simp [primitive, abs_of_pos hy]
  have hsub : substitutedIntegrand x = Real.sin x / Real.cos x := by
    unfold substitutedIntegrand
    rw [(Real.hasDerivAt_cos x).deriv]
    ring
  rw [hsub]
  exact hbase.congr_of_eventuallyEq hevent

theorem gap1 :
    AntiderivativesOn integrand = AntiderivativesOn quotientIntegrand := by
  have h : integrand = quotientIntegrand := by
    funext x
    change Real.tan x = Real.sin x / Real.cos x
    exact Real.tan_eq_sin_div_cos x
  rw [h]
theorem gap2 :
    AntiderivativesOn quotientIntegrand = AntiderivativesOn substitutedIntegrand := by
  have h : quotientIntegrand = substitutedIntegrand := by
    funext x
    unfold quotientIntegrand substitutedIntegrand
    rw [(Real.hasDerivAt_cos x).deriv]
    ring
  rw [h]
theorem gap3 :
    AntiderivativesOn substitutedIntegrand = PrimitiveFamily primitive := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (substitutedIntegrand x) x) ↔
      (∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C)
  constructor
  · intro hF
    have hderiv : ∀ x ∈ branch,
        HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      simpa using (hF x hx).sub (primitive_hasDerivAt x hx)
    have hdiff : DifferentiableOn ℝ (fun y => F y - primitive y) branch := by
      intro x hx
      exact (hderiv x hx).differentiableAt.differentiableWithinAt
    have hderiv_eq : ∀ x ∈ branch,
        deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      exact (hderiv x hx).deriv
    have hopen : IsOpen branch := by
      simpa only [branch] using
        (isOpen_Ioo : IsOpen (Set.Ioo (-Real.pi / 2) (Real.pi / 2)))
    have hconn : IsPreconnected branch := by
      rw [branch]
      exact (convex_Ioo (-Real.pi / 2) (Real.pi / 2)).isPreconnected
    have hzero : (0 : ℝ) ∈ branch := by
      change -Real.pi / 2 < (0 : ℝ) ∧ (0 : ℝ) < Real.pi / 2
      constructor <;> linarith [Real.pi_pos]
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have heq : F x - primitive x = F 0 - primitive 0 :=
      hopen.is_const_of_deriv_eq_zero hconn hdiff hderiv_eq hx hzero
    linarith
  · rintro ⟨C, hC⟩
    intro x hx
    have hopen : IsOpen branch := by
      simpa only [branch] using
        (isOpen_Ioo : IsOpen (Set.Ioo (-Real.pi / 2) (Real.pi / 2)))
    have hevent :
        F =ᶠ[nhds x] (fun y => primitive y + C) := by
      apply Filter.Eventually.mono (hopen.mem_nhds hx)
      intro y hy
      exact hC y hy
    exact ((primitive_hasDerivAt x hx).add_const C).congr_of_eventuallyEq hevent
theorem gap4 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  calc
    AntiderivativesOn integrand = AntiderivativesOn quotientIntegrand := gap1
    _ = AntiderivativesOn substitutedIntegrand := gap2
    _ = PrimitiveFamily primitive := gap3

end
end ProofGap.Exercise1697
