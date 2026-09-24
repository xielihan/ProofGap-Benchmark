import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1703

noncomputable section

def branch : Set ℝ := Set.Ioo 0 Real.pi
def halfTan (x : ℝ) := Real.tan (x / 2)
def integrand (x : ℝ) := 1 / Real.sin x
def rewrittenIntegrand (x : ℝ) :=
  (1 / (2 * (Real.cos (x / 2)) ^ 2)) / halfTan x
def substitutedIntegrand (x : ℝ) := deriv halfTan x / halfTan x
def primitive (x : ℝ) := Real.log |halfTan x|
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private theorem halfTan_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt halfTan (1 / (2 * (Real.cos (x / 2)) ^ 2)) x := by
  change 0 < x ∧ x < Real.pi at hx
  have hc : Real.cos (x / 2) ≠ 0 := by
    apply ne_of_gt
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  unfold halfTan
  convert
    (Real.hasDerivAt_tan hc).comp x
      ((hasDerivAt_id x).div_const 2) using 1 <;>
    field_simp [hc] <;> ring

theorem gap1 (x : ℝ) (hx : x ∈ branch) :
    integrand x = rewrittenIntegrand x := by
  change 0 < x ∧ x < Real.pi at hx
  have ht0 : 0 < x / 2 := by linarith
  have htpi : x / 2 < Real.pi := by linarith [Real.pi_pos]
  have hs : Real.sin (x / 2) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ht0 htpi)
  have hc : Real.cos (x / 2) ≠ 0 := by
    apply ne_of_gt
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have hsin :
      Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
    convert Real.sin_two_mul (x / 2) using 1 <;> ring
  unfold integrand rewrittenIntegrand halfTan
  rw [Real.tan_eq_sin_div_cos, hsin]
  field_simp [hs, hc] <;> ring
theorem gap2 (x : ℝ) (hx : x ∈ branch) :
    rewrittenIntegrand x = substitutedIntegrand x := by
  rw [rewrittenIntegrand, substitutedIntegrand,
    (halfTan_hasDerivAt x hx).deriv]
theorem gap3 (x : ℝ) (hx : x ∈ branch) :
    integrand x = substitutedIntegrand x := by
  exact (gap1 x hx).trans (gap2 x hx)
theorem gap4 :
    AntiderivativesOn integrand = AntiderivativesOn rewrittenIntegrand := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
      ∀ x ∈ branch, HasDerivAt F (rewrittenIntegrand x) x
  constructor
  · intro h x hx
    simpa only [gap1 x hx] using h x hx
  · intro h x hx
    simpa only [gap1 x hx] using h x hx
theorem gap5 :
    AntiderivativesOn rewrittenIntegrand =
      AntiderivativesOn substitutedIntegrand := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (rewrittenIntegrand x) x) ↔
      ∀ x ∈ branch, HasDerivAt F (substitutedIntegrand x) x
  constructor
  · intro h x hx
    simpa only [gap2 x hx] using h x hx
  · intro h x hx
    simpa only [gap2 x hx] using h x hx
theorem gap6 :
    AntiderivativesOn substitutedIntegrand = PrimitiveFamily primitive := by
  have hprimitive :
      ∀ x ∈ branch,
        HasDerivAt primitive (substitutedIntegrand x) x := by
    intro x hx
    have hxi : 0 < x ∧ x < Real.pi := hx
    have ht0 : 0 < x / 2 := by linarith
    have htpi : x / 2 < Real.pi / 2 := by linarith
    have htan : 0 < halfTan x := by
      unfold halfTan
      exact Real.tan_pos_of_pos_of_lt_pi_div_two ht0 htpi
    have hhalf := halfTan_hasDerivAt x hx
    have hhalf' :
        HasDerivAt halfTan (deriv halfTan x) x :=
      hhalf.differentiableAt.hasDerivAt
    have hlog :=
      (Real.hasDerivAt_log htan.ne').comp x hhalf'
    have hlocal :
        primitive =ᶠ[nhds x] (Real.log ∘ halfTan) := by
      filter_upwards [Ioo_mem_nhds hxi.1 hxi.2] with y hy
      have hy0 : 0 < y / 2 := by
        linarith [hy.1]
      have hypi : y / 2 < Real.pi / 2 := by
        linarith [hy.2]
      have hytan : 0 < halfTan y := by
        unfold halfTan
        exact Real.tan_pos_of_pos_of_lt_pi_div_two hy0 hypi
      simp [primitive, Function.comp_def, abs_of_pos hytan]
    simpa [substitutedIntegrand, div_eq_mul_inv, mul_comm] using
      hlog.congr_of_eventuallyEq hlocal
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (substitutedIntegrand x) x) ↔
      ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C
  constructor
  · intro hF
    have hzero :
        ∀ x ∈ branch,
          HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      convert (hF x hx).sub (hprimitive x hx) using 1 <;> simp
    have hdiff :
        DifferentiableOn ℝ (fun y => F y - primitive y) branch := by
      intro x hx
      exact (hzero x hx).differentiableAt.differentiableWithinAt
    have hderiv :
        ∀ x ∈ branch, deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      exact (hzero x hx).deriv
    have hconst :
        ∀ x ∈ branch, ∀ y ∈ branch,
          F x - primitive x = F y - primitive y := by
      intro x hx y hy
      exact isOpen_Ioo.is_const_of_deriv_eq_zero
        isPreconnected_Ioo hdiff hderiv hx hy
    have hmid : Real.pi / 2 ∈ branch := by
      change 0 < Real.pi / 2 ∧ Real.pi / 2 < Real.pi
      constructor <;> linarith [Real.pi_pos]
    refine ⟨F (Real.pi / 2) - primitive (Real.pi / 2), ?_⟩
    intro x hx
    have heq :
        F x - primitive x =
          F (Real.pi / 2) - primitive (Real.pi / 2) :=
      hconst x hx (Real.pi / 2) hmid
    linarith
  · rintro ⟨C, hC⟩ x hx
    have hxi : 0 < x ∧ x < Real.pi := hx
    have hEq :
        F =ᶠ[nhds x] (fun y => primitive y + C) := by
      filter_upwards [Ioo_mem_nhds hxi.1 hxi.2] with y hy
      exact hC y hy
    exact
      ((hprimitive x hx).add_const C).congr_of_eventuallyEq hEq
theorem gap7 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  rw [gap4, gap5, gap6]

end
end ProofGap.Exercise1703
