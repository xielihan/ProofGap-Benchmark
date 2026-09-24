import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2160

noncomputable section

def branch : Set ℝ := Set.Ioi 0
def realSelfPower (x : ℝ) := Real.rpow x x
def expForm (x : ℝ) := Real.exp (x * Real.log x)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}
def integrand (x : ℝ) := realSelfPower x * (1 + Real.log x)
def expIntegrand (x : ℝ) := expForm x * (1 + Real.log x)
def chainIntegrand (x : ℝ) :=
  expForm x * deriv (fun y : ℝ => y * Real.log y) x

private lemma selfPower_eq_expForm {x : ℝ} (hx : x ∈ branch) :
    realSelfPower x = expForm x := by
  change 0 < x at hx
  unfold realSelfPower expForm
  have hr : Real.rpow x x = Real.exp (Real.log x * x) := by
    exact (Real.rpow_def_of_pos hx) x
  simpa only [mul_comm] using hr

private lemma hasDerivAt_mul_log {x : ℝ} (hx : x ∈ branch) :
    HasDerivAt (fun y : ℝ => y * Real.log y) (1 + Real.log x) x := by
  change 0 < x at hx
  simpa [hx.ne', add_comm] using
    (hasDerivAt_id x).mul (Real.hasDerivAt_log hx.ne')

private lemma hasDerivAt_expForm {x : ℝ} (hx : x ∈ branch) :
    HasDerivAt expForm (chainIntegrand x) x := by
  have hinner := hasDerivAt_mul_log hx
  simpa only [expForm, chainIntegrand, hinner.deriv] using
    (Real.hasDerivAt_exp (x * Real.log x)).comp x hinner

theorem gap1 :
    AntiderivativesOn integrand =
      AntiderivativesOn expIntegrand := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · intro h x hx
    simpa only [integrand, expIntegrand, selfPower_eq_expForm hx] using h x hx
  · intro h x hx
    simpa only [integrand, expIntegrand, selfPower_eq_expForm hx] using h x hx
theorem gap2 :
    AntiderivativesOn expIntegrand =
      AntiderivativesOn chainIntegrand := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · intro h x hx
    have hd := hasDerivAt_mul_log hx
    simpa only [expIntegrand, chainIntegrand, hd.deriv] using h x hx
  · intro h x hx
    have hd := hasDerivAt_mul_log hx
    simpa only [expIntegrand, chainIntegrand, hd.deriv] using h x hx
theorem gap3 :
    AntiderivativesOn chainIntegrand = PrimitiveFamily expForm := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    let g : ℝ → ℝ := fun y => F y - expForm y
    have hg : ∀ x ∈ branch, HasDerivAt g 0 x := by
      intro x hx
      simpa only [g, sub_self] using
        (hF x hx).sub (hasDerivAt_expForm hx)
    have hdiff : DifferentiableOn ℝ g branch := by
      intro x hx
      exact (hg x hx).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ branch, deriv g x = 0 := by
      intro x hx
      exact (hg x hx).deriv
    refine ⟨g 1, ?_⟩
    intro x hx
    have hone : (1 : ℝ) ∈ branch := by
      change (0 : ℝ) < 1
      exact zero_lt_one
    have hconst : g x = g 1 := by
      apply isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi hdiff hderiv
      · exact hx
      · exact hone
    change F x - expForm x = F 1 - expForm 1 at hconst
    simpa only [g, add_comm] using (sub_eq_iff_eq_add.mp hconst)
  · rintro ⟨C, hF⟩
    intro x hx
    have hp :
        HasDerivAt (fun y => expForm y + C) (chainIntegrand x) x :=
      (hasDerivAt_expForm hx).add_const C
    have hFw : HasDerivWithinAt F (chainIntegrand x) branch x :=
      hp.hasDerivWithinAt.congr
        (fun y hy => hF y hy)
        (hF x hx)
    exact hFw.hasDerivAt (isOpen_Ioi.mem_nhds hx)
theorem gap4 :
    PrimitiveFamily expForm = PrimitiveFamily realSelfPower := by
  apply Set.ext
  intro F
  simp only [PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x hx
    simpa only [selfPower_eq_expForm hx] using hF x hx
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x hx
    simpa only [selfPower_eq_expForm hx] using hF x hx
theorem gap5 :
    AntiderivativesOn integrand = PrimitiveFamily realSelfPower := by
  calc
    AntiderivativesOn integrand = AntiderivativesOn expIntegrand := gap1
    _ = AntiderivativesOn chainIntegrand := gap2
    _ = PrimitiveFamily expForm := gap3
    _ = PrimitiveFamily realSelfPower := gap4

end
end ProofGap.Exercise2160
