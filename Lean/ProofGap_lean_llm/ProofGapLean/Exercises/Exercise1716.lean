import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1716

noncomputable section

def branch : Set ℝ := Set.Ioo (-1 : ℝ) 1
def substitution (x : ℝ) := Real.log ((1 + x) / (1 - x))
def integrand (x : ℝ) := substitution x / (1 - x ^ 2)
def substitutedIntegrand (x : ℝ) :=
  (1 / 2 : ℝ) * (substitution x * deriv substitution x)
def primitive (x : ℝ) := (1 / 4 : ℝ) * (substitution x) ^ 2
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private theorem hasDerivAt_substitution (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt substitution (2 / (1 - x ^ 2)) x := by
  rcases hx with ⟨hxlo, hxhi⟩
  have hplus : 1 + x ≠ 0 := ne_of_gt (by linarith)
  have hminus : 1 - x ≠ 0 := ne_of_gt (by linarith)
  have hprod : 0 < (1 + x) * (1 - x) :=
    mul_pos (by linarith) (by linarith)
  have hsq : 1 - x ^ 2 ≠ 0 := by
    apply ne_of_gt
    nlinarith
  have hnum : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    simpa using (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)
  have hden : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
  have hquot := hnum.div hden hminus
  have harg : (1 + x) / (1 - x) ≠ 0 := div_ne_zero hplus hminus
  have hlog := (Real.hasDerivAt_log harg).comp x hquot
  unfold substitution
  convert hlog using 1 <;> field_simp [hplus, hminus, hsq] <;> ring

private theorem integrand_eq_substituted (x : ℝ) (hx : x ∈ branch) :
    integrand x = substitutedIntegrand x := by
  have hs := hasDerivAt_substitution x hx
  unfold integrand substitutedIntegrand
  rw [hs.deriv]
  ring

private theorem hasDerivAt_primitive (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (substitutedIntegrand x) x := by
  have hs := hasDerivAt_substitution x hx
  have hp := (hs.pow 2).const_mul (1 / 4 : ℝ)
  convert hp using 1 <;>
    simp [primitive, substitutedIntegrand, hs.deriv] <;> ring

theorem gap1 :
    AntiderivativesOn integrand =
      AntiderivativesOn substitutedIntegrand := by
  ext F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · intro hF x hx
    rw [← integrand_eq_substituted x hx]
    exact hF x hx
  · intro hF x hx
    rw [integrand_eq_substituted x hx]
    exact hF x hx
theorem gap2 :
    AntiderivativesOn substitutedIntegrand = PrimitiveFamily primitive := by
  ext F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    have hz : ∀ x ∈ branch,
        HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      convert (hF x hx).sub (hasDerivAt_primitive x hx) using 1 <;> simp
    have hopen : IsOpen branch := by
      simpa only [branch] using
        (isOpen_Ioo : IsOpen (Set.Ioo (-1 : ℝ) 1))
    have hdiff : DifferentiableOn ℝ (fun y => F y - primitive y) branch := by
      intro x hx
      exact (hz x hx).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ branch,
        deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      exact (hz x hx).deriv
    have hpre : IsPreconnected branch := by
      simpa only [branch] using
        (isPreconnected_Ioo : IsPreconnected (Set.Ioo (-1 : ℝ) 1))
    have hzero_mem : (0 : ℝ) ∈ branch := by
      constructor <;> norm_num
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have heq : F x - primitive x = F 0 - primitive 0 :=
      hopen.is_const_of_deriv_eq_zero hpre hdiff hzero hx hzero_mem
    linarith
  · rintro ⟨C, hC⟩
    intro x hx
    have hopen : IsOpen branch := by
      simpa only [branch] using
        (isOpen_Ioo : IsOpen (Set.Ioo (-1 : ℝ) 1))
    have hevent :=
      Filter.mem_of_superset (hopen.mem_nhds hx) fun y hy => hC y hy
    exact ((hasDerivAt_primitive x hx).add_const C).congr_of_eventuallyEq hevent
theorem gap3 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  exact gap1.trans gap2

end
end ProofGap.Exercise1716
