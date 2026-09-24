import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1655

noncomputable section

def domain (a : ℝ) : Set ℝ := Set.Ioi (-a)
def integrand (a x : ℝ) : ℝ := 1 / (x + a)
def primitive (a x : ℝ) : ℝ := Real.log |x + a|
def AntiderivativesOn (a : ℝ) (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F (domain a) ∧
    ∀ x ∈ domain a, deriv F x = g x}
def PrimitiveFamily (a : ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain a, F x = p x + C}

theorem gap1 (a : ℝ) :
    AntiderivativesOn a (integrand a) = PrimitiveFamily a (primitive a) := by
  have hopen : IsOpen (domain a) := by
    simpa [domain] using (isOpen_Ioi : IsOpen (Set.Ioi (-a)))
  have hpre : IsPreconnected (domain a) := by
    rw [domain]
    exact isPreconnected_Ioi
  have hp : ∀ x ∈ domain a,
      HasDerivAt (primitive a) (integrand a x) x := by
    intro x hx
    have hpos : 0 < x + a := by
      change -a < x at hx
      linarith
    have hne : x + a ≠ 0 := ne_of_gt hpos
    have hlin : HasDerivAt (fun y : ℝ => y + a) 1 x :=
      (hasDerivAt_id x).add_const a
    have hlog :
        HasDerivAt (fun y : ℝ => Real.log (y + a)) (integrand a x) x := by
      simpa [integrand, one_div, Function.comp_def] using
        (Real.hasDerivAt_log hne).comp x hlin
    have hlocal :
        primitive a =ᶠ[nhds x] (fun y : ℝ => Real.log (y + a)) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      have hypos : 0 < y + a := by
        change -a < y at hy
        linarith
      simp [primitive, abs_of_pos hypos]
    exact hlog.congr_of_eventuallyEq hlocal
  apply Set.ext
  intro F
  constructor
  · intro hF
    change DifferentiableOn ℝ F (domain a) ∧
      (∀ x ∈ domain a, deriv F x = integrand a x) at hF
    change ∃ C : ℝ, ∀ x ∈ domain a, F x = primitive a x + C
    let H : ℝ → ℝ := fun x => F x - primitive a x
    have hpDiff : DifferentiableOn ℝ (primitive a) (domain a) := by
      intro x hx
      exact (hp x hx).differentiableAt.differentiableWithinAt
    have hHdiff : DifferentiableOn ℝ H (domain a) := by
      dsimp [H]
      exact hF.1.sub hpDiff
    have hHderiv : ∀ x ∈ domain a, deriv H x = 0 := by
      intro x hx
      have hFd : DifferentiableAt ℝ F x :=
        (hF.1 x hx).differentiableAt (hopen.mem_nhds hx)
      have hs : HasDerivAt H (deriv F x - integrand a x) x := by
        dsimp [H]
        exact hFd.hasDerivAt.sub (hp x hx)
      calc
        deriv H x = deriv F x - integrand a x := hs.deriv
        _ = 0 := sub_eq_zero.mpr (hF.2 x hx)
    let b : ℝ := -a + 1
    have hb : b ∈ domain a := by
      change -a < b
      dsimp [b]
      linarith
    refine ⟨H b, ?_⟩
    intro x hx
    have heq : H x = H b :=
      hopen.is_const_of_deriv_eq_zero hpre hHdiff hHderiv hx hb
    dsimp [H] at heq ⊢
    linarith
  · intro hF
    change ∃ C : ℝ, ∀ x ∈ domain a, F x = primitive a x + C at hF
    change DifferentiableOn ℝ F (domain a) ∧
      (∀ x ∈ domain a, deriv F x = integrand a x)
    rcases hF with ⟨C, hC⟩
    have hHas : ∀ x ∈ domain a, HasDerivAt F (integrand a x) x := by
      intro x hx
      have hlocal : F =ᶠ[nhds x] (fun y => primitive a y + C) := by
        filter_upwards [hopen.mem_nhds hx] with y hy
        exact hC y hy
      exact ((hp x hx).add_const C).congr_of_eventuallyEq hlocal
    constructor
    · intro x hx
      exact (hHas x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hHas x hx).deriv

end
end ProofGap.Exercise1655
