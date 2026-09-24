import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1791

noncomputable section

def domain : Set ℝ := Set.Ioi 0
def integrand (x : ℝ) : ℝ := Real.log x
def primitive (x : ℝ) : ℝ := x * (Real.log x - 1)
def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

theorem gap1 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt (fun y => y * Real.log y - y) (integrand x) x := by
  have hxpos : 0 < x := by
    simpa [domain] using hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  simpa [integrand, hx0] using
    ((hasDerivAt_id x).mul (Real.hasDerivAt_log hx0)).sub (hasDerivAt_id x)

theorem gap2 (x : ℝ) (hx : x ∈ domain) :
    x * Real.log x - x = primitive x := by
  unfold primitive
  ring

theorem gap3 :
    Family integrand domain = Translates primitive domain := by
  have hprimitive :
      primitive = (fun y : ℝ => y * Real.log y - y) := by
    funext y
    simp only [primitive, mul_sub, mul_one]
  ext F
  constructor
  · intro hF
    change IsAntiderivativeOn F integrand domain at hF
    change ∃ C, ∀ x ∈ domain, F x = primitive x + C
    let G : ℝ → ℝ := fun y => F y - primitive y
    have hzero : ∀ x ∈ domain, HasDerivAt G 0 x := by
      intro x hx
      have hP : HasDerivAt primitive (integrand x) x := by
        rw [hprimitive]
        exact gap1 x hx
      simpa [G] using (hF x hx).sub hP
    have hdiff : DifferentiableOn ℝ G domain := by
      intro x hx
      exact (hzero x hx).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ domain, deriv G x = 0 := by
      intro x hx
      exact (hzero x hx).deriv
    have hopen : IsOpen domain := by
      simpa only [domain] using (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))
    have hpre : IsPreconnected domain := by
      simpa only [domain] using
        (isPreconnected_Ioi : IsPreconnected (Set.Ioi (0 : ℝ)))
    have hone : (1 : ℝ) ∈ domain := by
      simp [domain]
    refine ⟨F 1 - primitive 1, ?_⟩
    intro x hx
    have hc : G x = G 1 :=
      hopen.is_const_of_deriv_eq_zero hpre hdiff hderiv hx hone
    change F x - primitive x = F 1 - primitive 1 at hc
    calc
      F x = primitive x + (F x - primitive x) := by ring
      _ = primitive x + (F 1 - primitive 1) := by rw [hc]
  · intro hF
    change ∃ C, ∀ x ∈ domain, F x = primitive x + C at hF
    rcases hF with ⟨C, hC⟩
    change IsAntiderivativeOn F integrand domain
    intro x hx
    have hP : HasDerivAt primitive (integrand x) x := by
      rw [hprimitive]
      exact gap1 x hx
    have hPC :
        HasDerivAt (fun y => primitive y + C) (integrand x) x :=
      hP.add_const C
    have hopen : IsOpen domain := by
      simpa only [domain] using (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))
    exact hPC.congr_of_eventuallyEq
      (Filter.mem_of_superset (hopen.mem_nhds hx)
        (fun y hy => hC y hy))

end

end ProofGap.Exercise1791
