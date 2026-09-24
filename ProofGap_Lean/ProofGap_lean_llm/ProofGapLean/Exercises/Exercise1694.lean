import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise1694

noncomputable section

def branch : Set ℝ := Set.Ioi (Real.exp 1)
def loglog (x : ℝ) := Real.log (Real.log x)
def integrand (x : ℝ) := 1 / (x * Real.log x * loglog x)
def firstSubstitution (x : ℝ) :=
  deriv Real.log x / (Real.log x * loglog x)
def secondSubstitution (x : ℝ) :=
  deriv loglog x / loglog x
def primitive (x : ℝ) := Real.log |loglog x|
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private theorem branch_facts {x : ℝ} (hx : x ∈ branch) :
    0 < x ∧ 1 < Real.log x ∧ 0 < loglog x := by
  have hxpos : 0 < x := (Real.exp_pos 1).trans hx
  have hlog : 1 < Real.log x := by
    simpa using Real.strictMonoOn_log (Real.exp_pos 1) hxpos hx
  have hll : 0 < loglog x := by
    simpa [loglog] using Real.log_pos hlog
  exact ⟨hxpos, hlog, hll⟩

private theorem primitive_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (secondSubstitution x) x := by
  rcases branch_facts hx with ⟨hxpos, hlog, hllpos⟩
  have hlogpos : 0 < Real.log x := zero_lt_one.trans hlog
  have hlogDeriv : HasDerivAt Real.log x⁻¹ x :=
    Real.hasDerivAt_log hxpos.ne'
  have hllDeriv :
      HasDerivAt loglog ((Real.log x)⁻¹ * x⁻¹) x := by
    simpa [loglog] using
      (Real.hasDerivAt_log hlogpos.ne').comp x hlogDeriv
  have hplain0 :
      HasDerivAt (fun y => Real.log (loglog y))
        ((loglog x)⁻¹ * ((Real.log x)⁻¹ * x⁻¹)) x :=
    (Real.hasDerivAt_log hllpos.ne').comp x hllDeriv
  have hplain :
      HasDerivAt (fun y => Real.log (loglog y))
        (secondSubstitution x) x := by
    simpa [secondSubstitution, hllDeriv.deriv, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc] using hplain0
  have hevent :
      primitive =ᶠ[nhds x] (fun y : ℝ => Real.log (loglog y)) := by
    have hpos : ∀ᶠ y in nhds x, 0 < loglog y :=
      hllDeriv.continuousAt (isOpen_Ioi.mem_nhds hllpos)
    filter_upwards [hpos] with y hy
    simp [primitive, abs_of_pos hy]
  exact hplain.congr_of_eventuallyEq hevent

theorem gap1 :
    AntiderivativesOn integrand = AntiderivativesOn firstSubstitution := by
  ext F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · intro hF x hx
    rcases branch_facts hx with ⟨hxpos, hlog, hll⟩
    have hlogpos : 0 < Real.log x := zero_lt_one.trans hlog
    have hdlog : deriv Real.log x = x⁻¹ :=
      (Real.hasDerivAt_log hxpos.ne').deriv
    have heq : integrand x = firstSubstitution x := by
      simp only [integrand, firstSubstitution]
      rw [hdlog]
      field_simp [hxpos.ne', hlogpos.ne', hll.ne']
    rw [← heq]
    exact hF x hx
  · intro hF x hx
    rcases branch_facts hx with ⟨hxpos, hlog, hll⟩
    have hlogpos : 0 < Real.log x := zero_lt_one.trans hlog
    have hdlog : deriv Real.log x = x⁻¹ :=
      (Real.hasDerivAt_log hxpos.ne').deriv
    have heq : integrand x = firstSubstitution x := by
      simp only [integrand, firstSubstitution]
      rw [hdlog]
      field_simp [hxpos.ne', hlogpos.ne', hll.ne']
    rw [heq]
    exact hF x hx
theorem gap2 :
    AntiderivativesOn firstSubstitution = AntiderivativesOn secondSubstitution := by
  ext F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · intro hF x hx
    rcases branch_facts hx with ⟨hxpos, hlog, hll⟩
    have hlogpos : 0 < Real.log x := zero_lt_one.trans hlog
    have hlogDeriv : HasDerivAt Real.log x⁻¹ x :=
      Real.hasDerivAt_log hxpos.ne'
    have hllDeriv :
        HasDerivAt loglog ((Real.log x)⁻¹ * x⁻¹) x := by
      simpa [loglog] using
        (Real.hasDerivAt_log hlogpos.ne').comp x hlogDeriv
    have hdlog : deriv Real.log x = x⁻¹ := hlogDeriv.deriv
    have hdll : deriv loglog x = (Real.log x)⁻¹ * x⁻¹ :=
      hllDeriv.deriv
    have heq : firstSubstitution x = secondSubstitution x := by
      simp only [firstSubstitution, secondSubstitution]
      rw [hdlog, hdll]
      field_simp [hxpos.ne', hlogpos.ne', hll.ne']
    rw [← heq]
    exact hF x hx
  · intro hF x hx
    rcases branch_facts hx with ⟨hxpos, hlog, hll⟩
    have hlogpos : 0 < Real.log x := zero_lt_one.trans hlog
    have hlogDeriv : HasDerivAt Real.log x⁻¹ x :=
      Real.hasDerivAt_log hxpos.ne'
    have hllDeriv :
        HasDerivAt loglog ((Real.log x)⁻¹ * x⁻¹) x := by
      simpa [loglog] using
        (Real.hasDerivAt_log hlogpos.ne').comp x hlogDeriv
    have hdlog : deriv Real.log x = x⁻¹ := hlogDeriv.deriv
    have hdll : deriv loglog x = (Real.log x)⁻¹ * x⁻¹ :=
      hllDeriv.deriv
    have heq : firstSubstitution x = secondSubstitution x := by
      simp only [firstSubstitution, secondSubstitution]
      rw [hdlog, hdll]
      field_simp [hxpos.ne', hlogpos.ne', hll.ne']
    rw [heq]
    exact hF x hx
theorem gap3 :
    AntiderivativesOn secondSubstitution = PrimitiveFamily primitive := by
  ext F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    let a : ℝ := Real.exp (1 : ℝ) + (1 : ℝ)
    have ha : a ∈ branch := by
      change Real.exp (1 : ℝ) < Real.exp (1 : ℝ) + (1 : ℝ)
      exact lt_add_of_pos_right _ (zero_lt_one : (0 : ℝ) < 1)
    let G : ℝ → ℝ := fun y => F y - primitive y
    have hG : ∀ x ∈ branch, HasDerivAt G 0 x := by
      intro x hx
      simpa [G] using
        (hF x hx).sub (primitive_hasDerivAt x hx)
    refine ⟨G a, ?_⟩
    intro x hx
    have hx' : Real.exp (1 : ℝ) < x := hx
    have ha' : Real.exp (1 : ℝ) < a := ha
    have hEq : G x = G a := by
      rcases lt_trichotomy x a with hxa | hxa | hxa
      · have hcont : ContinuousOn G (Set.Icc x a) := by
          intro y hy
          exact
            (hG y (hx'.trans_le hy.1)).continuousAt.continuousWithinAt
        have hdiff : DifferentiableOn ℝ G (Set.Ioo x a) := by
          intro y hy
          exact
            (hG y (hx'.trans hy.1)).differentiableAt.differentiableWithinAt
        obtain ⟨c, hc, hslope⟩ :=
          exists_deriv_eq_slope G hxa hcont hdiff
        have hdc : deriv G c = 0 :=
          (hG c (hx'.trans hc.1)).deriv
        have hq : (G a - G x) / (a - x) = 0 :=
          hslope.symm.trans hdc
        have hden : a - x ≠ 0 := by
          linarith
        have hnum : G a - G x = 0 :=
          (div_eq_zero_iff.mp hq).resolve_right hden
        exact (sub_eq_zero.mp hnum).symm
      · exact congrArg G hxa
      · have hcont : ContinuousOn G (Set.Icc a x) := by
          intro y hy
          exact
            (hG y (ha'.trans_le hy.1)).continuousAt.continuousWithinAt
        have hdiff : DifferentiableOn ℝ G (Set.Ioo a x) := by
          intro y hy
          exact
            (hG y (ha'.trans hy.1)).differentiableAt.differentiableWithinAt
        obtain ⟨c, hc, hslope⟩ :=
          exists_deriv_eq_slope G hxa hcont hdiff
        have hdc : deriv G c = 0 :=
          (hG c (ha'.trans hc.1)).deriv
        have hq : (G x - G a) / (x - a) = 0 :=
          hslope.symm.trans hdc
        have hden : x - a ≠ 0 := by
          linarith
        have hnum : G x - G a = 0 :=
          (div_eq_zero_iff.mp hq).resolve_right hden
        exact sub_eq_zero.mp hnum
    dsimp [G] at hEq ⊢
    linarith
  · rintro ⟨C, hFC⟩
    intro x hx
    have hp := primitive_hasDerivAt x hx
    have hsum :
        HasDerivAt (fun y => primitive y + C) (secondSubstitution x) x :=
      hp.add_const C
    have hmem : ∀ᶠ y in nhds x, y ∈ branch :=
      isOpen_Ioi.mem_nhds hx
    have heq : F =ᶠ[nhds x] (fun y => primitive y + C) := by
      filter_upwards [hmem] with y hy
      exact hFC y hy
    exact hsum.congr_of_eventuallyEq heq
theorem gap4 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  exact gap1.trans (gap2.trans gap3)

end
end ProofGap.Exercise1694
