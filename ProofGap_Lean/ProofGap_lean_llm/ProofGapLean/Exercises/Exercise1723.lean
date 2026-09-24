import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1723

noncomputable section

def branch : Set ℝ := Set.Ioi (-1)
def integrand (x : ℝ) := x ^ 2 / (1 + x)
def expandedIntegrand (x : ℝ) := x - 1 + 1 / (1 + x)
def primitive (x : ℝ) := (1 / 2 : ℝ) * x ^ 2 - x + Real.log |1 + x|
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private theorem primitiveDerivative (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (expandedIntegrand x) x := by
  have hx' : -1 < x := by simpa [branch] using hx
  have hne : 1 + x ≠ 0 := by linarith
  have hquad :
      HasDerivAt (fun y : ℝ => (1 / 2 : ℝ) * y ^ 2 - y) (x - 1) x := by
    convert ((((hasDerivAt_id x).pow 2).const_mul (1 / 2 : ℝ)).sub
      (hasDerivAt_id x)) using 1 <;> simp [id] <;> ring
  have hinner : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    simpa using (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)
  have hlog :
      HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + x)) x := by
    simpa [one_div] using (Real.hasDerivAt_log hne).comp x hinner
  have hsum :
      HasDerivAt
        (fun y : ℝ => ((1 / 2 : ℝ) * y ^ 2 - y) + Real.log (1 + y))
        (x - 1 + 1 / (1 + x)) x := by
    simpa only [Pi.add_apply] using hquad.add hlog
  have hopen : IsOpen branch := by
    simpa [branch] using (isOpen_Ioi : IsOpen (Set.Ioi (-1 : ℝ)))
  have hevent :
      (fun y : ℝ => ((1 / 2 : ℝ) * y ^ 2 - y) + Real.log (1 + y)) =ᶠ[nhds x]
        primitive := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    have hy' : 0 < 1 + y := by
      have : -1 < y := by simpa [branch] using hy
      linarith
    simp [primitive, abs_of_pos hy']
  exact hsum.congr_of_eventuallyEq hevent.symm

private theorem constantFromZeroDerivative
    (g : ℝ → ℝ) (hg : ∀ x ∈ branch, HasDerivAt g 0 x) :
    ∀ x ∈ branch, g x = g 0 := by
  intro x hx
  have hx' : -1 < x := by simpa [branch] using hx
  rcases lt_trichotomy x 0 with hlt | heq | hgt
  · have hseg : Set.Icc x 0 ⊆ branch := by
      intro y hy
      simpa [branch] using lt_of_lt_of_le hx' hy.1
    have hcont : ContinuousOn g (Set.Icc x 0) := by
      intro y hy
      exact (hg y (hseg hy)).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ g (Set.Ioo x 0) := by
      intro y hy
      have hy' : y ∈ Set.Icc x 0 := ⟨le_of_lt hy.1, le_of_lt hy.2⟩
      exact (hg y (hseg hy')).differentiableAt.differentiableWithinAt
    obtain ⟨c, hc, hcder⟩ :=
      exists_deriv_eq_slope (f := g) hlt hcont hdiff
    have hc' : c ∈ Set.Icc x 0 := ⟨le_of_lt hc.1, le_of_lt hc.2⟩
    have hz : deriv g c = 0 := (hg c (hseg hc')).deriv
    rw [hz] at hcder
    have hden : (0 : ℝ) - x ≠ 0 := by linarith
    field_simp [hden] at hcder
    linarith
  · subst x
    rfl
  · have hseg : Set.Icc 0 x ⊆ branch := by
      intro y hy
      have : (-1 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy.1
      simpa [branch] using this
    have hcont : ContinuousOn g (Set.Icc 0 x) := by
      intro y hy
      exact (hg y (hseg hy)).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ g (Set.Ioo 0 x) := by
      intro y hy
      have hy' : y ∈ Set.Icc 0 x := ⟨le_of_lt hy.1, le_of_lt hy.2⟩
      exact (hg y (hseg hy')).differentiableAt.differentiableWithinAt
    obtain ⟨c, hc, hcder⟩ :=
      exists_deriv_eq_slope (f := g) hgt hcont hdiff
    have hc' : c ∈ Set.Icc 0 x := ⟨le_of_lt hc.1, le_of_lt hc.2⟩
    have hz : deriv g c = 0 := (hg c (hseg hc')).deriv
    rw [hz] at hcder
    have hden : x - (0 : ℝ) ≠ 0 := by linarith
    field_simp [hden] at hcder
    linarith

theorem gap1 :
    AntiderivativesOn integrand = AntiderivativesOn expandedIntegrand := by
  apply Set.ext
  intro F
  change
    (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
      ∀ x ∈ branch, HasDerivAt F (expandedIntegrand x) x
  constructor
  · intro hF x hx
    have hx' : -1 < x := by simpa [branch] using hx
    have hne : 1 + x ≠ 0 := by linarith
    have heq : integrand x = expandedIntegrand x := by
      unfold integrand expandedIntegrand
      field_simp [hne]
      <;> ring
    simpa [heq] using hF x hx
  · intro hF x hx
    have hx' : -1 < x := by simpa [branch] using hx
    have hne : 1 + x ≠ 0 := by linarith
    have heq : integrand x = expandedIntegrand x := by
      unfold integrand expandedIntegrand
      field_simp [hne]
      <;> ring
    simpa [heq] using hF x hx
theorem gap2 :
    AntiderivativesOn expandedIntegrand = PrimitiveFamily primitive := by
  apply Set.ext
  intro F
  change
    (∀ x ∈ branch, HasDerivAt F (expandedIntegrand x) x) ↔
      ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C
  constructor
  · intro hF
    have hzero : ∀ x ∈ branch,
        HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      simpa using (hF x hx).sub (primitiveDerivative x hx)
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have hconst := constantFromZeroDerivative
      (fun y => F y - primitive y) hzero x hx
    linarith
  · rintro ⟨C, hC⟩
    intro x hx
    have hopen : IsOpen branch := by
      simpa [branch] using (isOpen_Ioi : IsOpen (Set.Ioi (-1 : ℝ)))
    have hevent : F =ᶠ[nhds x] fun y => primitive y + C := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hC y hy
    exact ((primitiveDerivative x hx).add_const C).congr_of_eventuallyEq hevent
theorem gap3 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  calc
    AntiderivativesOn integrand = AntiderivativesOn expandedIntegrand := gap1
    _ = PrimitiveFamily primitive := gap2

end
end ProofGap.Exercise1723
