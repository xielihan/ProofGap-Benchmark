import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace ProofGap.Exercise1724

noncomputable section

def branch : Set ℝ := Set.Ioi (-3)
def integrand (x : ℝ) := x ^ 3 / (3 + x)
def expandedIntegrand (x : ℝ) := x ^ 2 - 3 * x + 9 - 27 / (3 + x)
def primitive (x : ℝ) :=
  (1 / 3 : ℝ) * x ^ 3 - (3 / 2 : ℝ) * x ^ 2 +
    9 * x - 27 * Real.log |3 + x|
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private theorem integrand_eq_expanded (x : ℝ) (hx : x ∈ branch) :
    integrand x = expandedIntegrand x := by
  change -3 < x at hx
  have hne : 3 + x ≠ 0 := by linarith
  unfold integrand expandedIntegrand
  field_simp [hne]
  ring

private theorem primitive_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (expandedIntegrand x) x := by
  change -3 < x at hx
  have hpos : 0 < 3 + x := by linarith
  have haff : HasDerivAt (fun y : ℝ => 3 + y) 1 x := by
    convert (hasDerivAt_const x (3 : ℝ)).add (hasDerivAt_id x) using 1 <;> ring
  have hlog : HasDerivAt (fun y : ℝ => Real.log (3 + y)) (3 + x)⁻¹ x := by
    convert (Real.hasDerivAt_log (ne_of_gt hpos)).comp x haff using 1 <;> ring
  have hcalc :
      HasDerivAt
        (fun y : ℝ =>
          (1 / 3 : ℝ) * y ^ 3 - (3 / 2 : ℝ) * y ^ 2 +
            9 * y - 27 * Real.log (3 + y))
        (expandedIntegrand x) x := by
    convert
      (((((hasDerivAt_const x (1 / 3 : ℝ)).mul ((hasDerivAt_id x).pow 3)).sub
          ((hasDerivAt_const x (3 / 2 : ℝ)).mul ((hasDerivAt_id x).pow 2))).add
          ((hasDerivAt_const x (9 : ℝ)).mul (hasDerivAt_id x))).sub
          ((hasDerivAt_const x (27 : ℝ)).mul hlog))
      using 1 <;> simp [expandedIntegrand] <;> ring
  have hprimitive :
      primitive =
        (fun y : ℝ =>
          (1 / 3 : ℝ) * y ^ 3 - (3 / 2 : ℝ) * y ^ 2 +
            9 * y - 27 * Real.log (3 + y)) := by
    funext y
    unfold primitive
    rw [Real.log_abs]
  rw [hprimitive]
  exact hcalc

private theorem antiderivatives_differ_by_constant
    {F G q : ℝ → ℝ}
    (hF : ∀ x ∈ branch, HasDerivAt F (q x) x)
    (hG : ∀ x ∈ branch, HasDerivAt G (q x) x) :
    ∃ C : ℝ, ∀ x ∈ branch, F x = G x + C := by
  have ordered : ∀ {a b : ℝ}, a ∈ branch → b ∈ branch → a < b →
      F a - G a = F b - G b := by
    intro a b ha hb hab
    change -3 < a at ha
    change -3 < b at hb
    have hcont : ContinuousOn (fun t => F t - G t) (Set.Icc a b) := by
      intro z hz
      have hzbr : z ∈ branch := by
        change -3 < z
        exact lt_of_lt_of_le ha hz.1
      exact ((hF z hzbr).sub (hG z hzbr)).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ (fun t => F t - G t) (Set.Ioo a b) := by
      intro z hz
      have hzbr : z ∈ branch := by
        change -3 < z
        exact lt_trans ha hz.1
      exact ((hF z hzbr).sub (hG z hzbr)).differentiableAt.differentiableWithinAt
    obtain ⟨z, hz, hzslope⟩ :=
      exists_deriv_eq_slope (fun t => F t - G t) hab hcont hdiff
    have hzbr : z ∈ branch := by
      change -3 < z
      exact lt_trans ha hz.1
    have hslope :
        ((F b - G b) - (F a - G a)) / (b - a) = 0 := by
      rw [← hzslope]
      simpa using ((hF z hzbr).sub (hG z hzbr)).deriv
    have hne : b - a ≠ 0 := by linarith
    field_simp [hne] at hslope
    linarith
  have hzero : (0 : ℝ) ∈ branch := by
    change (-3 : ℝ) < 0
    linarith
  refine ⟨F 0 - G 0, ?_⟩
  intro x hx
  have heq : F x - G x = F 0 - G 0 := by
    rcases lt_trichotomy x 0 with hlt | heq | hgt
    · exact ordered hx hzero hlt
    · subst x
      rfl
    · exact (ordered hzero hx hgt).symm
  linarith

theorem gap1 :
    AntiderivativesOn integrand = AntiderivativesOn expandedIntegrand := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    change ∀ x ∈ branch, HasDerivAt F (expandedIntegrand x) x
    intro x hx
    simpa [integrand_eq_expanded x hx] using hF x hx
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (expandedIntegrand x) x at hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    intro x hx
    simpa [integrand_eq_expanded x hx] using hF x hx
theorem gap2 :
    AntiderivativesOn expandedIntegrand = PrimitiveFamily primitive := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (expandedIntegrand x) x at hF
    change ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C
    exact antiderivatives_differ_by_constant hF primitive_hasDerivAt
  · intro hF
    change ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C at hF
    change ∀ x ∈ branch, HasDerivAt F (expandedIntegrand x) x
    rcases hF with ⟨C, hC⟩
    intro x hx
    have hopen : IsOpen branch := by
      simpa [branch] using (isOpen_Ioi : IsOpen (Set.Ioi (-3 : ℝ)))
    have heq : F =ᶠ[nhds x] (fun y => primitive y + C) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hC y hy
    exact ((primitive_hasDerivAt x hx).add_const C).congr_of_eventuallyEq heq
theorem gap3 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  rw [gap1, gap2]

end
end ProofGap.Exercise1724
