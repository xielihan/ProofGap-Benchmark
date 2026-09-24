import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1713

noncomputable section

def branch : Set ℝ := Set.Ioi 0
def substitution (x : ℝ) := x + 1 / x
def integrand (x : ℝ) := (x ^ 2 - 1) / (x ^ 4 + 1)
def rewrittenIntegrand (x : ℝ) :=
  (1 - 1 / x ^ 2) / (x ^ 2 + 1 / x ^ 2)
def substitutedIntegrand (x : ℝ) :=
  deriv substitution x / ((substitution x) ^ 2 - 2)
def primitive (x : ℝ) :=
  1 / (2 * Real.sqrt 2) *
    Real.log
      |(x ^ 2 - x * Real.sqrt 2 + 1) /
        (x ^ 2 + x * Real.sqrt 2 + 1)|
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private theorem integrand_eq_rewritten_on_branch
    (x : ℝ) (hx : x ∈ branch) :
    integrand x = rewrittenIntegrand x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hden : x ^ 4 + 1 ≠ 0 := by positivity
  unfold integrand rewrittenIntegrand
  field_simp [hx0, hden]

private theorem hasDerivAt_substitution_on_branch
    (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt substitution (1 - 1 / x ^ 2) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  unfold substitution
  convert (hasDerivAt_id x).add (hasDerivAt_inv hx0) using 1
  · funext y
    simp only [Pi.add_apply, id_eq, one_div]
  · field_simp [hx0]
    ring

private theorem rewritten_eq_substituted_on_branch
    (x : ℝ) (hx : x ∈ branch) :
    rewrittenIntegrand x = substitutedIntegrand x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hdeneq :
      (x + 1 / x) ^ 2 - 2 = x ^ 2 + 1 / x ^ 2 := by
    field_simp [hx0]
    ring
  unfold rewrittenIntegrand substitutedIntegrand
  rw [(hasDerivAt_substitution_on_branch x hx).deriv]
  unfold substitution
  rw [hdeneq]

private theorem hasDerivAt_primitive_on_branch
    (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (integrand x) x := by
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  have hs_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hpositive : ∀ y : ℝ,
      0 < (y ^ 2 - y * Real.sqrt 2 + 1) /
        (y ^ 2 + y * Real.sqrt 2 + 1) := by
    intro y
    have hq₁ : y ^ 2 - y * Real.sqrt 2 + 1 > 0 := by
      nlinarith [sq_nonneg (y - Real.sqrt 2 / 2)]
    have hq₂ : y ^ 2 + y * Real.sqrt 2 + 1 > 0 := by
      nlinarith [sq_nonneg (y + Real.sqrt 2 / 2)]
    exact div_pos hq₁ hq₂
  have hq₁ : x ^ 2 - x * Real.sqrt 2 + 1 ≠ 0 :=
    ne_of_gt (by
      nlinarith [sq_nonneg (x - Real.sqrt 2 / 2)])
  have hq₂ : x ^ 2 + x * Real.sqrt 2 + 1 ≠ 0 :=
    ne_of_gt (by
      nlinarith [sq_nonneg (x + Real.sqrt 2 / 2)])
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;> norm_num [id_eq]
  have hlin : HasDerivAt (fun y : ℝ => y * Real.sqrt 2)
      (Real.sqrt 2) x := by
    convert (hasDerivAt_id x).mul_const (Real.sqrt 2) using 1 <;>
      norm_num [id_eq]
  have hnum : HasDerivAt
      (fun y : ℝ => y ^ 2 - y * Real.sqrt 2 + 1)
      (2 * x - Real.sqrt 2) x := by
    exact (hsq.sub hlin).add_const 1
  have hden : HasDerivAt
      (fun y : ℝ => y ^ 2 + y * Real.sqrt 2 + 1)
      (2 * x + Real.sqrt 2) x := by
    exact (hsq.add hlin).add_const 1
  have hcross :
      (2 * x - Real.sqrt 2) * (x ^ 2 + x * Real.sqrt 2 + 1) -
          (x ^ 2 - x * Real.sqrt 2 + 1) * (2 * x + Real.sqrt 2) =
        2 * Real.sqrt 2 * (x ^ 2 - 1) := by
    ring
  have hprod :
      (x ^ 2 - x * Real.sqrt 2 + 1) *
          (x ^ 2 + x * Real.sqrt 2 + 1) = x ^ 4 + 1 := by
    calc
      (x ^ 2 - x * Real.sqrt 2 + 1) *
          (x ^ 2 + x * Real.sqrt 2 + 1) =
          x ^ 4 + (2 - (Real.sqrt 2) ^ 2) * x ^ 2 + 1 := by ring
      _ = x ^ 4 + 1 := by rw [hs_sq]; ring
  have hscalar :
      ((((2 * x - Real.sqrt 2) *
              (x ^ 2 + x * Real.sqrt 2 + 1) -
            (x ^ 2 - x * Real.sqrt 2 + 1) *
              (2 * x + Real.sqrt 2)) /
          (x ^ 2 + x * Real.sqrt 2 + 1) ^ 2) /
        ((x ^ 2 - x * Real.sqrt 2 + 1) /
          (x ^ 2 + x * Real.sqrt 2 + 1))) =
        2 * Real.sqrt 2 * (x ^ 2 - 1) / (x ^ 4 + 1) := by
    rw [hcross]
    calc
      (2 * Real.sqrt 2 * (x ^ 2 - 1) /
            (x ^ 2 + x * Real.sqrt 2 + 1) ^ 2) /
          ((x ^ 2 - x * Real.sqrt 2 + 1) /
            (x ^ 2 + x * Real.sqrt 2 + 1)) =
          2 * Real.sqrt 2 * (x ^ 2 - 1) /
            ((x ^ 2 - x * Real.sqrt 2 + 1) *
              (x ^ 2 + x * Real.sqrt 2 + 1)) := by
        field_simp [hq₁, hq₂] <;> ring
      _ = 2 * Real.sqrt 2 * (x ^ 2 - 1) / (x ^ 4 + 1) := by
        rw [hprod]
  have hquot := hnum.div hden hq₂
  have hlograw := hquot.log (ne_of_gt (hpositive x))
  simp only [Pi.div_apply] at hlograw
  have hlog : HasDerivAt
      (fun y : ℝ => Real.log
        |(y ^ 2 - y * Real.sqrt 2 + 1) /
          (y ^ 2 + y * Real.sqrt 2 + 1)|)
      (2 * Real.sqrt 2 * (x ^ 2 - 1) / (x ^ 4 + 1)) x := by
    have habs :
        (fun y : ℝ => Real.log
          |(y ^ 2 - y * Real.sqrt 2 + 1) /
            (y ^ 2 + y * Real.sqrt 2 + 1)|) =
        (fun y : ℝ => Real.log
          ((y ^ 2 - y * Real.sqrt 2 + 1) /
            (y ^ 2 + y * Real.sqrt 2 + 1))) := by
      funext y
      rw [abs_of_pos (hpositive y)]
    rw [habs]
    convert hlograw using 1
    exact hscalar.symm
  have hp0 : HasDerivAt primitive
      ((x ^ 2 - 1) / (x ^ 4 + 1)) x := by
    unfold primitive
    convert hlog.const_mul (1 / (2 * Real.sqrt 2)) using 1
    field_simp [hs2]
  simpa only [integrand] using hp0

theorem gap1 :
    AntiderivativesOn integrand =
      AntiderivativesOn rewrittenIntegrand := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · intro h x hx
    simpa only [integrand_eq_rewritten_on_branch x hx] using h x hx
  · intro h x hx
    simpa only [integrand_eq_rewritten_on_branch x hx] using h x hx
theorem gap2 :
    AntiderivativesOn rewrittenIntegrand =
      AntiderivativesOn substitutedIntegrand := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · intro h x hx
    simpa only [rewritten_eq_substituted_on_branch x hx] using h x hx
  · intro h x hx
    simpa only [rewritten_eq_substituted_on_branch x hx] using h x hx
theorem gap3 :
    AntiderivativesOn substitutedIntegrand = PrimitiveFamily primitive := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    have hp : ∀ x ∈ branch, HasDerivAt primitive (substitutedIntegrand x) x := by
      intro x hx
      simpa only [integrand_eq_rewritten_on_branch x hx,
        rewritten_eq_substituted_on_branch x hx] using
        hasDerivAt_primitive_on_branch x hx
    have hdiff : DifferentiableOn ℝ F branch := by
      intro x hx
      exact (hF x hx).differentiableAt.differentiableWithinAt
    have hp_diff : DifferentiableOn ℝ primitive branch := by
      intro x hx
      exact (hp x hx).differentiableAt.differentiableWithinAt
    have hdiffI : DifferentiableOn ℝ (fun y => F y - primitive y)
        (Set.Ioi (0 : ℝ)) := by
      simpa [branch] using hdiff.sub hp_diff
    have hzeroI : ∀ x ∈ Set.Ioi (0 : ℝ),
        deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      have hx' : x ∈ branch := by simpa [branch] using hx
      simpa using ((hF x hx').sub (hp x hx')).deriv
    refine ⟨F 1 - primitive 1, ?_⟩
    intro x hx
    have hx' : x ∈ Set.Ioi (0 : ℝ) := by simpa [branch] using hx
    have h1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
    have heq : F x - primitive x = F 1 - primitive 1 :=
      isOpen_Ioi.is_const_of_deriv_eq_zero
        (isPreconnected_Ioi : IsPreconnected (Set.Ioi (0 : ℝ)))
        hdiffI hzeroI hx' h1
    linarith
  · rintro ⟨C, hF⟩ x hx
    have hp : HasDerivAt primitive (substitutedIntegrand x) x := by
      simpa only [integrand_eq_rewritten_on_branch x hx,
        rewritten_eq_substituted_on_branch x hx] using
        hasDerivAt_primitive_on_branch x hx
    have hx' : x ∈ Set.Ioi (0 : ℝ) := by simpa [branch] using hx
    have hbranch : branch ∈ nhds x := by
      simpa [branch] using isOpen_Ioi.mem_nhds hx'
    have heq : F =ᶠ[nhds x] fun y => C + primitive y := by
      filter_upwards [hbranch] with y hy
      rw [hF y hy, add_comm]
    exact (hp.const_add C).congr_of_eventuallyEq heq
theorem gap4 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  rw [gap1, gap2, gap3]

end
end ProofGap.Exercise1713
