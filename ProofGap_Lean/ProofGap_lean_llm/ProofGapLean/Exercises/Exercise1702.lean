import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Neighborhoods
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1702

noncomputable section

def branch : Set ℝ := Set.Ioo (-Real.pi / 2) (Real.pi / 2)
def integrand (x : ℝ) :=
  1 / ((Real.sin x) ^ 2 + 2 * (Real.cos x) ^ 2)
def rewrittenIntegrand (x : ℝ) :=
  (1 / (Real.cos x) ^ 2) / ((Real.tan x) ^ 2 + 2)
def substitutedIntegrand (x : ℝ) :=
  deriv Real.tan x / ((Real.sqrt 2) ^ 2 + (Real.tan x) ^ 2)
def primitive (x : ℝ) :=
  1 / Real.sqrt 2 * Real.arctan (Real.tan x / Real.sqrt 2)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private theorem hasDerivAt_primitive (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (substitutedIntegrand x) x := by
  have hmem : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · calc
        -(Real.pi / 2) = -Real.pi / 2 := by ring
        _ < x := hx.1
    · exact hx.2
  have hcos_pos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo hmem
  have hcos : Real.cos x ≠ 0 := ne_of_gt hcos_pos
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt_pos
  have hsum : 1 + (Real.tan x / Real.sqrt 2) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (Real.tan x / Real.sqrt 2)]
  have hden : (Real.sqrt 2) ^ 2 + (Real.tan x) ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_pos hsqrt_pos, sq_nonneg (Real.tan x)]
  have hscaled :
      HasDerivAt
        (fun y => 1 / Real.sqrt 2 *
          Real.arctan (Real.tan y / Real.sqrt 2))
        (1 / Real.sqrt 2 *
          ((1 / (1 + (Real.tan x / Real.sqrt 2) ^ 2)) *
            ((1 / (Real.cos x) ^ 2) / Real.sqrt 2))) x := by
    exact
      ((Real.hasDerivAt_arctan (Real.tan x / Real.sqrt 2)).comp x
        ((Real.hasDerivAt_tan hcos).div_const (Real.sqrt 2))).const_mul
          (1 / Real.sqrt 2)
  have hcoef :
      1 / Real.sqrt 2 *
          ((1 / (1 + (Real.tan x / Real.sqrt 2) ^ 2)) *
            ((1 / (Real.cos x) ^ 2) / Real.sqrt 2)) =
        substitutedIntegrand x := by
    unfold substitutedIntegrand
    rw [(Real.hasDerivAt_tan hcos).deriv]
    field_simp [hsqrt, hcos, hsum, hden]
    <;> ring
  simpa only [primitive, hcoef] using hscaled

theorem gap1 (x : ℝ) (hx : x ∈ branch) :
    integrand x = rewrittenIntegrand x := by
  have hmem : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · calc
        -(Real.pi / 2) = -Real.pi / 2 := by ring
        _ < x := hx.1
    · exact hx.2
  have hcos_pos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo hmem
  have hcos : Real.cos x ≠ 0 := ne_of_gt hcos_pos
  have hcos_sq : 0 < (Real.cos x) ^ 2 := sq_pos_of_pos hcos_pos
  have hden₁ : (Real.sin x) ^ 2 + 2 * (Real.cos x) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (Real.sin x)]
  have hden₂ : (Real.tan x) ^ 2 + 2 ≠ 0 := by
    nlinarith [sq_nonneg (Real.tan x)]
  unfold integrand rewrittenIntegrand
  rw [Real.tan_eq_sin_div_cos] at hden₂ ⊢
  field_simp [hcos, hden₁, hden₂]
  <;> ring
theorem gap2 (x : ℝ) (hx : x ∈ branch) :
    rewrittenIntegrand x = substitutedIntegrand x := by
  have hmem : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · calc
        -(Real.pi / 2) = -Real.pi / 2 := by ring
        _ < x := hx.1
    · exact hx.2
  have hcos_pos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo hmem
  have hcos : Real.cos x ≠ 0 := ne_of_gt hcos_pos
  have hderiv : deriv Real.tan x = 1 / (Real.cos x) ^ 2 :=
    (Real.hasDerivAt_tan hcos).deriv
  unfold rewrittenIntegrand substitutedIntegrand
  rw [hderiv, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring
theorem gap3 (x : ℝ) (hx : x ∈ branch) :
    integrand x = substitutedIntegrand x := by
  exact (gap1 x hx).trans (gap2 x hx)
theorem gap4 :
    AntiderivativesOn integrand = AntiderivativesOn rewrittenIntegrand := by
  apply Set.ext
  intro F
  change (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
    (∀ x ∈ branch, HasDerivAt F (rewrittenIntegrand x) x)
  constructor
  · intro hF x hx
    rw [← gap1 x hx]
    exact hF x hx
  · intro hF x hx
    rw [gap1 x hx]
    exact hF x hx
theorem gap5 :
    AntiderivativesOn rewrittenIntegrand =
      AntiderivativesOn substitutedIntegrand := by
  apply Set.ext
  intro F
  change (∀ x ∈ branch, HasDerivAt F (rewrittenIntegrand x) x) ↔
    (∀ x ∈ branch, HasDerivAt F (substitutedIntegrand x) x)
  constructor
  · intro hF x hx
    rw [← gap2 x hx]
    exact hF x hx
  · intro hF x hx
    rw [gap2 x hx]
    exact hF x hx
theorem gap6 :
    AntiderivativesOn substitutedIntegrand = PrimitiveFamily primitive := by
  apply Set.ext
  intro F
  change (∀ x ∈ branch, HasDerivAt F (substitutedIntegrand x) x) ↔
    (∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C)
  constructor
  · intro hF
    let g : ℝ → ℝ := fun y => F y - primitive y
    have hzero : ∀ x ∈ branch, HasDerivAt g 0 x := by
      intro x hx
      dsimp [g]
      convert (hF x hx).sub (hasDerivAt_primitive x hx) using 1
      ring
    have hdiff : DifferentiableOn ℝ g branch := by
      intro x hx
      exact (hzero x hx).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ branch, deriv g x = 0 := by
      intro x hx
      exact (hzero x hx).deriv
    have hdiff' : DifferentiableOn ℝ g (Set.Ioo (-Real.pi / 2) (Real.pi / 2)) := by
      simpa only [branch] using hdiff
    have hderiv' : ∀ x ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2), deriv g x = 0 := by
      simpa only [branch] using hderiv
    have hconnected : IsPreconnected (Set.Ioo (-Real.pi / 2) (Real.pi / 2)) :=
      (convex_Ioo (-Real.pi / 2) (Real.pi / 2)).isPreconnected
    have hzero_mem : (0 : ℝ) ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2) := by
      constructor <;> nlinarith [Real.pi_pos]
    refine ⟨g 0, ?_⟩
    intro x hx
    have hx' : x ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2) := by
      simpa only [branch] using hx
    have heq : g x = g 0 :=
      isOpen_Ioo.is_const_of_deriv_eq_zero hconnected hdiff' hderiv' hx' hzero_mem
    dsimp [g] at heq ⊢
    linarith
  · rintro ⟨C, hC⟩ x hx
    have hopen : IsOpen branch := by
      simpa [branch] using isOpen_Ioo
    have hevent : Filter.EventuallyEq (nhds x) F (fun y => primitive y + C) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hC y hy
    have hpC : HasDerivAt (fun y => primitive y + C) (substitutedIntegrand x) x := by
      simpa [add_comm] using (hasDerivAt_primitive x hx).const_add C
    exact hpC.congr_of_eventuallyEq hevent
theorem gap7 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  calc
    AntiderivativesOn integrand = AntiderivativesOn rewrittenIntegrand := gap4
    _ = AntiderivativesOn substitutedIntegrand := gap5
    _ = PrimitiveFamily primitive := gap6

end
end ProofGap.Exercise1702
