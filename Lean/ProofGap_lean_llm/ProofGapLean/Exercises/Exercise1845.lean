import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1845

noncomputable section

def branch : Set ℝ := Set.Ioo (-Real.pi) Real.pi
def integrand (x : ℝ) :=
  1 / (Real.sin x + 2 * Real.cos x + 3)
def transformedIntegrand (x : ℝ) :=
  (1 / (Real.cos (x / 2)) ^ 2) /
    (2 * Real.tan (x / 2) + 4 +
      (1 / Real.cos (x / 2)) ^ 2)
def tangentIntegrand (x : ℝ) :=
  deriv (fun t : ℝ => Real.tan (t / 2)) x /
    ((Real.tan (x / 2) + 1) ^ 2 + 4)
def primitive (x : ℝ) :=
  Real.arctan ((Real.tan (x / 2) + 1) / 2)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def TwiceFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn tangentIntegrand,
    ∀ x ∈ branch, F x = 2 * G x}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C}

private theorem half_mem_cos_positive (x : ℝ) (hx : x ∈ branch) :
    0 < Real.cos (x / 2) := by
  apply Real.cos_pos_of_mem_Ioo
  unfold branch at hx
  constructor <;> nlinarith [hx.1, hx.2]

private theorem secant_sq_eq_tan_sq_add_one (x : ℝ) (hx : x ∈ branch) :
    (1 / Real.cos (x / 2)) ^ 2 = Real.tan (x / 2) ^ 2 + 1 := by
  have hc := half_mem_cos_positive x hx
  rw [Real.tan_eq_sin_div_cos]
  field_simp [ne_of_gt hc]
  nlinarith [Real.sin_sq_add_cos_sq (x / 2)]

private theorem transformed_denominator_eq (x : ℝ) (hx : x ∈ branch) :
    2 * Real.tan (x / 2) + 4 + (1 / Real.cos (x / 2)) ^ 2 =
      (Real.tan (x / 2) + 1) ^ 2 + 4 := by
  rw [secant_sq_eq_tan_sq_add_one x hx]
  ring

private theorem original_denominator_factorization (x : ℝ) (hx : x ∈ branch) :
    Real.sin x + 2 * Real.cos x + 3 =
      (2 * Real.tan (x / 2) + 4 + (1 / Real.cos (x / 2)) ^ 2) *
        Real.cos (x / 2) ^ 2 := by
  have hc := half_mem_cos_positive x hx
  have hhalf : x / 2 + x / 2 = x := by ring
  have hsin :
      Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
    calc
      Real.sin x = Real.sin (x / 2 + x / 2) := by rw [hhalf]
      _ = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
        rw [Real.sin_add]
        ring
  have hcos :
      Real.cos x = Real.cos (x / 2) ^ 2 - Real.sin (x / 2) ^ 2 := by
    calc
      Real.cos x = Real.cos (x / 2 + x / 2) := by rw [hhalf]
      _ = Real.cos (x / 2) ^ 2 - Real.sin (x / 2) ^ 2 := by
        rw [Real.cos_add]
        ring
  rw [hsin, hcos, Real.tan_eq_sin_div_cos]
  field_simp [ne_of_gt hc]
  nlinarith [Real.sin_sq_add_cos_sq (x / 2)]

private theorem integrand_eq_transformed_on_branch (x : ℝ) (hx : x ∈ branch) :
    integrand x = transformedIntegrand x := by
  have hc := half_mem_cos_positive x hx
  have hden :
      0 < 2 * Real.tan (x / 2) + 4 +
        (1 / Real.cos (x / 2)) ^ 2 := by
    rw [transformed_denominator_eq x hx]
    positivity
  unfold integrand transformedIntegrand
  rw [original_denominator_factorization x hx]
  field_simp [ne_of_gt hc, ne_of_gt hden]

private theorem hasDerivAt_tan_half_on_branch (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y : ℝ => Real.tan (y / 2))
      ((1 / Real.cos (x / 2)) ^ 2 / 2) x := by
  have hc := half_mem_cos_positive x hx
  convert (Real.hasDerivAt_tan (ne_of_gt hc)).comp x
    ((hasDerivAt_id x).div_const 2) using 1 <;> ring

private theorem transformed_eq_two_tangent_on_branch (x : ℝ) (hx : x ∈ branch) :
    transformedIntegrand x = 2 * tangentIntegrand x := by
  have ht := hasDerivAt_tan_half_on_branch x hx
  have hderiv :
      deriv (fun y : ℝ => Real.tan (y / 2)) x =
        (1 / Real.cos (x / 2)) ^ 2 / 2 := ht.deriv
  unfold transformedIntegrand tangentIntegrand
  rw [hderiv, transformed_denominator_eq x hx]
  simp only [div_eq_mul_inv, one_mul]
  ring

private theorem hasDerivAt_primitive_on_branch (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (transformedIntegrand x) x := by
  have ht := hasDerivAt_tan_half_on_branch x hx
  have hu :
      HasDerivAt
        (fun y : ℝ => (Real.tan (y / 2) + 1) / 2)
        ((1 / Real.cos (x / 2)) ^ 2 / 4) x := by
    convert (ht.add_const 1).div_const 2 using 1 <;> ring
  have hraw :=
    (Real.hasDerivAt_arctan ((Real.tan (x / 2) + 1) / 2)).comp x hu
  have hleft :
      0 < 1 + ((Real.tan (x / 2) + 1) / 2) ^ 2 := by positivity
  have hright :
      0 < (Real.tan (x / 2) + 1) ^ 2 + 4 := by positivity
  have hcoef :
      (1 / (1 + ((Real.tan (x / 2) + 1) / 2) ^ 2) *
          ((1 / Real.cos (x / 2)) ^ 2 / 4)) =
        transformedIntegrand x := by
    unfold transformedIntegrand
    rw [transformed_denominator_eq x hx]
    simp only [div_eq_mul_inv, one_mul] at hleft hright ⊢
    field_simp [ne_of_gt hleft, ne_of_gt hright]
    ring
  simpa only [primitive, Function.comp_apply, hcoef] using hraw

private theorem constant_on_branch_of_hasDerivAt_zero
    (H : ℝ → ℝ) (hH : ∀ x ∈ branch, HasDerivAt H 0 x) :
    Set.Pairwise branch (fun x y => H x = H y) := by
  change Set.Pairwise (Set.Ioo (-Real.pi) Real.pi) (fun x y => H x = H y)
  have hconst :
      ∀ {x y : ℝ}, x ∈ Set.Ioo (-Real.pi) Real.pi →
        y ∈ Set.Ioo (-Real.pi) Real.pi → H x = H y := by
    apply isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    · intro x hx
      exact (hH x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hH x hx).deriv
  intro x hx y hy hxy
  exact hconst hx hy

theorem gap1 :
    AntiderivativesOn integrand =
      AntiderivativesOn transformedIntegrand := by
  apply Set.ext
  intro F
  change
    (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
      (∀ x ∈ branch, HasDerivAt F (transformedIntegrand x) x)
  constructor
  · intro hF x hx
    simpa only [integrand_eq_transformed_on_branch x hx] using hF x hx
  · intro hF x hx
    simpa only [integrand_eq_transformed_on_branch x hx] using hF x hx
theorem gap2 :
    AntiderivativesOn transformedIntegrand = TwiceFamily := by
  apply Set.ext
  intro F
  change
    (∀ x ∈ branch, HasDerivAt F (transformedIntegrand x) x) ↔
      ∃ G, (∀ x ∈ branch, HasDerivAt G (tangentIntegrand x) x) ∧
        ∀ x ∈ branch, F x = 2 * G x
  constructor
  · intro hF
    refine ⟨fun y => F y / 2, ?_, ?_⟩
    · intro x hx
      have hcoef : transformedIntegrand x / 2 = tangentIntegrand x := by
        rw [transformed_eq_two_tangent_on_branch x hx]
        ring
      simpa only [hcoef] using (hF x hx).div_const 2
    · intro x hx
      ring
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    have hopen : IsOpen branch := by
      simpa only [branch] using
        (isOpen_Ioo : IsOpen (Set.Ioo (-Real.pi) Real.pi))
    have heq : F =ᶠ[nhds x] fun y => 2 * G y := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hFG y hy
    have htwo :
        HasDerivAt (fun y => 2 * G y) (transformedIntegrand x) x := by
      simpa only [transformed_eq_two_tangent_on_branch x hx] using
        (hG x hx).const_mul 2
    exact htwo.congr_of_eventuallyEq heq
theorem gap3 :
    TwiceFamily = PrimitiveFamily := by
  apply Set.ext
  intro F
  change
    (∃ G, (∀ x ∈ branch, HasDerivAt G (tangentIntegrand x) x) ∧
        ∀ x ∈ branch, F x = 2 * G x) ↔
      ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C
  constructor
  · rintro ⟨G, hG, hFG⟩
    have hzero : (0 : ℝ) ∈ branch := by
      change -Real.pi < 0 ∧ 0 < Real.pi
      constructor <;> linarith [Real.pi_pos]
    have hderiv :
        ∀ x ∈ branch,
          HasDerivAt (fun y => 2 * G y - primitive y) 0 x := by
      intro x hx
      have hd := ((hG x hx).const_mul 2).sub
        (hasDerivAt_primitive_on_branch x hx)
      have hcoef :
          2 * tangentIntegrand x - transformedIntegrand x = 0 := by
        rw [transformed_eq_two_tangent_on_branch x hx]
        ring
      simpa only [hcoef] using hd
    have hconst := constant_on_branch_of_hasDerivAt_zero
      (fun y => 2 * G y - primitive y) hderiv
    refine ⟨2 * G 0 - primitive 0, ?_⟩
    intro x hx
    by_cases hxo : x = 0
    · subst x
      rw [hFG 0 hzero]
      ring
    · have hc := hconst hx hzero hxo
      dsimp only at hc
      rw [hFG x hx]
      linarith
  · rintro ⟨C, hFC⟩
    refine ⟨fun y => (primitive y + C) / 2, ?_, ?_⟩
    · intro x hx
      have hd := ((hasDerivAt_primitive_on_branch x hx).add_const C).div_const 2
      have hcoef : transformedIntegrand x / 2 = tangentIntegrand x := by
        rw [transformed_eq_two_tangent_on_branch x hx]
        ring
      simpa only [hcoef] using hd
    · intro x hx
      rw [hFC x hx]
      ring
theorem gap4 :
    AntiderivativesOn integrand = PrimitiveFamily := by
  calc
    AntiderivativesOn integrand =
        AntiderivativesOn transformedIntegrand := gap1
    _ = TwiceFamily := gap2
    _ = PrimitiveFamily := gap3

end
end ProofGap.Exercise1845
