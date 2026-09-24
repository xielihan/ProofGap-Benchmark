import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise1916

noncomputable section

def branch : Set ℝ := Set.Ioo 0 (1 / 5 : ℝ)
def u (x : ℝ) := x ^ 5 - 5 * x
def integrand (x : ℝ) :=
  (x ^ 4 - 1) / (x * (x ^ 4 - 5) * (x ^ 5 - 5 * x + 1))
def substitutedIntegrand (x : ℝ) :=
  1 / (u x * (u x + 1)) * deriv u x
def partialFractionIntegrand (x : ℝ) :=
  (1 / u x - 1 / (u x + 1)) * deriv u x
def firstLogIntegrand (x : ℝ) := 1 / u x * deriv u x
def secondLogIntegrand (x : ℝ) :=
  1 / (u x + 1) * deriv (fun t : ℝ => u t + 1) x
def primitive (x : ℝ) :=
  (1 / 5 : ℝ) *
    Real.log |(x * (x ^ 4 - 5)) / (x ^ 5 - 5 * x + 1)|
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def FifthFamily (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn f,
    ∀ x ∈ branch, F x = (1 / 5 : ℝ) * G x}
def SplitFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn firstLogIntegrand,
    ∃ H ∈ AntiderivativesOn secondLogIntegrand,
      ∀ x ∈ branch, F x = (1 / 5 : ℝ) * G x - (1 / 5 : ℝ) * H x}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C}

private lemma branch_signs {x : ℝ} (hx : x ∈ branch) :
    u x < 0 ∧ 0 < u x + 1 := by
  rcases hx with ⟨hx0, hx5⟩
  have hx1 : x < 1 := by
    norm_num at hx5 ⊢
    linarith
  have hx2 : x ^ 2 < 1 := by
    have hprod : 0 < (1 - x) * (x + 1) :=
      mul_pos (sub_pos.mpr hx1) (by linarith)
    nlinarith
  have hx4 : x ^ 4 < 1 := by
    have hprod : 0 < (1 - x ^ 2) * (x ^ 2 + 1) :=
      mul_pos (sub_pos.mpr hx2) (by nlinarith [sq_nonneg x])
    nlinarith
  have hu : u x < 0 := by
    have huform : u x = x * (x ^ 4 - 5) := by
      simp only [u]
      ring
    rw [huform]
    exact mul_neg_of_pos_of_neg hx0 (by linarith)
  have hupow : 0 < x ^ 5 := pow_pos hx0 5
  have hu1 : 0 < u x + 1 := by
    simp only [u]
    norm_num at hx5
    nlinarith
  exact ⟨hu, hu1⟩

private lemma hasDerivAt_u_local (x : ℝ) :
    HasDerivAt u (5 * x ^ 4 - 5) x := by
  simpa [u] using
    (((hasDerivAt_id x).pow 5).sub ((hasDerivAt_id x).const_mul 5))

private lemma denominator_eq {x : ℝ} :
    x ^ 5 - 5 * x + 1 = u x + 1 := by
  simp only [u]

private lemma scaled_substituted_eq_integrand {x : ℝ} (hx : x ∈ branch) :
    integrand x = (1 / 5 : ℝ) * substitutedIntegrand x := by
  rcases branch_signs hx with ⟨hu, hu1⟩
  have hdu := (hasDerivAt_u_local x).deriv
  have hxu : x * (x ^ 4 - 5) = u x := by
    simp only [u]
    ring
  have hden : x ^ 5 - 5 * x + 1 = u x + 1 := denominator_eq
  have hune : u x ≠ 0 := ne_of_lt hu
  have hu1ne : u x + 1 ≠ 0 := ne_of_gt hu1
  simp only [integrand, substitutedIntegrand]
  rw [hdu, hxu, hden]
  field_simp [hune, hu1ne] <;> ring

private lemma scaled_partial_eq_integrand {x : ℝ} (hx : x ∈ branch) :
    integrand x = (1 / 5 : ℝ) * partialFractionIntegrand x := by
  rcases branch_signs hx with ⟨hu, hu1⟩
  have hdu := (hasDerivAt_u_local x).deriv
  have hxu : x * (x ^ 4 - 5) = u x := by
    simp only [u]
    ring
  have hden : x ^ 5 - 5 * x + 1 = u x + 1 := denominator_eq
  have hune : u x ≠ 0 := ne_of_lt hu
  have hu1ne : u x + 1 ≠ 0 := ne_of_gt hu1
  simp only [integrand, partialFractionIntegrand]
  rw [hdu, hxu, hden]
  field_simp [hune, hu1ne] <;> ring

private lemma scaled_split_eq_integrand {x : ℝ} (hx : x ∈ branch) :
    integrand x =
      (1 / 5 : ℝ) * firstLogIntegrand x -
        (1 / 5 : ℝ) * secondLogIntegrand x := by
  rcases branch_signs hx with ⟨hu, hu1⟩
  have hdu := (hasDerivAt_u_local x).deriv
  have hdu1 := ((hasDerivAt_u_local x).add_const 1).deriv
  have hxu : x * (x ^ 4 - 5) = u x := by
    simp only [u]
    ring
  have hden : x ^ 5 - 5 * x + 1 = u x + 1 := denominator_eq
  have hune : u x ≠ 0 := ne_of_lt hu
  have hu1ne : u x + 1 ≠ 0 := ne_of_gt hu1
  simp only [integrand, firstLogIntegrand, secondLogIntegrand]
  rw [hdu, hdu1, hxu, hden]
  field_simp [hune, hu1ne] <;> ring

private theorem antiderivatives_eq_fifth_of_scale
    {f g : ℝ → ℝ}
    (hscale : ∀ x ∈ branch, f x = (1 / 5 : ℝ) * g x) :
    AntiderivativesOn f = FifthFamily g := by
  ext F
  simp only [AntiderivativesOn, FifthFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨fun y => 5 * F y, ?_, ?_⟩
    · intro x hx
      have hd := (hF x hx).const_mul 5
      have hval : 5 * f x = g x := by
        rw [hscale x hx]
        ring
      simpa only [hval] using hd
    · intro x hx
      ring
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    have hd : HasDerivAt (fun y => (1 / 5 : ℝ) * G y)
        ((1 / 5 : ℝ) * g x) x := (hG x hx).const_mul (1 / 5 : ℝ)
    have hd' : HasDerivAt (fun y => (1 / 5 : ℝ) * G y) (f x) x := by
      simpa only [hscale x hx] using hd
    have heq : Filter.EventuallyEq (nhds x) F
        (fun y => (1 / 5 : ℝ) * G y) :=
      ((isOpen_Ioo.eventually_mem hx).mono fun y hy => hFG y hy)
    exact hd'.congr_of_eventuallyEq heq

private lemma logarithm_u_add_one_antiderivative :
    (fun x => Real.log (u x + 1)) ∈
      AntiderivativesOn secondLogIntegrand := by
  intro x hx
  rcases branch_signs hx with ⟨_, hu1⟩
  have hd := (Real.hasDerivAt_log (ne_of_gt hu1)).comp x
    ((hasDerivAt_u_local x).add_const 1)
  rw [secondLogIntegrand, ((hasDerivAt_u_local x).add_const 1).deriv]
  simpa [one_div] using hd

private theorem antiderivatives_eq_split :
    AntiderivativesOn integrand = SplitFamily := by
  ext F
  simp only [AntiderivativesOn, SplitFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    let H : ℝ → ℝ := fun y => Real.log (u y + 1)
    have hH : ∀ x ∈ branch, HasDerivAt H (secondLogIntegrand x) x :=
      logarithm_u_add_one_antiderivative
    refine ⟨fun y => 5 * F y + H y, ?_, H, hH, ?_⟩
    · intro x hx
      have hd := ((hF x hx).const_mul 5).add (hH x hx)
      have hrel := scaled_split_eq_integrand hx
      have hval : 5 * integrand x + secondLogIntegrand x =
          firstLogIntegrand x := by
        linarith
      simpa only [hval] using hd
    · intro x hx
      ring
  · rintro ⟨G, hG, H, hH, hFGH⟩
    intro x hx
    have hd := ((hG x hx).const_mul (1 / 5 : ℝ)).sub
      ((hH x hx).const_mul (1 / 5 : ℝ))
    have hd' : HasDerivAt
        (fun y => (1 / 5 : ℝ) * G y - (1 / 5 : ℝ) * H y)
        (integrand x) x := by
      have hrel := scaled_split_eq_integrand hx
      simpa only [hrel] using hd
    have heq : Filter.EventuallyEq (nhds x) F
        (fun y => (1 / 5 : ℝ) * G y - (1 / 5 : ℝ) * H y) :=
      ((isOpen_Ioo.eventually_mem hx).mono fun y hy => hFGH y hy)
    exact hd'.congr_of_eventuallyEq heq

private def logarithmicPrimitive (x : ℝ) : ℝ :=
  (1 / 5 : ℝ) * (Real.log (-u x) - Real.log (u x + 1))

private lemma logarithm_neg_u_hasDerivAt {x : ℝ} (hx : x ∈ branch) :
    HasDerivAt (fun y => Real.log (-u y)) (firstLogIntegrand x) x := by
  rcases branch_signs hx with ⟨hu, _⟩
  have hneg : 0 < -u x := neg_pos.mpr hu
  have hd := (Real.hasDerivAt_log (ne_of_gt hneg)).comp x
    (hasDerivAt_u_local x).neg
  have hdu := (hasDerivAt_u_local x).deriv
  simp only [firstLogIntegrand]
  rw [hdu]
  convert hd using 1
  field_simp [ne_of_lt hu] <;> ring

private lemma logarithmicPrimitive_hasDerivAt {x : ℝ} (hx : x ∈ branch) :
    HasDerivAt logarithmicPrimitive (integrand x) x := by
  have hfirst := logarithm_neg_u_hasDerivAt (x := x) hx
  have hsecond := logarithm_u_add_one_antiderivative x hx
  have hd := (hfirst.const_mul (1 / 5 : ℝ)).sub
    (hsecond.const_mul (1 / 5 : ℝ))
  have hrel := scaled_split_eq_integrand (x := x) hx
  have hfun :
      logarithmicPrimitive =
        ((fun y => (1 / 5 : ℝ) * Real.log (-u y)) -
          (fun y => (1 / 5 : ℝ) * Real.log (u y + 1))) := by
    funext y
    change (1 / 5 : ℝ) *
        (Real.log (-u y) - Real.log (u y + 1)) =
      (1 / 5 : ℝ) * Real.log (-u y) -
        (1 / 5 : ℝ) * Real.log (u y + 1)
    ring
  rw [hfun, hrel]
  exact hd

private lemma primitive_eq_logarithmicPrimitive {x : ℝ} (hx : x ∈ branch) :
    primitive x = logarithmicPrimitive x := by
  rcases branch_signs hx with ⟨hu, hu1⟩
  have hxu : x * (x ^ 4 - 5) = u x := by
    simp only [u]
    ring
  have hden : x ^ 5 - 5 * x + 1 = u x + 1 := denominator_eq
  have hdiv : u x / (u x + 1) < 0 := div_neg_of_neg_of_pos hu hu1
  have habs : |u x / (u x + 1)| = (-u x) / (u x + 1) := by
    rw [abs_of_neg hdiv]
    field_simp [ne_of_gt hu1] <;> ring
  simp only [primitive, logarithmicPrimitive]
  rw [hxu, hden, habs,
    Real.log_div (neg_ne_zero.mpr (ne_of_lt hu)) (ne_of_gt hu1)]

private lemma primitive_hasDerivAt {x : ℝ} (hx : x ∈ branch) :
    HasDerivAt primitive (integrand x) x := by
  have hd := logarithmicPrimitive_hasDerivAt (x := x) hx
  have heq : Filter.EventuallyEq (nhds x) primitive logarithmicPrimitive :=
    ((isOpen_Ioo.eventually_mem hx).mono fun y hy =>
      primitive_eq_logarithmicPrimitive (x := y) hy)
  exact hd.congr_of_eventuallyEq heq

private lemma constant_on_branch_of_hasDerivAt_zero
    {F : ℝ → ℝ}
    (hF : ∀ x ∈ branch, HasDerivAt F 0 x) :
    ∀ x ∈ branch, ∀ y ∈ branch, F x = F y := by
  rw [branch] at hF ⊢
  intro x hx y hy
  exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun z hz => (hF z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hF z hz).deriv) hx hy

theorem gap1 :
    AntiderivativesOn integrand = FifthFamily substitutedIntegrand := by
  exact antiderivatives_eq_fifth_of_scale
    (fun x hx => scaled_substituted_eq_integrand (x := x) hx)
theorem gap2 :
    AntiderivativesOn integrand = FifthFamily partialFractionIntegrand := by
  exact antiderivatives_eq_fifth_of_scale
    (fun x hx => scaled_partial_eq_integrand (x := x) hx)
theorem gap3 :
    AntiderivativesOn integrand = SplitFamily := by
  exact antiderivatives_eq_split
theorem gap4 :
    AntiderivativesOn integrand = PrimitiveFamily := by
  ext F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    have hzero : ∀ x ∈ branch,
        HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      have hP := primitive_hasDerivAt (x := x) hx
      convert (hF x hx).sub hP using 1 <;> ring
    have hconst := constant_on_branch_of_hasDerivAt_zero hzero
    let x₀ : ℝ := 1 / 10
    have hx₀ : x₀ ∈ branch := by
      norm_num [x₀, branch]
    refine ⟨F x₀ - primitive x₀, ?_⟩
    intro x hx
    have heq := hconst x hx x₀ hx₀
    change F x - primitive x = F x₀ - primitive x₀ at heq
    linarith
  · rintro ⟨C, hFC⟩
    intro x hx
    have hd : HasDerivAt (fun y => primitive y + C) (integrand x) x :=
      (primitive_hasDerivAt (x := x) hx).add_const C
    have heq : Filter.EventuallyEq (nhds x) F
        (fun y => primitive y + C) :=
      ((isOpen_Ioo.eventually_mem hx).mono fun y hy => hFC y hy)
    exact hd.congr_of_eventuallyEq heq

end
end ProofGap.Exercise1916
