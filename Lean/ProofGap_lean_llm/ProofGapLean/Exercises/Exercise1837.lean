import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1837

noncomputable section

def branch : Set ℝ := Set.univ
def integrand (x : ℝ) := 1 / (x ^ 2 - x + 2)
def completedSquareIntegrand (x : ℝ) :=
  1 / ((x - 1 / 2) ^ 2 + (Real.sqrt 7 / 2) ^ 2) *
    deriv (fun t : ℝ => t - 1 / 2) x
def primitive (x : ℝ) :=
  2 / Real.sqrt 7 * Real.arctan ((2 * x - 1) / Real.sqrt 7)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C}

private theorem completedSquareIntegrand_eq_integrand (x : ℝ) :
    completedSquareIntegrand x = integrand x := by
  have hs : (Real.sqrt 7) ^ 2 = (7 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hd : deriv (fun t : ℝ => t - 1 / 2) x = 1 := by
    simpa using ((hasDerivAt_id x).sub_const (1 / 2)).deriv
  have hden :
      (x - 1 / 2) ^ 2 + (Real.sqrt 7 / 2) ^ 2 = x ^ 2 - x + 2 := by
    rw [div_pow, hs]
    ring
  unfold completedSquareIntegrand integrand
  rw [hd, mul_one, hden]

private theorem hasDerivAt_primitive (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have hspos : 0 < Real.sqrt 7 := Real.sqrt_pos.2 (by norm_num)
  have hsne : Real.sqrt 7 ≠ 0 := ne_of_gt hspos
  have hs : (Real.sqrt 7) ^ 2 = (7 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hdenpos : 0 < x ^ 2 - x + 2 := by
    nlinarith [sq_nonneg (x - 1 / 2)]
  have hden : x ^ 2 - x + 2 ≠ 0 := ne_of_gt hdenpos
  have hargden :
      1 + ((2 * x - 1) / Real.sqrt 7) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg ((2 * x - 1) / Real.sqrt 7)]
  have hg : HasDerivAt
      (fun y : ℝ => (2 * y - 1) / Real.sqrt 7)
      (2 / Real.sqrt 7) x := by
    simpa using
      ((((hasDerivAt_id x).const_mul 2).sub_const 1).div_const
        (Real.sqrt 7))
  have hp :=
    ((Real.hasDerivAt_arctan ((2 * x - 1) / Real.sqrt 7)).comp x hg).const_mul
      (2 / Real.sqrt 7)
  have hcoef :
      2 / Real.sqrt 7 *
          (1 / (1 + ((2 * x - 1) / Real.sqrt 7) ^ 2) *
            (2 / Real.sqrt 7)) =
        1 / (x ^ 2 - x + 2) := by
    apply (eq_div_iff hden).2
    field_simp [hsne, hargden] <;>
      nlinarith [hs]
  change HasDerivAt
    (fun y : ℝ => 2 / Real.sqrt 7 *
      Real.arctan ((2 * y - 1) / Real.sqrt 7))
    (1 / (x ^ 2 - x + 2)) x
  simpa only [Function.comp_apply, hcoef] using hp

private theorem value_eq_zero_of_hasDerivAt_zero
    (f : ℝ → ℝ) (hf : ∀ x : ℝ, HasDerivAt f 0 x) (x : ℝ) :
    f x = f 0 := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hcont : ContinuousOn f (Set.Icc x 0) := by
      intro z _
      exact (hf z).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ f (Set.Ioo x 0) := by
      intro z _
      exact (hf z).differentiableAt.differentiableWithinAt
    obtain ⟨c, _, hslope⟩ := exists_deriv_eq_slope f hx hcont hdiff
    have hc0 : deriv f c = 0 := (hf c).deriv
    rw [hc0] at hslope
    change 0 = (f 0 - f x) / (0 - x) at hslope
    have hne : (0 : ℝ) - x ≠ 0 := by linarith
    field_simp [hne] at hslope
    linarith
  · subst x
    rfl
  · have hcont : ContinuousOn f (Set.Icc 0 x) := by
      intro z _
      exact (hf z).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ f (Set.Ioo 0 x) := by
      intro z _
      exact (hf z).differentiableAt.differentiableWithinAt
    obtain ⟨c, _, hslope⟩ := exists_deriv_eq_slope f hx hcont hdiff
    have hc0 : deriv f c = 0 := (hf c).deriv
    rw [hc0] at hslope
    change 0 = (f x - f 0) / (x - 0) at hslope
    have hne : x - (0 : ℝ) ≠ 0 := by linarith
    field_simp [hne] at hslope
    linarith

private theorem antiderivative_eq_primitive_add_const
    (F : ℝ → ℝ)
    (hF : ∀ x : ℝ, HasDerivAt F (integrand x) x) :
    ∃ C : ℝ, ∀ x : ℝ, F x = primitive x + C := by
  have hzero : ∀ x : ℝ,
      HasDerivAt (fun y => F y - primitive y) 0 x := by
    intro x
    simpa using (hF x).sub (hasDerivAt_primitive x)
  refine ⟨F 0 - primitive 0, ?_⟩
  intro x
  have hx := value_eq_zero_of_hasDerivAt_zero
    (fun y => F y - primitive y) hzero x
  change F x - primitive x = F 0 - primitive 0 at hx
  linarith

theorem gap1 :
    AntiderivativesOn integrand =
      AntiderivativesOn completedSquareIntegrand := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    change ∀ x ∈ branch, HasDerivAt F (completedSquareIntegrand x) x
    intro x hx
    simpa only [completedSquareIntegrand_eq_integrand] using hF x hx
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (completedSquareIntegrand x) x at hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    intro x hx
    simpa only [completedSquareIntegrand_eq_integrand] using hF x hx
theorem gap2 :
    AntiderivativesOn completedSquareIntegrand = PrimitiveFamily := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (completedSquareIntegrand x) x at hF
    change ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C
    have hF' : ∀ x : ℝ, HasDerivAt F (integrand x) x := by
      intro x
      simpa only [completedSquareIntegrand_eq_integrand] using
        hF x (by simp [branch])
    rcases antiderivative_eq_primitive_add_const F hF' with ⟨C, hC⟩
    exact ⟨C, fun x _ => hC x⟩
  · intro hF
    change ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C at hF
    change ∀ x ∈ branch, HasDerivAt F (completedSquareIntegrand x) x
    rcases hF with ⟨C, hC⟩
    have hEq : F = fun x => primitive x + C := by
      funext x
      exact hC x (by simp [branch])
    intro x _
    rw [hEq]
    simpa only [completedSquareIntegrand_eq_integrand] using
      (hasDerivAt_primitive x).add_const C
theorem gap3 :
    AntiderivativesOn integrand = PrimitiveFamily := by
  exact gap1.trans gap2

end
end ProofGap.Exercise1837
