import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1718

noncomputable section

def branch : Set ℝ := Set.univ
def integrand (x : ℝ) :=
  Real.sin x * Real.cos x /
    ((Real.sin x) ^ 4 + (Real.cos x) ^ 4)
def doubledAngleIntegrand (x : ℝ) :=
  (1 / 2 : ℝ) *
    (Real.sin (2 * x) / (1 - (1 / 2 : ℝ) * (Real.sin (2 * x)) ^ 2))
def substitutedIntegrand (x : ℝ) :=
  -(1 / 2 : ℝ) *
    (deriv (fun t : ℝ => Real.cos (2 * t)) x /
      (1 + (Real.cos (2 * x)) ^ 2))
def primitive (x : ℝ) := -(1 / 2 : ℝ) * Real.arctan (Real.cos (2 * x))
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private theorem integrand_eq_doubled (x : ℝ) :
    integrand x = doubledAngleIntegrand x := by
  have htrig := Real.sin_sq_add_cos_sq x
  have hden :
      Real.sin x ^ 4 + Real.cos x ^ 4 =
        1 - (1 / 2 : ℝ) * (2 * Real.sin x * Real.cos x) ^ 2 := by
    calc
      Real.sin x ^ 4 + Real.cos x ^ 4 =
          (Real.sin x ^ 2 + Real.cos x ^ 2) ^ 2 -
            2 * (Real.sin x * Real.cos x) ^ 2 := by ring
      _ = 1 - (1 / 2 : ℝ) *
            (2 * Real.sin x * Real.cos x) ^ 2 := by
          rw [htrig]
          ring
  unfold integrand doubledAngleIntegrand
  rw [Real.sin_two_mul, ← hden]
  ring

private theorem doubled_eq_substituted (x : ℝ) :
    doubledAngleIntegrand x = substitutedIntegrand x := by
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (2 * t))
      (-2 * Real.sin (2 * x)) x := by
    convert (Real.hasDerivAt_cos (2 * x)).comp x
      ((hasDerivAt_id x).const_mul 2) using 1 <;> ring
  have htrig := Real.sin_sq_add_cos_sq (2 * x)
  have hright : 1 + Real.cos (2 * x) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (Real.cos (2 * x))]
  have hden :
      1 - (1 / 2 : ℝ) * Real.sin (2 * x) ^ 2 =
        (1 / 2 : ℝ) * (1 + Real.cos (2 * x) ^ 2) := by
    nlinarith
  have hdenleft :
      (1 / 2 : ℝ) * (1 + Real.cos (2 * x) ^ 2) ≠ 0 := by
    exact mul_ne_zero (by norm_num) hright
  unfold doubledAngleIntegrand substitutedIntegrand
  rw [hcos.deriv, hden]
  field_simp [hdenleft, hright] <;> ring

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (substitutedIntegrand x) x := by
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (2 * t))
      (-2 * Real.sin (2 * x)) x := by
    convert (Real.hasDerivAt_cos (2 * x)).comp x
      ((hasDerivAt_id x).const_mul 2) using 1 <;> ring
  unfold primitive substitutedIntegrand
  rw [hcos.deriv]
  convert ((Real.hasDerivAt_arctan (Real.cos (2 * x))).comp x hcos).const_mul
      (-(1 / 2 : ℝ)) using 1 <;> ring

private theorem hasDerivAt_zero_eq (G : ℝ → ℝ)
    (hG : ∀ x : ℝ, HasDerivAt G 0 x) (x y : ℝ) : G x = G y := by
  have hdiff : Differentiable ℝ G := fun z => (hG z).differentiableAt
  have hderiv : ∀ z : ℝ, deriv G z = 0 := fun z => (hG z).deriv
  exact (is_const_of_deriv_eq_zero hdiff hderiv) x y

theorem gap1 :
    AntiderivativesOn integrand =
      AntiderivativesOn doubledAngleIntegrand := by
  ext F
  constructor
  · intro h
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at h
    change ∀ x ∈ branch, HasDerivAt F (doubledAngleIntegrand x) x
    intro x hx
    rw [← integrand_eq_doubled x]
    exact h x hx
  · intro h
    change ∀ x ∈ branch, HasDerivAt F (doubledAngleIntegrand x) x at h
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    intro x hx
    rw [integrand_eq_doubled x]
    exact h x hx
theorem gap2 :
    AntiderivativesOn doubledAngleIntegrand =
      AntiderivativesOn substitutedIntegrand := by
  ext F
  constructor
  · intro h
    change ∀ x ∈ branch, HasDerivAt F (doubledAngleIntegrand x) x at h
    change ∀ x ∈ branch, HasDerivAt F (substitutedIntegrand x) x
    intro x hx
    rw [← doubled_eq_substituted x]
    exact h x hx
  · intro h
    change ∀ x ∈ branch, HasDerivAt F (substitutedIntegrand x) x at h
    change ∀ x ∈ branch, HasDerivAt F (doubledAngleIntegrand x) x
    intro x hx
    rw [doubled_eq_substituted x]
    exact h x hx
theorem gap3 :
    AntiderivativesOn substitutedIntegrand = PrimitiveFamily primitive := by
  ext F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (substitutedIntegrand x) x at hF
    change ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C
    let G : ℝ → ℝ := fun x => F x - primitive x
    have hG : ∀ x : ℝ, HasDerivAt G 0 x := by
      intro x
      simpa [G] using
        (hF x (by simp [branch])).sub (primitive_hasDerivAt x)
    refine ⟨G 0, ?_⟩
    intro x hx
    have hconst : G x = G 0 := hasDerivAt_zero_eq G hG x 0
    dsimp [G] at hconst ⊢
    linarith
  · rintro ⟨C, hC⟩
    change ∀ x ∈ branch, HasDerivAt F (substitutedIntegrand x) x
    have hFC : F = fun x => primitive x + C := by
      funext x
      exact hC x (by simp [branch])
    rw [hFC]
    intro x hx
    exact (primitive_hasDerivAt x).add_const C
theorem gap4 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  calc
    AntiderivativesOn integrand =
        AntiderivativesOn doubledAngleIntegrand := gap1
    _ = AntiderivativesOn substitutedIntegrand := gap2
    _ = PrimitiveFamily primitive := gap3

end
end ProofGap.Exercise1718
