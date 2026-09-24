import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1842

noncomputable section

def branch : Set ℝ := Set.univ
def denominator (x : ℝ) := x ^ 4 - x ^ 2 + 2
def integrand (x : ℝ) := x ^ 3 / denominator x
def firstSubstitutedIntegrand (x : ℝ) :=
  x ^ 2 * deriv (fun t : ℝ => t ^ 2) x / denominator x
def shiftedIntegrand (x : ℝ) :=
  (x ^ 2 - 1 / 2 + 1 / 2) /
    ((x ^ 2 - 1 / 2) ^ 2 + 7 / 4) *
      deriv (fun t : ℝ => t ^ 2 - 1 / 2) x
def logIntegrand (x : ℝ) :=
  deriv (fun t : ℝ => (t ^ 2 - 1 / 2) ^ 2) x /
    ((x ^ 2 - 1 / 2) ^ 2 + 7 / 4)
def atanIntegrand (x : ℝ) :=
  deriv (fun t : ℝ => t ^ 2 - 1 / 2) x /
    ((x ^ 2 - 1 / 2) ^ 2 + (Real.sqrt 7 / 2) ^ 2)
def primitive (x : ℝ) :=
  (1 / 4 : ℝ) * Real.log (denominator x) +
    1 / (2 * Real.sqrt 7) *
      Real.arctan ((2 * x ^ 2 - 1) / Real.sqrt 7)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def HalfFamily (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn f,
    ∀ x ∈ branch, F x = (1 / 2 : ℝ) * G x}
def SplitFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn logIntegrand,
    ∃ H ∈ AntiderivativesOn atanIntegrand,
      ∀ x ∈ branch, F x = (1 / 4 : ℝ) * G x + (1 / 4 : ℝ) * H x}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C}

private lemma square_hasDerivAt (x : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
  convert (hasDerivAt_id x).pow 2 using 1 <;> norm_num <;> ring

private lemma square_deriv (x : ℝ) :
    deriv (fun t : ℝ => t ^ 2) x = 2 * x :=
  (square_hasDerivAt x).deriv

private lemma shifted_hasDerivAt (x : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ 2 - 1 / 2) (2 * x) x := by
  simpa using (square_hasDerivAt x).sub_const (1 / 2 : ℝ)

private lemma shifted_deriv (x : ℝ) :
    deriv (fun t : ℝ => t ^ 2 - 1 / 2) x = 2 * x :=
  (shifted_hasDerivAt x).deriv

private lemma shiftedSquare_hasDerivAt (x : ℝ) :
    HasDerivAt (fun t : ℝ => (t ^ 2 - 1 / 2) ^ 2)
      (4 * x * (x ^ 2 - 1 / 2)) x := by
  convert (shifted_hasDerivAt x).pow 2 using 1 <;> ring

private lemma shiftedSquare_deriv (x : ℝ) :
    deriv (fun t : ℝ => (t ^ 2 - 1 / 2) ^ 2) x =
      4 * x * (x ^ 2 - 1 / 2) :=
  (shiftedSquare_hasDerivAt x).deriv

private lemma denominator_shift (x : ℝ) :
    denominator x = (x ^ 2 - 1 / 2) ^ 2 + 7 / 4 := by
  simp only [denominator]
  ring

private lemma shifted_denominator_pos (x : ℝ) :
    0 < (x ^ 2 - 1 / 2) ^ 2 + 7 / 4 := by
  nlinarith [sq_nonneg (x ^ 2 - 1 / 2)]

private lemma denominator_pos (x : ℝ) : 0 < denominator x := by
  rw [denominator_shift]
  exact shifted_denominator_pos x

private lemma sqrtSeven_pos : 0 < Real.sqrt 7 :=
  Real.sqrt_pos.2 (by norm_num)

private lemma sqrtSeven_ne : Real.sqrt 7 ≠ 0 :=
  ne_of_gt sqrtSeven_pos

private lemma sqrtSeven_sq : (Real.sqrt 7) ^ 2 = 7 :=
  Real.sq_sqrt (by norm_num)

private lemma atan_denominator_eq (x : ℝ) :
    (x ^ 2 - 1 / 2) ^ 2 + (Real.sqrt 7 / 2) ^ 2 = denominator x := by
  rw [denominator, div_pow, sqrtSeven_sq]
  ring

private lemma firstSubstitutedIntegrand_eq (x : ℝ) :
    firstSubstitutedIntegrand x = 2 * integrand x := by
  rw [firstSubstitutedIntegrand, square_deriv, integrand]
  ring

private lemma shiftedIntegrand_eq (x : ℝ) :
    shiftedIntegrand x = firstSubstitutedIntegrand x := by
  rw [shiftedIntegrand, shifted_deriv, firstSubstitutedIntegrand_eq, integrand]
  rw [← denominator_shift]
  ring

private lemma split_derivative_identity (x : ℝ) :
    (1 / 4 : ℝ) * logIntegrand x + (1 / 4 : ℝ) * atanIntegrand x =
      integrand x := by
  rw [logIntegrand, shiftedSquare_deriv, atanIntegrand, shifted_deriv]
  rw [← denominator_shift, atan_denominator_eq]
  rw [integrand]
  ring

private lemma split_scaled_identity (x : ℝ) :
    4 * integrand x - atanIntegrand x = logIntegrand x := by
  linarith [split_derivative_identity x]

private def logarithmicPart (x : ℝ) : ℝ :=
  Real.log ((x ^ 2 - 1 / 2) ^ 2 + 7 / 4)

private def arctangentPart (x : ℝ) : ℝ :=
  2 / Real.sqrt 7 * Real.arctan ((2 * x ^ 2 - 1) / Real.sqrt 7)

private lemma logarithmicPart_hasDerivAt (x : ℝ) :
    HasDerivAt logarithmicPart (logIntegrand x) x := by
  have hbase := (shiftedSquare_hasDerivAt x).add_const (7 / 4 : ℝ)
  have hlog := hbase.log (ne_of_gt (shifted_denominator_pos x))
  convert hlog using 1
  rw [logIntegrand, shiftedSquare_deriv]

private lemma arctangentPart_hasDerivAt (x : ℝ) :
    HasDerivAt arctangentPart (atanIntegrand x) x := by
  have hz : HasDerivAt
      (fun t : ℝ => (2 * t ^ 2 - 1) / Real.sqrt 7)
      (4 * x / Real.sqrt 7) x := by
    convert (((square_hasDerivAt x).const_mul 2).sub_const 1).div_const
      (Real.sqrt 7) using 1 <;> simp <;> ring
  have h := hz.arctan.const_mul (2 / Real.sqrt 7)
  convert h using 1
  rw [atanIntegrand, shifted_deriv, atan_denominator_eq, denominator_shift]
  have hshift :
      (x ^ 2 - 1 / 2) ^ 2 + 7 / 4 ≠ 0 :=
    ne_of_gt (shifted_denominator_pos x)
  have hzden :
      1 + ((2 * x ^ 2 - 1) / Real.sqrt 7) ^ 2 ≠ 0 := by
    positivity
  field_simp [sqrtSeven_ne, hshift, hzden]
  rw [sqrtSeven_sq]
  ring

private lemma primitive_eq_parts (x : ℝ) :
    primitive x =
      (1 / 4 : ℝ) * logarithmicPart x +
        (1 / 4 : ℝ) * arctangentPart x := by
  rw [primitive, denominator_shift]
  simp only [logarithmicPart, arctangentPart]
  field_simp [sqrtSeven_ne]
  ring

private lemma primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have hfun : primitive = fun y =>
      (1 / 4 : ℝ) * logarithmicPart y +
        (1 / 4 : ℝ) * arctangentPart y := by
    funext y
    exact primitive_eq_parts y
  rw [hfun]
  have h := ((logarithmicPart_hasDerivAt x).const_mul (1 / 4 : ℝ)).add
    ((arctangentPart_hasDerivAt x).const_mul (1 / 4 : ℝ))
  convert h using 1
  exact (split_derivative_identity x).symm

private lemma antiderivative_eq_primitive_add_const
    (F : ℝ → ℝ) (hF : F ∈ AntiderivativesOn integrand) :
    ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C := by
  let K : ℝ → ℝ := fun x => F x - primitive x
  have hK : ∀ x : ℝ, HasDerivAt K 0 x := by
    intro x
    simpa [K] using
      (hF x (by simp [branch])).sub (primitive_hasDerivAt x)
  have hdiff : Differentiable ℝ K := by
    intro x
    exact (hK x).differentiableAt
  have hderiv : ∀ x : ℝ, deriv K x = 0 := by
    intro x
    exact (hK x).deriv
  have hconst := is_const_of_deriv_eq_zero hdiff hderiv
  refine ⟨K 0, ?_⟩
  intro x hx
  have hkx : K x = K 0 := hconst x 0
  dsimp [K] at hkx ⊢
  linarith

theorem gap1 :
    AntiderivativesOn integrand = HalfFamily firstSubstitutedIntegrand := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    refine ⟨fun x => 2 * F x, ?_, ?_⟩
    · intro x hx
      have h := (hF x hx).const_mul 2
      convert h using 1
      rw [firstSubstitutedIntegrand_eq]
    · intro x hx
      ring
  · rintro ⟨G, hG, hFG⟩
    have hEq : F = fun x => (1 / 2 : ℝ) * G x := by
      funext x
      exact hFG x (by simp [branch])
    rw [hEq]
    intro x hx
    have h := (hG x hx).const_mul (1 / 2 : ℝ)
    convert h using 1
    rw [firstSubstitutedIntegrand_eq]
    ring
theorem gap2 :
    HalfFamily firstSubstitutedIntegrand = HalfFamily shiftedIntegrand := by
  have hfun : firstSubstitutedIntegrand = shiftedIntegrand := by
    funext x
    exact (shiftedIntegrand_eq x).symm
  rw [hfun]
theorem gap3 :
    AntiderivativesOn integrand = HalfFamily shiftedIntegrand := by
  exact gap1.trans gap2
theorem gap4 :
    AntiderivativesOn integrand = SplitFamily := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    refine ⟨fun x => 4 * F x - arctangentPart x, ?_, arctangentPart, ?_, ?_⟩
    · intro x hx
      have h := ((hF x hx).const_mul 4).sub (arctangentPart_hasDerivAt x)
      convert h using 1
      exact (split_scaled_identity x).symm
    · intro x hx
      exact arctangentPart_hasDerivAt x
    · intro x hx
      ring
  · rintro ⟨G, hG, H, hH, hF⟩
    have hEq : F = fun x => (1 / 4 : ℝ) * G x + (1 / 4 : ℝ) * H x := by
      funext x
      exact hF x (by simp [branch])
    rw [hEq]
    intro x hx
    have h := ((hG x hx).const_mul (1 / 4 : ℝ)).add
      ((hH x hx).const_mul (1 / 4 : ℝ))
    convert h using 1
    exact (split_derivative_identity x).symm
theorem gap5 :
    AntiderivativesOn integrand = PrimitiveFamily := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    exact antiderivative_eq_primitive_add_const F hF
  · rintro ⟨C, hC⟩
    have hEq : F = fun x => primitive x + C := by
      funext x
      exact hC x (by simp [branch])
    rw [hEq]
    intro x hx
    exact (primitive_hasDerivAt x).add_const C

end
end ProofGap.Exercise1842
