import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1816

noncomputable section

def branch : Set ℝ := Set.univ
def integrand (x : ℝ) := x ^ 2 / (1 + x ^ 2) ^ 2
def scaledIntegrand (x : ℝ) :=
  x / (1 + x ^ 2) ^ 2 * deriv (fun t : ℝ => 1 + t ^ 2) x
def reciprocalChainIntegrand (x : ℝ) :=
  x * deriv (fun t : ℝ => 1 / (1 + t ^ 2)) x
def arctanIntegrand (x : ℝ) := 1 / (1 + x ^ 2)
def boundary (x : ℝ) := -x / (2 * (1 + x ^ 2))
def primitive (x : ℝ) := boundary x + (1 / 2 : ℝ) * Real.arctan x
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def HalfFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn scaledIntegrand,
    ∀ x ∈ branch, F x = (1 / 2 : ℝ) * G x}
def NegativeHalfFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn reciprocalChainIntegrand,
    ∀ x ∈ branch, F x = (-1 / 2 : ℝ) * G x}
def ByPartsFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn arctanIntegrand,
    ∀ x ∈ branch, F x = boundary x + (1 / 2 : ℝ) * G x}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C}

private lemma one_add_sq_ne_zero (x : ℝ) : 1 + x ^ 2 ≠ 0 := by
  nlinarith [sq_nonneg x]

private lemma hasDerivAt_quadratic (x : ℝ) :
    HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * x) x := by
  convert (hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).pow 2) using 1 <;>
    simp [id] <;> ring

private lemma scaledIntegrand_eq (x : ℝ) :
    scaledIntegrand x = 2 * integrand x := by
  unfold scaledIntegrand integrand
  rw [(hasDerivAt_quadratic x).deriv]
  ring

private lemma hasDerivAt_reciprocalQuadratic (x : ℝ) :
    HasDerivAt (fun t : ℝ => 1 / (1 + t ^ 2))
      (-2 * x / (1 + x ^ 2) ^ 2) x := by
  convert (hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_quadratic x)
    (one_add_sq_ne_zero x) using 1 <;> simp [id] <;> ring

private lemma reciprocalChainIntegrand_eq (x : ℝ) :
    reciprocalChainIntegrand x = -2 * integrand x := by
  unfold reciprocalChainIntegrand integrand
  rw [(hasDerivAt_reciprocalQuadratic x).deriv]
  ring

private lemma hasDerivAt_boundary (x : ℝ) :
    HasDerivAt boundary ((x ^ 2 - 1) / (2 * (1 + x ^ 2) ^ 2)) x := by
  unfold boundary
  convert (hasDerivAt_id x).neg.div
    ((hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_quadratic x))
    (mul_ne_zero (by norm_num) (one_add_sq_ne_zero x)) using 1 <;>
    simp [id] <;>
    field_simp [one_add_sq_ne_zero x] <;>
    ring

private lemma hasDerivAt_primitive (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  unfold primitive
  convert (hasDerivAt_boundary x).add
    ((Real.hasDerivAt_arctan x).const_mul (1 / 2 : ℝ)) using 1
  unfold integrand
  field_simp [one_add_sq_ne_zero x]
  ring

private lemma eq_at_zero_of_hasDerivAt_zero
    (H : ℝ → ℝ) (hH : ∀ x : ℝ, HasDerivAt H 0 x) (x : ℝ) : H x = H 0 := by
  have hdiff : Differentiable ℝ H := fun y => (hH y).differentiableAt
  exact is_const_of_deriv_eq_zero hdiff (fun y => (hH y).deriv) x 0

private theorem antiderivatives_eq_negativeHalf :
    AntiderivativesOn integrand = NegativeHalfFamily := by
  ext F
  constructor
  · intro hF
    refine ⟨fun y => -2 * F y, ?_, ?_⟩
    · intro x hx
      rw [reciprocalChainIntegrand_eq]
      exact (hF x hx).const_mul (-2)
    · intro x hx
      dsimp
      ring
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    have hEq : F = fun y => (-1 / 2 : ℝ) * G y := by
      funext y
      exact hFG y (Set.mem_univ y)
    rw [hEq]
    convert (hG x hx).const_mul (-1 / 2 : ℝ) using 1
    rw [reciprocalChainIntegrand_eq]
    ring

private theorem antiderivatives_eq_byParts :
    AntiderivativesOn integrand = ByPartsFamily := by
  ext F
  constructor
  · intro hF
    refine ⟨fun y => 2 * (F y - boundary y), ?_, ?_⟩
    · intro x hx
      convert ((hF x hx).sub (hasDerivAt_boundary x)).const_mul 2 using 1
      unfold arctanIntegrand integrand
      field_simp [one_add_sq_ne_zero x]
      ring
    · intro x hx
      dsimp
      ring
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    have hEq : F = fun y => boundary y + (1 / 2 : ℝ) * G y := by
      funext y
      exact hFG y (Set.mem_univ y)
    rw [hEq]
    convert (hasDerivAt_boundary x).add
      ((hG x hx).const_mul (1 / 2 : ℝ)) using 1
    unfold arctanIntegrand integrand
    field_simp [one_add_sq_ne_zero x]
    ring

private theorem antiderivatives_eq_primitive :
    AntiderivativesOn integrand = PrimitiveFamily := by
  ext F
  constructor
  · intro hF
    have hzero : ∀ x : ℝ,
        HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x
      convert (hF x (Set.mem_univ x)).sub (hasDerivAt_primitive x) using 1 <;> ring
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have hc : F x - primitive x = F 0 - primitive 0 :=
      eq_at_zero_of_hasDerivAt_zero (fun y => F y - primitive y) hzero x
    linarith
  · rintro ⟨C, hFC⟩
    intro x hx
    have hEq : F = fun y => primitive y + C := by
      funext y
      exact hFC y (Set.mem_univ y)
    rw [hEq]
    convert (hasDerivAt_primitive x).add (hasDerivAt_const x C) using 1 <;> ring

theorem gap1 :
    AntiderivativesOn integrand = HalfFamily := by
  ext F
  constructor
  · intro hF
    refine ⟨fun y => 2 * F y, ?_, ?_⟩
    · intro x hx
      rw [scaledIntegrand_eq]
      exact (hF x hx).const_mul 2
    · intro x hx
      dsimp
      ring
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    have hEq : F = fun y => (1 / 2 : ℝ) * G y := by
      funext y
      exact hFG y (Set.mem_univ y)
    rw [hEq]
    convert (hG x hx).const_mul (1 / 2 : ℝ) using 1
    rw [scaledIntegrand_eq]
    ring
theorem gap2 :
    HalfFamily = NegativeHalfFamily := by
  calc
    HalfFamily = AntiderivativesOn integrand := gap1.symm
    _ = NegativeHalfFamily := antiderivatives_eq_negativeHalf
theorem gap3 :
    NegativeHalfFamily = ByPartsFamily := by
  calc
    NegativeHalfFamily = AntiderivativesOn integrand := antiderivatives_eq_negativeHalf.symm
    _ = ByPartsFamily := antiderivatives_eq_byParts
theorem gap4 :
    AntiderivativesOn integrand = ByPartsFamily := by
  exact antiderivatives_eq_byParts
theorem gap5 :
    AntiderivativesOn integrand = PrimitiveFamily := by
  exact antiderivatives_eq_primitive

end
end ProofGap.Exercise1816
