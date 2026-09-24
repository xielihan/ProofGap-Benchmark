import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1994

noncomputable section

def originalIntegrand (x : ℝ) := Real.sin x ^ 2 * Real.cos x ^ 4
def firstReducedIntegrand (x : ℝ) :=
  Real.sin (2 * x) ^ 2 * Real.cos x ^ 2
def secondReducedIntegrand (x : ℝ) :=
  Real.sin (2 * x) ^ 2 * (1 + Real.cos (2 * x))
def averageIntegrand (x : ℝ) := (1 - Real.cos (4 * x)) / 2
def sineSubstitutionIntegrand (x : ℝ) :=
  Real.sin (2 * x) ^ 2 *
    deriv (fun y : ℝ => Real.sin (2 * y)) x
def primitive (x : ℝ) :=
  x / 16 - 1 / 64 * Real.sin (4 * x) +
    1 / 48 * Real.sin (2 * x) ^ 3
def Antiderivatives (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x, HasDerivAt F (f x) x}
def ScaledFamily (f : ℝ → ℝ) (c : ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives f, ∀ x, F x = c * G x}
def DecompositionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives averageIntegrand,
    ∃ H ∈ Antiderivatives sineSubstitutionIntegrand,
      ∀ x, F x = 1 / 8 * G x + 1 / 16 * H x}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = primitive x + C}

private theorem antiderivatives_eq_scaled_of_pointwise
    (f g : ℝ → ℝ) (c : ℝ) (hc : c ≠ 0)
    (hfg : ∀ x, f x = c * g x) :
    Antiderivatives f = ScaledFamily g c := by
  ext F
  constructor
  · intro hF
    change ∀ x, HasDerivAt F (f x) x at hF
    change ∃ G, (∀ x, HasDerivAt G (g x) x) ∧ ∀ x, F x = c * G x
    refine ⟨fun x => c⁻¹ * F x, ?_, ?_⟩
    · intro x
      have hd := (hF x).const_mul c⁻¹
      convert hd using 1
      rw [hfg x]
      field_simp [hc]
    · intro x
      field_simp [hc]
  · rintro ⟨G, hG, hF⟩
    change ∀ x, HasDerivAt G (g x) x at hG
    change ∀ x, HasDerivAt F (f x) x
    rw [show F = fun x => c * G x from funext hF]
    intro x
    have hd := (hG x).const_mul c
    convert hd using 1
    exact hfg x

private theorem hasDerivAt_sin_two (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sin (2 * y))
      (2 * Real.cos (2 * x)) x := by
  have hlin : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul 2
  convert (Real.hasDerivAt_sin (2 * x)).comp x hlin using 1 <;> ring

private theorem deriv_sin_two (x : ℝ) :
    deriv (fun y : ℝ => Real.sin (2 * y)) x =
      2 * Real.cos (2 * x) :=
  (hasDerivAt_sin_two x).deriv

private theorem original_decomposition_identity (x : ℝ) :
    originalIntegrand x =
      1 / 8 * averageIntegrand x +
        1 / 16 * sineSubstitutionIntegrand x := by
  have hcos4 :
      Real.cos (4 * x) = 2 * Real.cos (2 * x) ^ 2 - 1 := by
    convert Real.cos_two_mul (2 * x) using 1 <;> ring
  have hsq :
      1 - Real.cos (4 * x) = 2 * Real.sin (2 * x) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (2 * x)]
  unfold originalIntegrand averageIntegrand sineSubstitutionIntegrand
  rw [deriv_sin_two, hsq, Real.cos_two_mul, Real.sin_two_mul]
  ring

private def sinePrimitive (x : ℝ) :=
  1 / 3 * Real.sin (2 * x) ^ 3

private theorem sinePrimitive_hasDerivAt (x : ℝ) :
    HasDerivAt sinePrimitive (sineSubstitutionIntegrand x) x := by
  rw [show sinePrimitive = fun y =>
    1 / 3 * ((Real.sin (2 * y) * Real.sin (2 * y)) * Real.sin (2 * y)) from by
      funext y
      unfold sinePrimitive
      ring]
  have hs := hasDerivAt_sin_two x
  have hd := ((hs.mul hs).mul hs).const_mul (1 / 3)
  convert hd using 1
  unfold sineSubstitutionIntegrand
  rw [deriv_sin_two]
  simp only [Pi.mul_apply]
  ring

private def averagePrimitive (x : ℝ) :=
  x / 2 - Real.sin (4 * x) / 8

private theorem averagePrimitive_hasDerivAt (x : ℝ) :
    HasDerivAt averagePrimitive (averageIntegrand x) x := by
  have hlin : HasDerivAt (fun y : ℝ => 4 * y) 4 x := by
    simpa using (hasDerivAt_id x).const_mul 4
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (4 * y))
      (4 * Real.cos (4 * x)) x := by
    convert (Real.hasDerivAt_sin (4 * x)).comp x hlin using 1 <;> ring
  unfold averagePrimitive
  have hd := ((hasDerivAt_id x).div_const 2).sub (hsin.div_const 8)
  convert hd using 1
  unfold averageIntegrand
  ring

private theorem primitive_decomposition_identity (x : ℝ) :
    primitive x =
      1 / 8 * averagePrimitive x + 1 / 16 * sinePrimitive x := by
  unfold primitive averagePrimitive sinePrimitive
  ring

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (originalIntegrand x) x := by
  rw [show primitive = fun y =>
    1 / 8 * averagePrimitive y + 1 / 16 * sinePrimitive y from
      funext primitive_decomposition_identity]
  have hd := ((averagePrimitive_hasDerivAt x).const_mul (1 / 8)).add
    ((sinePrimitive_hasDerivAt x).const_mul (1 / 16))
  convert hd using 1
  exact original_decomposition_identity x

private theorem eq_of_everywhere_hasDerivAt_zero
    (f : ℝ → ℝ) (hf : ∀ x, HasDerivAt f 0 x) (x y : ℝ) :
    f x = f y := by
  have hdiff : Differentiable ℝ f := fun z => (hf z).differentiableAt
  have hderiv : ∀ z, deriv f z = 0 := fun z => (hf z).deriv
  exact is_const_of_deriv_eq_zero hdiff hderiv x y

theorem gap1 :
    Antiderivatives originalIntegrand =
      ScaledFamily firstReducedIntegrand (1 / 4) := by
  apply antiderivatives_eq_scaled_of_pointwise
  · norm_num
  · intro x
    unfold originalIntegrand firstReducedIntegrand
    rw [Real.sin_two_mul]
    ring
theorem gap2 :
    ScaledFamily firstReducedIntegrand (1 / 4) =
      ScaledFamily secondReducedIntegrand (1 / 8) := by
  rw [← gap1]
  apply antiderivatives_eq_scaled_of_pointwise
  · norm_num
  · intro x
    unfold originalIntegrand secondReducedIntegrand
    rw [Real.sin_two_mul, Real.cos_two_mul]
    ring
theorem gap3 :
    Antiderivatives originalIntegrand =
      ScaledFamily secondReducedIntegrand (1 / 8) := by
  exact gap1.trans gap2
theorem gap4 :
    Antiderivatives originalIntegrand = DecompositionFamily := by
  ext F
  constructor
  · intro hF
    change ∀ x, HasDerivAt F (originalIntegrand x) x at hF
    change ∃ G, (∀ x, HasDerivAt G (averageIntegrand x) x) ∧
      ∃ H, (∀ x, HasDerivAt H (sineSubstitutionIntegrand x) x) ∧
        ∀ x, F x = 1 / 8 * G x + 1 / 16 * H x
    refine ⟨fun y => 8 * F y - 1 / 2 * sinePrimitive y, ?_,
      sinePrimitive, sinePrimitive_hasDerivAt, ?_⟩
    · intro x
      have hd := ((hF x).const_mul 8).sub
        ((sinePrimitive_hasDerivAt x).const_mul (1 / 2))
      convert hd using 1
      rw [original_decomposition_identity x]
      ring
    · intro x
      ring
  · rintro ⟨G, hG, H, hH, hF⟩
    change ∀ x, HasDerivAt G (averageIntegrand x) x at hG
    change ∀ x, HasDerivAt H (sineSubstitutionIntegrand x) x at hH
    rw [show F = fun y => 1 / 8 * G y + 1 / 16 * H y from funext hF]
    intro x
    have hd := ((hG x).const_mul (1 / 8)).add
      ((hH x).const_mul (1 / 16))
    convert hd using 1
    exact original_decomposition_identity x
theorem gap5 :
    DecompositionFamily = PrimitiveFamily := by
  rw [← gap4]
  ext F
  constructor
  · intro hF
    change ∀ x, HasDerivAt F (originalIntegrand x) x at hF
    change ∃ C : ℝ, ∀ x, F x = primitive x + C
    have hzero : ∀ x, HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x
      simpa using (hF x).sub (primitive_hasDerivAt x)
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have hc := eq_of_everywhere_hasDerivAt_zero
      (fun y => F y - primitive y) hzero x 0
    linarith
  · rintro ⟨C, hF⟩
    change ∀ x, HasDerivAt F (originalIntegrand x) x
    rw [show F = fun y => primitive y + C from funext hF]
    intro x
    exact (primitive_hasDerivAt x).add_const C
theorem gap6 :
    Antiderivatives originalIntegrand = PrimitiveFamily := by
  exact gap4.trans gap5

end
end ProofGap.Exercise1994
