import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace ProofGap.Exercise2001

noncomputable section

def branch : Set ℝ := {x | Real.sin x ≠ 0 ∧ Real.cos x ≠ 0}
def cot (x : ℝ) := Real.cos x / Real.sin x
def csc (x : ℝ) := 1 / Real.sin x
def originalIntegrand (x : ℝ) :=
  1 / (Real.sin x ^ 4 * Real.cos x ^ 4)
def doubleAngleIntegrand (x : ℝ) := 1 / Real.sin (2 * x) ^ 4
def cotangentIntegrand (x : ℝ) :=
  csc (2 * x) ^ 2 * deriv (fun y : ℝ => cot (2 * y)) x
def polynomialCotangentIntegrand (x : ℝ) :=
  (1 + cot (2 * x) ^ 2) * deriv (fun y : ℝ => cot (2 * y)) x
def primitive (x : ℝ) :=
  -8 * cot (2 * x) - 8 / 3 * cot (2 * x) ^ 3
def Antiderivatives (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def ScaledFamily (f : ℝ → ℝ) (c : ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives f, ∀ x ∈ branch, F x = c * G x}
def ComponentwisePrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ K : ℝ → ℝ,
    (∀ x ∈ branch, F x = primitive x + K x) ∧
    (∀ x ∈ branch, HasDerivAt K 0 x)}

private lemma hasDerivAt_of_eq_on_branch
    {f g : ℝ → ℝ} {f' x : ℝ} (hx : x ∈ branch)
    (hfg : ∀ y ∈ branch, f y = g y)
    (hg : HasDerivAt g f' x) : HasDerivAt f f' x := by
  apply hg.congr_of_eventuallyEq
  filter_upwards
    [Real.continuous_sin.continuousAt.eventually_ne hx.1,
      Real.continuous_cos.continuousAt.eventually_ne hx.2] with y hsin hcos
  exact hfg y ⟨hsin, hcos⟩

private lemma sin_two_ne_zero (x : ℝ) (hx : x ∈ branch) :
    Real.sin (2 * x) ≠ 0 := by
  rw [Real.sin_two_mul]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hx.1) hx.2

private lemma hasDerivAt_cot (x : ℝ) (hx : Real.sin x ≠ 0) :
    HasDerivAt cot (-1 / Real.sin x ^ 2) x := by
  unfold cot
  apply ((Real.hasDerivAt_cos x).div (Real.hasDerivAt_sin x) hx).congr_deriv
  field_simp [hx]
  nlinarith [Real.sin_sq_add_cos_sq x]

private lemma hasDerivAt_cot_two (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y : ℝ => cot (2 * y))
      (-2 / Real.sin (2 * x) ^ 2) x := by
  have hinner :
      HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    convert (hasDerivAt_id x).const_mul 2 using 1 <;> ring
  have h :=
    (hasDerivAt_cot (2 * x) (sin_two_ne_zero x hx)).comp x hinner
  convert h using 1 <;> ring

private lemma original_eq_sixteen_double (x : ℝ) (hx : x ∈ branch) :
    originalIntegrand x = 16 * doubleAngleIntegrand x := by
  have hs := hx.1
  have hc := hx.2
  unfold originalIntegrand doubleAngleIntegrand
  rw [Real.sin_two_mul]
  field_simp [hs, hc]
  ring

private lemma cotangent_eq_neg_two_double (x : ℝ) (hx : x ∈ branch) :
    cotangentIntegrand x = -2 * doubleAngleIntegrand x := by
  have hs2 := sin_two_ne_zero x hx
  unfold cotangentIntegrand csc doubleAngleIntegrand
  rw [(hasDerivAt_cot_two x hx).deriv]
  field_simp [hs2]

private lemma csc_sq_eq_one_add_cot_sq (x : ℝ) (hx : Real.sin x ≠ 0) :
    csc x ^ 2 = 1 + cot x ^ 2 := by
  unfold csc cot
  field_simp [hx]
  nlinarith [Real.sin_sq_add_cos_sq x]

private lemma polynomial_eq_cotangent (x : ℝ) (hx : x ∈ branch) :
    polynomialCotangentIntegrand x = cotangentIntegrand x := by
  unfold polynomialCotangentIntegrand cotangentIntegrand
  rw [csc_sq_eq_one_add_cot_sq (2 * x) (sin_two_ne_zero x hx)]

private lemma hasDerivAt_primitive (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (-8 * polynomialCotangentIntegrand x) x := by
  have hc := hasDerivAt_cot_two x hx
  have h :=
    (hc.const_mul (-8)).sub
      ((hc.pow 3).const_mul (8 / 3))
  unfold primitive
  apply h.congr_deriv
  unfold polynomialCotangentIntegrand
  rw [hc.deriv]
  ring

private theorem antiderivatives_eq_scaled
    (f g : ℝ → ℝ) (c : ℝ) (hc : c ≠ 0)
    (hfg : ∀ x ∈ branch, f x = c * g x) :
    Antiderivatives f = ScaledFamily g c := by
  ext F
  constructor
  · intro hF
    refine ⟨fun y => F y / c, ?_, ?_⟩
    · intro x hx
      convert (hF x hx).div_const c using 1
      rw [hfg x hx]
      field_simp [hc]
    · intro x hx
      field_simp [hc]
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    apply hasDerivAt_of_eq_on_branch
      (f := F) (g := fun y => c * G y) hx hFG
    apply ((hG x hx).const_mul c).congr_deriv
    rw [hfg x hx]

theorem gap1 :
    Antiderivatives originalIntegrand =
      ScaledFamily doubleAngleIntegrand 16 := by
  exact antiderivatives_eq_scaled originalIntegrand doubleAngleIntegrand 16
    (by norm_num) original_eq_sixteen_double
theorem gap2 :
    ScaledFamily doubleAngleIntegrand 16 =
      ScaledFamily cotangentIntegrand (-8) := by
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩
    refine ⟨fun y => -2 * G y, ?_, ?_⟩
    · intro x hx
      apply ((hG x hx).const_mul (-2)).congr_deriv
      rw [cotangent_eq_neg_two_double x hx]
    · intro x hx
      rw [hFG x hx]
      ring
  · rintro ⟨H, hH, hFH⟩
    refine ⟨fun y => -(1 / 2 : ℝ) * H y, ?_, ?_⟩
    · intro x hx
      apply ((hH x hx).const_mul (-(1 / 2 : ℝ))).congr_deriv
      rw [cotangent_eq_neg_two_double x hx]
      ring
    · intro x hx
      rw [hFH x hx]
      ring
theorem gap3 :
    Antiderivatives originalIntegrand =
      ScaledFamily cotangentIntegrand (-8) := by
  rw [gap1, gap2]
theorem gap4 :
    Antiderivatives originalIntegrand =
      ScaledFamily polynomialCotangentIntegrand (-8) := by
  rw [gap3]
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩
    refine ⟨G, ?_, hFG⟩
    intro x hx
    rw [polynomial_eq_cotangent x hx]
    exact hG x hx
  · rintro ⟨G, hG, hFG⟩
    refine ⟨G, ?_, hFG⟩
    intro x hx
    rw [← polynomial_eq_cotangent x hx]
    exact hG x hx
theorem gap5 :
    ScaledFamily polynomialCotangentIntegrand (-8) =
      ComponentwisePrimitiveFamily := by
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩
    refine ⟨fun y => -8 * G y - primitive y, ?_, ?_⟩
    · intro x hx
      rw [hFG x hx]
      ring
    · intro x hx
      have h :=
        ((hG x hx).const_mul (-8)).sub (hasDerivAt_primitive x hx)
      convert h using 1 <;> ring
  · rintro ⟨K, hFK, hK⟩
    refine ⟨fun y => -(primitive y + K y) / 8, ?_, ?_⟩
    · intro x hx
      have h :=
        ((hasDerivAt_primitive x hx).add (hK x hx)).neg.div_const 8
      convert h using 1 <;> ring
    · intro x hx
      rw [hFK x hx]
      ring
theorem gap6 :
    Antiderivatives originalIntegrand =
      ComponentwisePrimitiveFamily := by
  rw [gap4, gap5]

end
end ProofGap.Exercise2001
