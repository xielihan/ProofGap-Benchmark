import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1996

noncomputable section

def originalIntegrand (x : ℝ) := Real.sin x ^ 5 * Real.cos x ^ 5
def doubleAngleIntegrand (x : ℝ) := 1 / 32 * Real.sin (2 * x) ^ 5
def cosineSubstitutionIntegrand (x : ℝ) :=
  (1 - Real.cos (2 * x) ^ 2) ^ 2 *
    deriv (fun y : ℝ => Real.cos (2 * y)) x
def primitive (x : ℝ) :=
  -1 / 64 * Real.cos (2 * x) +
    1 / 96 * Real.cos (2 * x) ^ 3 -
    1 / 320 * Real.cos (2 * x) ^ 5
def Antiderivatives (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x, HasDerivAt F (f x) x}
def ScaledFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives cosineSubstitutionIntegrand,
    ∀ x, F x = -1 / 64 * G x}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = primitive x + C}

private theorem originalIntegrand_eq_doubleAngleIntegrand (x : ℝ) :
    originalIntegrand x = doubleAngleIntegrand x := by
  rw [originalIntegrand, doubleAngleIntegrand, Real.sin_two_mul]
  ring

private theorem hasDerivAt_cos_two (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.cos (2 * y))
      (-Real.sin (2 * x) * 2) x := by
  simpa only [Function.comp_def, id_eq, mul_one] using
    (Real.hasDerivAt_cos (2 * x)).comp x
      ((hasDerivAt_id x).const_mul 2)

private theorem cosineSubstitutionIntegrand_eq_neg64_doubleAngleIntegrand
    (x : ℝ) :
    cosineSubstitutionIntegrand x = -64 * doubleAngleIntegrand x := by
  rw [cosineSubstitutionIntegrand, doubleAngleIntegrand,
    (hasDerivAt_cos_two x).deriv]
  have hs : Real.sin (2 * x) ^ 2 = 1 - Real.cos (2 * x) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (2 * x)]
  rw [← hs]
  ring

private theorem scaledCosineSubstitutionIntegrand_eq_doubleAngleIntegrand
    (x : ℝ) :
    -1 / 64 * cosineSubstitutionIntegrand x = doubleAngleIntegrand x := by
  rw [cosineSubstitutionIntegrand_eq_neg64_doubleAngleIntegrand]
  ring

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (doubleAngleIntegrand x) x := by
  have hc := hasDerivAt_cos_two x
  have hs : Real.sin (2 * x) ^ 2 = 1 - Real.cos (2 * x) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (2 * x)]
  have hs5 :
      Real.sin (2 * x) ^ 5 =
        Real.sin (2 * x) * (1 - Real.cos (2 * x) ^ 2) ^ 2 := by
    calc
      Real.sin (2 * x) ^ 5 =
          Real.sin (2 * x) * (Real.sin (2 * x) ^ 2) ^ 2 := by ring
      _ = Real.sin (2 * x) * (1 - Real.cos (2 * x) ^ 2) ^ 2 := by rw [hs]
  have hp :=
    (((hc.const_mul (-1 / 64)).add
      ((hc.pow 3).const_mul (1 / 96))).sub
        ((hc.pow 5).const_mul (1 / 320)))
  convert hp using 1
  rw [doubleAngleIntegrand, hs5]
  ring

theorem gap1 :
    Antiderivatives originalIntegrand =
      Antiderivatives doubleAngleIntegrand := by
  ext F
  constructor <;> intro hF <;>
    change ∀ x, HasDerivAt F _ x at hF ⊢
  · intro x
    simpa only [originalIntegrand_eq_doubleAngleIntegrand] using hF x
  · intro x
    simpa only [originalIntegrand_eq_doubleAngleIntegrand] using hF x
theorem gap2 :
    Antiderivatives doubleAngleIntegrand = ScaledFamily := by
  ext F
  constructor
  · intro hF
    change ∀ x, HasDerivAt F (doubleAngleIntegrand x) x at hF
    change ∃ G ∈ Antiderivatives cosineSubstitutionIntegrand,
      ∀ x, F x = -1 / 64 * G x
    refine ⟨fun x => -64 * F x, ?_, ?_⟩
    · change ∀ x, HasDerivAt (fun y => -64 * F y)
        (cosineSubstitutionIntegrand x) x
      intro x
      simpa only [cosineSubstitutionIntegrand_eq_neg64_doubleAngleIntegrand] using
        (hF x).const_mul (-64)
    · intro x
      ring
  · rintro ⟨G, hG, hFG⟩
    change ∀ x, HasDerivAt G (cosineSubstitutionIntegrand x) x at hG
    have hfun : F = fun x => -1 / 64 * G x := funext hFG
    rw [hfun]
    change ∀ x, HasDerivAt (fun y => -1 / 64 * G y)
      (doubleAngleIntegrand x) x
    intro x
    convert (hG x).const_mul (-1 / 64) using 1
    exact (scaledCosineSubstitutionIntegrand_eq_doubleAngleIntegrand x).symm
theorem gap3 :
    Antiderivatives originalIntegrand = ScaledFamily := by
  exact gap1.trans gap2
theorem gap4 :
    Antiderivatives originalIntegrand = PrimitiveFamily := by
  ext F
  constructor
  · intro hF
    change ∀ x, HasDerivAt F (originalIntegrand x) x at hF
    change ∃ C : ℝ, ∀ x, F x = primitive x + C
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have hderiv : ∀ y, HasDerivAt (fun z => F z - primitive z) 0 y := by
      intro y
      simpa only [originalIntegrand_eq_doubleAngleIntegrand, sub_self] using
        (hF y).sub (primitive_hasDerivAt y)
    have hdiff : Differentiable ℝ (fun z : ℝ => F z - primitive z) := by
      intro y
      exact (hderiv y).differentiableAt
    have hzero : ∀ y, deriv (fun z : ℝ => F z - primitive z) y = 0 := by
      intro y
      exact (hderiv y).deriv
    have hx : F x - primitive x = F 0 - primitive 0 :=
      is_const_of_deriv_eq_zero hdiff hzero x 0
    linarith
  · rintro ⟨C, hFC⟩
    have hfun : F = fun x => primitive x + C := funext hFC
    rw [hfun]
    change ∀ x, HasDerivAt (fun y => primitive y + C)
      (originalIntegrand x) x
    intro x
    simpa only [originalIntegrand_eq_doubleAngleIntegrand] using
      (primitive_hasDerivAt x).add_const C

end
end ProofGap.Exercise1996
