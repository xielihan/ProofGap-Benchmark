import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1995

noncomputable section

def originalIntegrand (x : ℝ) := Real.sin x ^ 4 * Real.cos x ^ 5
def substitutedIntegrand (x : ℝ) :=
  Real.sin x ^ 4 * (1 - Real.sin x ^ 2) ^ 2 * deriv Real.sin x
def primitive (x : ℝ) :=
  1 / 5 * Real.sin x ^ 5 -
    2 / 7 * Real.sin x ^ 7 +
    1 / 9 * Real.sin x ^ 9
def Antiderivatives (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x, HasDerivAt F (f x) x}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = primitive x + C}

private theorem integrands_eq (x : ℝ) :
    originalIntegrand x = substitutedIntegrand x := by
  unfold originalIntegrand substitutedIntegrand
  rw [(Real.hasDerivAt_sin x).deriv]
  have hcos : 1 - Real.sin x ^ 2 = Real.cos x ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq x]
  rw [hcos]
  ring

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (substitutedIntegrand x) x := by
  convert
    ((((Real.hasDerivAt_sin x).pow 5).const_mul (1 / 5 : ℝ)).sub
      (((Real.hasDerivAt_sin x).pow 7).const_mul (2 / 7 : ℝ))).add
      (((Real.hasDerivAt_sin x).pow 9).const_mul (1 / 9 : ℝ))
    using 1
  unfold substitutedIntegrand
  rw [(Real.hasDerivAt_sin x).deriv]
  norm_num
  ring

private theorem differ_by_const {f F G : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F (f x) x)
    (hG : ∀ x, HasDerivAt G (f x) x) :
    ∃ C : ℝ, ∀ x, F x = G x + C := by
  let H : ℝ → ℝ := fun x => F x - G x
  have hH : ∀ x, HasDerivAt H 0 x := by
    intro x
    convert (hF x).sub (hG x) using 1
    ring
  have hdiff : Differentiable ℝ H := fun x => (hH x).differentiableAt
  have hderiv : ∀ x, deriv H x = 0 := fun x => (hH x).deriv
  refine ⟨H 0, ?_⟩
  intro x
  have hx : H x = H 0 :=
    is_const_of_deriv_eq_zero hdiff hderiv x 0
  dsimp [H] at hx ⊢
  linarith

theorem gap1 :
    Antiderivatives originalIntegrand =
      Antiderivatives substitutedIntegrand := by
  ext F
  constructor
  · intro h x
    rw [← integrands_eq x]
    exact h x
  · intro h x
    rw [integrands_eq x]
    exact h x
theorem gap2 :
    Antiderivatives substitutedIntegrand = PrimitiveFamily := by
  ext F
  constructor
  · intro h
    exact differ_by_const h primitive_hasDerivAt
  · rintro ⟨C, hC⟩
    intro x
    have hfun : F = fun y => primitive y + C := funext hC
    rw [hfun]
    exact (primitive_hasDerivAt x).add_const C
theorem gap3 :
    Antiderivatives originalIntegrand = PrimitiveFamily := by
  calc
    Antiderivatives originalIntegrand =
        Antiderivatives substitutedIntegrand := gap1
    _ = PrimitiveFamily := gap2

end
end ProofGap.Exercise1995
