import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1991

noncomputable section

def originalIntegrand (x : ℝ) := Real.cos x ^ 5
def factoredIntegrand (x : ℝ) := Real.cos x ^ 4 * Real.cos x
def substitutedIntegrand (x : ℝ) :=
  (1 - Real.sin x ^ 2) ^ 2 * deriv Real.sin x
def expandedIntegrand (x : ℝ) :=
  (1 - 2 * Real.sin x ^ 2 + Real.sin x ^ 4) * deriv Real.sin x
def primitive (x : ℝ) :=
  Real.sin x - 2 / 3 * Real.sin x ^ 3 + 1 / 5 * Real.sin x ^ 5
def Antiderivatives (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x, HasDerivAt F (f x) x}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = primitive x + C}

theorem gap1 :
    Antiderivatives originalIntegrand =
      Antiderivatives factoredIntegrand := by
  apply congrArg Antiderivatives
  funext x
  simp [originalIntegrand, factoredIntegrand, pow_succ]
theorem gap2 :
    Antiderivatives factoredIntegrand =
      Antiderivatives substitutedIntegrand := by
  apply congrArg Antiderivatives
  funext x
  unfold factoredIntegrand substitutedIntegrand
  rw [(Real.hasDerivAt_sin x).deriv]
  have htrig := Real.sin_sq_add_cos_sq x
  have hcos : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
    linarith
  calc
    Real.cos x ^ 4 * Real.cos x = (Real.cos x ^ 2) ^ 2 * Real.cos x := by ring
    _ = (1 - Real.sin x ^ 2) ^ 2 * Real.cos x := by rw [hcos]
theorem gap3 :
    Antiderivatives originalIntegrand =
      Antiderivatives substitutedIntegrand := by
  exact gap1.trans gap2
theorem gap4 :
    Antiderivatives originalIntegrand =
      Antiderivatives expandedIntegrand := by
  calc
    Antiderivatives originalIntegrand = Antiderivatives substitutedIntegrand := gap3
    _ = Antiderivatives expandedIntegrand := by
      apply congrArg Antiderivatives
      funext x
      unfold substitutedIntegrand expandedIntegrand
      ring
theorem gap5 :
    Antiderivatives expandedIntegrand = PrimitiveFamily := by
  have hp : ∀ x, HasDerivAt primitive (expandedIntegrand x) x := by
    intro x
    have hs := Real.hasDerivAt_sin x
    unfold primitive expandedIntegrand
    rw [hs.deriv]
    convert (hs.sub ((hs.pow 3).const_mul (2 / 3))).add
      ((hs.pow 5).const_mul (1 / 5)) using 1 <;> norm_num <;> ring
  ext F
  constructor
  · intro hF
    change ∀ x, HasDerivAt F (expandedIntegrand x) x at hF
    let D : ℝ → ℝ := fun x => F x - primitive x
    have hD : ∀ x, HasDerivAt D 0 x := by
      intro x
      dsimp [D]
      convert (hF x).sub (hp x) using 1
      ring
    have hDdiff : Differentiable ℝ D := fun x => (hD x).differentiableAt
    have hDderiv : ∀ x, deriv D x = 0 := fun x => (hD x).deriv
    refine ⟨D 0, ?_⟩
    intro x
    have hx : D x = D 0 :=
      is_const_of_deriv_eq_zero hDdiff hDderiv x 0
    dsimp [D] at hx ⊢
    linarith
  · rintro ⟨C, hC⟩
    change ∀ x, HasDerivAt F (expandedIntegrand x) x
    have hEq : F = fun x => primitive x + C := funext hC
    rw [hEq]
    intro x
    simpa [add_comm] using (hp x).const_add C
theorem gap6 :
    Antiderivatives originalIntegrand = PrimitiveFamily := by
  exact gap4.trans gap5

end
end ProofGap.Exercise1991
