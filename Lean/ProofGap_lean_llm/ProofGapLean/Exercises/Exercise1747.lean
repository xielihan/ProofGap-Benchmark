import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise1747

noncomputable section

def original (x : ℝ) : ℝ := Real.sin x ^ 3
def substituted (x : ℝ) : ℝ :=
  (Real.cos x ^ 2 - 1) * (-Real.sin x)
def primitive (x : ℝ) : ℝ := (1 / 3) * Real.cos x ^ 3 - Real.cos x
def Antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | Differentiable ℝ F ∧ ∀ x, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (substituted x) x := by
  unfold primitive substituted
  convert
    (((Real.hasDerivAt_cos x).pow 3).const_mul (1 / 3)).sub
      (Real.hasDerivAt_cos x) using 1 <;> ring

theorem gap1 : Antiderivatives original = Antiderivatives substituted := by
  apply congrArg Antiderivatives
  funext x
  unfold original substituted
  rw [← Real.sin_sq_add_cos_sq x]
  ring

theorem gap2 : Antiderivatives substituted = PrimitiveFamily primitive := by
  ext F
  change
    (Differentiable ℝ F ∧ ∀ x, deriv F x = substituted x) ↔
      ∃ C : ℝ, ∀ x, F x = primitive x + C
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    have hpDiff : Differentiable ℝ primitive :=
      fun x => (primitive_hasDerivAt x).differentiableAt
    let h : ℝ → ℝ := fun x => F x - primitive x
    have hdiff : Differentiable ℝ h := hFdiff.sub hpDiff
    have hderiv : ∀ x, deriv h x = 0 := by
      intro x
      change deriv (fun y => F y - primitive y) x = 0
      calc
        deriv (fun y => F y - primitive y) x =
            deriv F x - deriv primitive x :=
          deriv_sub (hFdiff x) (hpDiff x)
        _ = 0 := by
          rw [hFderiv x, (primitive_hasDerivAt x).deriv]
          ring
    have hmono : Monotone h :=
      monotone_of_deriv_nonneg hdiff (fun x => by rw [hderiv x])
    have hanti : Antitone h :=
      antitone_of_deriv_nonpos hdiff (fun x => by rw [hderiv x])
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have hx : h x = h 0 := by
      rcases le_total x 0 with hx0 | h0x
      · exact le_antisymm (hmono hx0) (hanti hx0)
      · exact le_antisymm (hanti h0x) (hmono h0x)
    dsimp [h] at hx
    linarith
  · rintro ⟨C, hC⟩
    have hEq : F = fun x => primitive x + C := funext hC
    rw [hEq]
    constructor
    · exact fun x => ((primitive_hasDerivAt x).add_const C).differentiableAt
    · intro x
      exact ((primitive_hasDerivAt x).add_const C).deriv

theorem gap3 : Antiderivatives original = PrimitiveFamily primitive := by
  exact gap1.trans gap2

end
end ProofGap.Exercise1747
