import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1742

noncomputable section

def original (x : ℝ) : ℝ := Real.cos x ^ 2
def reduced (x : ℝ) : ℝ := (1 + Real.cos (2 * x)) / 2
def primitive (x : ℝ) : ℝ := x / 2 + (1 / 4) * Real.sin (2 * x)
def Antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | Differentiable ℝ F ∧ ∀ x, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}

private theorem original_eq_reduced : original = reduced := by
  funext x
  unfold original reduced
  rw [Real.cos_two_mul]
  ring

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (reduced x) x := by
  unfold primitive reduced
  convert
    ((hasDerivAt_id x).div_const 2).add
      (((Real.hasDerivAt_sin (2 * x)).comp x
        ((hasDerivAt_id x).const_mul 2)).const_mul (1 / 4)) using 1 <;>
    ring

theorem gap1 : Antiderivatives original = Antiderivatives reduced := by
  rw [original_eq_reduced]

theorem gap2 : Antiderivatives reduced = PrimitiveFamily primitive := by
  ext F
  change
    (Differentiable ℝ F ∧ ∀ x, deriv F x = reduced x) ↔
      ∃ C : ℝ, ∀ x, F x = primitive x + C
  constructor
  · rintro ⟨hF, hFd⟩
    have hp : Differentiable ℝ primitive :=
      fun x => (primitive_hasDerivAt x).differentiableAt
    have hdiff : Differentiable ℝ (fun x => F x - primitive x) :=
      hF.sub hp
    have hderiv : ∀ x, deriv (fun y => F y - primitive y) x = 0 := by
      intro x
      simpa only [hFd x, sub_self] using
        (((hF x).hasDerivAt.sub (primitive_hasDerivAt x)).deriv)
    have hmono : Monotone (fun x => F x - primitive x) :=
      monotone_of_deriv_nonneg hdiff (fun x => by simp only [hderiv x, le_refl])
    have hanti : Antitone (fun x => F x - primitive x) :=
      antitone_of_deriv_nonpos hdiff (fun x => by simp only [hderiv x, le_refl])
    have hconst : ∀ x, F x - primitive x = F 0 - primitive 0 := by
      intro x
      rcases le_total x 0 with hx | hx
      · exact le_antisymm (hmono hx) (hanti hx)
      · exact le_antisymm (hanti hx) (hmono hx)
    refine ⟨F 0 - primitive 0, fun x => ?_⟩
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp (hconst x))
  · rintro ⟨C, hC⟩
    have hEq : F = fun x => primitive x + C := funext hC
    subst F
    have hp : Differentiable ℝ primitive :=
      fun x => (primitive_hasDerivAt x).differentiableAt
    constructor
    · exact hp.add (differentiable_const C)
    · intro x
      exact ((primitive_hasDerivAt x).add_const C).deriv

theorem gap3 : Antiderivatives original = PrimitiveFamily primitive := by
  exact gap1.trans gap2

end
end ProofGap.Exercise1742
