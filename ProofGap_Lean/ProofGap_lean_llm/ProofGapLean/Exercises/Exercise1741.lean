import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1741

noncomputable section

def original (x : ℝ) : ℝ := Real.sin x ^ 2
def reduced (x : ℝ) : ℝ := (1 - Real.cos (2 * x)) / 2
def primitive (x : ℝ) : ℝ := x / 2 - (1 / 4) * Real.sin (2 * x)
def Antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | Differentiable ℝ F ∧ ∀ x, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}

theorem gap1 : Antiderivatives original = Antiderivatives reduced := by
  apply congrArg Antiderivatives
  funext x
  unfold original reduced
  rw [Real.cos_two_mul, Real.sin_sq]
  ring

theorem gap2 : Antiderivatives reduced = PrimitiveFamily primitive := by
  have hprimitive (x : ℝ) : HasDerivAt primitive (reduced x) x := by
    unfold primitive reduced
    convert
      ((hasDerivAt_id x).div_const 2).sub
        (((Real.hasDerivAt_sin (2 * x)).comp x
          ((hasDerivAt_id x).const_mul 2)).const_mul (1 / 4))
      using 1 <;> ring
  ext F
  change
    (Differentiable ℝ F ∧ ∀ x, deriv F x = reduced x) ↔
      ∃ C : ℝ, ∀ x, F x = primitive x + C
  constructor
  · rintro ⟨hF, hdF⟩
    have hzero (x : ℝ) :
        HasDerivAt (fun y => F y - primitive y) 0 x := by
      simpa [hdF x] using (hF x).hasDerivAt.sub (hprimitive x)
    have hdiff : Differentiable ℝ (fun y => F y - primitive y) :=
      fun x => (hzero x).differentiableAt
    have hderiv (x : ℝ) : deriv (fun y => F y - primitive y) x = 0 :=
      (hzero x).deriv
    have hmono : Monotone (fun y => F y - primitive y) := by
      apply monotone_of_deriv_nonneg hdiff
      intro x
      rw [hderiv x]
    have hanti : Antitone (fun y => F y - primitive y) := by
      apply antitone_of_deriv_nonpos hdiff
      intro x
      rw [hderiv x]
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have hc : F x - primitive x = F 0 - primitive 0 := by
      rcases le_total x 0 with hx | hx
      · exact le_antisymm (hmono hx) (hanti hx)
      · exact le_antisymm (hanti hx) (hmono hx)
    calc
      F x = primitive x + (F x - primitive x) := by ring
      _ = primitive x + (F 0 - primitive 0) := by rw [hc]
  · rintro ⟨C, hC⟩
    have hEq : F = fun x => primitive x + C := funext hC
    refine ⟨?_, ?_⟩
    · rw [hEq]
      exact fun x => ((hprimitive x).add_const C).differentiableAt
    · intro x
      rw [hEq]
      exact ((hprimitive x).add_const C).deriv

theorem gap3 : Antiderivatives original = PrimitiveFamily primitive := by
  calc
    Antiderivatives original = Antiderivatives reduced := gap1
    _ = PrimitiveFamily primitive := gap2

end
end ProofGap.Exercise1741
