import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1735

noncomputable section

def original (x : ℝ) : ℝ := 1 / ((x ^ 2 + 1) * (x ^ 2 + 2))
def partialFractions (x : ℝ) : ℝ := 1 / (x ^ 2 + 1) - 1 / (x ^ 2 + 2)
def primitive (x : ℝ) : ℝ :=
  Real.arctan x - (1 / Real.sqrt 2) * Real.arctan (x / Real.sqrt 2)
def Antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | Differentiable ℝ F ∧ ∀ x, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (partialFractions x) x := by
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsne : Real.sqrt 2 ≠ 0 := ne_of_gt hspos
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hden1 : 1 + x ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg x]
  have hden2 : x ^ 2 + 1 ≠ 0 := by
    nlinarith [sq_nonneg x]
  have hden3 : x ^ 2 + 2 ≠ 0 := by
    nlinarith [sq_nonneg x]
  have hscaled : 1 + (x / Real.sqrt 2) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (x / Real.sqrt 2)]
  have hd :=
    (Real.hasDerivAt_arctan x).sub
      (((Real.hasDerivAt_arctan (x / Real.sqrt 2)).comp x
        ((hasDerivAt_id x).div_const (Real.sqrt 2))).const_mul
          (1 / Real.sqrt 2))
  have hfun :
      primitive =
        Real.arctan - fun y : ℝ =>
          (1 / Real.sqrt 2) *
            (Real.arctan ∘ fun z : ℝ => id z / Real.sqrt 2) y := by
    funext y
    rfl
  rw [hfun]
  convert hd using 1
  unfold partialFractions
  field_simp [hsne, hden1, hden2, hden3, hscaled]
  rw [hsq]
  ring

private theorem exists_const_add_of_deriv_eq
    {F p : ℝ → ℝ} (hF : Differentiable ℝ F) (hp : Differentiable ℝ p)
    (hderiv : ∀ x, deriv F x = deriv p x) :
    ∃ C : ℝ, ∀ x, F x = p x + C := by
  let h : ℝ → ℝ := fun x => F x - p x
  have hd : Differentiable ℝ h := hF.sub hp
  have hz : ∀ x, deriv h x = 0 := by
    intro x
    have hsub : HasDerivAt h (deriv F x - deriv p x) x := by
      dsimp [h]
      exact (hF x).hasDerivAt.sub (hp x).hasDerivAt
    calc
      deriv h x = deriv F x - deriv p x := hsub.deriv
      _ = 0 := sub_eq_zero.mpr (hderiv x)
  refine ⟨F 0 - p 0, ?_⟩
  intro x
  have hc : h x = h 0 := is_const_of_deriv_eq_zero hd hz x 0
  dsimp [h] at hc
  linarith

theorem gap1 : Antiderivatives original = Antiderivatives partialFractions := by
  apply congrArg Antiderivatives
  funext x
  unfold original partialFractions
  have h1 : x ^ 2 + 1 ≠ 0 := by
    nlinarith [sq_nonneg x]
  have h2 : x ^ 2 + 2 ≠ 0 := by
    nlinarith [sq_nonneg x]
  field_simp [h1, h2] <;> ring

theorem gap2 : Antiderivatives partialFractions = PrimitiveFamily primitive := by
  ext F
  change
    (Differentiable ℝ F ∧ ∀ x, deriv F x = partialFractions x) ↔
      ∃ C : ℝ, ∀ x, F x = primitive x + C
  have hp : Differentiable ℝ primitive :=
    fun x => (primitive_hasDerivAt x).differentiableAt
  constructor
  · rintro ⟨hF, hF'⟩
    apply exists_const_add_of_deriv_eq hF hp
    intro x
    calc
      deriv F x = partialFractions x := hF' x
      _ = deriv primitive x := (primitive_hasDerivAt x).deriv.symm
  · rintro ⟨C, hC⟩
    have hFC : F = fun x => primitive x + C := funext hC
    subst F
    constructor
    · exact fun x => ((primitive_hasDerivAt x).add_const C).differentiableAt
    · intro x
      exact ((primitive_hasDerivAt x).add_const C).deriv

theorem gap3 : Antiderivatives original = PrimitiveFamily primitive := by
  exact gap1.trans gap2

end
end ProofGap.Exercise1735
