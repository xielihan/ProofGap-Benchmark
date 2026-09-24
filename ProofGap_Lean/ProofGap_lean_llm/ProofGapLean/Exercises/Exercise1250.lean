import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1250

noncomputable section

def f (x : ℝ) : ℝ := x ^ 3
def slope (x₁ x₂ : ℝ) : ℝ := (f x₂ - f x₁) / (x₂ - x₁)

theorem gap1 (ξ : ℝ) :
    deriv f ξ = 3 * ξ ^ 2 := by
  have hf : f = (id * id) * id := by
    funext x
    change x ^ 3 = (x * x) * x
    ring
  rw [hf]
  have h :=
    (((hasDerivAt_id ξ).mul (hasDerivAt_id ξ)).mul (hasDerivAt_id ξ))
  convert h.deriv using 1 <;> simp [id] <;> ring

theorem gap2 :
    (3 : ℝ) * 0 ^ 2 = 0 := by
  norm_num

theorem gap3 :
    deriv f 0 = 0 := by
  rw [gap1]
  exact gap2

theorem gap4 (x₁ x₂ : ℝ) (h₁ : x₁ < 0) (h₂ : 0 < x₂) :
    slope x₁ x₂ = (x₂ ^ 3 - x₁ ^ 3) / (x₂ - x₁) := by
  rfl

theorem gap5 (x₁ x₂ : ℝ) (h₁ : x₁ < 0) (h₂ : 0 < x₂) :
    (x₂ ^ 3 - x₁ ^ 3) / (x₂ - x₁) =
      x₂ ^ 2 + x₁ * x₂ + x₁ ^ 2 := by
  have hne : x₂ - x₁ ≠ 0 := by
    linarith
  apply (div_eq_iff hne).2
  ring

theorem gap6 (x₁ x₂ : ℝ) (h₁ : x₁ < 0) (h₂ : 0 < x₂) :
    slope x₁ x₂ = x₂ ^ 2 + x₁ * x₂ + x₁ ^ 2 := by
  calc
    slope x₁ x₂ = (x₂ ^ 3 - x₁ ^ 3) / (x₂ - x₁) := gap4 x₁ x₂ h₁ h₂
    _ = x₂ ^ 2 + x₁ * x₂ + x₁ ^ 2 := gap5 x₁ x₂ h₁ h₂

theorem gap7 (x₁ x₂ : ℝ) (h₁ : x₁ < 0) (h₂ : 0 < x₂) :
    x₂ ^ 2 + x₁ * x₂ + x₁ ^ 2 =
      x₂ ^ 2 + x₁ ^ 2 - |x₁| * |x₂| := by
  rw [abs_of_neg h₁, abs_of_pos h₂]
  ring

theorem gap8 (x₁ x₂ : ℝ) (h₁ : x₁ < 0) (h₂ : 0 < x₂) :
    x₂ ^ 2 + x₁ ^ 2 - |x₁| * |x₂| >
      x₂ ^ 2 + x₁ ^ 2 - 2 * |x₁| * |x₂| := by
  have hp : 0 < |x₁| * |x₂| :=
    mul_pos (abs_pos.mpr (ne_of_lt h₁)) (abs_pos.mpr (ne_of_gt h₂))
  nlinarith

theorem gap9 (x₁ x₂ : ℝ) :
    x₂ ^ 2 + x₁ ^ 2 - 2 * |x₁| * |x₂| =
      (|x₁| - |x₂|) ^ 2 := by
  rw [← sq_abs x₁, ← sq_abs x₂]
  ring

theorem gap10 (x₁ x₂ : ℝ) :
    (|x₁| - |x₂|) ^ 2 ≥ 0 := by
  exact sq_nonneg (|x₁| - |x₂|)

theorem gap11 (x₁ x₂ : ℝ) (h₁ : x₁ < 0) (h₂ : 0 < x₂) :
    x₂ ^ 2 + x₁ * x₂ + x₁ ^ 2 > 0 := by
  rw [gap7 x₁ x₂ h₁ h₂]
  have hstrict := gap8 x₁ x₂ h₁ h₂
  rw [gap9 x₁ x₂] at hstrict
  exact lt_of_le_of_lt (gap10 x₁ x₂) hstrict

theorem gap12 (x₁ x₂ : ℝ) (h₁ : x₁ < 0) (h₂ : 0 < x₂)
    (habs : |x₁| = |x₂|) :
    x₁ = -x₂ := by
  rw [abs_of_neg h₁, abs_of_pos h₂] at habs
  linarith

theorem gap13 (x₁ x₂ : ℝ) (h₁ : x₁ < 0) (h₂ : 0 < x₂)
    (habs : |x₁| = |x₂|) :
    x₂ ^ 2 + x₁ * x₂ + x₁ ^ 2 =
      x₂ ^ 2 - x₂ ^ 2 + x₂ ^ 2 := by
  rw [gap12 x₁ x₂ h₁ h₂ habs]
  ring

theorem gap14 (x₂ : ℝ) :
    x₂ ^ 2 - x₂ ^ 2 + x₂ ^ 2 = x₂ ^ 2 := by
  ring

theorem gap15 (x₂ : ℝ) (h₂ : 0 < x₂) :
    x₂ ^ 2 > 0 := by
  simpa [pow_two] using mul_pos h₂ h₂

theorem gap16 (x₁ x₂ : ℝ) (h₁ : x₁ < 0) (h₂ : 0 < x₂)
    (habs : |x₁| = |x₂|) :
    x₂ ^ 2 + x₁ * x₂ + x₁ ^ 2 > 0 := by
  exact gap11 x₁ x₂ h₁ h₂

theorem gap17 (x₁ x₂ : ℝ) (h₁ : x₁ < 0) (h₂ : 0 < x₂) :
    slope x₁ x₂ > 0 := by
  rw [gap6 x₁ x₂ h₁ h₂]
  exact gap11 x₁ x₂ h₁ h₂

theorem gap18 (x₁ x₂ : ℝ) (h₁ : x₁ < 0) (h₂ : 0 < x₂) :
    0 = deriv f 0 := by
  exact gap3.symm

theorem gap19 (x₁ x₂ : ℝ) (h₁ : x₁ < 0) (h₂ : 0 < x₂) :
    slope x₁ x₂ > deriv f 0 := by
  rw [gap3]
  exact gap17 x₁ x₂ h₁ h₂

theorem gap20 :
    ¬∃ x₁ x₂ : ℝ,
      x₁ ∈ Set.Ioo (-1 : ℝ) 1 ∧ x₂ ∈ Set.Ioo (-1 : ℝ) 1 ∧
      x₁ < 0 ∧ 0 < x₂ ∧ slope x₁ x₂ = deriv f 0 := by
  rintro ⟨x₁, x₂, hx₁, hx₂, h₁, h₂, heq⟩
  exact (ne_of_gt (gap19 x₁ x₂ h₁ h₂)) heq

theorem gap21 :
    ¬∀ ξ ∈ Set.Ioo (-1 : ℝ) 1,
      ∃ x₁ ∈ Set.Ioo (-1 : ℝ) 1, ∃ x₂ ∈ Set.Ioo (-1 : ℝ) 1,
        x₁ < ξ ∧ ξ < x₂ ∧ slope x₁ x₂ = deriv f ξ := by
  intro h
  obtain ⟨x₁, hx₁, x₂, hx₂, h₁, h₂, heq⟩ :=
    h 0 (by constructor <;> norm_num)
  exact (ne_of_gt (gap19 x₁ x₂ h₁ h₂)) heq

end

end ProofGap.Exercise1250
