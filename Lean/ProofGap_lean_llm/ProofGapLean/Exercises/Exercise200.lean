import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise200

noncomputable section

def f (a b c x : ℝ) : ℝ := a + b * Real.rpow c x
def FitsData (a b c : ℝ) : Prop :=
  0 < c ∧ f a b c 0 = 15 ∧ f a b c 2 = 30 ∧ f a b c 4 = 90

/-- Source: `proof_gap/exercise_200/1.txt`; retain the positive exponential base. -/
theorem gap1 (a b c : ℝ) (hc : 0 < c) : f a b c 0 = a + b := by
  simp [f]

/-- Source: `proof_gap/exercise_200/2.txt`. -/
theorem gap2 (a b c : ℝ) (h : FitsData a b c) : a + b = 15 := by
  rw [← gap1 a b c h.1]
  exact h.2.1

/-- Source: `proof_gap/exercise_200/3.txt`. -/
theorem gap3 (a b c : ℝ) (h : FitsData a b c) : f a b c 0 = 15 := by
  exact h.2.1

/-- Source: `proof_gap/exercise_200/4.txt`. -/
theorem gap4 (a b c : ℝ) : f a b c 2 = a + b * c ^ 2 := by
  simp [f, Real.rpow_natCast]

/-- Source: `proof_gap/exercise_200/5.txt`. -/
theorem gap5 (a b c : ℝ) (h : FitsData a b c) : a + b * c ^ 2 = 30 := by
  rw [← gap4]
  exact h.2.2.1

/-- Source: `proof_gap/exercise_200/6.txt`. -/
theorem gap6 (a b c : ℝ) (h : FitsData a b c) : f a b c 2 = 30 := by
  exact h.2.2.1

/-- Source: `proof_gap/exercise_200/7.txt`. -/
theorem gap7 (a b c : ℝ) : f a b c 4 = a + b * c ^ 4 := by
  simp [f, Real.rpow_natCast]

/-- Source: `proof_gap/exercise_200/8.txt`. -/
theorem gap8 (a b c : ℝ) (h : FitsData a b c) : a + b * c ^ 4 = 90 := by
  rw [← gap7]
  exact h.2.2.2

/-- Source: `proof_gap/exercise_200/9.txt`. -/
theorem gap9 (a b c : ℝ) (h : FitsData a b c) : f a b c 4 = 90 := by
  exact h.2.2.2

/-- Source: `proof_gap/exercise_200/10.txt`. -/
theorem gap10 (a b c : ℝ) (h : FitsData a b c) : a = 10 := by
  have h₀ := gap2 a b c h
  have h₂ := gap5 a b c h
  have h₄ := gap8 a b c h
  have hd₁ : b * (c ^ 2 - 1) = 15 := by
    nlinarith
  have hd₂ : b * c ^ 2 * (c ^ 2 - 1) = 60 := by
    nlinarith
  have hmul : b * c ^ 2 * (c ^ 2 - 1) = 15 * c ^ 2 := by
    calc
      b * c ^ 2 * (c ^ 2 - 1) =
          c ^ 2 * (b * (c ^ 2 - 1)) := by ring
      _ = c ^ 2 * 15 := by rw [hd₁]
      _ = 15 * c ^ 2 := by ring
  have hc₂ : c ^ 2 = 4 := by
    linarith
  nlinarith

/-- Source: `proof_gap/exercise_200/11.txt`. -/
theorem gap11 (a b c : ℝ) (h : FitsData a b c) : b = 5 := by
  have h₀ := gap2 a b c h
  have ha := gap10 a b c h
  linarith

/-- Source: `proof_gap/exercise_200/12.txt`; positivity rules out c=-2. -/
theorem gap12 (a b c : ℝ) (h : FitsData a b c) : c = 2 := by
  have hc := h.1
  have h₂ := gap5 a b c h
  have ha := gap10 a b c h
  have hb := gap11 a b c h
  nlinarith

/-- Source: `proof_gap/exercise_200/13.txt`. -/
theorem gap13 (a b c : ℝ) (h : FitsData a b c) : c ≠ -2 := by
  have hc := h.1
  linarith

/-- Source: `proof_gap/exercise_200/14.txt`. -/
theorem gap14 (a b c : ℝ) (h : FitsData a b c) :
    ∀ x, f a b c x = 10 + 5 * Real.rpow 2 x := by
  intro x
  rw [f, gap10 a b c h, gap11 a b c h, gap12 a b c h]

end

end ProofGap.Exercise200
