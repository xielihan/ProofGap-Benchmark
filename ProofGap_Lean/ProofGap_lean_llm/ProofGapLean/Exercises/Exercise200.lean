import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise200

noncomputable section

def f (a b c x : ℝ) : ℝ := a + b * Real.rpow c x
def FitsData (a b c : ℝ) : Prop :=
  0 < c ∧ f a b c 0 = 15 ∧ f a b c 2 = 30 ∧ f a b c 4 = 90

/-- Exercise 200, gap 1; retain the positive exponential base. -/
theorem gap1 (a b c : ℝ) (hc : 0 < c) : f a b c 0 = a + b := by
  simp [f]

/-- Exercise 200, gap 2. -/
theorem gap2 (a b c : ℝ) (h : FitsData a b c) : a + b = 15 := by
  rw [← gap1 a b c h.1]
  exact h.2.1

/-- Exercise 200, gap 3. -/
theorem gap3 (a b c : ℝ) (h : FitsData a b c) : f a b c 0 = 15 := by
  exact h.2.1

/-- Exercise 200, gap 4. -/
theorem gap4 (a b c : ℝ) : f a b c 2 = a + b * c ^ 2 := by
  simp [f, Real.rpow_natCast]

/-- Exercise 200, gap 5. -/
theorem gap5 (a b c : ℝ) (h : FitsData a b c) : a + b * c ^ 2 = 30 := by
  rw [← gap4]
  exact h.2.2.1

/-- Exercise 200, gap 6. -/
theorem gap6 (a b c : ℝ) (h : FitsData a b c) : f a b c 2 = 30 := by
  exact h.2.2.1

/-- Exercise 200, gap 7. -/
theorem gap7 (a b c : ℝ) : f a b c 4 = a + b * c ^ 4 := by
  simp [f, Real.rpow_natCast]

/-- Exercise 200, gap 8. -/
theorem gap8 (a b c : ℝ) (h : FitsData a b c) : a + b * c ^ 4 = 90 := by
  rw [← gap7]
  exact h.2.2.2

/-- Exercise 200, gap 9. -/
theorem gap9 (a b c : ℝ) (h : FitsData a b c) : f a b c 4 = 90 := by
  exact h.2.2.2

/-- Exercise 200, gap 10. -/
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

/-- Exercise 200, gap 11. -/
theorem gap11 (a b c : ℝ) (h : FitsData a b c) : b = 5 := by
  have h₀ := gap2 a b c h
  have ha := gap10 a b c h
  linarith

/-- Exercise 200, gap 12; positivity rules out c=-2. -/
theorem gap12 (a b c : ℝ) (h : FitsData a b c) : c = 2 := by
  have hc := h.1
  have h₂ := gap5 a b c h
  have ha := gap10 a b c h
  have hb := gap11 a b c h
  nlinarith

/-- Exercise 200, gap 13. -/
theorem gap13 (a b c : ℝ) (h : FitsData a b c) : c ≠ -2 := by
  have hc := h.1
  linarith

/-- Exercise 200, gap 14. -/
theorem gap14 (a b c : ℝ) (h : FitsData a b c) :
    ∀ x, f a b c x = 10 + 5 * Real.rpow 2 x := by
  intro x
  rw [f, gap10 a b c h, gap11 a b c h, gap12 a b c h]

end

end ProofGap.Exercise200
