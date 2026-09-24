import ProofGapLean.Prelude.Core
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise159

noncomputable section

def arg (x : ℝ) : ℝ := 2 * x / (1 + x)
def domain : Set ℝ := {x | x ≠ -1 ∧ |arg x| ≤ 1}

/-- Source: `proof_gap/exercise_159/1.txt`; the arcsine condition is not true for every real x. -/
theorem gap1 : ∀ x : ℝ, x ∈ domain ↔ x ≠ -1 ∧ |arg x| ≤ 1 := by
  intro x
  rfl

/-- Source: `proof_gap/exercise_159/2.txt`. -/
theorem gap2 : ∀ x : ℝ, x ∈ domain → -1 ≤ arg x := by
  intro x hx
  exact (abs_le.mp hx.2).1

/-- Source: `proof_gap/exercise_159/3.txt`. -/
theorem gap3 : ∀ x : ℝ, x ∈ domain → arg x ≤ 1 := by
  intro x hx
  exact (abs_le.mp hx.2).2

/-- Source: `proof_gap/exercise_159/4.txt`. -/
theorem gap4 : (-1 : ℝ) ≤ 1 := by
  norm_num

/-- Source: `proof_gap/exercise_159/5.txt`; rewrite the ratio on its domain. -/
theorem gap5 : ∀ x : ℝ, x ≠ -1 → -1 ≤ 2 - 2 / (1 + x) ↔ -1 ≤ arg x := by
  intro x
  by_cases hx : x = -1
  · subst x
    norm_num [arg]
  · have hden : 1 + x ≠ 0 := by
      intro h
      apply hx
      linarith
    have heq : 2 - 2 / (1 + x) = arg x := by
      rw [arg]
      field_simp [hden]
      ring
    rw [heq]
    simp [hx]

/-- Source: `proof_gap/exercise_159/6.txt`. -/
theorem gap6 : ∀ x : ℝ, x ≠ -1 → 2 - 2 / (1 + x) ≤ 1 ↔ arg x ≤ 1 := by
  intro x
  by_cases hx : x = -1
  · subst x
    norm_num [arg]
  · have hden : 1 + x ≠ 0 := by
      intro h
      apply hx
      linarith
    have heq : 2 - 2 / (1 + x) = arg x := by
      rw [arg]
      field_simp [hden]
      ring
    rw [heq]
    simp [hx]

/-- Source: `proof_gap/exercise_159/7.txt`. -/
theorem gap7 : (-1 : ℝ) ≤ 1 := by
  norm_num

/-- Source: `proof_gap/exercise_159/8.txt`. -/
theorem gap8 : ∀ x : ℝ, x ∈ domain → -3 ≤ -2 / (1 + x) := by
  intro x hx
  have h := (gap5 x).2 (gap2 x hx) hx.1
  ring_nf at h ⊢
  linarith

/-- Source: `proof_gap/exercise_159/9.txt`. -/
theorem gap9 : ∀ x : ℝ, x ∈ domain → -2 / (1 + x) ≤ -1 := by
  intro x hx
  have h := (gap6 x).2 (gap3 x hx) hx.1
  ring_nf at h ⊢
  linarith

/-- Source: `proof_gap/exercise_159/10.txt`. -/
theorem gap10 : (-3 : ℝ) ≤ -1 := by
  norm_num

/-- Source: `proof_gap/exercise_159/11.txt`. -/
theorem gap11 : ∀ x : ℝ, x ∈ domain → 2 / 3 ≤ 1 + x := by
  intro x hx
  have hquot : -2 / (1 + x) < 0 :=
    lt_of_le_of_lt (gap9 x hx) (by norm_num)
  have hden : 0 < 1 + x := by
    rcases (div_neg_iff.mp hquot) with h | h
    · norm_num at h
    · exact h.2
  have hmul := (le_div_iff₀ hden).1 (gap8 x hx)
  linarith

/-- Source: `proof_gap/exercise_159/12.txt`. -/
theorem gap12 : ∀ x : ℝ, x ∈ domain → 1 + x ≤ 2 := by
  intro x hx
  have hquot : -2 / (1 + x) < 0 :=
    lt_of_le_of_lt (gap9 x hx) (by norm_num)
  have hden : 0 < 1 + x := by
    rcases (div_neg_iff.mp hquot) with h | h
    · norm_num at h
    · exact h.2
  have hmul := (div_le_iff₀ hden).1 (gap9 x hx)
  linarith

/-- Source: `proof_gap/exercise_159/13.txt`. -/
theorem gap13 : (2 / 3 : ℝ) ≤ 2 := by
  norm_num

/-- Source: `proof_gap/exercise_159/14.txt`. -/
theorem gap14 : ∀ x : ℝ, x ∈ domain → -(1 : ℝ) / 3 ≤ x := by
  intro x hx
  have h := gap11 x hx
  linarith

/-- Source: `proof_gap/exercise_159/15.txt`. -/
theorem gap15 : ∀ x : ℝ, x ∈ domain → x ≤ 1 := by
  intro x hx
  have h := gap12 x hx
  linarith

/-- Source: `proof_gap/exercise_159/16.txt`. -/
theorem gap16 : (-(1 : ℝ) / 3) ≤ 1 := by
  norm_num

/-- Source: `proof_gap/exercise_159/17.txt`. -/
theorem gap17 : domain = Set.Icc (-(1 : ℝ) / 3) 1 := by
  ext x
  constructor
  · intro hx
    exact ⟨gap14 x hx, gap15 x hx⟩
  · rintro ⟨hxlo, hxhi⟩
    have hdenlo : 2 / 3 ≤ 1 + x := by linarith
    have hdenhi : 1 + x ≤ 2 := by linarith
    have hden : 0 < 1 + x := lt_of_lt_of_le (by norm_num) hdenlo
    have hxne : x ≠ -1 := by linarith
    have hlowquot : -3 ≤ -2 / (1 + x) := by
      apply (le_div_iff₀ hden).2
      nlinarith
    have huppquot : -2 / (1 + x) ≤ -1 := by
      apply (div_le_iff₀ hden).2
      linarith
    have harglo : -1 ≤ arg x := by
      apply (gap5 x).1
      intro _
      ring_nf at hlowquot ⊢
      linarith
    have harghi : arg x ≤ 1 := by
      apply (gap6 x).1
      intro _
      ring_nf at huppquot ⊢
      linarith
    exact ⟨hxne, abs_le.2 ⟨harglo, harghi⟩⟩

end

end ProofGap.Exercise159
