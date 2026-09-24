import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise839

noncomputable section

def y (x : ℝ) : ℝ := (x + 1) * (x + 2) ^ 2 * (x + 3) ^ 3
def expanded (x : ℝ) : ℝ :=
  (x + 2) ^ 2 * (x + 3) ^ 3 +
  2 * (x + 1) * (x + 2) * (x + 3) ^ 3 +
  3 * (x + 1) * (x + 2) ^ 2 * (x + 3) ^ 2
def factored (x : ℝ) : ℝ :=
  2 * (x + 2) * (x + 3) ^ 2 * (3 * x ^ 2 + 11 * x + 9)

/-- Correct the source's spurious biconditional to the product-rule identity. -/
theorem gap1 (x : ℝ) : deriv y x = expanded x := by
  have h1 : HasDerivAt (fun t : ℝ => t + 1) 1 x := by
    simpa [id] using (hasDerivAt_id x).add_const (1 : ℝ)
  have h2 : HasDerivAt (fun t : ℝ => t + 2) 1 x := by
    simpa [id] using (hasDerivAt_id x).add_const (2 : ℝ)
  have h3 : HasDerivAt (fun t : ℝ => t + 3) 1 x := by
    simpa [id] using (hasDerivAt_id x).add_const (3 : ℝ)
  have hprod := (h1.mul (h2.mul h2)).mul ((h3.mul h3).mul h3)
  have hy : HasDerivAt y (expanded x) x := by
    convert hprod using 1
    · funext t
      dsimp [y]
      ring
    · dsimp [expanded]
      ring
  exact hy.deriv
theorem gap2 (x : ℝ) :
    expanded x =
      (x + 2) * (x + 3) ^ 2 *
        ((x + 2) * (x + 3) + 2 * (x + 1) * (x + 3) +
          3 * (x + 1) * (x + 2)) := by
  unfold expanded
  ring
theorem gap3 (x : ℝ) : expanded x = factored x := by
  unfold expanded factored
  ring
theorem gap4 (x : ℝ) : deriv y x = 0 ↔ factored x = 0 := by
  rw [gap1, gap3]
theorem gap5 (x : ℝ) :
    deriv y x = 0 ↔ x = -2 ∨ x = -3 ∨ 3 * x ^ 2 + 11 * x + 9 = 0 := by
  rw [gap4]
  unfold factored
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | hq
    · rcases mul_eq_zero.mp h with h | h3
      · rcases mul_eq_zero.mp h with h2 | hx2
        · norm_num at h2
        · exact Or.inl (by linarith)
      · have hx3 : x + 3 = 0 := by
          simpa using h3
        exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr hq)
  · rintro (hx | hx | hq)
    · subst x
      norm_num
    · subst x
      norm_num
    · simp [hq]

/-- Apply the quadratic formula only to the quadratic factor. -/
theorem gap6 (x : ℝ) :
    3 * x ^ 2 + 11 * x + 9 = 0 ↔
      x = (-11 + Real.sqrt 13) / 6 ∨ x = (-11 - Real.sqrt 13) / 6 := by
  have hsqrt : (Real.sqrt (13 : ℝ)) ^ 2 = 13 :=
    Real.sq_sqrt (by norm_num)
  constructor
  · intro h
    have hprod :
        (6 * x + 11 - Real.sqrt 13) *
            (6 * x + 11 + Real.sqrt 13) = 0 := by
      nlinarith [hsqrt]
    rcases mul_eq_zero.mp hprod with hp | hm
    · left
      linarith
    · right
      linarith
  · intro h
    rcases h with hp | hm
    · rw [hp]
      nlinarith [hsqrt]
    · rw [hm]
      nlinarith [hsqrt]
theorem gap7 (x : ℝ) :
    x ∈ ({-3, -2, (-11 + Real.sqrt 13) / 6,
      (-11 - Real.sqrt 13) / 6} : Set ℝ) ↔ deriv y x = 0 := by
  rw [gap5, gap6]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h3 | h2 | hp | hm)
    · exact Or.inr (Or.inl h3)
    · exact Or.inl h2
    · exact Or.inr (Or.inr (Or.inl hp))
    · exact Or.inr (Or.inr (Or.inr hm))
  · rintro (h2 | h3 | hp | hm)
    · exact Or.inr (Or.inl h2)
    · exact Or.inl h3
    · exact Or.inr (Or.inr (Or.inl hp))
    · exact Or.inr (Or.inr (Or.inr hm))

end

end ProofGap.Exercise839
