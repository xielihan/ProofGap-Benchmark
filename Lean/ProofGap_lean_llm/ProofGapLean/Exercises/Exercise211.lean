import ProofGapLean.Prelude.Core
import ProofGapLean.Prelude.Elementary

namespace ProofGap.Exercise211

noncomputable section

def exterior : Set ℝ := {t | 2 ≤ |t|}

/-- Source: `proof_gap/exercise_211/1.txt`; x must be nonzero. -/
private theorem exists_add_inv_eq_of_two_le_abs (t : ℝ) (ht : 2 ≤ |t|) :
    ∃ x : ℝ, x ≠ 0 ∧ x + 1 / x = t := by
  let d : ℝ := Real.sqrt (t ^ 2 - 4)
  have ht_sq : 4 ≤ t ^ 2 := by
    by_cases ht_nonneg : 0 ≤ t
    · rw [abs_of_nonneg ht_nonneg] at ht
      nlinarith
    · have ht_nonpos : t ≤ 0 := le_of_not_ge ht_nonneg
      rw [abs_of_nonpos ht_nonpos] at ht
      nlinarith
  have hrad : 0 ≤ t ^ 2 - 4 := by linarith
  have hd_nonneg : 0 ≤ d := Real.sqrt_nonneg _
  have hd_sq : d ^ 2 = t ^ 2 - 4 := by
    dsimp [d]
    exact Real.sq_sqrt hrad
  have hsum_ne : t + d ≠ 0 := by
    intro hzero
    nlinarith
  refine ⟨(t + d) / 2, div_ne_zero hsum_ne (by norm_num), ?_⟩
  field_simp [hsum_ne]
  nlinarith

theorem gap1 (f : ℝ → ℝ)
    (h : ∀ x : ℝ, x ≠ 0 → f (x + 1 / x) = x ^ 2 + 1 / x ^ 2) :
    ∀ x : ℝ, x ≠ 0 → f (x + 1 / x) = (x + 1 / x) ^ 2 - 2 := by
  intro x hx
  rw [h x hx]
  field_simp [hx]
  ring

/-- Source: `proof_gap/exercise_211/2.txt`; the premise only determines f on |t|≥2. -/
theorem gap2 (f : ℝ → ℝ)
    (h : ∀ x : ℝ, x ≠ 0 → f (x + 1 / x) = x ^ 2 + 1 / x ^ 2) :
    ∀ t : ℝ, t ∈ exterior → f t = t ^ 2 - 2 := by
  intro t ht
  rcases exists_add_inv_eq_of_two_le_abs t ht with ⟨x, hx, rfl⟩
  exact gap1 f h x hx

end

end ProofGap.Exercise211
