import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1441

noncomputable section

def y (x : ℝ) : ℝ := 10 / (1 + Real.sin x ^ 2)

theorem gap1 (k : ℤ) :
    Real.sin ((k : ℝ) * Real.pi) = 0 := by
  simpa using Real.sin_int_mul_pi k

theorem gap2 (k : ℤ) :
    IsMaxOn y Set.univ ((k : ℝ) * Real.pi) := by
  intro x _
  change y x ≤ y ((k : ℝ) * Real.pi)
  have hpoint : y ((k : ℝ) * Real.pi) = 10 := by
    simp [y, gap1 k]
  rw [hpoint]
  unfold y
  have hs : 0 ≤ Real.sin x ^ 2 := sq_nonneg _
  have hd : 0 < 1 + Real.sin x ^ 2 := by
    nlinarith
  apply (div_le_iff₀ hd).2
  nlinarith

theorem gap3 (k : ℤ) :
    y ((k : ℝ) * Real.pi) = 10 := by
  simp [y, gap1 k]

theorem gap4 (k : ℤ) :
    |Real.sin (((k : ℝ) + 1 / 2) * Real.pi)| = 1 := by
  let t : ℝ := ((k : ℝ) + 1 / 2) * Real.pi
  have ht : t = (k : ℝ) * Real.pi + Real.pi / 2 := by
    dsimp [t]
    ring
  have hc : Real.cos t = 0 := by
    rw [ht, Real.cos_add, gap1 k, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    ring
  have hsin_sq : Real.sin t ^ 2 = 1 := by
    simpa [hc] using Real.sin_sq_add_cos_sq t
  have habs_sq : |Real.sin t| ^ 2 = 1 := by
    rw [sq_abs]
    exact hsin_sq
  have habs_nonneg : 0 ≤ |Real.sin t| := abs_nonneg _
  change |Real.sin t| = 1
  nlinarith

theorem gap5 (k : ℤ) :
    IsMinOn y Set.univ (((k : ℝ) + 1 / 2) * Real.pi) := by
  intro x _
  change y (((k : ℝ) + 1 / 2) * Real.pi) ≤ y x
  have hs : Real.sin (((k : ℝ) + 1 / 2) * Real.pi) ^ 2 = 1 := by
    calc
      Real.sin (((k : ℝ) + 1 / 2) * Real.pi) ^ 2 =
          |Real.sin (((k : ℝ) + 1 / 2) * Real.pi)| ^ 2 := by
            rw [sq_abs]
      _ = 1 := by
        rw [gap4 k]
        norm_num
  have hpoint : y (((k : ℝ) + 1 / 2) * Real.pi) = 5 := by
    norm_num [y, hs]
  rw [hpoint]
  unfold y
  have hsx : 0 ≤ Real.sin x ^ 2 := sq_nonneg _
  have hd : 0 < 1 + Real.sin x ^ 2 := by
    nlinarith
  have hc : 0 ≤ Real.cos x ^ 2 := sq_nonneg _
  have htrig := Real.sin_sq_add_cos_sq x
  have hsle : Real.sin x ^ 2 ≤ 1 := by
    nlinarith
  apply (le_div_iff₀ hd).2
  nlinarith

theorem gap6 (k : ℤ) :
    y (((k : ℝ) + 1 / 2) * Real.pi) = 5 := by
  have hs : Real.sin (((k : ℝ) + 1 / 2) * Real.pi) ^ 2 = 1 := by
    calc
      Real.sin (((k : ℝ) + 1 / 2) * Real.pi) ^ 2 =
          |Real.sin (((k : ℝ) + 1 / 2) * Real.pi)| ^ 2 := by
            rw [sq_abs]
      _ = 1 := by
        rw [gap4 k]
        norm_num
  norm_num [y, hs]

end
end ProofGap.Exercise1441
