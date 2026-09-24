import ProofGapLean.Prelude.Core
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise827_1

noncomputable section

def averageVelocity (Δt : ℝ) : ℝ :=
  (10 * (20 + Δt) + 5 * (20 + Δt) ^ 2 -
    (10 * 20 + 5 * 20 ^ 2)) / Δt

/-- Source: `proof_gap/exercise_827_1/1.txt`; bind the average velocity by its
definition. -/
theorem gap1 (vbar Δt : ℝ) (hv : vbar = averageVelocity Δt) :
    vbar = (10 * (20 + Δt) + 5 * (20 + Δt) ^ 2 -
      (10 * 20 + 5 * 20 ^ 2)) / Δt := by
  simpa [averageVelocity] using hv

/-- Source: `proof_gap/exercise_827_1/2.txt`; add `Δt≠0`. -/
theorem gap2 (Δt : ℝ) (hΔ : Δt ≠ 0) :
    (10 * (20 + Δt) + 5 * (20 + Δt) ^ 2 -
      (10 * 20 + 5 * 20 ^ 2)) / Δt = 210 + 5 * Δt := by
  field_simp [hΔ]
  ring

/-- Source: `proof_gap/exercise_827_1/3.txt`; add the definition of `v̄`. -/
theorem gap3 (vbar Δt : ℝ) (hv : vbar = averageVelocity Δt)
    (hΔ : Δt ≠ 0) : vbar = 210 + 5 * Δt := by
  calc
    vbar = averageVelocity Δt := hv
    _ = 210 + 5 * Δt := by
      simpa [averageVelocity] using gap2 Δt hΔ

/-- Source: `proof_gap/exercise_827_1/4.txt`; restore `Δt=1`. -/
theorem gap4 (vbar Δt : ℝ) (hv : vbar = 210 + 5 * Δt)
    (hΔ : Δt = 1) : vbar = 210 + 5 * 1 := by
  simpa [hΔ] using hv

/-- Source: `proof_gap/exercise_827_1/5.txt`. -/
theorem gap5 : (210 : ℝ) + 5 * 1 = 215 := by
  norm_num

/-- Source: `proof_gap/exercise_827_1/6.txt`. -/
theorem gap6 (vbar : ℝ) (hv : vbar = 210 + 5 * 1) : vbar = 215 := by
  calc
    vbar = 210 + 5 * 1 := hv
    _ = 215 := gap5

end

end ProofGap.Exercise827_1
