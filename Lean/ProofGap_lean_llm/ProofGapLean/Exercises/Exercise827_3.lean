import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise827_3

noncomputable section

def averageVelocity (Δt : ℝ) : ℝ :=
  (10 * (20 + Δt) + 5 * (20 + Δt) ^ 2 -
    (10 * 20 + 5 * 20 ^ 2)) / Δt

/-- Source: `proof_gap/exercise_827_3/1.txt`; bind the average velocity. -/
theorem gap1 (vbar Δt : ℝ) (hv : vbar = averageVelocity Δt) :
    vbar = (10 * (20 + Δt) + 5 * (20 + Δt) ^ 2 -
      (10 * 20 + 5 * 20 ^ 2)) / Δt := by
  simpa [averageVelocity] using hv

/-- Source: `proof_gap/exercise_827_3/2.txt`; add `Δt≠0`. -/
theorem gap2 (Δt : ℝ) (hΔ : Δt ≠ 0) :
    (10 * (20 + Δt) + 5 * (20 + Δt) ^ 2 -
      (10 * 20 + 5 * 20 ^ 2)) / Δt = 210 + 5 * Δt := by
  apply (div_eq_iff hΔ).2
  ring

/-- Source: `proof_gap/exercise_827_3/3.txt`. -/
theorem gap3 (vbar Δt : ℝ) (hv : vbar = averageVelocity Δt)
    (hΔ : Δt ≠ 0) : vbar = 210 + 5 * Δt := by
  calc
    vbar = averageVelocity Δt := hv
    _ = 210 + 5 * Δt := by
      simpa [averageVelocity] using gap2 Δt hΔ

/-- Source: `proof_gap/exercise_827_3/4.txt`; restore `Δt=0.01`. -/
theorem gap4 (vbar Δt : ℝ) (hv : vbar = 210 + 5 * Δt)
    (hΔ : Δt = 0.01) : vbar = 210.05 := by
  norm_num [hΔ] at hv ⊢
  exact hv

end

end ProofGap.Exercise827_3
