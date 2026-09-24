import ProofGapLean.Prelude.Core
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise827_2

noncomputable section

def averageVelocity (Δt : ℝ) : ℝ :=
  (10 * (20 + Δt) + 5 * (20 + Δt) ^ 2 -
    (10 * 20 + 5 * 20 ^ 2)) / Δt

theorem gap1 (vbar Δt : ℝ) (hv : vbar = averageVelocity Δt) :
    vbar = (10 * (20 + Δt) + 5 * (20 + Δt) ^ 2 -
      (10 * 20 + 5 * 20 ^ 2)) / Δt := by
  simpa [averageVelocity] using hv
theorem gap2 (Δt : ℝ) (hΔ : Δt ≠ 0) :
    averageVelocity Δt = 210 + 5 * Δt := by
  unfold averageVelocity
  field_simp [hΔ] <;> ring
theorem gap3 (vbar Δt : ℝ) (hv : vbar = averageVelocity Δt) (hΔ : Δt ≠ 0) :
    vbar = 210 + 5 * Δt := by
  calc
    vbar = averageVelocity Δt := hv
    _ = 210 + 5 * Δt := gap2 Δt hΔ

/-- Restore the omitted increment `Δt=0.1`. -/
theorem gap4 (vbar Δt : ℝ) (hv : vbar = 210 + 5 * Δt) (hΔ : Δt = 0.1) :
    vbar = 210.5 := by
  norm_num [hΔ] at hv ⊢
  exact hv

end

end ProofGap.Exercise827_2
