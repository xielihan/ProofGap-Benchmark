import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise825_2

noncomputable section

def secantSlope (Δx : ℝ) : ℝ := ((2 + Δx) ^ 2 - 4) / Δx

/-- Source: `proof_gap/exercise_825_2/1.txt`; type the primed slope as a real number. -/
theorem gap1 (kAA' Δx : ℝ) (hk : kAA' = secantSlope Δx) :
    kAA' = ((2 + Δx) ^ 2 - 4) / Δx := by
  simpa only [secantSlope] using hk

/-- Source: `proof_gap/exercise_825_2/2.txt`; add the omitted `Δx≠0`. -/
theorem gap2 (Δx : ℝ) (hΔx : Δx ≠ 0) :
    ((2 + Δx) ^ 2 - 4) / Δx = 4 + Δx := by
  apply (div_eq_iff hΔx).2
  ring

/-- Source: `proof_gap/exercise_825_2/3.txt`; use the source value `Δx=0.1`. -/
theorem gap3 : (4 : ℝ) + 0.1 = 4.1 := by
  norm_num

/-- Source: `proof_gap/exercise_825_2/4.txt`. -/
theorem gap4 (kAA' : ℝ) (hk : kAA' = secantSlope 0.1) : kAA' = 4.1 := by
  calc
    kAA' = secantSlope 0.1 := hk
    _ = 4 + 0.1 := by
      apply gap2
      norm_num
    _ = 4.1 := gap3

/-- Source: `proof_gap/exercise_825_2/5.txt`; express the limit by `Tendsto`. -/
theorem gap5 :
    Filter.Tendsto (fun Δx : ℝ => 4 + Δx) (nhds 0) (nhds 4) := by
  have h : ContinuousAt (fun Δx : ℝ => (4 : ℝ) + Δx) 0 :=
    continuousAt_const.add continuousAt_id
  simpa only [ContinuousAt, add_zero] using h

/-- Source: `proof_gap/exercise_825_2/6.txt`; express the limit by `Tendsto`. -/
theorem gap6 :
    Filter.Tendsto (fun Δx : ℝ => 4 + Δx) (nhds 0) (nhds 4) := by
  exact gap5

/-- Source: `proof_gap/exercise_825_2/7.txt`; bind the tangent slope. -/
theorem gap7 (kA : ℝ)
    (hk : Filter.Tendsto (fun Δx : ℝ => 4 + Δx) (nhds 0) (nhds kA)) :
    kA = 4 := by
  exact tendsto_nhds_unique hk gap5

end

end ProofGap.Exercise825_2
