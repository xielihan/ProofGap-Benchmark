import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise825_4

noncomputable section

def chordSlope (Δx : ℝ) : ℝ := ((2 + Δx) ^ 2 - 4) / Δx

private theorem four_add_tendsto :
    Filter.Tendsto (fun Δx : ℝ => 4 + Δx) (nhds 0) (nhds 4) := by
  have h4 : Filter.Tendsto (fun _ : ℝ => (4 : ℝ)) (nhds 0) (nhds 4) :=
    tendsto_const_nhds
  have hId : Filter.Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0) := by
    change ContinuousAt (fun x : ℝ => x) 0
    exact continuousAt_id
  simpa only [Pi.add_apply, add_zero] using h4.add hId

theorem gap1 (k Δx : ℝ) (hk : k = chordSlope Δx) :
    k = ((2 + Δx) ^ 2 - 4) / Δx := by
  simpa [chordSlope] using hk
theorem gap2 (Δx : ℝ) (hΔ : Δx ≠ 0) :
    ((2 + Δx) ^ 2 - 4) / Δx = 4 + Δx := by
  apply (div_eq_iff hΔ).2
  ring
theorem gap3 (k Δx : ℝ) (hk : k = chordSlope Δx) (hΔ : Δx ≠ 0) :
    k = 4 + Δx := by
  calc
    k = chordSlope Δx := hk
    _ = 4 + Δx := by simpa [chordSlope] using gap2 Δx hΔ
theorem gap4 (kA : ℝ)
    (h : Filter.Tendsto (fun Δx : ℝ => 4 + Δx) (nhds 0) (nhds kA)) :
    kA = 4 := by
  exact tendsto_nhds_unique h four_add_tendsto
theorem gap5 :
    Filter.Tendsto (fun Δx : ℝ => 4 + Δx) (nhds 0) (nhds 4) := by
  exact four_add_tendsto
theorem gap6 (kA : ℝ)
    (h : Filter.Tendsto (fun Δx : ℝ => 4 + Δx) (nhds 0) (nhds kA)) :
    kA = 4 := by
  exact gap4 kA h

end

end ProofGap.Exercise825_4
