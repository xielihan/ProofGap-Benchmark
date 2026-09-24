import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise825_3

noncomputable section

def secantSlope (Δx : ℝ) : ℝ := ((2 + Δx) ^ 2 - 4) / Δx

theorem gap1 (kAA' Δx : ℝ) (h : kAA' = secantSlope Δx) :
    kAA' = ((2 + Δx) ^ 2 - 4) / Δx := by
  simpa [secantSlope] using h
theorem gap2 (Δx : ℝ) (h : Δx ≠ 0) : secantSlope Δx = 4 + Δx := by
  unfold secantSlope
  apply (div_eq_iff h).2
  ring
theorem gap3 : (4 : ℝ) + 0.01 = 4.01 := by
  norm_num
theorem gap4 (kAA' : ℝ) (h : kAA' = secantSlope 0.01) : kAA' = 4.01 := by
  calc
    kAA' = secantSlope 0.01 := h
    _ = 4 + 0.01 := gap2 0.01 (by norm_num)
    _ = 4.01 := gap3
theorem gap5 : Filter.Tendsto (fun Δx : ℝ => 4 + Δx) (nhds 0) (nhds 4) := by
  have hconst : Filter.Tendsto (fun _ : ℝ => (4 : ℝ)) (nhds 0) (nhds 4) :=
    tendsto_const_nhds
  have hid : Filter.Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0) := by
    change Filter.map (fun x : ℝ => x) (nhds 0) ≤ nhds 0
    simp
  simpa using hconst.add hid
theorem gap6 : Filter.Tendsto (fun Δx : ℝ => 4 + Δx) (nhds 0) (nhds 4) := by
  exact gap5
theorem gap7 (kA : ℝ)
    (h : Filter.Tendsto (fun Δx : ℝ => 4 + Δx) (nhds 0) (nhds kA)) :
    kA = 4 := by
  exact tendsto_nhds_unique h gap5

end
end ProofGap.Exercise825_3
