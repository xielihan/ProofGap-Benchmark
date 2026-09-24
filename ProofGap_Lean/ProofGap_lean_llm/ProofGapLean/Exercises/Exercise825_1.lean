import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise825_1

noncomputable section

def secantSlope (Δx : ℝ) : ℝ := ((2 + Δx) ^ 2 - 4) / Δx

/-- Exercise 825_1, gap 1; bind the average slope by its
definition. -/
theorem gap1 (k Δx : ℝ) (hk : k = secantSlope Δx) :
    k = ((2 + Δx) ^ 2 - 4) / Δx := by
  simpa [secantSlope] using hk

/-- Exercise 825_1, gap 2; add `Δx≠0`. -/
theorem gap2 (Δx : ℝ) (hΔ : Δx ≠ 0) :
    ((2 + Δx) ^ 2 - 4) / Δx = 4 + Δx := by
  apply (div_eq_iff hΔ).2
  ring

/-- Exercise 825_1, gap 3; restore `Δx=1`. -/
theorem gap3 (Δx : ℝ) (hΔ : Δx = 1) : 4 + Δx = 5 := by
  norm_num [hΔ]

/-- Exercise 825_1, gap 4; restore the definitions of the
secant slope and `Δx`. -/
theorem gap4 (k Δx : ℝ) (hk : k = secantSlope Δx) (hΔ : Δx = 1) :
    k = 5 := by
  have hΔ0 : Δx ≠ 0 := by
    rw [hΔ]
    norm_num
  calc
    k = ((2 + Δx) ^ 2 - 4) / Δx := gap1 k Δx hk
    _ = 4 + Δx := gap2 Δx hΔ0
    _ = 5 := gap3 Δx hΔ

/-- Exercise 825_1, gap 5; replace an unspecified `lim`
value by `Tendsto`. -/
theorem gap5 (k : ℝ)
    (hk : Filter.Tendsto (fun Δx : ℝ => 4 + Δx)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds k)) :
    Filter.Tendsto (fun Δx : ℝ => 4 + Δx)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds k) := by
  exact hk

/-- Exercise 825_1, gap 6. -/
theorem gap6 :
    Filter.Tendsto (fun Δx : ℝ => 4 + Δx)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 4) := by
  have hconst : ContinuousAt (fun _ : ℝ => (4 : ℝ)) 0 :=
    continuousAt_const
  have hid : ContinuousAt (fun x : ℝ => x) 0 :=
    continuousAt_id
  have hfull :
      Filter.Tendsto (fun x : ℝ => 4 + x) (nhds 0) (nhds 4) := by
    simpa using (hconst.add hid).tendsto
  exact hfull.mono_left (inf_le_left :
    nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ ≤ nhds 0)

/-- Exercise 825_1, gap 7; characterize the named tangent
slope by the preceding limit. -/
theorem gap7 (k : ℝ)
    (hk : Filter.Tendsto (fun Δx : ℝ => 4 + Δx)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds k)) :
    k = 4 := by
  exact tendsto_nhds_unique hk gap6

end

end ProofGap.Exercise825_1
