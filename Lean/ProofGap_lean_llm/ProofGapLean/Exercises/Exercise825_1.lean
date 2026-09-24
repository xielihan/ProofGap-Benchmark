import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise825_1

noncomputable section

def secantSlope (Δx : ℝ) : ℝ := ((2 + Δx) ^ 2 - 4) / Δx

/-- Source: `proof_gap/exercise_825_1/1.txt`; bind the average slope by its
definition. -/
theorem gap1 (k Δx : ℝ) (hk : k = secantSlope Δx) :
    k = ((2 + Δx) ^ 2 - 4) / Δx := by
  simpa [secantSlope] using hk

/-- Source: `proof_gap/exercise_825_1/2.txt`; add `Δx≠0`. -/
theorem gap2 (Δx : ℝ) (hΔ : Δx ≠ 0) :
    ((2 + Δx) ^ 2 - 4) / Δx = 4 + Δx := by
  apply (div_eq_iff hΔ).2
  ring

/-- Source: `proof_gap/exercise_825_1/3.txt`; restore `Δx=1`. -/
theorem gap3 (Δx : ℝ) (hΔ : Δx = 1) : 4 + Δx = 5 := by
  norm_num [hΔ]

/-- Source: `proof_gap/exercise_825_1/4.txt`; restore the definitions of the
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

/-- Source: `proof_gap/exercise_825_1/5.txt`; replace an unspecified `lim`
value by `Tendsto`. -/
theorem gap5 (k : ℝ)
    (hk : Filter.Tendsto (fun Δx : ℝ => 4 + Δx)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds k)) :
    Filter.Tendsto (fun Δx : ℝ => 4 + Δx)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds k) := by
  exact hk

/-- Source: `proof_gap/exercise_825_1/6.txt`. -/
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

/-- Source: `proof_gap/exercise_825_1/7.txt`; characterize the named tangent
slope by the preceding limit. -/
theorem gap7 (k : ℝ)
    (hk : Filter.Tendsto (fun Δx : ℝ => 4 + Δx)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds k)) :
    k = 4 := by
  exact tendsto_nhds_unique hk gap6

end

end ProofGap.Exercise825_1
