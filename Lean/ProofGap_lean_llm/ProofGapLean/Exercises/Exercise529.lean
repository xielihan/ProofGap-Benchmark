import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise529

noncomputable section

def original (x : ℝ) : ℝ := Real.log (1 + x) / x
def rewritten (x : ℝ) : ℝ := Real.log (Real.rpow (1 + x) (1 / x))
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_529/1.txt`. -/
theorem gap1 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero rewritten L := by
  unfold HasLimitAtZero
  have hfilter :
      nhdsWithin 0 ({0} : Set ℝ)ᶜ ≤ nhds 0 := by
    exact inf_le_left
  have hnear_nhds : ∀ᶠ x : ℝ in nhds 0, -1 < x :=
    eventually_gt_nhds (by norm_num)
  have hnear : ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ, -1 < x :=
    hfilter hnear_nhds
  have heq : original =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] rewritten := by
    filter_upwards [hnear] with x hx
    have hpos : 0 < 1 + x := by linarith
    unfold original rewritten
    change Real.log (1 + x) / x = Real.log ((1 + x) ^ (1 / x))
    simpa [div_eq_mul_inv, mul_comm] using
      (Real.log_rpow hpos (1 / x)).symm
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

/-- Source: `proof_gap/exercise_529/2.txt`. -/
theorem gap2 : HasLimitAtZero rewritten (Real.log (Real.exp 1)) := by
  rw [Real.log_exp]
  apply (gap1 1).mp
  unfold HasLimitAtZero original
  have hinner : HasDerivAt (fun x : ℝ => 1 + x) 1 0 := by
    simpa using
      ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add
        (hasDerivAt_id (0 : ℝ)))
  have hlog : HasDerivAt Real.log 1 (1 + (0 : ℝ)) := by
    simpa using
      (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0))
  have hderiv : HasDerivAt (fun x : ℝ => Real.log (1 + x)) 1 0 := by
    simpa [Function.comp_def] using hlog.comp 0 hinner
  simpa [Real.log_one, div_eq_mul_inv, mul_comm] using
    hderiv.tendsto_slope_zero

/-- Source: `proof_gap/exercise_529/3.txt`. -/
theorem gap3 : Real.log (Real.exp 1) = 1 := by
  simpa using Real.log_exp 1

/-- Source: `proof_gap/exercise_529/4.txt`. -/
theorem gap4 : HasLimitAtZero original 1 := by
  rw [gap1]
  simpa [gap3] using gap2

end

end ProofGap.Exercise529
