import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise599

noncomputable section

def f (x : ℝ) : ℝ := Real.rpow 2 x
def leftFilter : Filter ℝ := nhdsWithin 0 (Set.Iio 0)
def rightFilter : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)

/-- Source: `proof_gap/exercise_599/1.txt`. -/
private theorem continuous_f : Continuous f := by
  have hfg : f = (fun x : ℝ => Real.exp (Real.log 2 * x)) := by
    funext x
    unfold f
    change (2 : ℝ) ^ x = Real.exp (Real.log 2 * x)
    exact Real.rpow_def_of_pos (by norm_num) x
  rw [hfg]
  exact Real.continuous_exp.comp (continuous_const.mul continuous_id)

theorem gap1 (x : ℝ) (hx : x < 0) : 0 < f x := by
  unfold f
  exact Real.rpow_pos_of_pos (by norm_num) x

/-- Source: `proof_gap/exercise_599/2.txt`. -/
theorem gap2 (x : ℝ) (hx : x < 0) : f x < 1 := by
  unfold f
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  calc
    Real.rpow 2 x = Real.exp (Real.log 2 * x) := by
      change (2 : ℝ) ^ x = Real.exp (Real.log 2 * x)
      exact Real.rpow_def_of_pos (by norm_num) x
    _ < 1 := (Real.exp_lt_one_iff).2 (mul_neg_of_pos_of_neg hlog hx)

/-- Source: `proof_gap/exercise_599/3.txt`. -/
theorem gap3 (x : ℝ) (hx : x < 0) : (0 : ℝ) < 1 := by
  norm_num

/-- Source: `proof_gap/exercise_599/4.txt`. -/
theorem gap4 : Filter.Tendsto f leftFilter (nhds 1) := by
  change Filter.Tendsto f (nhdsWithin 0 (Set.Iio 0)) (nhds 1)
  have hf0 : f 0 = 1 := by simp [f]
  rw [← hf0]
  exact continuous_f.continuousAt.continuousWithinAt

/-- Source: `proof_gap/exercise_599/5.txt`. -/
theorem gap5 (x : ℝ) (hx : 0 < x) : 1 < f x := by
  unfold f
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  calc
    1 < Real.exp (Real.log 2 * x) :=
      (Real.one_lt_exp_iff).2 (mul_pos hlog hx)
    _ = Real.rpow 2 x := by
      change Real.exp (Real.log 2 * x) = (2 : ℝ) ^ x
      exact (Real.rpow_def_of_pos (by norm_num) x).symm

/-- Source: `proof_gap/exercise_599/6.txt`. -/
theorem gap6 : Filter.Tendsto f rightFilter (nhds 1) := by
  change Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)
  have hf0 : f 0 = 1 := by simp [f]
  rw [← hf0]
  exact continuous_f.continuousAt.continuousWithinAt

/-- Source: `proof_gap/exercise_599/7.txt`. -/
theorem gap7 :
    Filter.Tendsto f leftFilter (nhds 1) ∧
      Filter.Tendsto f rightFilter (nhds 1) := by
  exact ⟨gap4, gap6⟩

end

end ProofGap.Exercise599
