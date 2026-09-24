import ProofGapLean.Prelude.Sequences

open Filter Topology
noncomputable section

namespace ProofGap.Exercise129

def x (n : ℕ) : ℝ := 1 / (n : ℝ)
def y (n : ℕ) : ℝ := n

/-- Source: `proof_gap/exercise_129/1.txt`. -/
theorem gap1 : Tendsto x atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0)
  simpa [one_div, Function.comp_def] using
    ((tendsto_inv_atTop_zero :
      Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0)).comp
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))

/-- Source: `proof_gap/exercise_129/2.txt`; restore positive indices. -/
theorem gap2 : ∀ n : ℕ, 0 < n → x n * y n = 1 := by
  intro n hn
  simp [x, y, hn.ne']

/-- Source: `proof_gap/exercise_129/3.txt`. -/
theorem gap3 : Tendsto (fun n => x n * y n) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (gap2 n (by omega)).symm

/-- Source: `proof_gap/exercise_129/4.txt`. -/
theorem gap4 : ¬ Tendsto (fun n => x n * y n) atTop (𝓝 0) := by
  intro hzero
  have : (1 : ℝ) = 0 := tendsto_nhds_unique gap3 hzero
  norm_num at this

end ProofGap.Exercise129
