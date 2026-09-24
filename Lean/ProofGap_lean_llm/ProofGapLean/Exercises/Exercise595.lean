import ProofGapLean.Prelude.Analysis

namespace ProofGap.Exercise595

noncomputable section

def f (x : ℝ) : ℝ := Real.arctan (1 / (1 - x))
def leftFilter : Filter ℝ := nhdsWithin 1 (Set.Iio 1)
def rightFilter : Filter ℝ := nhdsWithin 1 (Set.Ioi 1)

/-- Source: `proof_gap/exercise_595/1.txt`. -/
private theorem arctan_one_sub_tendsto
    (l : Filter ℝ) (hl : l ≤ nhds (1 : ℝ)) :
    Filter.Tendsto (fun x : ℝ => Real.arctan (1 - x)) l (nhds 0) := by
  have hone : Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
      (nhds (1 : ℝ)) (nhds (1 : ℝ)) :=
    tendsto_const_nhds
  have hid : Filter.Tendsto (fun x : ℝ => x)
      (nhds (1 : ℝ)) (nhds (1 : ℝ)) :=
    continuous_id.continuousAt
  have hsub : Filter.Tendsto (fun x : ℝ => 1 - x) l (nhds 0) := by
    simpa using (hone.sub hid).mono_left hl
  have hatan : Filter.Tendsto Real.arctan (nhds (0 : ℝ))
      (nhds (Real.arctan 0)) :=
    Real.continuous_arctan.continuousAt
  simpa [Function.comp_def] using hatan.comp hsub

theorem gap1 : Filter.Tendsto f leftFilter (nhds (Real.pi / 2)) := by
  have hl : leftFilter ≤ nhds (1 : ℝ) := by
    rw [leftFilter]
    exact inf_le_left
  have hcore := arctan_one_sub_tendsto leftFilter hl
  have hlim : Filter.Tendsto
      (fun x : ℝ => Real.pi / 2 - Real.arctan (1 - x))
      leftFilter (nhds (Real.pi / 2)) := by
    simpa using
      (tendsto_const_nhds.sub hcore :
        Filter.Tendsto
          (fun x : ℝ => Real.pi / 2 - Real.arctan (1 - x))
          leftFilter (nhds (Real.pi / 2 - 0)))
  have heq : f =ᶠ[leftFilter]
      (fun x : ℝ => Real.pi / 2 - Real.arctan (1 - x)) := by
    rw [leftFilter]
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa only [f, one_div] using
      (Real.arctan_inv_of_pos (sub_pos.mpr hx))
  exact hlim.congr' heq.symm

/-- Source: `proof_gap/exercise_595/2.txt`. -/
theorem gap2 : Filter.Tendsto f rightFilter (nhds (-Real.pi / 2)) := by
  have hl : rightFilter ≤ nhds (1 : ℝ) := by
    rw [rightFilter]
    exact inf_le_left
  have hcore := arctan_one_sub_tendsto rightFilter hl
  have hlim : Filter.Tendsto
      (fun x : ℝ => -(Real.pi / 2) - Real.arctan (1 - x))
      rightFilter (nhds (-(Real.pi / 2))) := by
    simpa using
      (tendsto_const_nhds.sub hcore :
        Filter.Tendsto
          (fun x : ℝ => -(Real.pi / 2) - Real.arctan (1 - x))
          rightFilter (nhds (-(Real.pi / 2) - 0)))
  have heq : f =ᶠ[rightFilter]
      (fun x : ℝ => -(Real.pi / 2) - Real.arctan (1 - x)) := by
    rw [rightFilter]
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa only [f, one_div, neg_div] using
      (Real.arctan_inv_of_neg (sub_neg.mpr hx))
  have hf : Filter.Tendsto f rightFilter (nhds (-(Real.pi / 2))) :=
    hlim.congr' heq.symm
  simpa only [neg_div] using hf

end

end ProofGap.Exercise595
