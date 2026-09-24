import ProofGapLean.Prelude.Analysis

namespace ProofGap.Exercise696

noncomputable section

def y (x : ℝ) : ℝ := Real.arctan (1 / x)
def SingularPoint (f : ℝ → ℝ) (a : ℝ) : Prop := ¬ ContinuousAt f a

/-- Source: `proof_gap/exercise_696/1.txt`; bind the right-hand approach to
the actual singular point `0`. -/
theorem gap1 :
    Filter.Tendsto y (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.pi / 2)) := by
  have h_atan :
      Filter.Tendsto (fun x : ℝ => Real.arctan x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa only [Real.arctan_zero] using
      (Real.continuous_arctan.continuousAt.mono_left
        (show nhdsWithin 0 (Set.Ioi 0) ≤ nhds 0 from inf_le_left))
  have hlim :
      Filter.Tendsto (fun x : ℝ => Real.pi / 2 - Real.arctan x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.pi / 2)) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub h_atan)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  simpa only [y, one_div] using (Real.arctan_inv_of_pos hx).symm

/-- Source: `proof_gap/exercise_696/2.txt`; bind the left-hand approach to
the actual singular point `0`. -/
theorem gap2 :
    Filter.Tendsto y (nhdsWithin 0 (Set.Iio 0))
      (nhds (-Real.pi / 2)) := by
  have h_atan :
      Filter.Tendsto (fun x : ℝ => Real.arctan x)
        (nhdsWithin 0 (Set.Iio 0)) (nhds 0) := by
    simpa only [Real.arctan_zero] using
      (Real.continuous_arctan.continuousAt.mono_left
        (show nhdsWithin 0 (Set.Iio 0) ≤ nhds 0 from inf_le_left))
  have hlim :
      Filter.Tendsto (fun x : ℝ => -Real.pi / 2 - Real.arctan x)
        (nhdsWithin 0 (Set.Iio 0)) (nhds (-Real.pi / 2)) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub h_atan)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  simpa only [y, one_div, neg_div] using (Real.arctan_inv_of_neg hx).symm

/-- Source: `proof_gap/exercise_696/3.txt`. -/
theorem gap3 : SingularPoint y 0 := by
  intro hcont
  have hright :
      Filter.Tendsto y (nhdsWithin 0 (Set.Ioi 0)) (nhds (y 0)) :=
    hcont.mono_left inf_le_left
  have heq : y 0 = Real.pi / 2 :=
    tendsto_nhds_unique hright gap1
  have heq0 : (0 : ℝ) = Real.pi / 2 := by
    simpa [y] using heq
  exact (ne_of_gt (half_pos Real.pi_pos)) heq0.symm

/-- Source: `proof_gap/exercise_696/4.txt`. -/
theorem gap4 (x : ℝ) (hx : x ∈ ({0} : Set ℝ)) :
    SingularPoint y x := by
  have hxeq : x = 0 := by
    simpa only [Set.mem_singleton_iff] using hx
  subst x
  exact gap3

end

end ProofGap.Exercise696
