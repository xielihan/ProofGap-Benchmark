import ProofGapLean.Prelude.Sequences

open Filter Topology
noncomputable section

namespace ProofGap.Exercise127_2

def x (n : ℕ) : ℝ := 1 / (n : ℝ)
def y₁ (n : ℕ) : ℝ := n
def y₂ (n : ℕ) : ℝ := n ^ 2

private theorem x_tendsto : Tendsto x atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0)
  simpa [one_div, Function.comp_def] using
    ((tendsto_inv_atTop_zero :
      Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0)).comp
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))

private theorem y₁_tendsto_atTop :
    Tendsto y₁ atTop (atTop : Filter ℝ) := by
  exact tendsto_natCast_atTop_atTop

private theorem y₂_tendsto_atTop :
    Tendsto y₂ atTop (atTop : Filter ℝ) := by
  apply Filter.tendsto_atTop_mono' atTop
    (f₁ := fun n : ℕ => (n : ℝ))
  · filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp [y₂]
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  · exact tendsto_natCast_atTop_atTop

/-- Exercise 127_2, gap 1. -/
theorem gap1 : ProofGap.ConvergentSeq x := by
  exact ⟨0, x_tendsto⟩

/-- Exercise 127_2, gap 2. -/
theorem gap2 : ¬ ProofGap.ConvergentSeq y₁ := by
  rintro ⟨l, hl⟩
  exact not_tendsto_nhds_of_tendsto_atTop y₁_tendsto_atTop l hl

/-- Exercise 127_2, gap 3; the product identity is positive-indexed. -/
theorem gap3 : ∀ n : ℕ, 0 < n → x n * y₁ n = 1 := by
  intro n hn
  simp [x, y₁, hn.ne']

/-- Exercise 127_2, gap 4. -/
theorem gap4 : ProofGap.ConvergentSeq (fun n => x n * y₁ n) := by
  refine ⟨1, ?_⟩
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (gap3 n (by omega)).symm

/-- Exercise 127_2, gap 5; start the second example separately. -/
theorem gap5 : ProofGap.ConvergentSeq x := by
  exact gap1

/-- Exercise 127_2, gap 6. -/
theorem gap6 : ¬ ProofGap.ConvergentSeq y₂ := by
  rintro ⟨l, hl⟩
  exact not_tendsto_nhds_of_tendsto_atTop y₂_tendsto_atTop l hl

/-- Exercise 127_2, gap 7. -/
theorem gap7 : ∀ n : ℕ, 0 < n → x n * y₂ n = n := by
  intro n hn
  rw [x, y₂]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- Exercise 127_2, gap 8. -/
theorem gap8 : ¬ ProofGap.ConvergentSeq (fun n => x n * y₂ n) := by
  have htop :
      Tendsto (fun n => x n * y₂ n) atTop (atTop : Filter ℝ) := by
    apply y₁_tendsto_atTop.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    simpa [y₁] using (gap7 n (by omega)).symm
  rintro ⟨l, hl⟩
  exact not_tendsto_nhds_of_tendsto_atTop htop l hl

end ProofGap.Exercise127_2
