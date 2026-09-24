import ProofGapLean.Prelude.Sequences

open Filter Topology

noncomputable section

namespace ProofGap.Exercise119

def x (n : ℕ) : ℝ :=
  3 * (1 - 1 / (n : ℝ)) + 2 * (-1 : ℝ) ^ n

/-- Exercise 119, gap 1. -/
theorem gap1 :
    ∀ n : ℕ, 2 * (-1 : ℝ) ^ n ∈ ({2, -2} : Set ℝ) := by
  intro n
  rcases neg_one_pow_eq_or ℝ n with h | h
  · simp [h]
  · simp [h]

private theorem inv_nat_tendsto :
    Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
  simpa [one_div] using
    ((tendsto_inv_atTop_zero :
      Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0)).comp
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))

private theorem x_even (k : ℕ) :
    x (2 * k) = 5 - 3 * (1 / ((2 * k : ℕ) : ℝ)) := by
  rw [x, show 2 * k = 2 * k by rfl, pow_mul]
  norm_num
  ring

private theorem x_odd (k : ℕ) :
    x (2 * k + 1) = 1 - 3 * (1 / ((2 * k + 1 : ℕ) : ℝ)) := by
  rw [x, pow_add, pow_mul]
  norm_num
  ring

private theorem five_mem_cluster : 5 ∈ ProofGap.ClusterSet x := by
  let p : ℕ → ℕ := fun k => 2 * k
  have hp : StrictMono p := by
    intro a b hab
    dsimp [p]
    omega
  refine ⟨p, hp, ?_⟩
  have hinv := inv_nat_tendsto.comp hp.tendsto_atTop
  have h :
      Tendsto
        (fun k : ℕ => (5 : ℝ) - 3 * (1 / ((p k : ℕ) : ℝ)))
        atTop (𝓝 ((5 : ℝ) - 3 * 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv)
  norm_num at h
  apply h.congr'
  filter_upwards with k
  simpa [p, Function.comp_apply] using (x_even k).symm

private theorem one_mem_cluster : 1 ∈ ProofGap.ClusterSet x := by
  let p : ℕ → ℕ := fun k => 2 * k + 1
  have hp : StrictMono p := by
    intro a b hab
    dsimp [p]
    omega
  refine ⟨p, hp, ?_⟩
  have hinv := inv_nat_tendsto.comp hp.tendsto_atTop
  have h :
      Tendsto
        (fun k : ℕ => (1 : ℝ) - 3 * (1 / ((p k : ℕ) : ℝ)))
        atTop (𝓝 ((1 : ℝ) - 3 * 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv)
  norm_num at h
  apply h.congr'
  filter_upwards with k
  simpa [p, Function.comp_apply] using (x_odd k).symm

/-- Exercise 119, gap 2. -/
theorem gap2 :
    ProofGap.ClusterSet x = ({5, 1} : Set ℝ) := by
  ext a
  constructor
  · intro ha
    rcases ha with ⟨p, hp, hlim⟩
    have hinv :
        Tendsto (fun k : ℕ => 1 / ((p k : ℕ) : ℝ)) atTop (𝓝 0) :=
      inv_nat_tendsto.comp hp.tendsto_atTop
    have hy :
        Tendsto
          (fun k : ℕ => 3 + 2 * (-1 : ℝ) ^ (p k))
          atTop (𝓝 a) := by
      have hadd :
          Tendsto
            (fun k : ℕ => (x ∘ p) k +
              3 * (1 / ((p k : ℕ) : ℝ)))
            atTop (𝓝 (a + 3 * 0)) :=
        hlim.add (tendsto_const_nhds.mul hinv)
      norm_num at hadd
      apply hadd.congr'
      filter_upwards with k
      simp [x]
      ring
    have hpoly :
        Tendsto
          (fun k : ℕ =>
            (3 + 2 * (-1 : ℝ) ^ (p k) - 5) *
              (3 + 2 * (-1 : ℝ) ^ (p k) - 1))
          atTop (𝓝 ((a - 5) * (a - 1))) :=
      (hy.sub tendsto_const_nhds).mul (hy.sub tendsto_const_nhds)
    have hzero :
        Tendsto
          (fun k : ℕ =>
            (3 + 2 * (-1 : ℝ) ^ (p k) - 5) *
              (3 + 2 * (-1 : ℝ) ^ (p k) - 1))
          atTop (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards with k
      have hv := gap1 (p k)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with hv | hv <;> rw [hv] <;> norm_num
    have hroot : (a - 5) * (a - 1) = 0 :=
      tendsto_nhds_unique hpoly hzero
    rcases mul_eq_zero.mp hroot with h5 | h1
    · have : a = 5 := by linarith
      simp [this]
    · have : a = 1 := by linarith
      simp [this]
  · intro ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact five_mem_cluster
    · exact one_mem_cluster

end ProofGap.Exercise119
