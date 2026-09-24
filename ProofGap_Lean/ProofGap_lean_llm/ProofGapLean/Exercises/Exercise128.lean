import ProofGapLean.Prelude.Sequences

open Filter Topology

noncomputable section

namespace ProofGap.Exercise128

def x (n : ℕ) : ℝ := (1 + (-1 : ℝ) ^ n) / 2
def y (n : ℕ) : ℝ := (1 - (-1 : ℝ) ^ n) / 2

private theorem even_strictMono : StrictMono (fun k : ℕ => 2 * k) := by
  intro a b hab
  exact (Nat.mul_lt_mul_left (by omega : 0 < 2)).2 hab

private theorem odd_strictMono : StrictMono (fun k : ℕ => 2 * k + 1) := by
  intro a b hab
  exact Nat.add_lt_add_right
    ((Nat.mul_lt_mul_left (by omega : 0 < 2)).2 hab) 1

private theorem x_even (k : ℕ) : x (2 * k) = 1 := by
  simp [x, pow_mul]

private theorem x_odd (k : ℕ) : x (2 * k + 1) = 0 := by
  simp [x, pow_add, pow_mul]

private theorem y_even (k : ℕ) : y (2 * k) = 0 := by
  simp [y, pow_mul]

private theorem y_odd (k : ℕ) : y (2 * k + 1) = 1 := by
  simp [y, pow_add, pow_mul]

/-- Exercise 128, gap 1. -/
theorem gap1 : ¬ ProofGap.ConvergentSeq x := by
  rintro ⟨l, hlim⟩
  have heven :
      Tendsto (x ∘ fun k : ℕ => 2 * k) atTop (𝓝 l) :=
    hlim.comp even_strictMono.tendsto_atTop
  have hodd :
      Tendsto (x ∘ fun k : ℕ => 2 * k + 1) atTop (𝓝 l) :=
    hlim.comp odd_strictMono.tendsto_atTop
  have heven_const :
      Tendsto (x ∘ fun k : ℕ => 2 * k) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards with k
    exact (x_even k).symm
  have hodd_const :
      Tendsto (x ∘ fun k : ℕ => 2 * k + 1) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards with k
    exact (x_odd k).symm
  have hl1 : l = 1 := tendsto_nhds_unique heven heven_const
  have hl0 : l = 0 := tendsto_nhds_unique hodd hodd_const
  norm_num [hl1] at hl0

/-- Exercise 128, gap 2. -/
theorem gap2 : ¬ ProofGap.ConvergentSeq y := by
  rintro ⟨l, hlim⟩
  have heven :
      Tendsto (y ∘ fun k : ℕ => 2 * k) atTop (𝓝 l) :=
    hlim.comp even_strictMono.tendsto_atTop
  have hodd :
      Tendsto (y ∘ fun k : ℕ => 2 * k + 1) atTop (𝓝 l) :=
    hlim.comp odd_strictMono.tendsto_atTop
  have heven_const :
      Tendsto (y ∘ fun k : ℕ => 2 * k) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards with k
    exact (y_even k).symm
  have hodd_const :
      Tendsto (y ∘ fun k : ℕ => 2 * k + 1) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards with k
    exact (y_odd k).symm
  have hl0 : l = 0 := tendsto_nhds_unique heven heven_const
  have hl1 : l = 1 := tendsto_nhds_unique hodd hodd_const
  norm_num [hl0] at hl1

/-- Exercise 128, gap 3. -/
theorem gap3 : ∀ n : ℕ, x n + y n = 1 := by
  intro n
  simp [x, y]
  ring

/-- Exercise 128, gap 4. -/
theorem gap4 : ∀ n : ℕ, x n * y n = 0 := by
  intro n
  rcases neg_one_pow_eq_or ℝ n with h | h
  · simp [x, y, h]
  · simp [x, y, h]

/-- Exercise 128, gap 5. -/
theorem gap5 : ProofGap.ConvergentSeq (fun n => x n + y n) := by
  refine ⟨1, ?_⟩
  apply tendsto_const_nhds.congr'
  filter_upwards with n
  exact (gap3 n).symm

/-- Exercise 128, gap 6. -/
theorem gap6 : ProofGap.ConvergentSeq (fun n => x n * y n) := by
  refine ⟨0, ?_⟩
  apply tendsto_const_nhds.congr'
  filter_upwards with n
  exact (gap4 n).symm

end ProofGap.Exercise128
