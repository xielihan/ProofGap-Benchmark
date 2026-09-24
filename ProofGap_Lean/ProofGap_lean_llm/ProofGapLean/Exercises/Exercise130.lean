import ProofGapLean.Prelude.Sequences

open Filter Topology
noncomputable section

namespace ProofGap.Exercise130

def alternatingX (n : ℕ) : ℝ := (1 + (-1 : ℝ) ^ n) / 2
def alternatingY (n : ℕ) : ℝ := (1 - (-1 : ℝ) ^ n) / 2
def smallX (n : ℕ) : ℝ := 1 / (n : ℝ) ^ 2
def largeY (n : ℕ) : ℝ := n

private theorem inv_nat_tendsto :
    Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
  simpa [one_div, Function.comp_def] using
    ((tendsto_inv_atTop_zero :
      Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0)).comp
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))

private theorem even_strictMono : StrictMono (fun k : ℕ => 2 * k) := by
  intro a b hab
  exact (Nat.mul_lt_mul_left (by omega : 0 < 2)).2 hab

private theorem odd_strictMono : StrictMono (fun k : ℕ => 2 * k + 1) := by
  intro a b hab
  exact Nat.add_lt_add_right
    ((Nat.mul_lt_mul_left (by omega : 0 < 2)).2 hab) 1

/-- Exercise 130, gap 1. -/
theorem gap1 :
    Tendsto (fun n => alternatingX n * alternatingY n) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards with n
  rcases neg_one_pow_eq_or ℝ n with h | h
  · simp [alternatingX, alternatingY, h]
  · simp [alternatingX, alternatingY, h]

/-- Exercise 130, gap 2. -/
theorem gap2 : ¬ ProofGap.ConvergentSeq alternatingX := by
  rintro ⟨l, hlim⟩
  have heven := hlim.comp even_strictMono.tendsto_atTop
  have hodd := hlim.comp odd_strictMono.tendsto_atTop
  have heven_const :
      Tendsto (alternatingX ∘ fun k : ℕ => 2 * k) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards with k
    simp [alternatingX, pow_mul]
  have hodd_const :
      Tendsto (alternatingX ∘ fun k : ℕ => 2 * k + 1) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards with k
    simp [alternatingX, pow_add, pow_mul]
  have hl1 : l = 1 := tendsto_nhds_unique heven heven_const
  have hl0 : l = 0 := tendsto_nhds_unique hodd hodd_const
  norm_num [hl1] at hl0

/-- Exercise 130, gap 3. -/
theorem gap3 : ¬ ProofGap.ConvergentSeq alternatingY := by
  rintro ⟨l, hlim⟩
  have heven := hlim.comp even_strictMono.tendsto_atTop
  have hodd := hlim.comp odd_strictMono.tendsto_atTop
  have heven_const :
      Tendsto (alternatingY ∘ fun k : ℕ => 2 * k) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards with k
    simp [alternatingY, pow_mul]
  have hodd_const :
      Tendsto (alternatingY ∘ fun k : ℕ => 2 * k + 1) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards with k
    simp [alternatingY, pow_add, pow_mul]
  have hl0 : l = 0 := tendsto_nhds_unique heven heven_const
  have hl1 : l = 1 := tendsto_nhds_unique hodd hodd_const
  norm_num [hl0] at hl1

/-- Exercise 130, gap 4. -/
theorem gap4 :
    ¬ (Tendsto alternatingX atTop (𝓝 0) ∨
      Tendsto alternatingY atTop (𝓝 0)) := by
  rintro (hx | hy)
  · exact gap2 ⟨0, hx⟩
  · exact gap3 ⟨0, hy⟩

/-- Exercise 130, gap 5; separate the second example. -/
theorem gap5 :
    Tendsto (fun n => smallX n * largeY n) atTop (𝓝 0) := by
  apply inv_nat_tendsto.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  dsimp [smallX, largeY]
  field_simp

/-- Exercise 130, gap 6. -/
theorem gap6 :
    Tendsto smallX atTop (𝓝 0) := by
  have hsq :
      Tendsto (fun n : ℕ => (1 / (n : ℝ)) ^ 2) atTop (𝓝 (0 ^ 2)) :=
    inv_nat_tendsto.pow 2
  norm_num at hsq
  apply hsq.congr'
  filter_upwards with n
  simp [smallX]

/-- Exercise 130, gap 7. -/
theorem gap7 :
    ¬ ProofGap.ConvergentSeq largeY := by
  have htop :
      Tendsto largeY atTop (atTop : Filter ℝ) :=
    tendsto_natCast_atTop_atTop
  rintro ⟨l, hl⟩
  exact not_tendsto_nhds_of_tendsto_atTop htop l hl

end ProofGap.Exercise130
