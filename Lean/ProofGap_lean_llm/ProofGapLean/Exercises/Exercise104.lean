import ProofGapLean.Prelude.Sequences

open Filter Topology

namespace ProofGap.Exercise104

def x (n : ℕ) : ℝ :=
  1 + 2 * (-1 : ℝ) ^ (n + 1) + 3 * (-1 : ℝ) ^ (n * (n - 1) / 2)

def values : Set ℝ :=
  {v | ∃ n : ℕ, 0 < n ∧ v = x n}

private theorem triangular_four_mul (k : ℕ) :
    (4 * k) * (4 * k - 1) / 2 = (2 * k) * (4 * k - 1) := by
  rw [show 4 * k = 2 * (2 * k) by omega]
  simp [Nat.mul_assoc]

private theorem triangular_four_mul_add_one (k : ℕ) :
    (4 * k + 1) * ((4 * k + 1) - 1) / 2 =
      (4 * k + 1) * (2 * k) := by
  rw [show 4 * k + 1 - 1 = 2 * (2 * k) by omega]
  rw [show (4 * k + 1) * (2 * (2 * k)) =
    2 * ((4 * k + 1) * (2 * k)) by ring]
  simp

private theorem triangular_four_mul_add_two (k : ℕ) :
    (4 * k + 2) * ((4 * k + 2) - 1) / 2 =
      (2 * k + 1) * (4 * k + 1) := by
  rw [show 4 * k + 2 - 1 = 4 * k + 1 by omega]
  rw [show 4 * k + 2 = 2 * (2 * k + 1) by omega]
  simp [Nat.mul_assoc]

private theorem triangular_four_mul_add_three (k : ℕ) :
    (4 * k + 3) * ((4 * k + 3) - 1) / 2 =
      (4 * k + 3) * (2 * k + 1) := by
  rw [show 4 * k + 3 - 1 = 2 * (2 * k + 1) by omega]
  simp [Nat.mul_assoc, Nat.mul_comm]

/-- Source: `proof_gap/exercise_104/1.txt`. -/
theorem gap1 : ∀ k : ℕ, x (4 * k) = 1 - 2 + 3 := by
  intro k
  unfold x
  rw [triangular_four_mul]
  rw [(by
    apply Odd.neg_one_pow
    exact ⟨2 * k, by omega⟩ :
      (-1 : ℝ) ^ (4 * k + 1) = -1)]
  rw [(by
    apply Even.neg_one_pow
    exact ⟨k * (4 * k - 1), by ring⟩ :
      (-1 : ℝ) ^ ((2 * k) * (4 * k - 1)) = 1)]
  norm_num

/-- Source: `proof_gap/exercise_104/2.txt`. -/
theorem gap2 : ∀ k : ℕ, x (4 * k + 1) = 1 + 2 + 3 := by
  intro k
  unfold x
  rw [triangular_four_mul_add_one]
  rw [(by
    apply Even.neg_one_pow
    exact ⟨2 * k + 1, by omega⟩ :
      (-1 : ℝ) ^ (4 * k + 1 + 1) = 1)]
  rw [(by
    apply Even.neg_one_pow
    exact ⟨(4 * k + 1) * k, by ring⟩ :
      (-1 : ℝ) ^ ((4 * k + 1) * (2 * k)) = 1)]
  norm_num

/-- Source: `proof_gap/exercise_104/3.txt`. -/
theorem gap3 : ∀ k : ℕ, x (4 * k + 2) = 1 - 2 - 3 := by
  intro k
  unfold x
  rw [triangular_four_mul_add_two]
  rw [(by
    apply Odd.neg_one_pow
    exact ⟨2 * k + 1, by omega⟩ :
      (-1 : ℝ) ^ (4 * k + 2 + 1) = -1)]
  rw [(by
    apply Odd.neg_one_pow
    exact (by
      exact (show Odd (2 * k + 1) from ⟨k, by omega⟩).mul
        (show Odd (4 * k + 1) from ⟨2 * k, by omega⟩)) :
      (-1 : ℝ) ^ ((2 * k + 1) * (4 * k + 1)) = -1)]
  norm_num

/-- Source: `proof_gap/exercise_104/4.txt`. -/
theorem gap4 : ∀ k : ℕ, x (4 * k + 3) = 1 + 2 - 3 := by
  intro k
  unfold x
  rw [triangular_four_mul_add_three]
  rw [(by
    apply Even.neg_one_pow
    exact ⟨2 * k + 2, by omega⟩ :
      (-1 : ℝ) ^ (4 * k + 3 + 1) = 1)]
  rw [(by
    apply Odd.neg_one_pow
    exact (by
      exact (show Odd (4 * k + 3) from ⟨2 * k + 1, by omega⟩).mul
        (show Odd (2 * k + 1) from ⟨k, by omega⟩)) :
      (-1 : ℝ) ^ ((4 * k + 3) * (2 * k + 1)) = -1)]
  norm_num

private theorem x_bounds (n : ℕ) : -4 ≤ x n ∧ x n ≤ 6 := by
  rcases neg_one_pow_eq_or ℝ (n + 1) with h₁ | h₁ <;>
    rcases neg_one_pow_eq_or ℝ (n * (n - 1) / 2) with h₂ | h₂ <;>
    norm_num [x, h₁, h₂]

/-- Source: `proof_gap/exercise_104/5.txt`. -/
theorem gap5 : sInf values = -4 := by
  have hleast : IsLeast values (-4) := by
    constructor
    · have hx := gap3 0
      norm_num at hx
      exact ⟨2, by omega, hx.symm⟩
    · intro v hv
      rcases hv with ⟨n, hn, rfl⟩
      exact (x_bounds n).1
  exact hleast.csInf_eq

/-- Source: `proof_gap/exercise_104/6.txt`. -/
theorem gap6 : sSup values = 6 := by
  have hgreatest : IsGreatest values 6 := by
    constructor
    · have hx := gap2 0
      norm_num at hx
      exact ⟨1, by omega, hx.symm⟩
    · intro v hv
      rcases hv with ⟨n, hn, rfl⟩
      exact (x_bounds n).2
  exact hgreatest.csSup_eq

/-- Source: `proof_gap/exercise_104/7.txt`. -/
theorem gap7 : sInf (ProofGap.ClusterSet x) = -4 := by
  let p : ℕ → ℕ := fun k => 4 * k + 2
  have hp : StrictMono p := by
    intro a b hab
    dsimp [p]
    omega
  have hlim : Tendsto (x ∘ p) atTop (𝓝 (-4)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards with k
    have hx := gap3 k
    norm_num at hx
    simpa [p, Function.comp_apply] using hx.symm
  have hleast : IsLeast (ProofGap.ClusterSet x) (-4) := by
    constructor
    · exact ⟨p, hp, hlim⟩
    · intro a ha
      rcases ha with ⟨q, hq, hqa⟩
      apply le_of_tendsto_of_tendsto tendsto_const_nhds hqa
      filter_upwards with k
      exact (x_bounds (q k)).1
  exact hleast.csInf_eq

/-- Source: `proof_gap/exercise_104/8.txt`. -/
theorem gap8 : sSup (ProofGap.ClusterSet x) = 6 := by
  let p : ℕ → ℕ := fun k => 4 * k + 1
  have hp : StrictMono p := by
    intro a b hab
    dsimp [p]
    omega
  have hlim : Tendsto (x ∘ p) atTop (𝓝 6) := by
    apply tendsto_const_nhds.congr'
    filter_upwards with k
    have hx := gap2 k
    norm_num at hx
    simpa [p, Function.comp_apply] using hx.symm
  have hgreatest : IsGreatest (ProofGap.ClusterSet x) 6 := by
    constructor
    · exact ⟨p, hp, hlim⟩
    · intro a ha
      rcases ha with ⟨q, hq, hqa⟩
      apply le_of_tendsto hqa
      filter_upwards with k
      exact (x_bounds (q k)).2
  exact hgreatest.csSup_eq

end ProofGap.Exercise104
