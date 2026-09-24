import ProofGapLean.Prelude.Analysis

open Filter

namespace ProofGap.Exercise109

noncomputable section

def x (n : ℕ) : ℝ :=
  1 + (n : ℝ) * Real.sin ((n : ℝ) * Real.pi / 2)

def values : Set ℝ :=
  {v | ∃ n : ℕ, 0 < n ∧ v = x n}

private theorem sin_three_pi_div_two :
    Real.sin (3 * Real.pi / 2) = -1 := by
  rw [show (3 : ℝ) * Real.pi / 2 =
    2 * Real.pi - Real.pi / 2 by ring]
  rw [Real.sin_two_pi_sub, Real.sin_pi_div_two]

private theorem x_four_mul_add_three (n : ℕ) :
    x (4 * n + 3) = 1 - ((4 * n + 3 : ℕ) : ℝ) := by
  have hang :
      ((4 * n + 3 : ℕ) : ℝ) * Real.pi / 2 =
        3 * Real.pi / 2 + (n : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [x, hang, Real.sin_add_nat_mul_two_pi, sin_three_pi_div_two]
  ring

private theorem x_four_mul_add_one (n : ℕ) :
    x (4 * n + 1) = 1 + ((4 * n + 1 : ℕ) : ℝ) := by
  have hang :
      ((4 * n + 1 : ℕ) : ℝ) * Real.pi / 2 =
        Real.pi / 2 + (n : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [x, hang, Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]
  ring

private theorem low_subsequence_tendsto :
    Tendsto (fun n : ℕ => x (4 * n + 3))
      atTop (atBot : Filter ℝ) := by
  have hcast :
      Tendsto (fun n : ℕ => -(n : ℝ)) atTop (atBot : Filter ℝ) :=
    tendsto_neg_atTop_atBot.comp
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop (atTop : Filter ℝ))
  apply Filter.tendsto_atBot_mono _ hcast
  intro n
  rw [x_four_mul_add_three]
  push_cast
  linarith [show (0 : ℝ) ≤ n by positivity]

private theorem high_subsequence_tendsto :
    Tendsto (fun n : ℕ => x (4 * n + 1))
      atTop (atTop : Filter ℝ) := by
  have hcast :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop (atTop : Filter ℝ) :=
    tendsto_natCast_atTop_atTop
  apply Filter.tendsto_atTop_mono _ hcast
  intro n
  rw [x_four_mul_add_one]
  push_cast
  linarith [show (0 : ℝ) ≤ n by positivity]

/-- Source: `proof_gap/exercise_109/1.txt`. -/
theorem gap1 : x 1 = 1 + 1 := by
  norm_num [x, Real.sin_pi_div_two]

/-- Source: `proof_gap/exercise_109/2.txt`. -/
theorem gap2 : x 2 = 1 + 0 := by
  norm_num [x, Real.sin_pi]

/-- Source: `proof_gap/exercise_109/3.txt`. -/
theorem gap3 : x 3 = 1 - 3 := by
  rw [x]
  norm_num
  rw [sin_three_pi_div_two]
  norm_num

/-- Source: `proof_gap/exercise_109/4.txt`. -/
theorem gap4 : x 4 = 1 + 0 := by
  rw [x]
  norm_num
  have hang : (4 : ℝ) * Real.pi / 2 = 2 * Real.pi := by ring
  rw [hang, Real.sin_two_pi]

/-- Source: `proof_gap/exercise_109/5.txt`. -/
theorem gap5 : x 5 = 1 + 5 := by
  rw [x]
  norm_num
  have hang : (5 : ℝ) * Real.pi / 2 =
      Real.pi / 2 + 2 * Real.pi := by ring
  rw [hang, Real.sin_add_two_pi, Real.sin_pi_div_two]
  norm_num

/-- Source: `proof_gap/exercise_109/6.txt`. -/
theorem gap6 : ¬ BddBelow values := by
  intro hb
  rcases hb with ⟨a, ha⟩
  have hev : ∀ᶠ n : ℕ in atTop, x (4 * n + 3) ≤ a - 1 :=
    tendsto_atBot.1 low_subsequence_tendsto (a - 1)
  rcases hev.exists with ⟨n, hn⟩
  have hmem : x (4 * n + 3) ∈ values :=
    ⟨4 * n + 3, by omega, rfl⟩
  linarith [ha hmem]

/-- Source: `proof_gap/exercise_109/7.txt`. -/
theorem gap7 : ¬ BddAbove values := by
  intro hb
  rcases hb with ⟨a, ha⟩
  have hev : ∀ᶠ n : ℕ in atTop, a + 1 ≤ x (4 * n + 1) :=
    tendsto_atTop.1 high_subsequence_tendsto (a + 1)
  rcases hev.exists with ⟨n, hn⟩
  have hmem : x (4 * n + 1) ∈ values :=
    ⟨4 * n + 1, by omega, rfl⟩
  linarith [ha hmem]

/-- Source: `proof_gap/exercise_109/8.txt`. -/
theorem gap8 :
    Tendsto (fun n : ℕ => x (4 * n + 3)) atTop (atBot : Filter ℝ) := by
  exact low_subsequence_tendsto

/-- Source: `proof_gap/exercise_109/9.txt`. -/
theorem gap9 :
    Tendsto (fun n : ℕ => x (4 * n + 1)) atTop (atTop : Filter ℝ) := by
  exact high_subsequence_tendsto

end

end ProofGap.Exercise109
