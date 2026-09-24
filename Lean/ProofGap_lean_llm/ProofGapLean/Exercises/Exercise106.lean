import ProofGapLean.Prelude.Sequences

open Filter

namespace ProofGap.Exercise106

def x (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * n

def values : Set ℝ :=
  {v | ∃ n : ℕ, 0 < n ∧ v = x n}

private theorem x_odd (n : ℕ) :
    x (2 * n + 1) = -((2 * n + 1 : ℕ) : ℝ) := by
  simp [x, pow_add, pow_mul]

private theorem x_even (n : ℕ) :
    x (2 * n + 2) = ((2 * n + 2 : ℕ) : ℝ) := by
  rw [show 2 * n + 2 = 2 * (n + 1) by omega]
  simp [x, pow_mul]

private theorem odd_tendsto :
    Tendsto (fun n : ℕ => x (2 * n + 1)) atTop (atBot : Filter ℝ) := by
  have hcast :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop (atTop : Filter ℝ) :=
    tendsto_natCast_atTop_atTop
  have hpos :
      Tendsto (fun n : ℕ => ((2 * n + 1 : ℕ) : ℝ))
        atTop (atTop : Filter ℝ) := by
    apply Filter.tendsto_atTop_mono _ hcast
    intro n
    exact_mod_cast (show n ≤ 2 * n + 1 by omega)
  apply (tendsto_neg_atTop_atBot.comp hpos).congr'
  filter_upwards with n
  exact (x_odd n).symm

private theorem even_tendsto :
    Tendsto (fun n : ℕ => x (2 * n + 2)) atTop (atTop : Filter ℝ) := by
  have hcast :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop (atTop : Filter ℝ) :=
    tendsto_natCast_atTop_atTop
  have hpos :
      Tendsto (fun n : ℕ => ((2 * n + 2 : ℕ) : ℝ))
        atTop (atTop : Filter ℝ) := by
    apply Filter.tendsto_atTop_mono _ hcast
    intro n
    exact_mod_cast (show n ≤ 2 * n + 2 by omega)
  apply hpos.congr'
  filter_upwards with n
  exact (x_even n).symm

/-- Source: `proof_gap/exercise_106/1.txt`; infimum -∞ means unbounded below. -/
theorem gap1 : ¬ BddBelow values := by
  intro hb
  rcases hb with ⟨a, ha⟩
  have hev :
      ∀ᶠ n : ℕ in atTop, (fun n : ℕ => x (2 * n + 1)) n ≤ a - 1 :=
    tendsto_atBot.1 odd_tendsto (a - 1)
  rcases hev.exists with ⟨n, hn⟩
  have hmem : x (2 * n + 1) ∈ values :=
    ⟨2 * n + 1, by omega, rfl⟩
  linarith [ha hmem]

/-- Source: `proof_gap/exercise_106/2.txt`; supremum +∞ means unbounded above. -/
theorem gap2 : ¬ BddAbove values := by
  intro hb
  rcases hb with ⟨a, ha⟩
  have hev :
      ∀ᶠ n : ℕ in atTop, a + 1 ≤ (fun n : ℕ => x (2 * n + 2)) n :=
    tendsto_atTop.1 even_tendsto (a + 1)
  rcases hev.exists with ⟨n, hn⟩
  have hmem : x (2 * n + 2) ∈ values :=
    ⟨2 * n + 2, by omega, rfl⟩
  linarith [ha hmem]

/-- Source: `proof_gap/exercise_106/3.txt`; the odd subsequence tends to -∞. -/
theorem gap3 :
    Tendsto (fun n : ℕ => x (2 * n + 1)) atTop (atBot : Filter ℝ) := by
  exact odd_tendsto

/-- Source: `proof_gap/exercise_106/4.txt`; the even subsequence tends to +∞. -/
theorem gap4 :
    Tendsto (fun n : ℕ => x (2 * n + 2)) atTop (atTop : Filter ℝ) := by
  exact even_tendsto

end ProofGap.Exercise106
