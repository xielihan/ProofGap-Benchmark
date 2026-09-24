import ProofGapLean.Prelude.Sequences

open Filter

namespace ProofGap.Exercise107

def x (n : ℕ) : ℝ :=
  -(n : ℝ) * (2 + (-1 : ℝ) ^ n)

def values : Set ℝ :=
  {v | ∃ n : ℕ, 0 < n ∧ v = x n}

private theorem x_le_neg_nat (n : ℕ) : x n ≤ -(n : ℝ) := by
  rcases neg_one_pow_eq_or ℝ n with h | h
  · have hn : (0 : ℝ) ≤ n := by positivity
    rw [x, h]
    norm_num
    linarith
  · rw [x, h]
    ring_nf
    exact le_rfl

private theorem x_tendsto_atBot :
    Tendsto x atTop (atBot : Filter ℝ) := by
  have hcast :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop (atTop : Filter ℝ) :=
    tendsto_natCast_atTop_atTop
  have hneg :
      Tendsto (fun n : ℕ => -(n : ℝ)) atTop (atBot : Filter ℝ) :=
    tendsto_neg_atTop_atBot.comp hcast
  exact Filter.tendsto_atBot_mono x_le_neg_nat hneg

/-- Source: `proof_gap/exercise_107/1.txt`. -/
theorem gap1 : ¬ BddBelow values := by
  intro hb
  rcases hb with ⟨a, ha⟩
  have hev : ∀ᶠ n : ℕ in atTop, x n ≤ a - 1 :=
    tendsto_atBot.1 x_tendsto_atBot (a - 1)
  rcases (hev.and (eventually_ge_atTop 1)).exists with ⟨n, hxn, hn⟩
  have hmem : x n ∈ values := ⟨n, by omega, rfl⟩
  linarith [ha hmem]

/-- Source: `proof_gap/exercise_107/2.txt`. -/
theorem gap2 : sSup values = -1 := by
  have hgreatest : IsGreatest values (-1) := by
    constructor
    · refine ⟨1, by omega, ?_⟩
      norm_num [x]
    · intro v hv
      rcases hv with ⟨n, hn, rfl⟩
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith [x_le_neg_nat n]
  exact hgreatest.csSup_eq

/-- Source: `proof_gap/exercise_107/3.txt`. -/
theorem gap3 : Tendsto x atTop (atBot : Filter ℝ) := by
  exact x_tendsto_atBot

/-- Source: `proof_gap/exercise_107/4.txt`. -/
theorem gap4 : Tendsto x atTop (atBot : Filter ℝ) := by
  exact x_tendsto_atBot

end ProofGap.Exercise107
