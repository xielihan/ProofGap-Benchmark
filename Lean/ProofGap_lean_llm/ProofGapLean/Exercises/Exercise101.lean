import ProofGapLean.Prelude.Sequences

open Filter Topology

namespace ProofGap.Exercise101

noncomputable section

def x (n : ℕ) : ℝ :=
  1 - 1 / (n : ℝ)

def values : Set ℝ :=
  {v | ∃ n : ℕ, 0 < n ∧ v = x n}

private theorem x_tendsto_one : Tendsto x atTop (𝓝 1) := by
  change Tendsto (fun n : ℕ => 1 - 1 / (n : ℝ)) atTop (𝓝 1)
  have hinv :
      Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
    simpa [one_div] using
      ((tendsto_inv_atTop_zero :
          Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0)).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  simpa using
    (tendsto_const_nhds.sub hinv :
      Tendsto (fun n : ℕ => 1 - 1 / (n : ℝ)) atTop (𝓝 (1 - 0)))

/-- Source: `proof_gap/exercise_101/1.txt`. -/
theorem gap1 :
    sInf values = 0 := by
  have hleast : IsLeast values 0 := by
    constructor
    · exact ⟨1, by omega, by norm_num [x]⟩
    · intro v hv
      rcases hv with ⟨n, hn, rfl⟩
      unfold x
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hinv : 1 / (n : ℝ) ≤ 1 :=
        (div_le_one hnR).mpr (by exact_mod_cast hn)
      linarith
  exact hleast.csInf_eq

/-- Source: `proof_gap/exercise_101/2.txt`. -/
theorem gap2 :
    sSup values = 1 := by
  have hlub : IsLUB values 1 := by
    constructor
    · intro v hv
      rcases hv with ⟨n, hn, rfl⟩
      unfold x
      have : 0 ≤ 1 / (n : ℝ) := by positivity
      linarith
    · intro b hb
      by_contra h
      have hblt : b < 1 := lt_of_not_ge h
      have hev : ∀ᶠ n : ℕ in atTop, b < x n :=
        x_tendsto_one.eventually (Ioi_mem_nhds hblt)
      rcases (hev.and (eventually_ge_atTop 1)).exists with ⟨n, hxn, hn⟩
      have hxmem : x n ∈ values := ⟨n, by omega, rfl⟩
      linarith [hb hxmem]
  exact hlub.csSup_eq ⟨x 1, ⟨1, by omega, rfl⟩⟩

/-- Source: `proof_gap/exercise_101/3.txt`; the convergent sequence has liminf 1. -/
theorem gap3 :
    Tendsto x atTop (𝓝 1) := by
  exact x_tendsto_one

/-- Source: `proof_gap/exercise_101/4.txt`; the convergent sequence has limsup 1. -/
theorem gap4 :
    Tendsto x atTop (𝓝 1) := by
  exact x_tendsto_one

/-- Source: `proof_gap/exercise_101/5.txt`. -/
theorem gap5 :
    Tendsto x atTop (𝓝 1) := by
  exact x_tendsto_one

end

end ProofGap.Exercise101
