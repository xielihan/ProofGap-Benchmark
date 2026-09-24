import ProofGapLean.Prelude.Analysis

open Filter Topology

namespace ProofGap.Exercise103

noncomputable section

def x (n : ℕ) : ℝ :=
  1 + (n : ℝ) / ((n : ℝ) + 1) * Real.cos ((n : ℝ) * Real.pi / 2)

def values : Set ℝ :=
  {v | ∃ n : ℕ, 0 < n ∧ v = x n}

private def p₀ (k : ℕ) : ℕ := 4 * k + 2

private def p₂ (k : ℕ) : ℕ := 4 * k + 4

private theorem p₀_strictMono : StrictMono p₀ := by
  intro a b hab
  dsimp [p₀]
  omega

private theorem p₂_strictMono : StrictMono p₂ := by
  intro a b hab
  dsimp [p₂]
  omega

private theorem x_bounds (n : ℕ) : 0 ≤ x n ∧ x n ≤ 2 := by
  have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcoeff0 : 0 ≤ (n : ℝ) / ((n : ℝ) + 1) := by positivity
  have hcoeff1 : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
    exact (div_le_one hden).2 (by linarith)
  have hcos0 := Real.neg_one_le_cos ((n : ℝ) * Real.pi / 2)
  have hcos1 := Real.cos_le_one ((n : ℝ) * Real.pi / 2)
  have hlo := mul_le_mul_of_nonneg_left hcos0 hcoeff0
  have hhi := mul_le_mul_of_nonneg_left hcos1 hcoeff0
  unfold x
  constructor <;> nlinarith

private theorem x_p₀ (k : ℕ) :
    x (p₀ k) = 1 / (((p₀ k : ℕ) : ℝ) + 1) := by
  have hang :
      ((p₀ k : ℕ) : ℝ) * Real.pi / 2 =
        ((2 * k + 1 : ℕ) : ℝ) * Real.pi := by
    dsimp [p₀]
    push_cast
    ring
  rw [x, hang, Real.cos_nat_mul_pi]
  have hpow : ((-1 : ℝ) ^ (2 * k + 1)) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  rw [hpow]
  have hne : (((p₀ k : ℕ) : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

private theorem x_p₂ (k : ℕ) :
    x (p₂ k) = 2 - 1 / (((p₂ k : ℕ) : ℝ) + 1) := by
  have hang :
      ((p₂ k : ℕ) : ℝ) * Real.pi / 2 =
        ((2 * k + 2 : ℕ) : ℝ) * Real.pi := by
    dsimp [p₂]
    push_cast
    ring
  rw [x, hang, Real.cos_nat_mul_pi]
  have hpow : ((-1 : ℝ) ^ (2 * k + 2)) = 1 := by
    rw [show 2 * k + 2 = 2 * (k + 1) by omega, pow_mul]
    norm_num
  rw [hpow]
  have hne : (((p₂ k : ℕ) : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

private theorem reciprocal_p₀_tendsto :
    Tendsto (fun k : ℕ => 1 / (((p₀ k : ℕ) : ℝ) + 1)) atTop (𝓝 0) := by
  have hp : Tendsto p₀ atTop atTop := p₀_strictMono.tendsto_atTop
  have hcast :
      Tendsto (fun k : ℕ => ((p₀ k : ℕ) : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp hp
  have hden :
      Tendsto (fun k : ℕ => ((p₀ k : ℕ) : ℝ) + 1) atTop atTop :=
    Filter.tendsto_atTop_mono (fun k => by linarith) hcast
  simpa [one_div] using
    ((tendsto_inv_atTop_zero :
      Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0)).comp hden)

private theorem reciprocal_p₂_tendsto :
    Tendsto (fun k : ℕ => 1 / (((p₂ k : ℕ) : ℝ) + 1)) atTop (𝓝 0) := by
  have hp : Tendsto p₂ atTop atTop := p₂_strictMono.tendsto_atTop
  have hcast :
      Tendsto (fun k : ℕ => ((p₂ k : ℕ) : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp hp
  have hden :
      Tendsto (fun k : ℕ => ((p₂ k : ℕ) : ℝ) + 1) atTop atTop :=
    Filter.tendsto_atTop_mono (fun k => by linarith) hcast
  simpa [one_div] using
    ((tendsto_inv_atTop_zero :
      Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0)).comp hden)

private theorem x_p₀_tendsto : Tendsto (x ∘ p₀) atTop (𝓝 0) := by
  apply reciprocal_p₀_tendsto.congr'
  filter_upwards with k
  exact (x_p₀ k).symm

private theorem x_p₂_tendsto : Tendsto (x ∘ p₂) atTop (𝓝 2) := by
  have h :
      Tendsto
        (fun k : ℕ => (2 : ℝ) - 1 / (((p₂ k : ℕ) : ℝ) + 1))
        atTop (𝓝 ((2 : ℝ) - 0)) :=
    tendsto_const_nhds.sub reciprocal_p₂_tendsto
  norm_num at h
  apply h.congr'
  filter_upwards with k
  simpa [one_div, Function.comp_apply] using (x_p₂ k).symm

/-- Source: `proof_gap/exercise_103/1.txt`. -/
theorem gap1 : x 1 = 1 := by
  norm_num [x, Real.cos_pi_div_two]

/-- Source: `proof_gap/exercise_103/2.txt`. -/
theorem gap2 : x 2 = 1 - 2 / 3 := by
  norm_num [x, Real.cos_pi]

/-- Source: `proof_gap/exercise_103/3.txt`. -/
theorem gap3 : x 3 = 1 := by
  rw [x]
  norm_num
  have hang : (3 : ℝ) * Real.pi / 2 = Real.pi + Real.pi / 2 := by ring
  rw [hang, Real.cos_add, Real.cos_pi, Real.sin_pi,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  norm_num

/-- Source: `proof_gap/exercise_103/4.txt`. -/
theorem gap4 : x 4 = 1 + 4 / 5 := by
  rw [x]
  norm_num
  have hang : (4 : ℝ) * Real.pi / 2 = 2 * Real.pi := by ring
  rw [hang, Real.cos_two_pi]
  norm_num

/-- Source: `proof_gap/exercise_103/5.txt`. -/
theorem gap5 : sInf values = 0 := by
  have hglb : IsGLB values 0 := by
    constructor
    · intro v hv
      rcases hv with ⟨n, hn, rfl⟩
      exact (x_bounds n).1
    · intro b hb
      by_contra h
      have hbpos : 0 < b := lt_of_not_ge h
      have hev : ∀ᶠ k : ℕ in atTop, x (p₀ k) < b :=
        x_p₀_tendsto.eventually (Iio_mem_nhds hbpos)
      rcases hev.exists with ⟨k, hk⟩
      have hmem : x (p₀ k) ∈ values :=
        ⟨p₀ k, by simp [p₀], rfl⟩
      linarith [hb hmem]
  exact hglb.csInf_eq ⟨x 1, ⟨1, by omega, rfl⟩⟩

/-- Source: `proof_gap/exercise_103/6.txt`. -/
theorem gap6 : sSup values = 2 := by
  have hlub : IsLUB values 2 := by
    constructor
    · intro v hv
      rcases hv with ⟨n, hn, rfl⟩
      exact (x_bounds n).2
    · intro b hb
      by_contra h
      have hblt : b < 2 := lt_of_not_ge h
      have hev : ∀ᶠ k : ℕ in atTop, b < x (p₂ k) :=
        x_p₂_tendsto.eventually (Ioi_mem_nhds hblt)
      rcases hev.exists with ⟨k, hk⟩
      have hmem : x (p₂ k) ∈ values :=
        ⟨p₂ k, by simp [p₂], rfl⟩
      linarith [hb hmem]
  exact hlub.csSup_eq ⟨x 1, ⟨1, by omega, rfl⟩⟩

/-- Source: `proof_gap/exercise_103/7.txt`. -/
theorem gap7 : sInf (ProofGap.ClusterSet x) = 0 := by
  have hleast : IsLeast (ProofGap.ClusterSet x) 0 := by
    constructor
    · exact ⟨p₀, p₀_strictMono, x_p₀_tendsto⟩
    · intro a ha
      rcases ha with ⟨p, hp, hlim⟩
      apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      filter_upwards with k
      exact (x_bounds (p k)).1
  exact hleast.csInf_eq

/-- Source: `proof_gap/exercise_103/8.txt`. -/
theorem gap8 : sSup (ProofGap.ClusterSet x) = 2 := by
  have hgreatest : IsGreatest (ProofGap.ClusterSet x) 2 := by
    constructor
    · exact ⟨p₂, p₂_strictMono, x_p₂_tendsto⟩
    · intro a ha
      rcases ha with ⟨p, hp, hlim⟩
      apply le_of_tendsto hlim
      filter_upwards with k
      exact (x_bounds (p k)).2
  exact hgreatest.csSup_eq

end

end ProofGap.Exercise103
