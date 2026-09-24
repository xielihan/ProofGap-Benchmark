import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Finite
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Topology

namespace ProofGap.Exercise139

noncomputable section

def partialSum (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, x i

def cesaro (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  partialSum x n / (n : ℝ)

private theorem Icc_eq_Ico_succ (a b : ℕ) :
    Finset.Icc a b = Finset.Ico a (b + 1) := by
  ext i
  simp

private theorem partialSum_add_tail (x : ℕ → ℝ) {N n : ℕ}
    (hN : N ≤ n) :
    partialSum x N + (∑ i ∈ Finset.Icc (N + 1) n, x i) =
      partialSum x n := by
  unfold partialSum
  rw [Icc_eq_Ico_succ, Icc_eq_Ico_succ, Icc_eq_Ico_succ]
  exact Finset.sum_Ico_consecutive x (by omega) (by omega)

/-- Source: `proof_gap/exercise_139/1.txt`. -/
theorem gap1 (x : ℕ → ℝ)
    (hx : Tendsto x atTop (atTop : Filter ℝ)) :
    ∀ M : ℝ, 0 < M →
      ∃ N : ℕ, ∀ n : ℕ, N < n → x n > 3 * M := by
  intro M hM
  have hev : ∀ᶠ n : ℕ in atTop, 3 * M < x n :=
    hx (Ioi_mem_atTop (3 * M))
  rw [eventually_atTop] at hev
  rcases hev with ⟨N, hN⟩
  exact ⟨N, fun n hn => hN n hn.le⟩

/-- Source: `proof_gap/exercise_139/2.txt`; N depends on M and n>N. -/
theorem gap2 (x : ℕ → ℝ) :
    ∀ M : ℝ, 0 < M → ∀ N n : ℕ, N < n →
      cesaro x n =
        partialSum x N / (n : ℝ) +
          (partialSum x n - partialSum x N) / ((n : ℝ) - N) *
            (1 - (N : ℝ) / n) := by
  intro M hM N n hN
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  have hden : (n : ℝ) - N ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hN.ne')
  have hdiff :
      partialSum x n - partialSum x N =
        ∑ i ∈ Finset.Icc (N + 1) n, x i := by
    linarith [partialSum_add_tail x hN.le]
  rw [cesaro, hdiff, ← partialSum_add_tail x hN.le]
  field_simp [hn0, hden]

/-- Source: `proof_gap/exercise_139/3.txt`. -/
theorem gap3 (x : ℕ → ℝ) (M : ℝ) (N n : ℕ)
    (hM : 0 < M) (hN : N < n)
    (htail : ∀ k : ℕ, N < k → k ≤ n → x k > 3 * M) :
    partialSum x N / (n : ℝ) +
        (partialSum x n - partialSum x N) / ((n : ℝ) - N) *
          (1 - (N : ℝ) / n) >
      partialSum x N / (n : ℝ) + 3 * M * (1 - (N : ℝ) / n) := by
  have hsnonempty : (Finset.Icc (N + 1) n).Nonempty :=
    ⟨N + 1, by simp; omega⟩
  have htailsum :
      ∑ i ∈ Finset.Icc (N + 1) n, (3 * M) <
        ∑ i ∈ Finset.Icc (N + 1) n, x i := by
    apply Finset.sum_lt_sum_of_nonempty hsnonempty
    intro i hi
    have hi' : N < i ∧ i ≤ n := by simpa using hi
    exact htail i hi'.1 hi'.2
  have hcard : (Finset.Icc (N + 1) n).card = n - N := by simp
  simp only [Finset.sum_const, nsmul_eq_mul] at htailsum
  rw [hcard] at htailsum
  have hcast : ((n - N : ℕ) : ℝ) = (n : ℝ) - N := by
    rw [Nat.cast_sub hN.le]
  rw [hcast] at htailsum
  have hdiff :
      partialSum x n - partialSum x N =
        ∑ i ∈ Finset.Icc (N + 1) n, x i := by
    linarith [partialSum_add_tail x hN.le]
  rw [hdiff]
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hdR : (0 : ℝ) < (n : ℝ) - N := by
    have : (N : ℝ) < n := by exact_mod_cast hN
    linarith
  have hw0 : 0 < 1 - (N : ℝ) / n := by
    rw [sub_pos, div_lt_one hnR]
    exact_mod_cast hN
  have havg :
      3 * M <
        (∑ i ∈ Finset.Icc (N + 1) n, x i) / ((n : ℝ) - N) := by
    rw [lt_div_iff₀ hdR]
    nlinarith
  have hmul := mul_lt_mul_of_pos_right havg hw0
  linarith

/-- Source: `proof_gap/exercise_139/4.txt`. -/
theorem gap4 (x : ℕ → ℝ) (M : ℝ) (N n : ℕ)
    (h : cesaro x n >
      partialSum x N / (n : ℝ) + 3 * M * (1 - (N : ℝ) / n)) :
    cesaro x n >
      partialSum x N / (n : ℝ) + 3 * M * (1 - (N : ℝ) / n) := by
  exact h

/-- Source: `proof_gap/exercise_139/5.txt`. -/
theorem gap5 (x : ℕ → ℝ) (N : ℕ) :
    Tendsto (fun n : ℕ => partialSum x N / (n : ℝ)) atTop
      (𝓝 0) := by
  exact tendsto_const_div_atTop_nhds_zero_nat _

/-- Source: `proof_gap/exercise_139/6.txt`. -/
theorem gap6 (N : ℕ) :
    Tendsto (fun n : ℕ => 1 - (N : ℝ) / n) atTop
      (𝓝 1) := by
  have h :
      Tendsto (fun n : ℕ => (N : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  simpa using tendsto_const_nhds.sub h

/-- Source: `proof_gap/exercise_139/7.txt`; N' depends on M and N. -/
theorem gap7 (x : ℕ → ℝ) (M : ℝ) (N : ℕ)
    (hM : 0 < M) :
    ∃ N' : ℕ, N < N' ∧ ∀ n : ℕ, N' < n →
      |partialSum x N| / (n : ℝ) < M / 2 ∧
      1 - (N : ℝ) / n > 1 / 2 := by
  have hM2 : 0 < M / 2 := by linarith
  have hhead :
      Tendsto (fun n : ℕ => |partialSum x N| / (n : ℝ))
        atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hweight := gap6 N
  have hev1 : ∀ᶠ n : ℕ in atTop, |partialSum x N| / (n : ℝ) < M / 2 :=
    (tendsto_order.1 hhead).2 _ hM2
  have hev2 : ∀ᶠ n : ℕ in atTop, 1 / 2 < 1 - (N : ℝ) / n :=
    (tendsto_order.1 hweight).1 _ (by norm_num)
  rw [eventually_atTop] at hev1 hev2
  rcases hev1 with ⟨K₁, hK₁⟩
  rcases hev2 with ⟨K₂, hK₂⟩
  refine ⟨max (max K₁ K₂) N + 1, by omega, fun n hn => ?_⟩
  exact ⟨hK₁ n (by omega), hK₂ n (by omega)⟩

/-- Source: `proof_gap/exercise_139/8.txt`; the cutoff is existential. -/
theorem gap8 (x : ℕ → ℝ)
    (hx : Tendsto x atTop (atTop : Filter ℝ)) :
    ∀ M : ℝ, 0 < M →
      ∃ N : ℕ, ∀ n : ℕ, N < n → cesaro x n > M := by
  intro M hM
  rcases gap1 x hx M hM with ⟨N, htail⟩
  rcases gap7 x M N hM with ⟨N', hNN', hsmall⟩
  refine ⟨N', fun n hn => ?_⟩
  have hNn : N < n := hNN'.trans hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsnonempty : (Finset.Icc (N + 1) n).Nonempty :=
    ⟨N + 1, by simp; omega⟩
  have htailsum :
      ∑ i ∈ Finset.Icc (N + 1) n, (3 * M) <
        ∑ i ∈ Finset.Icc (N + 1) n, x i := by
    apply Finset.sum_lt_sum_of_nonempty hsnonempty
    intro i hi
    have hi' : N < i ∧ i ≤ n := by simpa using hi
    exact htail i hi'.1
  have hcard : (Finset.Icc (N + 1) n).card = n - N := by simp
  simp only [Finset.sum_const, nsmul_eq_mul] at htailsum
  rw [hcard] at htailsum
  have hcast : ((n - N : ℕ) : ℝ) = (n : ℝ) - N := by
    rw [Nat.cast_sub hNn.le]
  rw [hcast] at htailsum
  have htailavg :
      3 * M * (1 - (N : ℝ) / n) <
        (∑ i ∈ Finset.Icc (N + 1) n, x i) / (n : ℝ) := by
    rw [lt_div_iff₀ hnR]
    have hid :
        3 * M * (1 - (N : ℝ) / n) * (n : ℝ) =
          ((n : ℝ) - N) * (3 * M) := by
      field_simp
    rw [hid]
    exact htailsum
  rcases hsmall n hn with ⟨hhead, hweight⟩
  have habs :
      |partialSum x N / (n : ℝ)| = |partialSum x N| / (n : ℝ) := by
    rw [abs_div, abs_of_pos hnR]
  rw [← habs] at hhead
  have hhead_lower :
      -(M / 2) < partialSum x N / (n : ℝ) :=
    (abs_lt.1 hhead).1
  rw [cesaro, ← partialSum_add_tail x hNn.le, add_div]
  nlinarith

/-- Source: `proof_gap/exercise_139/9.txt`. -/
theorem gap9 (x : ℕ → ℝ)
    (hx : Tendsto x atTop (atTop : Filter ℝ)) :
    Tendsto (cesaro x) atTop (atTop : Filter ℝ) := by
  apply tendsto_atTop.2
  intro M
  rcases gap8 x hx (max M 1) (by positivity) with ⟨N, hN⟩
  filter_upwards [Ici_mem_atTop (N + 1)] with n hn
  have hn' : N < n := Nat.lt_of_succ_le hn
  exact le_of_lt ((le_max_left M 1).trans_lt (hN n hn'))

/-- Source: `proof_gap/exercise_139/10.txt`. -/
theorem gap10 (x : ℕ → ℝ)
    (hx : Tendsto x atTop (atTop : Filter ℝ)) :
    Tendsto (cesaro x) atTop (atTop : Filter ℝ) := by
  exact gap9 x hx

end

end ProofGap.Exercise139
