import ProofGapLean.Prelude.Analysis

namespace ProofGap.Exercise2690

noncomputable section

open Filter
open scoped BigOperators

def weight (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

def oscillation (n : ℕ) : ℝ :=
  Real.sin (n + 1) * Real.sin (((n + 1 : ℕ) : ℝ) ^ 2)

def cosineDifference (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) *
    (Real.cos (((n + 1 : ℕ) : ℝ) * n) -
      Real.cos (((n + 1 : ℕ) : ℝ) * (n + 2)))

def partialOscillation (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, oscillation n

theorem gap1 :
    Antitone weight := by
  intro m n hmn
  simp only [weight]
  gcongr

theorem gap2 :
    Tendsto weight atTop (nhds 0) := by
  change Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0)
  simpa only [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem gap3 :
    ∀ N : ℕ,
      |partialOscillation N| =
        |∑ n ∈ Finset.range N, cosineDifference n| := by
  intro N
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  simp only [oscillation, cosineDifference]
  have h := Real.two_mul_sin_mul_sin
    ((((n + 1 : ℕ) : ℝ) ^ 2)) (((n + 1 : ℕ) : ℝ))
  have h' :
      2 * Real.sin (((n + 1 : ℕ) : ℝ)) *
          Real.sin ((((n + 1 : ℕ) : ℝ) ^ 2)) =
        Real.cos (((n + 1 : ℕ) : ℝ) * n) -
          Real.cos (((n + 1 : ℕ) : ℝ) * (n + 2)) := by
    calc
      2 * Real.sin (((n + 1 : ℕ) : ℝ)) *
            Real.sin ((((n + 1 : ℕ) : ℝ) ^ 2)) =
          2 * Real.sin ((((n + 1 : ℕ) : ℝ) ^ 2)) *
            Real.sin (((n + 1 : ℕ) : ℝ)) := by ring
      _ = Real.cos ((((n + 1 : ℕ) : ℝ) ^ 2) - ((n + 1 : ℕ) : ℝ)) -
            Real.cos ((((n + 1 : ℕ) : ℝ) ^ 2) + ((n + 1 : ℕ) : ℝ)) := h
      _ = Real.cos (((n + 1 : ℕ) : ℝ) * n) -
            Real.cos (((n + 1 : ℕ) : ℝ) * (n + 2)) := by
        congr 1 <;> congr 1 <;> push_cast <;> ring
  rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by norm_num]
  nlinarith [h']

theorem gap4 :
    ∀ N : ℕ,
      |∑ n ∈ Finset.range N, cosineDifference n| =
        |(1 / 2 : ℝ) *
          (Real.cos 0 - Real.cos ((N : ℝ) * (N + 1)))| := by
  intro N
  congr 1
  simp only [cosineDifference, ← Finset.mul_sum]
  rw [show
    (∑ n ∈ Finset.range N,
        (Real.cos (((n + 1 : ℕ) : ℝ) * n) -
          Real.cos (((n + 1 : ℕ) : ℝ) * (n + 2)))) =
      ∑ n ∈ Finset.range N,
        (Real.cos ((n : ℝ) * (n + 1)) -
          Real.cos (((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) + 1))) by
    apply Finset.sum_congr rfl
    intro n hn
    congr 2 <;> push_cast <;> ring]
  rw [Finset.sum_range_sub']
  norm_num

theorem gap5 :
    ∀ N : ℕ,
      |(1 / 2 : ℝ) *
          (Real.cos 0 - Real.cos ((N : ℝ) * (N + 1)))| ≤ 1 := by
  intro N
  have h :
      |Real.cos 0 - Real.cos ((N : ℝ) * (N + 1))| ≤ 2 := by
    calc
      |Real.cos 0 - Real.cos ((N : ℝ) * (N + 1))| ≤
          |Real.cos 0| + |Real.cos ((N : ℝ) * (N + 1))| :=
        by simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (Real.cos 0) 0 (Real.cos ((N : ℝ) * (N + 1))))
      _ ≤ 1 + 1 := add_le_add (Real.abs_cos_le_one 0)
        (Real.abs_cos_le_one ((N : ℝ) * (N + 1)))
      _ = 2 := by norm_num
  have h' : |1 - Real.cos ((N : ℝ) * (N + 1))| ≤ 2 := by
    simpa only [Real.cos_zero] using h
  rw [abs_mul]
  norm_num
  linarith [h']

theorem gap6 :
    ∀ N : ℕ, |partialOscillation N| ≤ 1 := by
  intro N
  rw [gap3 N, gap4 N]
  exact gap5 N

theorem gap7 :
    ∃ C : ℝ, ∀ N : ℕ, |partialOscillation N| ≤ C := by
  exact ⟨1, gap6⟩

theorem gap8 :
    ProofGap.SeriesConverges (fun n : ℕ => weight n * oscillation n) := by
  have hc :
      CauchySeq (fun N : ℕ =>
        ∑ n ∈ Finset.range N, weight n * oscillation n) := by
    simpa only [smul_eq_mul] using
      gap1.cauchySeq_series_mul_of_tendsto_zero_of_bounded gap2
        (fun N => by
          simpa only [Real.norm_eq_abs, partialOscillation] using gap6 N)
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hc
  change Summable (fun n : ℕ => weight n * oscillation n)
    (SummationFilter.conditional ℕ)
  refine ⟨l, ?_⟩
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    Filter.tendsto_map'_iff]
  simpa only [Function.comp_apply] using hl

end

end ProofGap.Exercise2690
