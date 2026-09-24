import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Interval

noncomputable def seriesFrom (m : ℕ) (u : ℕ → ℝ) : ℝ := ∑' n : ℕ, if n < m then 0 else u n
noncomputable def finiteSum (a b : ℕ) (u : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.Icc a b, u k
def ConvergentSeries (_x : ℝ) : Prop := True
def DivergentSeries (_x : ℝ) : Prop := True
def ConvergentSeriesTo (_x _s : ℝ) : Prop := True
def SeqLimTo (u : ℕ → ℝ) (s : ℝ) : Prop := Filter.Tendsto u Filter.atTop (𝓝 s)

-- exercise: exercise_2554

theorem proof_gap_exercise_2554_1 (a A l S : ℕ → ℝ) (p : ℕ → ℕ) :
    ∀ k : ℕ, ∀ n : ℕ, 0 < n → l n = finiteSum 1 n A := by
  sorry

theorem proof_gap_exercise_2554_2 (a A l S : ℕ → ℝ) (p : ℕ → ℕ) :
    ∀ k : ℕ, ∀ n : ℕ, 0 < n → l n = finiteSum 1 (p (n + 1) - 1) a := by
  sorry

theorem proof_gap_exercise_2554_3 (a A l S : ℕ → ℝ) (p : ℕ → ℕ) :
    ∀ n : ℕ, 0 < n → l n = S (p (n + 1) - 1) := by
  sorry

theorem proof_gap_exercise_2554_4 (a A l Sn : ℕ → ℝ) (p : ℕ → ℕ) (S : ℝ) :
    ∀ n : ℕ, SeqLimTo Sn S := by
  sorry

theorem proof_gap_exercise_2554_5 (a A l Sn : ℕ → ℝ) (p : ℕ → ℕ) (S : ℝ) :
    ∀ n : ℕ, SeqLimTo l S ↔ SeqLimTo (fun m => Sn (p (m + 1) - 1)) S := by
  sorry

theorem proof_gap_exercise_2554_6 (a A l Sn : ℕ → ℝ) (p : ℕ → ℕ) (S : ℝ) :
    ∀ n : ℕ, SeqLimTo (fun m => Sn (p (m + 1) - 1)) S := by
  sorry

theorem proof_gap_exercise_2554_7 (a A l Sn : ℕ → ℝ) (p : ℕ → ℕ) (S : ℝ) :
    ∀ n : ℕ, SeqLimTo l S := by
  sorry

theorem proof_gap_exercise_2554_8 (a A l Sn : ℕ → ℝ) (p : ℕ → ℕ) (S : ℝ) :
    ∀ n : ℕ, ConvergentSeriesTo (seriesFrom 1 A) S := by
  sorry

theorem proof_gap_exercise_2554_9 (b B : ℕ → ℝ) :
    ∀ n : ℕ, seriesFrom 1 b = seriesFrom 1 (fun n => (-1 : ℝ) ^ (n - 1)) := by
  sorry

theorem proof_gap_exercise_2554_10 (b B : ℕ → ℝ) :
    ∀ n : ℕ, DivergentSeries (seriesFrom 1 b) := by
  sorry

theorem proof_gap_exercise_2554_11 (b B : ℕ → ℝ) :
    ∀ n : ℕ, 0 < n → B n = 1 - 1 ∧ (1 : ℝ) - 1 = 0 := by
  sorry

theorem proof_gap_exercise_2554_12 (b B : ℕ → ℝ) :
    ∀ n : ℕ, ConvergentSeriesTo (seriesFrom 1 B) 0 := by
  sorry

theorem proof_gap_exercise_2554_13 :
    ∀ n : ℕ, ∃ b B : ℕ → ℝ,
      DivergentSeries (seriesFrom 1 b) ∧ ConvergentSeries (seriesFrom 1 B)
        ∧ (∀ n : ℕ, 0 < n → B n = b (2 * n - 1) + b (2 * n)) := by
  sorry

theorem proof_gap_exercise_2554_14 (A : ℕ → ℝ) (S : ℝ) :
    ConvergentSeriesTo (seriesFrom 1 A) S ∧
      (∃ b B : ℕ → ℝ,
        DivergentSeries (seriesFrom 1 b) ∧ ConvergentSeries (seriesFrom 1 B)
          ∧ (∀ n : ℕ, 0 < n → B n = b (2 * n - 1) + b (2 * n))) := by
  sorry
