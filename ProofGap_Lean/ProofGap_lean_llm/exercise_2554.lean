import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Interval
open Filter

noncomputable def seriesFrom (m : ℕ) (u : ℕ → ℝ) : ℝ := ∑' n : ℕ, if n < m then 0 else u n
noncomputable def finiteSum (a b : ℕ) (u : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.Icc a b, u k

def termsFromOne (u : ℕ → ℝ) : ℕ → ℝ := fun n => if n = 0 then 0 else u n
def ConvergentSeries (u : ℕ → ℝ) : Prop := Summable (termsFromOne u)
def DivergentSeries (u : ℕ → ℝ) : Prop := ¬ Summable (termsFromOne u)
def ConvergentSeriesTo (u : ℕ → ℝ) (s : ℝ) : Prop := HasSum (termsFromOne u) s
def SeqLimTo (u : ℕ → ℝ) (s : ℝ) : Prop := Tendsto u atTop (𝓝 s)

-- exercise: exercise_2554

theorem proof_gap_exercise_2554_1
  (a A l : ℕ → ℝ) (p : ℕ → ℕ) (S : ℝ)
  (hp1 : p 1 = 1)
  (hpinc : ∀ n : ℕ, 0 < n → p n < p (n + 1))
  (hblock : ∀ n : ℕ, 0 < n → A n = finiteSum (p n) (p (n + 1) - 1) a)
  (hconv : ConvergentSeriesTo a S)
  (hl : ∀ n : ℕ, 0 < n → l n = finiteSum 1 n A) :
    ∀ k : ℕ, ∀ n : ℕ, 0 < n → l n = finiteSum 1 n A := by
  sorry

theorem proof_gap_exercise_2554_2
  (a A l : ℕ → ℝ) (p : ℕ → ℕ) (S : ℝ)
  (hp1 : p 1 = 1)
  (hpinc : ∀ n : ℕ, 0 < n → p n < p (n + 1))
  (hblock : ∀ n : ℕ, 0 < n → A n = finiteSum (p n) (p (n + 1) - 1) a)
  (hconv : ConvergentSeriesTo a S)
  (hl : ∀ n : ℕ, 0 < n → l n = finiteSum 1 n A)
  (h1 : ∀ k : ℕ, ∀ n : ℕ, 0 < n → l n = finiteSum 1 n A) :
    ∀ k : ℕ, ∀ n : ℕ, 0 < n → l n = finiteSum 1 (p (n + 1) - 1) a := by
  sorry

theorem proof_gap_exercise_2554_3
  (a A l Sn : ℕ → ℝ) (p : ℕ → ℕ) (S : ℝ)
  (hp1 : p 1 = 1)
  (hpinc : ∀ n : ℕ, 0 < n → p n < p (n + 1))
  (hblock : ∀ n : ℕ, 0 < n → A n = finiteSum (p n) (p (n + 1) - 1) a)
  (hconv : ConvergentSeriesTo a S)
  (hl : ∀ n : ℕ, 0 < n → l n = finiteSum 1 n A)
  (h2 : ∀ k : ℕ, ∀ n : ℕ, 0 < n → l n = finiteSum 1 (p (n + 1) - 1) a)
  (hSn : ∀ n : ℕ, Sn n = finiteSum 1 n a) :
    ∀ n : ℕ, 0 < n → l n = Sn (p (n + 1) - 1) := by
  sorry

theorem proof_gap_exercise_2554_4
  (a A l Sn : ℕ → ℝ) (p : ℕ → ℕ) (S : ℝ)
  (hconv : ConvergentSeriesTo a S)
  (hSn : ∀ n : ℕ, Sn n = finiteSum 1 n a) :
    SeqLimTo Sn S := by
  sorry

theorem proof_gap_exercise_2554_5
  (a A l Sn : ℕ → ℝ) (p : ℕ → ℕ) (S : ℝ)
  (h3 : ∀ n : ℕ, 0 < n → l n = Sn (p (n + 1) - 1)) :
    SeqLimTo l S ↔ SeqLimTo (fun m => Sn (p (m + 1) - 1)) S := by
  sorry

theorem proof_gap_exercise_2554_6
  (a A l Sn : ℕ → ℝ) (p : ℕ → ℕ) (S : ℝ)
  (hpinc : ∀ n : ℕ, 0 < n → p n < p (n + 1))
  (h4 : SeqLimTo Sn S) :
    SeqLimTo (fun m => Sn (p (m + 1) - 1)) S := by
  sorry

theorem proof_gap_exercise_2554_7
  (a A l Sn : ℕ → ℝ) (p : ℕ → ℕ) (S : ℝ)
  (h5 : SeqLimTo l S ↔ SeqLimTo (fun m => Sn (p (m + 1) - 1)) S)
  (h6 : SeqLimTo (fun m => Sn (p (m + 1) - 1)) S) :
    SeqLimTo l S := by
  sorry

theorem proof_gap_exercise_2554_8
  (a A l Sn : ℕ → ℝ) (p : ℕ → ℕ) (S : ℝ)
  (hl : ∀ n : ℕ, 0 < n → l n = finiteSum 1 n A)
  (h7 : SeqLimTo l S) :
    ConvergentSeriesTo A S := by
  sorry

theorem proof_gap_exercise_2554_9
  (b B : ℕ → ℝ)
  (hb : ∀ n : ℕ, 0 < n → b n = (-1 : ℝ) ^ (n - 1)) :
    seriesFrom 1 b = seriesFrom 1 (fun n => (-1 : ℝ) ^ (n - 1)) := by
  sorry

theorem proof_gap_exercise_2554_10
  (b B : ℕ → ℝ)
  (hb : ∀ n : ℕ, 0 < n → b n = (-1 : ℝ) ^ (n - 1)) :
    DivergentSeries b := by
  sorry

theorem proof_gap_exercise_2554_11
  (b B : ℕ → ℝ)
  (hb : ∀ n : ℕ, 0 < n → b n = (-1 : ℝ) ^ (n - 1))
  (hB : ∀ n : ℕ, 0 < n → B n = b (2 * n - 1) + b (2 * n)) :
    ∀ n : ℕ, 0 < n → B n = 1 - 1 ∧ (1 : ℝ) - 1 = 0 := by
  sorry

theorem proof_gap_exercise_2554_12
  (b B : ℕ → ℝ)
  (hBzero : ∀ n : ℕ, 0 < n → B n = 1 - 1 ∧ (1 : ℝ) - 1 = 0) :
    ConvergentSeriesTo B 0 := by
  sorry

theorem proof_gap_exercise_2554_13 :
    ∃ b B : ℕ → ℝ,
      DivergentSeries b ∧ ConvergentSeries B
        ∧ (∀ n : ℕ, 0 < n → B n = b (2 * n - 1) + b (2 * n)) := by
  sorry

theorem proof_gap_exercise_2554_14
  (a A l Sn : ℕ → ℝ) (p : ℕ → ℕ) (S : ℝ)
  (hA : ConvergentSeriesTo A S)
  (hex : ∃ b B : ℕ → ℝ,
      DivergentSeries b ∧ ConvergentSeries B
        ∧ (∀ n : ℕ, 0 < n → B n = b (2 * n - 1) + b (2 * n))) :
    ConvergentSeriesTo A S ∧
      (∃ b B : ℕ → ℝ,
        DivergentSeries b ∧ ConvergentSeries B
          ∧ (∀ n : ℕ, 0 < n → B n = b (2 * n - 1) + b (2 * n))) := by
  sorry
