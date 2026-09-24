import Mathlib

open Filter
open scoped Topology BigOperators

namespace Exercise2722

def NegIntegerSet (x : ℝ) : Prop := ∃ k : ℤ, k < 0 ∧ x = k
noncomputable def u (x p : ℝ) (n : ℕ) : ℝ := (-1 : ℝ) ^ n / Real.rpow (x + n) p
def ConvergentSeries (f : ℕ → ℝ) : Prop := Summable fun n => f (n + 1)
def DivergentSeries (f : ℕ → ℝ) : Prop := ¬ ConvergentSeries f
def AbsoluteConvergentSeries (f : ℕ → ℝ) : Prop := Summable fun n => |f (n + 1)|
def ConditionalConvergentSeries (f : ℕ → ℝ) : Prop :=
  ConvergentSeries f ∧ ¬ AbsoluteConvergentSeries f
def MonoDecSeq (f : ℕ → ℝ) : Prop := Antitone f

/-- GAP 1: p-series comparison for `1 / (x+n)^p` when `p > 1`. -/
theorem proof_gap_exercise_2722_1 (A C : Set (ℝ × ℝ))
    (hu : ∀ x p : ℝ, ¬ NegIntegerSet x →
      ∀ n : ℕ, 1 ≤ n → u x p n = (-1 : ℝ) ^ n / Real.rpow (x + n) p) :
    ∀ p x : ℝ, p > 1 ∧ ¬ NegIntegerSet x →
      ConvergentSeries (fun n : ℕ => 1 / Real.rpow (x + n) p) := by
  sorry

/-- GAP 2: for `p > 1`, the original alternating series is absolutely convergent. -/
theorem proof_gap_exercise_2722_2 (A C : Set (ℝ × ℝ))
    (hu : ∀ x p : ℝ, ¬ NegIntegerSet x →
      ∀ n : ℕ, 1 ≤ n → u x p n = (-1 : ℝ) ^ n / Real.rpow (x + n) p)
    (hpser : ∀ p x : ℝ, p > 1 ∧ ¬ NegIntegerSet x →
      ConvergentSeries (fun n : ℕ => 1 / Real.rpow (x + n) p)) :
    ∀ p x : ℝ, p > 1 ∧ ¬ NegIntegerSet x → AbsoluteConvergentSeries (u x p) := by
  sorry

/-- GAP 3: when `0 < p ≤ 1`, the positive factor tends to zero. -/
theorem proof_gap_exercise_2722_3 (A C : Set (ℝ × ℝ))
    (hu : ∀ x p : ℝ, ¬ NegIntegerSet x →
      ∀ n : ℕ, 1 ≤ n → u x p n = (-1 : ℝ) ^ n / Real.rpow (x + n) p) :
    ∀ p x : ℝ, 0 < p ∧ p ≤ 1 ∧ ¬ NegIntegerSet x →
      Tendsto (fun n : ℕ => 1 / Real.rpow (x + n) p) atTop (𝓝 0) := by
  sorry

/-- GAP 4: when `0 < p ≤ 1`, the positive factor is monotone decreasing. -/
theorem proof_gap_exercise_2722_4 (A C : Set (ℝ × ℝ))
    (hu : ∀ x p : ℝ, ¬ NegIntegerSet x →
      ∀ n : ℕ, 1 ≤ n → u x p n = (-1 : ℝ) ^ n / Real.rpow (x + n) p) :
    ∀ p x : ℝ, 0 < p ∧ p ≤ 1 ∧ ¬ NegIntegerSet x →
      MonoDecSeq (fun n : ℕ => 1 / Real.rpow (x + n) p) := by
  sorry

/-- GAP 5: Leibniz criterion gives convergence for `0 < p ≤ 1`. -/
theorem proof_gap_exercise_2722_5 (A C : Set (ℝ × ℝ))
    (hzero : ∀ p x : ℝ, 0 < p ∧ p ≤ 1 ∧ ¬ NegIntegerSet x →
      Tendsto (fun n : ℕ => 1 / Real.rpow (x + n) p) atTop (𝓝 0))
    (hmono : ∀ p x : ℝ, 0 < p ∧ p ≤ 1 ∧ ¬ NegIntegerSet x →
      MonoDecSeq (fun n : ℕ => 1 / Real.rpow (x + n) p)) :
    ∀ p x : ℝ, 0 < p ∧ p ≤ 1 ∧ ¬ NegIntegerSet x → ConvergentSeries (u x p) := by
  sorry

/-- GAP 6: in the same range, absolute convergence fails. -/
theorem proof_gap_exercise_2722_6 (A C : Set (ℝ × ℝ))
    (hconv : ∀ p x : ℝ, 0 < p ∧ p ≤ 1 ∧ ¬ NegIntegerSet x → ConvergentSeries (u x p)) :
    ∀ p x : ℝ, 0 < p ∧ p ≤ 1 ∧ ¬ NegIntegerSet x → ¬ AbsoluteConvergentSeries (u x p) := by
  sorry

/-- GAP 7: convergence plus non-absolute convergence is conditional convergence. -/
theorem proof_gap_exercise_2722_7 (A C : Set (ℝ × ℝ))
    (hconv : ∀ p x : ℝ, 0 < p ∧ p ≤ 1 ∧ ¬ NegIntegerSet x → ConvergentSeries (u x p))
    (hnabs : ∀ p x : ℝ, 0 < p ∧ p ≤ 1 ∧ ¬ NegIntegerSet x → ¬ AbsoluteConvergentSeries (u x p)) :
    ∀ p x : ℝ, 0 < p ∧ p ≤ 1 ∧ ¬ NegIntegerSet x →
      ConditionalConvergentSeries (u x p) := by
  sorry

/-- GAP 8: for `p ≤ 0`, the terms do not tend to zero. -/
theorem proof_gap_exercise_2722_8 (A C : Set (ℝ × ℝ))
    (hu : ∀ x p : ℝ, ¬ NegIntegerSet x →
      ∀ n : ℕ, 1 ≤ n → u x p n = (-1 : ℝ) ^ n / Real.rpow (x + n) p) :
    ∀ p x : ℝ, p ≤ 0 → ¬ Tendsto (u x p) atTop (𝓝 0) := by
  sorry

/-- GAP 9: nonzero term limit implies divergence for `p ≤ 0`. -/
theorem proof_gap_exercise_2722_9 (A C : Set (ℝ × ℝ))
    (hnlim : ∀ p x : ℝ, p ≤ 0 → ¬ Tendsto (u x p) atTop (𝓝 0)) :
    ∀ p x : ℝ, p ≤ 0 → DivergentSeries (u x p) := by
  sorry

/-- GAP 10: identify the absolute and conditional convergence domains. -/
theorem proof_gap_exercise_2722_10 (A C : Set (ℝ × ℝ))
    (habs : ∀ p x : ℝ, p > 1 ∧ ¬ NegIntegerSet x → AbsoluteConvergentSeries (u x p))
    (hcond : ∀ p x : ℝ, 0 < p ∧ p ≤ 1 ∧ ¬ NegIntegerSet x →
      ConditionalConvergentSeries (u x p))
    (hdiv : ∀ p x : ℝ, p ≤ 0 → DivergentSeries (u x p)) :
    A = {z : ℝ × ℝ | ¬ NegIntegerSet z.1 ∧ z.2 > 1} ∧
    C = {z : ℝ × ℝ | ¬ NegIntegerSet z.1 ∧ 0 < z.2 ∧ z.2 ≤ 1} →
    A = {z : ℝ × ℝ | ¬ NegIntegerSet z.1 ∧ AbsoluteConvergentSeries (u z.1 z.2)} ∧
    C = {z : ℝ × ℝ | ¬ NegIntegerSet z.1 ∧ ConditionalConvergentSeries (u z.1 z.2)} := by
  sorry

end Exercise2722
