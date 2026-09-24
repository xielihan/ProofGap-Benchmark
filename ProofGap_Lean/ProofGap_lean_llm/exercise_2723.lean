import Mathlib

open Filter
open scoped Topology BigOperators

namespace Exercise2723

noncomputable def u (x p q : ℝ) (n : ℕ) : ℝ :=
  Real.rpow n p * Real.sin (n * x) / (1 + Real.rpow n q)
def ConvergentSeries (f : ℕ → ℝ) : Prop := Summable fun n => f (n + 1)
def DivergentSeries (f : ℕ → ℝ) : Prop := ¬ ConvergentSeries f
def AbsoluteConvergentSeries (f : ℕ → ℝ) : Prop := Summable fun n => |f (n + 1)|
def ConditionalConvergentSeries (f : ℕ → ℝ) : Prop :=
  ConvergentSeries f ∧ ¬ AbsoluteConvergentSeries f
def BoundedSeq (f : ℕ → ℝ) : Prop := ∃ M : ℝ, ∀ n, |f n| ≤ M
def AsymptoticAtTop (f g : ℕ → ℝ) : Prop := Tendsto (fun n => f n / g n) atTop (𝓝 1)

/-- GAP 1: lower comparison estimate from the source. -/
theorem proof_gap_exercise_2723_1 (A C : Set (ℝ × ℝ × ℝ)) :
    ∀ x q p n : ℝ, 0 < x ∧ x < Real.pi ∧ q > 0 ∧ n ≥ 1 →
      |Real.sin (n * x)| / (2 * Real.rpow n (q - p)) ≤
        |Real.rpow n p * Real.sin (n * x) / (1 + Real.rpow n q)| := by
  sorry

/-- GAP 2: upper comparison estimate from the source. -/
theorem proof_gap_exercise_2723_2 (A C : Set (ℝ × ℝ × ℝ)) :
    ∀ p x q n : ℝ, 0 < x ∧ x < Real.pi ∧ q > 0 ∧ n ≥ 1 →
      |Real.rpow n p * Real.sin (n * x) / (1 + Real.rpow n q)| ≤
        1 / Real.rpow n (q - p) := by
  sorry

/-- GAP 3: `p`-series convergence when exponent `q-p` is greater than `1`. -/
theorem proof_gap_exercise_2723_3 (A C : Set (ℝ × ℝ × ℝ)) :
    ∀ q p : ℝ, q - p > 1 →
      ConvergentSeries (fun n : ℕ => 1 / Real.rpow n (q - p)) := by
  sorry

/-- GAP 4: absolute convergence by comparison for `q-p > 1`. -/
theorem proof_gap_exercise_2723_4 (A C : Set (ℝ × ℝ × ℝ))
    (hpser : ∀ q p : ℝ, q - p > 1 →
      ConvergentSeries (fun n : ℕ => 1 / Real.rpow n (q - p))) :
    ∀ q p x : ℝ, 0 < x ∧ x < Real.pi ∧ q - p > 1 →
      AbsoluteConvergentSeries (u x p q) := by
  sorry

/-- GAP 5: divergence of the absolute-value series when `q ≤ p+1`. -/
theorem proof_gap_exercise_2723_5 (A C : Set (ℝ × ℝ × ℝ)) :
    ∀ q p x : ℝ, 0 < x ∧ x < Real.pi ∧ q ≤ p + 1 →
      DivergentSeries (fun n : ℕ => |u x p q n|) := by
  sorry

/-- GAP 6: failure of absolute convergence in the same range. -/
theorem proof_gap_exercise_2723_6 (A C : Set (ℝ × ℝ × ℝ))
    (hdivabs : ∀ q p x : ℝ, 0 < x ∧ x < Real.pi ∧ q ≤ p + 1 →
      DivergentSeries (fun n : ℕ => |u x p q n|)) :
    ∀ q p x : ℝ, 0 < x ∧ x < Real.pi ∧ q ≤ p + 1 →
      ¬ AbsoluteConvergentSeries (u x p q) := by
  sorry

/-- GAP 7: bounded partial sums of `sin(kx)` for `0 < x < π`. -/
theorem proof_gap_exercise_2723_7 (A C : Set (ℝ × ℝ × ℝ)) :
    ∀ p q x : ℝ, 0 < x ∧ x < Real.pi ∧ p < q ∧ q ≤ p + 1 →
      BoundedSeq (fun m : ℕ => Finset.sum (Finset.Icc 1 m) (fun k => Real.sin (k * x))) := by
  sorry

/-- GAP 8: asymptotic equivalence of the coefficient factor. -/
theorem proof_gap_exercise_2723_8 (A C : Set (ℝ × ℝ × ℝ)) :
    ∀ p q : ℝ, p < q ∧ q ≤ p + 1 →
      AsymptoticAtTop
        (fun n : ℕ => Real.rpow n p / (1 + Real.rpow n q))
        (fun n : ℕ => 1 / Real.rpow n (q - p)) := by
  sorry

/-- GAP 9: the coefficient factor tends to zero. -/
theorem proof_gap_exercise_2723_9 (A C : Set (ℝ × ℝ × ℝ))
    (hasymp : ∀ p q : ℝ, p < q ∧ q ≤ p + 1 →
      AsymptoticAtTop
        (fun n : ℕ => Real.rpow n p / (1 + Real.rpow n q))
        (fun n : ℕ => 1 / Real.rpow n (q - p))) :
    ∀ p q : ℝ, p < q ∧ q ≤ p + 1 →
      Tendsto (fun n : ℕ => Real.rpow n p / (1 + Real.rpow n q)) atTop (𝓝 0) := by
  sorry

/-- GAP 10: Dirichlet test gives convergence in the conditional range. -/
theorem proof_gap_exercise_2723_10 (A C : Set (ℝ × ℝ × ℝ))
    (hbounded : ∀ p q x : ℝ, 0 < x ∧ x < Real.pi ∧ p < q ∧ q ≤ p + 1 →
      BoundedSeq (fun m : ℕ => Finset.sum (Finset.Icc 1 m) (fun k => Real.sin (k * x))))
    (hzero : ∀ p q : ℝ, p < q ∧ q ≤ p + 1 →
      Tendsto (fun n : ℕ => Real.rpow n p / (1 + Real.rpow n q)) atTop (𝓝 0)) :
    ∀ p q x : ℝ, 0 < x ∧ x < Real.pi ∧ p < q ∧ q ≤ p + 1 →
      ConvergentSeries (u x p q) := by
  sorry

/-- GAP 11: convergence plus non-absolute convergence is conditional convergence. -/
theorem proof_gap_exercise_2723_11 (A C : Set (ℝ × ℝ × ℝ))
    (hnabs : ∀ q p x : ℝ, 0 < x ∧ x < Real.pi ∧ q ≤ p + 1 →
      ¬ AbsoluteConvergentSeries (u x p q))
    (hconv : ∀ p q x : ℝ, 0 < x ∧ x < Real.pi ∧ p < q ∧ q ≤ p + 1 →
      ConvergentSeries (u x p q)) :
    ∀ p q x : ℝ, 0 < x ∧ x < Real.pi ∧ p < q ∧ q ≤ p + 1 →
      ConditionalConvergentSeries (u x p q) := by
  sorry

/-- GAP 12: when `q ≤ p`, the term does not tend to zero. -/
theorem proof_gap_exercise_2723_12 (A C : Set (ℝ × ℝ × ℝ)) :
    ∀ q p x : ℝ, 0 < x ∧ x < Real.pi ∧ q ≤ p →
      ¬ Tendsto (u x p q) atTop (𝓝 0) := by
  sorry

/-- GAP 13: nonzero term limit gives divergence for `q ≤ p`. -/
theorem proof_gap_exercise_2723_13 (A C : Set (ℝ × ℝ × ℝ))
    (hnlim : ∀ q p x : ℝ, 0 < x ∧ x < Real.pi ∧ q ≤ p →
      ¬ Tendsto (u x p q) atTop (𝓝 0)) :
    ∀ q p x : ℝ, 0 < x ∧ x < Real.pi ∧ q ≤ p →
      DivergentSeries (u x p q) := by
  sorry

/-- GAP 14: identify the absolute and conditional convergence domains. -/
theorem proof_gap_exercise_2723_14 (A C : Set (ℝ × ℝ × ℝ))
    (habs : ∀ q p x : ℝ, 0 < x ∧ x < Real.pi ∧ q - p > 1 →
      AbsoluteConvergentSeries (u x p q))
    (hcond : ∀ p q x : ℝ, 0 < x ∧ x < Real.pi ∧ p < q ∧ q ≤ p + 1 →
      ConditionalConvergentSeries (u x p q)) :
    A = {z : ℝ × ℝ × ℝ | 0 < z.1 ∧ z.1 < Real.pi ∧ z.2.2 > z.2.1 + 1} ∧
    C = {z : ℝ × ℝ × ℝ | 0 < z.1 ∧ z.1 < Real.pi ∧ z.2.1 < z.2.2 ∧ z.2.2 ≤ z.2.1 + 1} →
    A = {z : ℝ × ℝ × ℝ | 0 < z.1 ∧ z.1 < Real.pi ∧ 0 < z.2.2 ∧
      AbsoluteConvergentSeries (u z.1 z.2.1 z.2.2)} ∧
    C = {z : ℝ × ℝ × ℝ | 0 < z.1 ∧ z.1 < Real.pi ∧ 0 < z.2.2 ∧
      ConditionalConvergentSeries (u z.1 z.2.1 z.2.2)} := by
  sorry

end Exercise2723
