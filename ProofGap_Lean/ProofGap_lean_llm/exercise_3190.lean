import Mathlib

/-!
Exercise 3190
The punctured two-variable limit at `(0, 0)` is expressed using `𝓝[≠] (0, 0)`.
-/

noncomputable section

open Filter Real
open scoped Topology

/-- GAP 1: The AM-GM bound used in the squeeze argument. -/
theorem proof_gap_exercise_3190_1 :
    ∀ x : ℝ, ∀ y : ℝ, x ^ 2 + y ^ 2 > 0 →
      |x ^ 2 * y ^ 2 * log (x ^ 2 + y ^ 2)| ≤
        ((x ^ 2 + y ^ 2) ^ 2 / 4) * |log (x ^ 2 + y ^ 2)| := by
  sorry

/-- GAP 2: One-sided auxiliary limit after setting `t = x^2 + y^2`. -/
theorem proof_gap_exercise_3190_2
    (hineq : ∀ x : ℝ, ∀ y : ℝ, x ^ 2 + y ^ 2 > 0 →
      |x ^ 2 * y ^ 2 * log (x ^ 2 + y ^ 2)| ≤
        ((x ^ 2 + y ^ 2) ^ 2 / 4) * |log (x ^ 2 + y ^ 2)|)
    (x y t : ℝ) (ht : t = x ^ 2 + y ^ 2) :
    Tendsto (fun t : ℝ => (1 / 4 : ℝ) * t ^ 2 * log t) (𝓝[>] 0) (𝓝 0) := by
  sorry

/-- GAP 3: Squeezed two-variable limit of the logarithmic exponent. -/
theorem proof_gap_exercise_3190_3
    (hineq : ∀ x : ℝ, ∀ y : ℝ, x ^ 2 + y ^ 2 > 0 →
      |x ^ 2 * y ^ 2 * log (x ^ 2 + y ^ 2)| ≤
        ((x ^ 2 + y ^ 2) ^ 2 / 4) * |log (x ^ 2 + y ^ 2)|)
    (x y t : ℝ) (ht : t = x ^ 2 + y ^ 2)
    (htlim : Tendsto (fun t : ℝ => (1 / 4 : ℝ) * t ^ 2 * log t) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun p : ℝ × ℝ => p.1 ^ 2 * p.2 ^ 2 * log (p.1 ^ 2 + p.2 ^ 2))
      (𝓝[≠] (0, 0)) (𝓝 0) := by
  sorry

/-- GAP 4: Rewrite the power as an exponential of the logarithmic exponent on
the punctured domain. -/
theorem proof_gap_exercise_3190_4
    (hineq : ∀ x : ℝ, ∀ y : ℝ, x ^ 2 + y ^ 2 > 0 →
      |x ^ 2 * y ^ 2 * log (x ^ 2 + y ^ 2)| ≤
        ((x ^ 2 + y ^ 2) ^ 2 / 4) * |log (x ^ 2 + y ^ 2)|)
    (x y t : ℝ) (ht : t = x ^ 2 + y ^ 2)
    (htlim : Tendsto (fun t : ℝ => (1 / 4 : ℝ) * t ^ 2 * log t) (𝓝[>] 0) (𝓝 0))
    (hexp0 : Tendsto (fun p : ℝ × ℝ =>
      p.1 ^ 2 * p.2 ^ 2 * log (p.1 ^ 2 + p.2 ^ 2)) (𝓝[≠] (0, 0)) (𝓝 0)) :
    (Tendsto (fun p : ℝ × ℝ => (p.1 ^ 2 + p.2 ^ 2) ^ (p.1 ^ 2 * p.2 ^ 2))
        (𝓝[≠] (0, 0)) (𝓝 (Real.exp 0)) ↔
      Tendsto (fun p : ℝ × ℝ =>
        Real.exp (p.1 ^ 2 * p.2 ^ 2 * log (p.1 ^ 2 + p.2 ^ 2)))
        (𝓝[≠] (0, 0)) (𝓝 (Real.exp 0))) := by
  sorry

/-- GAP 5: Continuity of the exponential transfers the exponent limit. -/
theorem proof_gap_exercise_3190_5
    (hineq : ∀ x : ℝ, ∀ y : ℝ, x ^ 2 + y ^ 2 > 0 →
      |x ^ 2 * y ^ 2 * log (x ^ 2 + y ^ 2)| ≤
        ((x ^ 2 + y ^ 2) ^ 2 / 4) * |log (x ^ 2 + y ^ 2)|)
    (x y t : ℝ) (ht : t = x ^ 2 + y ^ 2)
    (htlim : Tendsto (fun t : ℝ => (1 / 4 : ℝ) * t ^ 2 * log t) (𝓝[>] 0) (𝓝 0))
    (hexp0 : Tendsto (fun p : ℝ × ℝ =>
      p.1 ^ 2 * p.2 ^ 2 * log (p.1 ^ 2 + p.2 ^ 2)) (𝓝[≠] (0, 0)) (𝓝 0))
    (hpow_exp : (Tendsto (fun p : ℝ × ℝ =>
        (p.1 ^ 2 + p.2 ^ 2) ^ (p.1 ^ 2 * p.2 ^ 2)) (𝓝[≠] (0, 0)) (𝓝 (Real.exp 0)) ↔
      Tendsto (fun p : ℝ × ℝ =>
        Real.exp (p.1 ^ 2 * p.2 ^ 2 * log (p.1 ^ 2 + p.2 ^ 2))) (𝓝[≠] (0, 0)) (𝓝 (Real.exp 0)))) :
    Tendsto (fun p : ℝ × ℝ =>
      Real.exp (p.1 ^ 2 * p.2 ^ 2 * log (p.1 ^ 2 + p.2 ^ 2)))
      (𝓝[≠] (0, 0)) (𝓝 (Real.exp 0)) := by
  sorry

/-- GAP 6: `e^0 = 1`. -/
theorem proof_gap_exercise_3190_6
    (hineq : ∀ x : ℝ, ∀ y : ℝ, x ^ 2 + y ^ 2 > 0 →
      |x ^ 2 * y ^ 2 * log (x ^ 2 + y ^ 2)| ≤
        ((x ^ 2 + y ^ 2) ^ 2 / 4) * |log (x ^ 2 + y ^ 2)|) :
    Real.exp 0 = 1 := by
  sorry

/-- GAP 7: Final value of the requested two-variable limit. -/
theorem proof_gap_exercise_3190_7
    (hineq : ∀ x : ℝ, ∀ y : ℝ, x ^ 2 + y ^ 2 > 0 →
      |x ^ 2 * y ^ 2 * log (x ^ 2 + y ^ 2)| ≤
        ((x ^ 2 + y ^ 2) ^ 2 / 4) * |log (x ^ 2 + y ^ 2)|)
    (x y t : ℝ) (ht : t = x ^ 2 + y ^ 2)
    (htlim : Tendsto (fun t : ℝ => (1 / 4 : ℝ) * t ^ 2 * log t) (𝓝[>] 0) (𝓝 0))
    (hexp0 : Tendsto (fun p : ℝ × ℝ =>
      p.1 ^ 2 * p.2 ^ 2 * log (p.1 ^ 2 + p.2 ^ 2)) (𝓝[≠] (0, 0)) (𝓝 0))
    (hpow_exp : (Tendsto (fun p : ℝ × ℝ =>
        (p.1 ^ 2 + p.2 ^ 2) ^ (p.1 ^ 2 * p.2 ^ 2)) (𝓝[≠] (0, 0)) (𝓝 (Real.exp 0)) ↔
      Tendsto (fun p : ℝ × ℝ =>
        Real.exp (p.1 ^ 2 * p.2 ^ 2 * log (p.1 ^ 2 + p.2 ^ 2))) (𝓝[≠] (0, 0)) (𝓝 (Real.exp 0))))
    (hexp_lim : Tendsto (fun p : ℝ × ℝ =>
      Real.exp (p.1 ^ 2 * p.2 ^ 2 * log (p.1 ^ 2 + p.2 ^ 2)))
      (𝓝[≠] (0, 0)) (𝓝 (Real.exp 0)))
    (hexp_one : Real.exp 0 = 1) :
    Tendsto (fun p : ℝ × ℝ => (p.1 ^ 2 + p.2 ^ 2) ^ (p.1 ^ 2 * p.2 ^ 2))
      (𝓝[≠] (0, 0)) (𝓝 1) := by
  sorry

