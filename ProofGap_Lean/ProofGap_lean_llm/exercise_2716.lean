import Mathlib

open Filter
open scoped Topology BigOperators

namespace Exercise2716

noncomputable def term (x : ℝ) (n : ℕ) : ℝ := (n : ℝ) / x ^ n
noncomputable def yterm (y : ℝ) (n : ℕ) : ℝ := (n : ℝ) * y ^ n
def ConvergentSeries (f : ℕ → ℝ) : Prop := Summable fun n => f (n + 1)
def DivergentSeries (f : ℕ → ℝ) : Prop := ¬ ConvergentSeries f
def AbsoluteConvergentSeries (f : ℕ → ℝ) : Prop := Summable fun n => |f (n + 1)|
def ConditionalConvergentSeries (f : ℕ → ℝ) : Prop :=
  ConvergentSeries f ∧ ¬ AbsoluteConvergentSeries f
noncomputable def RadiusOfConvergence (a : ℕ → ℝ) : ℝ :=
  sSup {r : ℝ | 0 ≤ r ∧ ∀ z : ℝ, |z| < r → Summable fun n => a n * z ^ n}

/-- GAP 1: substitute `y = 1 / x` in the function series. -/
theorem proof_gap_exercise_2716_1 (x y : ℝ) (hx : x ≠ 0) (hy : y = 1 / x) :
    (fun n : ℕ => term x n) = fun n : ℕ => yterm y n := by
  sorry

/-- GAP 2: the power series with coefficients `n` has radius of convergence `1`. -/
theorem proof_gap_exercise_2716_2 (x y : ℝ) (hx : x ≠ 0) (hy : y = 1 / x)
    (hsub : (fun n : ℕ => term x n) = fun n : ℕ => yterm y n) :
    RadiusOfConvergence (fun n : ℕ => (n : ℝ)) = 1 := by
  sorry

/-- GAP 3: absolute convergence of `sum n y^n` is equivalent to `|y| < 1`. -/
theorem proof_gap_exercise_2716_3 (x y : ℝ) (hx : x ≠ 0) (hy : y = 1 / x)
    (hsub : (fun n : ℕ => term x n) = fun n : ℕ => yterm y n)
    (hr : RadiusOfConvergence (fun n : ℕ => (n : ℝ)) = 1) :
    AbsoluteConvergentSeries (fun n : ℕ => yterm y n) ↔ |y| < 1 := by
  sorry

/-- GAP 4: translate `|y| < 1` through `y = 1 / x`. -/
theorem proof_gap_exercise_2716_4 (x y : ℝ) (hx : x ≠ 0) (hy : y = 1 / x)
    (hsub : (fun n : ℕ => term x n) = fun n : ℕ => yterm y n)
    (hr : RadiusOfConvergence (fun n : ℕ => (n : ℝ)) = 1)
    (habs : AbsoluteConvergentSeries (fun n : ℕ => yterm y n) ↔ |y| < 1) :
    (|y| < 1 ↔ |(1 / x : ℝ)| < 1) ∧ (|(1 / x : ℝ)| < 1 ↔ |x| > 1) := by
  sorry

/-- GAP 5: real numbers of absolute value `1` are `1` or `-1`. -/
theorem proof_gap_exercise_2716_5 (x y : ℝ) (hx : x ≠ 0) (hy : y = 1 / x)
    (hsub : (fun n : ℕ => term x n) = fun n : ℕ => yterm y n)
    (hr : RadiusOfConvergence (fun n : ℕ => (n : ℝ)) = 1)
    (habs : AbsoluteConvergentSeries (fun n : ℕ => yterm y n) ↔ |y| < 1)
    (hxy : (|y| < 1 ↔ |(1 / x : ℝ)| < 1) ∧ (|(1 / x : ℝ)| < 1 ↔ |x| > 1)) :
    |x| = 1 → x = 1 ∨ x = -1 := by
  sorry

/-- GAP 6: on `|x| = 1`, the absolute value of the term is `n`. -/
theorem proof_gap_exercise_2716_6 (x y : ℝ) (hx : x ≠ 0) (hy : y = 1 / x)
    (hsub : (fun n : ℕ => term x n) = fun n : ℕ => yterm y n)
    (hr : RadiusOfConvergence (fun n : ℕ => (n : ℝ)) = 1)
    (habs : AbsoluteConvergentSeries (fun n : ℕ => yterm y n) ↔ |y| < 1)
    (hxy : (|y| < 1 ↔ |(1 / x : ℝ)| < 1) ∧ (|(1 / x : ℝ)| < 1 ↔ |x| > 1))
    (hone : |x| = 1 → x = 1 ∨ x = -1) :
    ∀ n : ℕ, 1 ≤ n → |x| = 1 → |term x n| = (n : ℝ) := by
  sorry

/-- GAP 7: the terms do not tend to zero at `|x| = 1`. -/
theorem proof_gap_exercise_2716_7 (x y : ℝ) (hx : x ≠ 0) (hy : y = 1 / x)
    (hterm : ∀ n : ℕ, 1 ≤ n → |x| = 1 → |term x n| = (n : ℝ)) :
    |x| = 1 → ¬ Tendsto (fun n : ℕ => term x n) atTop (𝓝 0) := by
  sorry

/-- GAP 8: nonzero term limit implies divergence on the boundary. -/
theorem proof_gap_exercise_2716_8 (x y : ℝ) (hx : x ≠ 0) (hy : y = 1 / x)
    (hnlim : |x| = 1 → ¬ Tendsto (fun n : ℕ => term x n) atTop (𝓝 0)) :
    |x| = 1 → DivergentSeries (fun n : ℕ => term x n) := by
  sorry

/-- GAP 9: for nonzero `x` with `|x| ≤ 1`, the series diverges. -/
theorem proof_gap_exercise_2716_9 (x y : ℝ) (hx : x ≠ 0) (hy : y = 1 / x)
    (hbdry : |x| = 1 → DivergentSeries (fun n : ℕ => term x n)) :
    x ≠ 0 ∧ |x| ≤ 1 → DivergentSeries (fun n : ℕ => term x n) := by
  sorry

/-- GAP 10: there is no real conditional convergence domain. -/
theorem proof_gap_exercise_2716_10 (x y : ℝ) (hx : x ≠ 0) (hy : y = 1 / x)
    (hdiv : x ≠ 0 ∧ |x| ≤ 1 → DivergentSeries (fun n : ℕ => term x n)) :
    ¬ (∃ x : ℝ, ConditionalConvergentSeries (fun n : ℕ => term x n)) := by
  sorry

/-- GAP 11: the absolute convergence domain is exactly `{x : ℝ | |x| > 1}`. -/
theorem proof_gap_exercise_2716_11 (x y : ℝ) (hx : x ≠ 0) (hy : y = 1 / x)
    (hnone : ¬ (∃ x : ℝ, ConditionalConvergentSeries (fun n : ℕ => term x n))) :
    x ∈ {x : ℝ | |x| > 1} ↔ AbsoluteConvergentSeries (fun n : ℕ => term x n) := by
  sorry

end Exercise2716
