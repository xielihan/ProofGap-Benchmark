import Mathlib

/-!
Exercise 3204
The discontinuity set is represented as a subset of `ℝ × ℝ`; closure is
Mathlib's topological closure.
-/

noncomputable section

open Filter Set Real
open scoped Topology

def exercise_3204_fun (p : ℝ × ℝ) : ℝ :=
  if p.2 = 0 then 0 else p.1 * sin (1 / p.2)

/-- GAP 1: Continuity away from the `x`-axis. -/
theorem proof_gap_exercise_3204_1
    (f : ℝ × ℝ → ℝ) (D : Set (ℝ × ℝ))
    (hf : ∀ x y : ℝ, f (x, y) = if y = 0 then 0 else x * sin (1 / y))
    (hD : D = {p : ℝ × ℝ | ¬ ContinuousAt f p}) :
    ∀ x0 : ℝ, ∀ y0 : ℝ, y0 ≠ 0 → ContinuousAt f (x0, y0) := by
  sorry

/-- GAP 2: Since `f (0, 0) = 0`, subtracting it does not change absolute value. -/
theorem proof_gap_exercise_3204_2
    (f : ℝ × ℝ → ℝ) (D : Set (ℝ × ℝ))
    (hf : ∀ x y : ℝ, f (x, y) = if y = 0 then 0 else x * sin (1 / y))
    (hD : D = {p : ℝ × ℝ | ¬ ContinuousAt f p})
    (haway : ∀ x0 : ℝ, ∀ y0 : ℝ, y0 ≠ 0 → ContinuousAt f (x0, y0)) :
    ∀ x y : ℝ, |f (x, y) - f (0, 0)| = |f (x, y)| := by
  sorry

/-- GAP 3: Bound `|f x y| ≤ |x|`. -/
theorem proof_gap_exercise_3204_3
    (f : ℝ × ℝ → ℝ) (D : Set (ℝ × ℝ))
    (hf : ∀ x y : ℝ, f (x, y) = if y = 0 then 0 else x * sin (1 / y))
    (hD : D = {p : ℝ × ℝ | ¬ ContinuousAt f p})
    (haway : ∀ x0 : ℝ, ∀ y0 : ℝ, y0 ≠ 0 → ContinuousAt f (x0, y0))
    (habs0 : ∀ x y : ℝ, |f (x, y) - f (0, 0)| = |f (x, y)|) :
    ∀ x y : ℝ, |f (x, y)| ≤ |x| := by
  sorry

/-- GAP 4: Combine the two absolute-value facts. -/
theorem proof_gap_exercise_3204_4
    (f : ℝ × ℝ → ℝ) (D : Set (ℝ × ℝ))
    (hf : ∀ x y : ℝ, f (x, y) = if y = 0 then 0 else x * sin (1 / y))
    (hD : D = {p : ℝ × ℝ | ¬ ContinuousAt f p})
    (haway : ∀ x0 : ℝ, ∀ y0 : ℝ, y0 ≠ 0 → ContinuousAt f (x0, y0))
    (habs0 : ∀ x y : ℝ, |f (x, y) - f (0, 0)| = |f (x, y)|)
    (hbound : ∀ x y : ℝ, |f (x, y)| ≤ |x|) :
    ∀ x y : ℝ, |f (x, y) - f (0, 0)| ≤ |x| := by
  sorry

/-- GAP 5: Squeeze bound implies continuity at the origin. -/
theorem proof_gap_exercise_3204_5
    (f : ℝ × ℝ → ℝ) (D : Set (ℝ × ℝ))
    (hf : ∀ x y : ℝ, f (x, y) = if y = 0 then 0 else x * sin (1 / y))
    (hD : D = {p : ℝ × ℝ | ¬ ContinuousAt f p})
    (haway : ∀ x0 : ℝ, ∀ y0 : ℝ, y0 ≠ 0 → ContinuousAt f (x0, y0))
    (habs0 : ∀ x y : ℝ, |f (x, y) - f (0, 0)| = |f (x, y)|)
    (hbound : ∀ x y : ℝ, |f (x, y)| ≤ |x|)
    (horigin_bound : ∀ x y : ℝ, |f (x, y) - f (0, 0)| ≤ |x|) :
    ContinuousAt f (0, 0) := by
  sorry

/-- GAP 6: On the line `x = x0`, the function equals `x0 * sin (1 / y)` for
punctured `y` near zero. -/
theorem proof_gap_exercise_3204_6
    (f : ℝ × ℝ → ℝ) (D : Set (ℝ × ℝ))
    (hf : ∀ x y : ℝ, f (x, y) = if y = 0 then 0 else x * sin (1 / y))
    (hD : D = {p : ℝ × ℝ | ¬ ContinuousAt f p})
    (horigin : ContinuousAt f (0, 0)) :
    ∀ x0 : ℝ, x0 ≠ 0 →
      (Tendsto (fun y : ℝ => f (x0, y)) (𝓝[≠] 0) (𝓝 0) ↔
        Tendsto (fun y : ℝ => x0 * sin (1 / y)) (𝓝[≠] 0) (𝓝 0)) := by
  sorry

/-- GAP 7: `x0 * sin (1 / y)` has no finite limit as `y → 0` when `x0 ≠ 0`. -/
theorem proof_gap_exercise_3204_7
    (f : ℝ × ℝ → ℝ) (D : Set (ℝ × ℝ))
    (hf : ∀ x y : ℝ, f (x, y) = if y = 0 then 0 else x * sin (1 / y))
    (hD : D = {p : ℝ × ℝ | ¬ ContinuousAt f p})
    (hline : ∀ x0 : ℝ, x0 ≠ 0 →
      (Tendsto (fun y : ℝ => f (x0, y)) (𝓝[≠] 0) (𝓝 0) ↔
        Tendsto (fun y : ℝ => x0 * sin (1 / y)) (𝓝[≠] 0) (𝓝 0))) :
    ∀ x0 : ℝ, x0 ≠ 0 →
      ¬ ∃ L : ℝ, Tendsto (fun y : ℝ => x0 * sin (1 / y)) (𝓝[≠] 0) (𝓝 L) := by
  sorry

/-- GAP 8: Nonexistence of the one-dimensional limit gives discontinuity at
`(x0, 0)`. -/
theorem proof_gap_exercise_3204_8
    (f : ℝ × ℝ → ℝ) (D : Set (ℝ × ℝ))
    (hf : ∀ x y : ℝ, f (x, y) = if y = 0 then 0 else x * sin (1 / y))
    (hD : D = {p : ℝ × ℝ | ¬ ContinuousAt f p})
    (hnolim : ∀ x0 : ℝ, x0 ≠ 0 →
      ¬ ∃ L : ℝ, Tendsto (fun y : ℝ => x0 * sin (1 / y)) (𝓝[≠] 0) (𝓝 L)) :
    ∀ x0 : ℝ, x0 ≠ 0 → ¬ ContinuousAt f (x0, 0) := by
  sorry

/-- GAP 9: Identify all discontinuities as the punctured `x`-axis. -/
theorem proof_gap_exercise_3204_9
    (f : ℝ × ℝ → ℝ) (D : Set (ℝ × ℝ))
    (hf : ∀ x y : ℝ, f (x, y) = if y = 0 then 0 else x * sin (1 / y))
    (hD : D = {p : ℝ × ℝ | ¬ ContinuousAt f p})
    (haway : ∀ x0 : ℝ, ∀ y0 : ℝ, y0 ≠ 0 → ContinuousAt f (x0, y0))
    (horigin : ContinuousAt f (0, 0))
    (haxis : ∀ x0 : ℝ, x0 ≠ 0 → ¬ ContinuousAt f (x0, 0)) :
    D = {p : ℝ × ℝ | p.2 = 0 ∧ p.1 ≠ 0} := by
  sorry

/-- GAP 10: The origin belongs to the closure of the punctured `x`-axis. -/
theorem proof_gap_exercise_3204_10
    (f : ℝ × ℝ → ℝ) (D : Set (ℝ × ℝ))
    (hf : ∀ x y : ℝ, f (x, y) = if y = 0 then 0 else x * sin (1 / y))
    (hD : D = {p : ℝ × ℝ | ¬ ContinuousAt f p})
    (hdisc : D = {p : ℝ × ℝ | p.2 = 0 ∧ p.1 ≠ 0}) :
    (0, 0) ∈ closure D := by
  sorry

/-- GAP 11: The origin is not itself a discontinuity point. -/
theorem proof_gap_exercise_3204_11
    (f : ℝ × ℝ → ℝ) (D : Set (ℝ × ℝ))
    (hf : ∀ x y : ℝ, f (x, y) = if y = 0 then 0 else x * sin (1 / y))
    (hD : D = {p : ℝ × ℝ | ¬ ContinuousAt f p})
    (horigin : ContinuousAt f (0, 0))
    (hclosure_origin : (0, 0) ∈ closure D) :
    (0, 0) ∉ D := by
  sorry

/-- GAP 12: Since the origin is in `closure D` but not in `D`, the set differs
from its closure. -/
theorem proof_gap_exercise_3204_12
    (f : ℝ × ℝ → ℝ) (D : Set (ℝ × ℝ))
    (hf : ∀ x y : ℝ, f (x, y) = if y = 0 then 0 else x * sin (1 / y))
    (hD : D = {p : ℝ × ℝ | ¬ ContinuousAt f p})
    (hclosure_origin : (0, 0) ∈ closure D)
    (hnot_origin : (0, 0) ∉ D) :
    D ≠ closure D := by
  sorry

/-- GAP 13: Restatement of the final non-closedness conclusion. -/
theorem proof_gap_exercise_3204_13
    (f : ℝ × ℝ → ℝ) (D : Set (ℝ × ℝ))
    (hf : ∀ x y : ℝ, f (x, y) = if y = 0 then 0 else x * sin (1 / y))
    (hD : D = {p : ℝ × ℝ | ¬ ContinuousAt f p})
    (hnot_closed_form : D ≠ closure D) :
    D ≠ closure D := by
  sorry

