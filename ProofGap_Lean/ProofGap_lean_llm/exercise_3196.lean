import Mathlib

/-!
Exercise 3196
Singularity classifications are encoded as local mathematical predicates about
continuity and limits, since Mathlib has no named predicate matching the text.
-/

noncomputable section

open Filter
open scoped Topology

def RemovableSingularPoint (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : Prop :=
  ¬ ContinuousAt u p ∧ ∃ L : ℝ, Tendsto u (𝓝[≠] p) (𝓝 L)

def InfiniteSingularPoint (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : Prop :=
  Tendsto (fun q : ℝ × ℝ => |u q|) (𝓝[≠] p) atTop

/-- GAP 1: Factor `x^3 + y^3` and cancel `x + y` near `(a, -a)`. -/
theorem proof_gap_exercise_3196_1
    (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ)
    (hu : ∀ x y : ℝ, x ^ 3 + y ^ 3 ≠ 0 → u (x, y) = (x + y) / (x ^ 3 + y ^ 3)) :
    ∀ a : ℝ, a ≠ 0 →
      (Tendsto (fun q : ℝ × ℝ => (q.1 + q.2) / (q.1 ^ 3 + q.2 ^ 3))
          (𝓝[≠] (a, -a)) (𝓝 (1 / (3 * a ^ 2))) ↔
        Tendsto (fun q : ℝ × ℝ => 1 / (q.1 ^ 2 - q.1 * q.2 + q.2 ^ 2))
          (𝓝[≠] (a, -a)) (𝓝 (1 / (3 * a ^ 2)))) := by
  sorry

/-- GAP 2: Evaluate the continuous quotient limit at `(a, -a)`. -/
theorem proof_gap_exercise_3196_2
    (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ)
    (hu : ∀ x y : ℝ, x ^ 3 + y ^ 3 ≠ 0 → u (x, y) = (x + y) / (x ^ 3 + y ^ 3))
    (hcancel : ∀ a : ℝ, a ≠ 0 →
      (Tendsto (fun q : ℝ × ℝ => (q.1 + q.2) / (q.1 ^ 3 + q.2 ^ 3))
          (𝓝[≠] (a, -a)) (𝓝 (1 / (3 * a ^ 2))) ↔
        Tendsto (fun q : ℝ × ℝ => 1 / (q.1 ^ 2 - q.1 * q.2 + q.2 ^ 2))
          (𝓝[≠] (a, -a)) (𝓝 (1 / (3 * a ^ 2))))) :
    ∀ a : ℝ, a ≠ 0 →
      Tendsto (fun q : ℝ × ℝ => 1 / (q.1 ^ 2 - q.1 * q.2 + q.2 ^ 2))
        (𝓝[≠] (a, -a)) (𝓝 (1 / (3 * a ^ 2))) := by
  sorry

/-- GAP 3: Combine cancellation and the evaluated quotient limit. -/
theorem proof_gap_exercise_3196_3
    (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ)
    (hu : ∀ x y : ℝ, x ^ 3 + y ^ 3 ≠ 0 → u (x, y) = (x + y) / (x ^ 3 + y ^ 3))
    (hcancel : ∀ a : ℝ, a ≠ 0 →
      (Tendsto (fun q : ℝ × ℝ => (q.1 + q.2) / (q.1 ^ 3 + q.2 ^ 3))
          (𝓝[≠] (a, -a)) (𝓝 (1 / (3 * a ^ 2))) ↔
        Tendsto (fun q : ℝ × ℝ => 1 / (q.1 ^ 2 - q.1 * q.2 + q.2 ^ 2))
          (𝓝[≠] (a, -a)) (𝓝 (1 / (3 * a ^ 2)))))
    (hlim_factor : ∀ a : ℝ, a ≠ 0 →
      Tendsto (fun q : ℝ × ℝ => 1 / (q.1 ^ 2 - q.1 * q.2 + q.2 ^ 2))
        (𝓝[≠] (a, -a)) (𝓝 (1 / (3 * a ^ 2)))) :
    ∀ a : ℝ, a ≠ 0 →
      Tendsto (fun q : ℝ × ℝ => (q.1 + q.2) / (q.1 ^ 3 + q.2 ^ 3))
        (𝓝[≠] (a, -a)) (𝓝 (1 / (3 * a ^ 2))) := by
  sorry

/-- GAP 4: Points `(a, -a)`, `a ≠ 0`, are removable singularities. -/
theorem proof_gap_exercise_3196_4
    (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ)
    (hu : ∀ x y : ℝ, x ^ 3 + y ^ 3 ≠ 0 → u (x, y) = (x + y) / (x ^ 3 + y ^ 3))
    (hlim : ∀ a : ℝ, a ≠ 0 →
      Tendsto (fun q : ℝ × ℝ => (q.1 + q.2) / (q.1 ^ 3 + q.2 ^ 3))
        (𝓝[≠] (a, -a)) (𝓝 (1 / (3 * a ^ 2)))) :
    ∀ a : ℝ, a ≠ 0 → RemovableSingularPoint u (a, -a) := by
  sorry

/-- GAP 5: The origin is an infinite singularity. -/
theorem proof_gap_exercise_3196_5
    (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ)
    (hu : ∀ x y : ℝ, x ^ 3 + y ^ 3 ≠ 0 → u (x, y) = (x + y) / (x ^ 3 + y ^ 3))
    (hrem : ∀ a : ℝ, a ≠ 0 → RemovableSingularPoint u (a, -a)) :
    InfiniteSingularPoint u (0, 0) := by
  sorry

/-- GAP 6: The discontinuity set is exactly the line `x + y = 0`. -/
theorem proof_gap_exercise_3196_6
    (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ)
    (hu : ∀ x y : ℝ, x ^ 3 + y ^ 3 ≠ 0 → u (x, y) = (x + y) / (x ^ 3 + y ^ 3))
    (hrem : ∀ a : ℝ, a ≠ 0 → RemovableSingularPoint u (a, -a))
    (hinf : InfiniteSingularPoint u (0, 0)) :
    p ∈ {q : ℝ × ℝ | q.1 + q.2 = 0} ↔ ¬ ContinuousAt u p := by
  sorry

