import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat

open Filter

open scoped RealInnerProductSpace

-- exercise: exercise_3299
-- Exercise 3299

noncomputable abbrev f1_3299 (f : ℝ × ℝ × ℝ -> ℝ) (x y z : ℝ) : ℝ := iteratedDeriv 1 (fun s => f (s, y, z)) x
noncomputable abbrev f2_3299 (f : ℝ × ℝ × ℝ -> ℝ) (x y z : ℝ) : ℝ := iteratedDeriv 1 (fun s => f (x, s, z)) y
noncomputable abbrev f3_3299 (f : ℝ × ℝ × ℝ -> ℝ) (x y z : ℝ) : ℝ := iteratedDeriv 1 (fun s => f (x, y, s)) z
noncomputable abbrev f11_3299 (f : ℝ × ℝ × ℝ -> ℝ) (x y z : ℝ) : ℝ := iteratedDeriv 2 (fun s => f (s, y, z)) x
noncomputable abbrev f22_3299 (f : ℝ × ℝ × ℝ -> ℝ) (x y z : ℝ) : ℝ := iteratedDeriv 2 (fun s => f (x, s, z)) y
noncomputable abbrev f33_3299 (f : ℝ × ℝ × ℝ -> ℝ) (x y z : ℝ) : ℝ := iteratedDeriv 2 (fun s => f (x, y, s)) z
noncomputable abbrev f12_3299 (f : ℝ × ℝ × ℝ -> ℝ) (x y z : ℝ) : ℝ := iteratedDeriv 1 (fun s => f1_3299 f x s z) y
noncomputable abbrev f13_3299 (f : ℝ × ℝ × ℝ -> ℝ) (x y z : ℝ) : ℝ := iteratedDeriv 1 (fun s => f1_3299 f x y s) z
noncomputable abbrev f23_3299 (f : ℝ × ℝ × ℝ -> ℝ) (x y z : ℝ) : ℝ := iteratedDeriv 1 (fun s => f2_3299 f x y s) z

theorem proof_gap_exercise_3299_1
  (f : ℝ × ℝ × ℝ -> ℝ)
  (u : ℝ -> ℝ)
  (dt du : ℝ)
  (hf : ContDiff ℝ (2 : ℕ∞) f)
  (hu : ∀ t : ℝ, u t = f (t, t ^ 2, t ^ 3))
  : ∀ t : ℝ,
      du =
      (f1_3299 f t (t ^ 2) (t ^ 3)
        + 2 * t * f2_3299 f t (t ^ 2) (t ^ 3)
        + 3 * t ^ 2 * f3_3299 f t (t ^ 2) (t ^ 3)) * dt
      := by
  sorry

theorem proof_gap_exercise_3299_2
  (f : ℝ × ℝ × ℝ -> ℝ)
  (u : ℝ -> ℝ)
  (dt du ddu : ℝ)
  (hf : ContDiff ℝ (2 : ℕ∞) f)
  (hu : ∀ t : ℝ, u t = f (t, t ^ 2, t ^ 3))
  (h_du : ∀ t : ℝ,
      du =
      (f1_3299 f t (t ^ 2) (t ^ 3)
        + 2 * t * f2_3299 f t (t ^ 2) (t ^ 3)
        + 3 * t ^ 2 * f3_3299 f t (t ^ 2) (t ^ 3)) * dt
      )
  : ∀ t : ℝ,
      ddu =
      (f11_3299 f t (t ^ 2) (t ^ 3)
        + 4 * t ^ 2 * f22_3299 f t (t ^ 2) (t ^ 3)
        + 9 * t ^ 4 * f33_3299 f t (t ^ 2) (t ^ 3)
        + 4 * t * f12_3299 f t (t ^ 2) (t ^ 3)
        + 6 * t ^ 2 * f13_3299 f t (t ^ 2) (t ^ 3)
        + 12 * t ^ 3 * f23_3299 f t (t ^ 2) (t ^ 3)
        + 2 * f2_3299 f t (t ^ 2) (t ^ 3)
        + 6 * t * f3_3299 f t (t ^ 2) (t ^ 3)) * dt ^ 2
      := by
  sorry
