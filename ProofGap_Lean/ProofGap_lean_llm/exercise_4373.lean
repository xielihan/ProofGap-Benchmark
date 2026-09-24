import Mathlib

set_option linter.style.longLine false

abbrev Point3 := ℝ × ℝ × ℝ
abbrev Point2 := ℝ × ℝ
noncomputable def VectorCurveInt (C : Set Point3) (ω : ℝ) : ℝ := 0
noncomputable def ScalarSurfaceInt {α : Type*} (S : Set α) (ω : ℝ) : ℝ := 0
noncomputable def sqrtn (n : ℕ) (x : ℝ) : ℝ := x ^ (1 / (n : ℕ))
noncomputable def dX : ℝ := 1
noncomputable def dY : ℝ := 1
noncomputable def dZ : ℝ := 1
noncomputable def dS : ℝ := 1
local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

-- exercise: exercise_4373
-- Exercise 4373, gap 1
theorem proof_gap_exercise_4373_1
  (C S : Set Point3) (Sxy : Set Point2) (a x y z : ℝ) (ha : a > 0)
  (hS : S = {p : Point3 | p.1 + p.2.1 + p.2.2 = (3 /. 2) * a ∧ 0 ≤ p.1 ∧ p.1 ≤ a ∧ 0 ≤ p.2.1 ∧ p.2.1 ≤ a ∧ 0 ≤ p.2.2 ∧ p.2.2 ≤ a})
  (hC : C = {p : Point3 | p ∈ S})
  (hSxy : Sxy = {q : Point2 | ∃ z : ℝ, (q.1, q.2, z) ∈ S}) :
  ScalarSurfaceInt Sxy (1 * dX * dY) = (3 /. 4) * a ^ 2 := by
  sorry

-- Exercise 4373, gap 2
theorem proof_gap_exercise_4373_2
  (C S : Set Point3) (Sxy : Set Point2) (a x y z : ℝ) (ha : a > 0)
  (h12 : ScalarSurfaceInt Sxy (1 * dX * dY) = (3 /. 4) * a ^ 2) :
  ∃ n : Point3, n = (1 /. sqrtn 2 3, 1 /. sqrtn 2 3, 1 /. sqrtn 2 3) := by
  sorry

-- Exercise 4373, gap 3
theorem proof_gap_exercise_4373_3
  (C S : Set Point3) (Sxy : Set Point2) (a x y z : ℝ) (ha : a > 0)
  (h13 : ∃ n : Point3, n = (1 /. sqrtn 2 3, 1 /. sqrtn 2 3, 1 /. sqrtn 2 3)) :
  VectorCurveInt C (((y ^ 2 - z ^ 2) * dX) + ((z ^ 2 - x ^ 2) * dY) + ((x ^ 2 - y ^ 2) * dZ)) =
    ScalarSurfaceInt S (((-2 * y - 2 * z) * (1 /. sqrtn 2 3) + (-2 * z - 2 * x) * (1 /. sqrtn 2 3) + (-2 * x - 2 * y) * (1 /. sqrtn 2 3)) * dS) := by
  sorry

-- Exercise 4373, gap 4
theorem proof_gap_exercise_4373_4
  (C S : Set Point3) (Sxy : Set Point2) (a x y z : ℝ) (ha : a > 0)
  (h14 : VectorCurveInt C (((y ^ 2 - z ^ 2) * dX) + ((z ^ 2 - x ^ 2) * dY) + ((x ^ 2 - y ^ 2) * dZ)) = ScalarSurfaceInt S (((-2 * y - 2 * z) * (1 /. sqrtn 2 3) + (-2 * z - 2 * x) * (1 /. sqrtn 2 3) + (-2 * x - 2 * y) * (1 /. sqrtn 2 3)) * dS)) :
  ScalarSurfaceInt S (((-2 * y - 2 * z) * (1 /. sqrtn 2 3) + (-2 * z - 2 * x) * (1 /. sqrtn 2 3) + (-2 * x - 2 * y) * (1 /. sqrtn 2 3)) * dS) =
    -4 * ScalarSurfaceInt S ((x + y + z) * (1 /. sqrtn 2 3) * dS) := by
  sorry

-- Exercise 4373, gap 5
theorem proof_gap_exercise_4373_5
  (C S : Set Point3) (Sxy : Set Point2) (a x y z : ℝ) (ha : a > 0)
  (h15 : ScalarSurfaceInt S (((-2 * y - 2 * z) * (1 /. sqrtn 2 3) + (-2 * z - 2 * x) * (1 /. sqrtn 2 3) + (-2 * x - 2 * y) * (1 /. sqrtn 2 3)) * dS) = -4 * ScalarSurfaceInt S ((x + y + z) * (1 /. sqrtn 2 3) * dS)) :
  -4 * ScalarSurfaceInt S ((x + y + z) * (1 /. sqrtn 2 3) * dS) =
    -6 * a * ScalarSurfaceInt S ((1 /. sqrtn 2 3) * dS) := by
  sorry

-- Exercise 4373, gap 6
theorem proof_gap_exercise_4373_6
  (C S : Set Point3) (Sxy : Set Point2) (a x y z : ℝ) (ha : a > 0) :
  ScalarSurfaceInt S ((1 /. sqrtn 2 3) * dS) = ScalarSurfaceInt Sxy (1 * dX * dY) := by
  sorry

-- Exercise 4373, gap 7
theorem proof_gap_exercise_4373_7
  (C S : Set Point3) (Sxy : Set Point2) (a x y z : ℝ) (ha : a > 0)
  (h12 : ScalarSurfaceInt Sxy (1 * dX * dY) = (3 /. 4) * a ^ 2)
  (h17 : ScalarSurfaceInt S ((1 /. sqrtn 2 3) * dS) = ScalarSurfaceInt Sxy (1 * dX * dY)) :
  -6 * a * ScalarSurfaceInt Sxy (1 * dX * dY) = -6 * a * (3 /. 4) * a ^ 2 := by
  sorry

-- Exercise 4373, gap 8
theorem proof_gap_exercise_4373_8
  (C S : Set Point3) (Sxy : Set Point2) (a x y z : ℝ) (ha : a > 0) :
  -6 * a * (3 /. 4) * a ^ 2 = -(9 /. 2) * a ^ 3 := by
  sorry

-- Exercise 4373, gap 9
theorem proof_gap_exercise_4373_9
  (C S : Set Point3) (Sxy : Set Point2) (a x y z : ℝ) (ha : a > 0)
  (h18 : -6 * a * ScalarSurfaceInt Sxy (1 * dX * dY) = -6 * a * (3 /. 4) * a ^ 2)
  (h19 : -6 * a * (3 /. 4) * a ^ 2 = -(9 /. 2) * a ^ 3) :
  -6 * a * ScalarSurfaceInt Sxy (1 * dX * dY) = -(9 /. 2) * a ^ 3 := by
  sorry

-- Exercise 4373, gap 10
theorem proof_gap_exercise_4373_10
  (C S : Set Point3) (Sxy : Set Point2) (a x y z : ℝ) (ha : a > 0)
  (h14 : VectorCurveInt C (((y ^ 2 - z ^ 2) * dX) + ((z ^ 2 - x ^ 2) * dY) + ((x ^ 2 - y ^ 2) * dZ)) = ScalarSurfaceInt S (((-2 * y - 2 * z) * (1 /. sqrtn 2 3) + (-2 * z - 2 * x) * (1 /. sqrtn 2 3) + (-2 * x - 2 * y) * (1 /. sqrtn 2 3)) * dS))
  (h15 : ScalarSurfaceInt S (((-2 * y - 2 * z) * (1 /. sqrtn 2 3) + (-2 * z - 2 * x) * (1 /. sqrtn 2 3) + (-2 * x - 2 * y) * (1 /. sqrtn 2 3)) * dS) = -4 * ScalarSurfaceInt S ((x + y + z) * (1 /. sqrtn 2 3) * dS))
  (h16 : -4 * ScalarSurfaceInt S ((x + y + z) * (1 /. sqrtn 2 3) * dS) = -6 * a * ScalarSurfaceInt S ((1 /. sqrtn 2 3) * dS))
  (h17 : ScalarSurfaceInt S ((1 /. sqrtn 2 3) * dS) = ScalarSurfaceInt Sxy (1 * dX * dY))
  (h20 : -6 * a * ScalarSurfaceInt Sxy (1 * dX * dY) = -(9 /. 2) * a ^ 3) :
  VectorCurveInt C (((y ^ 2 - z ^ 2) * dX) + ((z ^ 2 - x ^ 2) * dY) + ((x ^ 2 - y ^ 2) * dZ)) = -(9 /. 2) * a ^ 3 := by
  sorry
