import ProofGapLean.Prelude.Core
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise221_2

noncomputable section

def f (a b c x : ℝ) : ℝ := a * x ^ 2 + b * x + c

/-- Exercise 221_2, gap 1; completing the square requires a≠0. -/
private theorem quadratic_sub_factor (a b c x y : ℝ) :
    f a b c y - f a b c x =
      (y - x) * (a * (x + y) + b) := by
  unfold f
  ring

private theorem quadratic_vertex_balance (a b : ℝ) (ha : a ≠ 0) :
    a * (2 * (-b / (2 * a))) + b = 0 := by
  field_simp [ha] <;> ring

theorem gap1 (a b c : ℝ) (ha : a ≠ 0) : ∀ x,
    f a b c x =
      a * (x + b / (2 * a)) ^ 2 + (4 * a * c - b ^ 2) / (4 * a) := by
  intro x
  unfold f
  field_simp [ha] <;> ring

/-- Exercise 221_2, gap 2. -/
theorem gap2 (a b c : ℝ) (ha : 0 < a) :
    StrictAntiOn (f a b c) (Set.Iic (-b / (2 * a))) := by
  intro x hx y hy hxy
  change x ≤ -b / (2 * a) at hx
  change y ≤ -b / (2 * a) at hy
  have hsum : x + y < 2 * (-b / (2 * a)) := by
    linarith
  have hscaled :
      a * (x + y) < a * (2 * (-b / (2 * a))) :=
    mul_lt_mul_of_pos_left hsum ha
  have hlinear : a * (x + y) + b < 0 := by
    linarith [quadratic_vertex_balance a b (ne_of_gt ha)]
  have hprod : (y - x) * (a * (x + y) + b) < 0 :=
    mul_neg_of_pos_of_neg (sub_pos.mpr hxy) hlinear
  have hdiff : f a b c y - f a b c x < 0 := by
    rw [quadratic_sub_factor]
    exact hprod
  linarith

/-- Exercise 221_2, gap 3. -/
theorem gap3 (a b c : ℝ) (ha : 0 < a) :
    StrictMonoOn (f a b c) (Set.Ici (-b / (2 * a))) := by
  intro x hx y hy hxy
  change -b / (2 * a) ≤ x at hx
  change -b / (2 * a) ≤ y at hy
  have hsum : 2 * (-b / (2 * a)) < x + y := by
    linarith
  have hscaled :
      a * (2 * (-b / (2 * a))) < a * (x + y) :=
    mul_lt_mul_of_pos_left hsum ha
  have hlinear : 0 < a * (x + y) + b := by
    linarith [quadratic_vertex_balance a b (ne_of_gt ha)]
  have hprod : 0 < (y - x) * (a * (x + y) + b) :=
    mul_pos (sub_pos.mpr hxy) hlinear
  have hdiff : 0 < f a b c y - f a b c x := by
    rw [quadratic_sub_factor]
    exact hprod
  linarith

/-- Exercise 221_2, gap 4. -/
theorem gap4 (a b c : ℝ) (ha : a < 0) :
    StrictMonoOn (f a b c) (Set.Iic (-b / (2 * a))) := by
  intro x hx y hy hxy
  change x ≤ -b / (2 * a) at hx
  change y ≤ -b / (2 * a) at hy
  have hsum : x + y < 2 * (-b / (2 * a)) := by
    linarith
  have hscaled :
      a * (2 * (-b / (2 * a))) < a * (x + y) :=
    mul_lt_mul_of_neg_left hsum ha
  have hlinear : 0 < a * (x + y) + b := by
    linarith [quadratic_vertex_balance a b (ne_of_lt ha)]
  have hprod : 0 < (y - x) * (a * (x + y) + b) :=
    mul_pos (sub_pos.mpr hxy) hlinear
  have hdiff : 0 < f a b c y - f a b c x := by
    rw [quadratic_sub_factor]
    exact hprod
  linarith

/-- Exercise 221_2, gap 5. -/
theorem gap5 (a b c : ℝ) (ha : a < 0) :
    StrictAntiOn (f a b c) (Set.Ici (-b / (2 * a))) := by
  intro x hx y hy hxy
  change -b / (2 * a) ≤ x at hx
  change -b / (2 * a) ≤ y at hy
  have hsum : 2 * (-b / (2 * a)) < x + y := by
    linarith
  have hscaled :
      a * (x + y) < a * (2 * (-b / (2 * a))) :=
    mul_lt_mul_of_neg_left hsum ha
  have hlinear : a * (x + y) + b < 0 := by
    linarith [quadratic_vertex_balance a b (ne_of_lt ha)]
  have hprod : (y - x) * (a * (x + y) + b) < 0 :=
    mul_neg_of_pos_of_neg (sub_pos.mpr hxy) hlinear
  have hdiff : f a b c y - f a b c x < 0 := by
    rw [quadratic_sub_factor]
    exact hprod
  linarith

end

end ProofGap.Exercise221_2
