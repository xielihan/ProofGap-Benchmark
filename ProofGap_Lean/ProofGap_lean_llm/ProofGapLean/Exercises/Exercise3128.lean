import ProofGapLean.Prelude.Analysis
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3128

noncomputable section

open scoped BigOperators

def affineMap (a b y : ℝ) : ℝ :=
  a + (b - a) * y

def generalizedBernstein (f : ℝ → ℝ) (a b : ℝ)
    (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    f (a + (b - a) * ((k : ℝ) / n)) *
      (Nat.choose n k : ℝ) *
      ((x - a) ^ k * (b - x) ^ (n - k) / (b - a) ^ n)

/--
Exercise 3128, gap 1; interval preservation needs
the endpoint order `a<b`.
-/
theorem gap1 (a b x y : ℝ) (hab : a < b)
    (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hx : x = affineMap a b y) :
    x ∈ Set.Icc a b := by
  rw [hx]
  change a ≤ a + (b - a) * y ∧ a + (b - a) * y ≤ b
  constructor
  · exact le_add_of_nonneg_right
      (mul_nonneg (sub_nonneg.mpr (le_of_lt hab)) hy.1)
  · have hmul :=
      mul_le_mul_of_nonneg_left hy.2 (sub_nonneg.mpr (le_of_lt hab))
    calc
      a + (b - a) * y ≤ a + (b - a) * 1 := by
        simpa [add_comm] using add_le_add_left hmul a
      _ = b := by ring

/-- Exercise 3128, gap 2; invert a nondegenerate affine map. -/
theorem gap2 (a b x y : ℝ) (hab : a < b)
    (hx : x = affineMap a b y) :
    y = (x - a) / (b - a) := by
  have hne : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  apply (eq_div_iff hne).2
  rw [hx]
  unfold affineMap
  ring

/-- Exercise 3128, gap 3; complementary normalized coordinate. -/
theorem gap3 (a b x y : ℝ) (hab : a < b)
    (hx : x = affineMap a b y) :
    1 - y = (b - x) / (b - a) := by
  have hne : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  apply (eq_div_iff hne).2
  rw [hx]
  unfold affineMap
  ring

/-- Exercise 3128, gap 4; substitute the affine coordinate. -/
theorem gap4 (f : ℝ → ℝ) (a b x y : ℝ)
    (hx : x = affineMap a b y) :
    f x = f (affineMap a b y) := by
  exact congrArg f hx

/--
Exercise 3128, gap 5; define the generalized
Bernstein polynomial on a nondegenerate interval and positive degree.
-/
theorem gap5 (f : ℝ → ℝ) (a b x : ℝ)
    (hab : a < b) (hx : x ∈ Set.Icc a b) :
    ∀ n : ℕ, 1 ≤ n →
      generalizedBernstein f a b n x =
        ∑ k ∈ Finset.range (n + 1),
          f (a + (b - a) * ((k : ℝ) / n)) *
            (Nat.choose n k : ℝ) *
            ((x - a) ^ k * (b - x) ^ (n - k) / (b - a) ^ n) := by
  intro n hn
  rfl

end

end ProofGap.Exercise3128
