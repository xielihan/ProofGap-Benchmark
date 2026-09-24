import ProofGapLean.Prelude.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace ProofGap.Exercise2182_1
noncomputable section

open scoped BigOperators

def h (n : ℕ) : ℝ := 5 / (n : ℝ)
def cube (x : ℝ) : ℝ := x ^ 3
def cell (n i : ℕ) : Set ℝ :=
  Set.Icc (-2 + (i : ℝ) * h n) (-2 + ((i : ℝ) + 1) * h n)
def m (n i : ℕ) : ℝ := (-2 + (i : ℝ) * h n) ^ 3
def M (n i : ℕ) : ℝ := (-2 + ((i : ℝ) + 1) * h n) ^ 3
def lowerSum (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, m n i * h n
def upperSum (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, M n i * h n

private theorem sum_cast_range_formula (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ)) =
      (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [Nat.cast_succ]
      ring

private theorem sum_sq_cast_range_formula (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ) ^ 2) =
      (2 * (n : ℝ) ^ 3 - 3 * (n : ℝ) ^ 2 + (n : ℝ)) / 6 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [Nat.cast_succ]
      ring

private theorem sum_cube_cast_range_formula (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ) ^ 3) =
      ((n : ℝ) ^ 4 - 2 * (n : ℝ) ^ 3 + (n : ℝ) ^ 2) / 4 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [Nat.cast_succ]
      ring

private theorem sum_range_shift_real (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, f (i + 1)) =
      (∑ i ∈ Finset.range n, f i) + f n - f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [Finset.sum_range_succ, ih, Nat.succ_eq_add_one]
      ring

theorem gap1 (n i : ℕ) (hn : 0 < n) (hi : i < n) :
    cell n i =
      Set.Icc (-2 + (i : ℝ) * h n) (-2 + ((i : ℝ) + 1) * h n) := by
  rfl

theorem gap2 :
    MonotoneOn cube (Set.Icc (-2 : ℝ) 3) := by
  intro x hx y hy hxy
  dsimp [cube]
  have hq : 0 ≤ x ^ 2 + x * y + y ^ 2 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x + y)]
  have hm : 0 ≤ (y - x) * (x ^ 2 + x * y + y ^ 2) :=
    mul_nonneg (sub_nonneg.mpr hxy) hq
  nlinarith [hm]

theorem gap3 (n i : ℕ) (hn : 0 < n) (hi : i < n) :
    m n i = (-2 + (i : ℝ) * h n) ^ 3 ∧
      M n i = (-2 + ((i : ℝ) + 1) * h n) ^ 3 := by
  constructor <;> rfl

theorem gap4 (n : ℕ) (hn : 0 < n) :
    lowerSum n = ∑ i ∈ Finset.range n, m n i * h n := by
  rfl

theorem gap5 (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ Finset.range n, m n i * h n) =
      ∑ i ∈ Finset.range n, (-2 + (i : ℝ) * h n) ^ 3 * h n := by
  simp only [m]

theorem gap6 (n : ℕ) (hn : 0 < n) :
    lowerSum n =
      ∑ i ∈ Finset.range n, (-2 + (i : ℝ) * h n) ^ 3 * h n := by
  exact (gap4 n hn).trans (gap5 n hn)

theorem gap7 (n : ℕ) (hn : 0 < n) :
    lowerSum n =
      -8 * (n : ℝ) * h n
      + 12 * (h n) ^ 2 * (∑ i ∈ Finset.range n, (i : ℝ))
      - 6 * (h n) ^ 3 * (∑ i ∈ Finset.range n, (i : ℝ) ^ 2)
      + (h n) ^ 4 * (∑ i ∈ Finset.range n, (i : ℝ) ^ 3) := by
  rw [gap6 n hn]
  have h0 :
      (∑ i ∈ Finset.range n, -8 * h n) =
        (n : ℝ) * (-8 * h n) := by
    simp
  have h1 :
      (∑ i ∈ Finset.range n, (12 * (h n) ^ 2) * (i : ℝ)) =
        (12 * (h n) ^ 2) * (∑ i ∈ Finset.range n, (i : ℝ)) := by
    rw [Finset.mul_sum]
  have h2 :
      (∑ i ∈ Finset.range n, (6 * (h n) ^ 3) * (i : ℝ) ^ 2) =
        (6 * (h n) ^ 3) * (∑ i ∈ Finset.range n, (i : ℝ) ^ 2) := by
    rw [Finset.mul_sum]
  have h3 :
      (∑ i ∈ Finset.range n, (h n) ^ 4 * (i : ℝ) ^ 3) =
        (h n) ^ 4 * (∑ i ∈ Finset.range n, (i : ℝ) ^ 3) := by
    rw [Finset.mul_sum]
  calc
    (∑ i ∈ Finset.range n, (-2 + (i : ℝ) * h n) ^ 3 * h n) =
        ∑ i ∈ Finset.range n,
          (-8 * h n + (12 * (h n) ^ 2) * (i : ℝ) -
            (6 * (h n) ^ 3) * (i : ℝ) ^ 2 +
            (h n) ^ 4 * (i : ℝ) ^ 3) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i ∈ Finset.range n, -8 * h n) +
          (∑ i ∈ Finset.range n, (12 * (h n) ^ 2) * (i : ℝ)) -
          (∑ i ∈ Finset.range n, (6 * (h n) ^ 3) * (i : ℝ) ^ 2) +
          (∑ i ∈ Finset.range n, (h n) ^ 4 * (i : ℝ) ^ 3) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = -8 * (n : ℝ) * h n
        + 12 * (h n) ^ 2 * (∑ i ∈ Finset.range n, (i : ℝ))
        - 6 * (h n) ^ 3 * (∑ i ∈ Finset.range n, (i : ℝ) ^ 2)
        + (h n) ^ 4 * (∑ i ∈ Finset.range n, (i : ℝ) ^ 3) := by
      rw [h0, h1, h2, h3]
      ring

theorem gap8 (n : ℕ) (hn : 0 < n) :
    lowerSum n =
      -40
      + (12 * 25 * (n : ℝ) * ((n : ℝ) - 1)) / (2 * (n : ℝ) ^ 2)
      - 125 * (2 * (n : ℝ) ^ 3 - 3 * (n : ℝ) ^ 2 + n) / (n : ℝ) ^ 3
      + 625 * ((n : ℝ) ^ 4 - 2 * (n : ℝ) ^ 3 + (n : ℝ) ^ 2) /
          (4 * (n : ℝ) ^ 4) := by
  have hnR : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  rw [gap7 n hn, sum_cast_range_formula n, sum_sq_cast_range_formula n,
    sum_cube_cast_range_formula n]
  simp only [h]
  field_simp [hnR] <;> ring

theorem gap9 (n : ℕ) (hn : 0 < n) :
    -40
      + (12 * 25 * (n : ℝ) * ((n : ℝ) - 1)) / (2 * (n : ℝ) ^ 2)
      - 125 * (2 * (n : ℝ) ^ 3 - 3 * (n : ℝ) ^ 2 + n) / (n : ℝ) ^ 3
      + 625 * ((n : ℝ) ^ 4 - 2 * (n : ℝ) ^ 3 + (n : ℝ) ^ 2) /
          (4 * (n : ℝ) ^ 4) =
      65 / 4 - 175 / (2 * (n : ℝ)) + 125 / (4 * (n : ℝ) ^ 2) := by
  have hnR : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  field_simp [hnR] <;> ring

theorem gap10 (n : ℕ) (hn : 0 < n) :
    lowerSum n =
      65 / 4 - 175 / (2 * (n : ℝ)) + 125 / (4 * (n : ℝ) ^ 2) := by
  exact (gap8 n hn).trans (gap9 n hn)

theorem gap11 (n : ℕ) (hn : 0 < n) :
    upperSum n = ∑ i ∈ Finset.range n, M n i * h n := by
  rfl

theorem gap12 (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ Finset.range n, M n i * h n) =
      ∑ i ∈ Finset.range n, (-2 + ((i : ℝ) + 1) * h n) ^ 3 * h n := by
  simp only [M]

theorem gap13 (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ Finset.range n, (-2 + ((i : ℝ) + 1) * h n) ^ 3 * h n) =
      65 / 4 + 175 / (2 * (n : ℝ)) + 125 / (4 * (n : ℝ) ^ 2) := by
  have hnR : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  calc
    (∑ i ∈ Finset.range n,
        (-2 + ((i : ℝ) + 1) * h n) ^ 3 * h n) =
        (∑ i ∈ Finset.range n,
          (-2 + (i : ℝ) * h n) ^ 3 * h n) +
          (-2 + (n : ℝ) * h n) ^ 3 * h n -
          (-2 + (0 : ℝ) * h n) ^ 3 * h n := by
      simpa [Nat.cast_add, Nat.cast_one] using
        (sum_range_shift_real
          (fun j : ℕ => (-2 + (j : ℝ) * h n) ^ 3 * h n) n)
    _ = lowerSum n +
          (-2 + (n : ℝ) * h n) ^ 3 * h n -
          (-2 + (0 : ℝ) * h n) ^ 3 * h n := by
      rw [← gap6 n hn]
    _ = 65 / 4 + 175 / (2 * (n : ℝ)) +
          125 / (4 * (n : ℝ) ^ 2) := by
      rw [gap10 n hn]
      simp only [h]
      field_simp [hnR] <;> ring

theorem gap14 (n : ℕ) (hn : 0 < n) :
    upperSum n =
      65 / 4 + 175 / (2 * (n : ℝ)) + 125 / (4 * (n : ℝ) ^ 2) := by
  calc
    upperSum n = ∑ i ∈ Finset.range n, M n i * h n := gap11 n hn
    _ = ∑ i ∈ Finset.range n,
        (-2 + ((i : ℝ) + 1) * h n) ^ 3 * h n := gap12 n hn
    _ = 65 / 4 + 175 / (2 * (n : ℝ)) +
        125 / (4 * (n : ℝ) ^ 2) := gap13 n hn

end
end ProofGap.Exercise2182_1
