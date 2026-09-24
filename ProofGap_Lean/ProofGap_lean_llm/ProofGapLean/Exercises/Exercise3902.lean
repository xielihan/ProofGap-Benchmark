import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise3902

noncomputable section

open Filter
open scoped BigOperators Topology

def lowerSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n,
    ∑ j ∈ Finset.range n,
      ((1 + (i : ℝ) / n) ^ 2 +
          (1 + 2 * (j : ℝ) / n) ^ 2) *
        (1 / (n : ℝ)) * (2 / (n : ℝ))

def expandedLower (n : ℕ) : ℝ :=
  2 * (n : ℝ) / (n : ℝ) ^ 2 *
    ((n : ℝ) +
      2 / (n : ℝ) * ∑ i ∈ Finset.range n, (i : ℝ) +
      1 / (n : ℝ) ^ 2 * ∑ i ∈ Finset.range n, (i : ℝ) ^ 2 +
      (n : ℝ) +
      4 / (n : ℝ) * ∑ j ∈ Finset.range n, (j : ℝ) +
      4 / (n : ℝ) ^ 2 * ∑ j ∈ Finset.range n, (j : ℝ) ^ 2)

def lowerClosed (n : ℕ) : ℝ :=
  40 / 3 - 11 / (n : ℝ) + 5 / (3 * (n : ℝ) ^ 2)

def upperSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n,
    ∑ j ∈ Finset.range n,
      ((1 + ((i + 1 : ℕ) : ℝ) / n) ^ 2 +
          (1 + 2 * ((j + 1 : ℕ) : ℝ) / n) ^ 2) *
        (1 / (n : ℝ)) * (2 / (n : ℝ))

def upperClosed (n : ℕ) : ℝ :=
  40 / 3 + 11 / (n : ℝ) + 5 / (3 * (n : ℝ) ^ 2)

private theorem sum_range_cast_real (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ)) = ((n : ℝ) - 1) * n / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      simp [Finset.sum_range_succ, ih, Nat.cast_succ] <;> ring

private theorem sum_range_sq_real (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ) ^ 2) =
      ((n : ℝ) - 1) * n * (2 * (n : ℝ) - 1) / 6 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      simp [Finset.sum_range_succ, ih, Nat.cast_succ] <;> ring

private theorem sum_range_affine_real
    (n : ℕ) (f : ℕ → ℝ) (p q : ℝ) :
    (∑ i ∈ Finset.range n, (p * f i + q)) =
      p * (∑ i ∈ Finset.range n, f i) + (n : ℝ) * q := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp [Finset.sum_range_succ, ih, Nat.cast_succ] <;> ring

private theorem sum_range_quadratic_real
    (n : ℕ) (p q r : ℝ) :
    (∑ i ∈ Finset.range n,
      (p * (i : ℝ) ^ 2 + q * (i : ℝ) + r)) =
      p * (∑ i ∈ Finset.range n, (i : ℝ) ^ 2) +
        q * (∑ i ∈ Finset.range n, (i : ℝ)) + (n : ℝ) * r := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp [Finset.sum_range_succ, ih, Nat.cast_succ] <;> ring

private theorem sum_range_affine_square_real
    (n : ℕ) (a b : ℝ) :
    (∑ i ∈ Finset.range n, (a + b * (i : ℝ)) ^ 2) =
      b ^ 2 * (∑ i ∈ Finset.range n, (i : ℝ) ^ 2) +
        (2 * a * b) * (∑ i ∈ Finset.range n, (i : ℝ)) +
        (n : ℝ) * a ^ 2 := by
  calc
    _ = ∑ i ∈ Finset.range n,
        (b ^ 2 * (i : ℝ) ^ 2 + (2 * a * b) * (i : ℝ) + a ^ 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = _ := sum_range_quadratic_real n (b ^ 2) (2 * a * b) (a ^ 2)

private theorem double_sum_separable_real
    (n : ℕ) (a b : ℕ → ℝ) (c : ℝ) :
    (∑ i ∈ Finset.range n,
      ∑ j ∈ Finset.range n, (a i + b j) * c) =
      c * (n : ℝ) *
        ((∑ i ∈ Finset.range n, a i) +
          (∑ j ∈ Finset.range n, b j)) := by
  calc
    _ = ∑ i ∈ Finset.range n,
        ∑ j ∈ Finset.range n, (c * b j + c * a i) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = ∑ i ∈ Finset.range n,
        (c * (∑ j ∈ Finset.range n, b j) +
          (n : ℝ) * (c * a i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact sum_range_affine_real n b c (c * a i)
    _ = ∑ i ∈ Finset.range n,
        (((n : ℝ) * c) * a i +
          c * (∑ j ∈ Finset.range n, b j)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = ((n : ℝ) * c) * (∑ i ∈ Finset.range n, a i) +
        (n : ℝ) * (c * (∑ j ∈ Finset.range n, b j)) :=
          sum_range_affine_real n a ((n : ℝ) * c)
            (c * (∑ j ∈ Finset.range n, b j))
    _ = _ := by ring

theorem gap1 (n : ℕ) (hn : 0 < n) :
    lowerSum n =
      ∑ i ∈ Finset.range n,
        ∑ j ∈ Finset.range n,
          ((1 + (i : ℝ) / n) ^ 2 +
              (1 + 2 * (j : ℝ) / n) ^ 2) *
            (1 / (n : ℝ)) * (2 / (n : ℝ)) := by
  rfl

theorem gap2 (n : ℕ) (hn : 0 < n) :
    lowerSum n = expandedLower n := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hx :
      (∑ i ∈ Finset.range n, (1 + (i : ℝ) / n) ^ 2) =
        (n : ℝ) +
          2 / (n : ℝ) * (∑ i ∈ Finset.range n, (i : ℝ)) +
          1 / (n : ℝ) ^ 2 * (∑ i ∈ Finset.range n, (i : ℝ) ^ 2) := by
    calc
      _ = ∑ k ∈ Finset.range n,
          (1 + (1 / (n : ℝ)) * (k : ℝ)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = _ := by
        rw [sum_range_affine_square_real]
        ring
  have hy :
      (∑ j ∈ Finset.range n, (1 + 2 * (j : ℝ) / n) ^ 2) =
        (n : ℝ) +
          4 / (n : ℝ) * (∑ j ∈ Finset.range n, (j : ℝ)) +
          4 / (n : ℝ) ^ 2 * (∑ j ∈ Finset.range n, (j : ℝ) ^ 2) := by
    calc
      _ = ∑ k ∈ Finset.range n,
          (1 + (2 / (n : ℝ)) * (k : ℝ)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = _ := by
        rw [sum_range_affine_square_real]
        ring
  unfold lowerSum
  calc
    _ = ((1 / (n : ℝ)) * (2 / (n : ℝ))) * (n : ℝ) *
        ((∑ i ∈ Finset.range n, (1 + (i : ℝ) / n) ^ 2) +
          (∑ j ∈ Finset.range n, (1 + 2 * (j : ℝ) / n) ^ 2)) := by
      simpa only [mul_assoc] using
        (double_sum_separable_real n
          (fun i => (1 + (i : ℝ) / n) ^ 2)
          (fun j => (1 + 2 * (j : ℝ) / n) ^ 2)
          ((1 / (n : ℝ)) * (2 / (n : ℝ))))
    _ = expandedLower n := by
      rw [hx, hy]
      unfold expandedLower
      field_simp [hn0]
      ring

theorem gap3 (n : ℕ) (hn : 0 < n) :
    expandedLower n = lowerClosed n := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  unfold expandedLower lowerClosed
  simp only [sum_range_cast_real, sum_range_sq_real]
  field_simp [hn0]
  ring

theorem gap4 (n : ℕ) (hn : 0 < n) :
    lowerSum n = lowerClosed n := by
  calc
    lowerSum n = expandedLower n := gap2 n hn
    _ = lowerClosed n := gap3 n hn

theorem gap5 (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ) ^ 2) =
      ((n : ℝ) - 1) * n * (2 * (n : ℝ) - 1) / 6 := by
  exact sum_range_sq_real n

theorem gap6 (n : ℕ) :
    (∑ j ∈ Finset.range n, (j : ℝ) ^ 2) =
      ((n : ℝ) - 1) * n * (2 * (n : ℝ) - 1) / 6 := by
  exact gap5 n

theorem gap7 (n : ℕ) (hn : 0 < n) :
    upperSum n =
      ∑ i ∈ Finset.range n,
        ∑ j ∈ Finset.range n,
          ((1 + ((i + 1 : ℕ) : ℝ) / n) ^ 2 +
              (1 + 2 * ((j + 1 : ℕ) : ℝ) / n) ^ 2) *
            (1 / (n : ℝ)) * (2 / (n : ℝ)) := by
  rfl

theorem gap8 (n : ℕ) (hn : 0 < n) :
    upperSum n = upperClosed n := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hx :
      (∑ i ∈ Finset.range n, (1 + ((i + 1 : ℕ) : ℝ) / n) ^ 2) =
        (1 / (n : ℝ) ^ 2) * (∑ i ∈ Finset.range n, (i : ℝ) ^ 2) +
          (2 * (1 + 1 / (n : ℝ)) / (n : ℝ)) *
            (∑ i ∈ Finset.range n, (i : ℝ)) +
          (n : ℝ) * (1 + 1 / (n : ℝ)) ^ 2 := by
    calc
      _ = ∑ k ∈ Finset.range n,
          ((1 + 1 / (n : ℝ)) +
            (1 / (n : ℝ)) * (k : ℝ)) ^ 2 := by
              apply Finset.sum_congr rfl
              intro k hk
              simp only [Nat.cast_add, Nat.cast_one]
              ring
      _ = _ := by
        rw [sum_range_affine_square_real]
        ring
  have hy :
      (∑ j ∈ Finset.range n, (1 + 2 * ((j + 1 : ℕ) : ℝ) / n) ^ 2) =
        (4 / (n : ℝ) ^ 2) * (∑ j ∈ Finset.range n, (j : ℝ) ^ 2) +
          (4 * (1 + 2 / (n : ℝ)) / (n : ℝ)) *
            (∑ j ∈ Finset.range n, (j : ℝ)) +
          (n : ℝ) * (1 + 2 / (n : ℝ)) ^ 2 := by
    calc
      _ = ∑ k ∈ Finset.range n,
          ((1 + 2 / (n : ℝ)) +
            (2 / (n : ℝ)) * (k : ℝ)) ^ 2 := by
              apply Finset.sum_congr rfl
              intro k hk
              simp only [Nat.cast_add, Nat.cast_one]
              ring
      _ = _ := by
        rw [sum_range_affine_square_real]
        ring
  unfold upperSum
  calc
    _ = ((1 / (n : ℝ)) * (2 / (n : ℝ))) * (n : ℝ) *
        ((∑ i ∈ Finset.range n, (1 + ((i + 1 : ℕ) : ℝ) / n) ^ 2) +
          (∑ j ∈ Finset.range n,
            (1 + 2 * ((j + 1 : ℕ) : ℝ) / n) ^ 2)) := by
      simpa only [mul_assoc] using
        (double_sum_separable_real n
          (fun i => (1 + ((i + 1 : ℕ) : ℝ) / n) ^ 2)
          (fun j => (1 + 2 * ((j + 1 : ℕ) : ℝ) / n) ^ 2)
          ((1 / (n : ℝ)) * (2 / (n : ℝ))))
    _ = upperClosed n := by
      rw [hx, hy]
      unfold upperClosed
      simp only [sum_range_cast_real, sum_range_sq_real]
      field_simp [hn0]
      ring

theorem gap9 (n : ℕ) (hn : 0 < n) :
    upperSum n = upperClosed n := by
  exact gap8 n hn

theorem gap10 :
    Tendsto lowerSum atTop (nhds (40 / 3 : ℝ)) := by
  have h₁ :
      Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hc :
      Tendsto (fun _ : ℕ => (40 / 3 : ℝ)) atTop (nhds (40 / 3 : ℝ)) :=
    tendsto_const_nhds
  have h11 :
      Tendsto (fun n : ℕ => (11 : ℝ) * ((1 : ℝ) / (n : ℝ))) atTop
        (nhds ((11 : ℝ) * 0)) :=
    tendsto_const_nhds.mul h₁
  have h5 :
      Tendsto
        (fun n : ℕ => (5 / 3 : ℝ) * ((1 : ℝ) / (n : ℝ)) ^ 2) atTop
        (nhds ((5 / 3 : ℝ) * (0 : ℝ) ^ 2)) :=
    tendsto_const_nhds.mul (h₁.pow 2)
  have ht :
      Tendsto
        (fun n : ℕ =>
          (40 / 3 : ℝ) - 11 * ((1 : ℝ) / (n : ℝ)) +
            (5 / 3 : ℝ) * ((1 : ℝ) / (n : ℝ)) ^ 2)
        atTop (nhds (40 / 3 : ℝ)) := by
    simpa using (hc.sub h11).add h5
  refine ht.congr' (eventually_atTop.2 ⟨1, ?_⟩)
  intro n hn
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hnpos)
  rw [gap4 n hnpos]
  unfold lowerClosed
  field_simp [hn0]

theorem gap11 :
    Tendsto upperSum atTop (nhds (40 / 3 : ℝ)) := by
  have h₁ :
      Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hc :
      Tendsto (fun _ : ℕ => (40 / 3 : ℝ)) atTop (nhds (40 / 3 : ℝ)) :=
    tendsto_const_nhds
  have h11 :
      Tendsto (fun n : ℕ => (11 : ℝ) * ((1 : ℝ) / (n : ℝ))) atTop
        (nhds ((11 : ℝ) * 0)) :=
    tendsto_const_nhds.mul h₁
  have h5 :
      Tendsto
        (fun n : ℕ => (5 / 3 : ℝ) * ((1 : ℝ) / (n : ℝ)) ^ 2) atTop
        (nhds ((5 / 3 : ℝ) * (0 : ℝ) ^ 2)) :=
    tendsto_const_nhds.mul (h₁.pow 2)
  have ht :
      Tendsto
        (fun n : ℕ =>
          (40 / 3 : ℝ) + 11 * ((1 : ℝ) / (n : ℝ)) +
            (5 / 3 : ℝ) * ((1 : ℝ) / (n : ℝ)) ^ 2)
        atTop (nhds (40 / 3 : ℝ)) := by
    simpa using (hc.add h11).add h5
  refine ht.congr' (eventually_atTop.2 ⟨1, ?_⟩)
  intro n hn
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hnpos)
  rw [gap8 n hnpos]
  unfold upperClosed
  field_simp [hn0]

end

end ProofGap.Exercise3902
