import ProofGapLean.Prelude.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2181
noncomputable section

open scoped BigOperators

def width (n : ℕ) : ℝ := 5 / (n : ℝ)

def cell (n i : ℕ) : Set ℝ :=
  Set.Ioo (-1 + 5 * (i : ℝ) / n) (-1 + 5 * (i : ℝ) / n + width n)

def midpoint (n i : ℕ) : ℝ :=
  -1 + ((i : ℝ) + 1 / 2) * width n

def midpointSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (1 + midpoint n i) * width n

private theorem midpointIndexSum (n : ℕ) :
    (∑ i ∈ Finset.range n, ((i : ℝ) + 1 / 2)) = (n : ℝ) ^ 2 / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [Nat.cast_succ]
      ring

theorem gap1 (n : ℕ) (hn : 0 < n) :
    width n = 5 / (n : ℝ) := by
  rfl

theorem gap2 (n i : ℕ) (hn : 0 < n) (hi : i < n) :
    cell n i =
      Set.Ioo (-1 + 5 * (i : ℝ) / n)
        (-1 + 5 * (i : ℝ) / n + 5 / (n : ℝ)) := by
  rfl

theorem gap3 (n i : ℕ) (hn : 0 < n) (hi : i < n) :
    midpoint n i = -1 + ((i : ℝ) + 1 / 2) * (5 / (n : ℝ)) := by
  rfl

theorem gap4 (n : ℕ) (hn : 0 < n) :
    midpointSum n =
      ∑ i ∈ Finset.range n,
        (1 + (-1 + ((i : ℝ) + 1 / 2) * (5 / (n : ℝ)))) *
          (5 / (n : ℝ)) := by
  rfl

theorem gap5 (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ Finset.range n,
        (1 + (-1 + ((i : ℝ) + 1 / 2) * (5 / (n : ℝ)))) *
          (5 / (n : ℝ))) =
      25 / (n : ℝ) ^ 2 *
        ∑ i ∈ Finset.range n, ((i : ℝ) + 1 / 2) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hsum :
      ∀ m : ℕ,
        (∑ i ∈ Finset.range m,
            (1 + (-1 + ((i : ℝ) + 1 / 2) * (5 / (n : ℝ)))) *
              (5 / (n : ℝ))) =
          25 / (n : ℝ) ^ 2 *
            ∑ i ∈ Finset.range m, ((i : ℝ) + 1 / 2) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        simp only [Finset.sum_range_succ]
        rw [ih]
        field_simp [hn0] <;> ring
  exact hsum n

theorem gap6 (n : ℕ) (hn : 0 < n) :
    25 / (n : ℝ) ^ 2 *
        ∑ i ∈ Finset.range n, ((i : ℝ) + 1 / 2) =
      25 / 2 := by
  rw [midpointIndexSum]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp [hn0] <;> ring

theorem gap7 (n : ℕ) (hn : 0 < n) :
    midpointSum n = 25 / 2 := by
  rw [gap4 n hn, gap5 n hn, gap6 n hn]

end
end ProofGap.Exercise2181
