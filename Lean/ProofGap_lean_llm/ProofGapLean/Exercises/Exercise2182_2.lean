import ProofGapLean.Prelude.Finite
import Mathlib.Data.Real.Sqrt

namespace ProofGap.Exercise2182_2
noncomputable section

open scoped BigOperators

def m (n i : ℕ) : ℝ := Real.sqrt ((i : ℝ) / n)
def M (n i : ℕ) : ℝ := Real.sqrt (((i : ℝ) + 1) / n)
def lowerSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (1 / (n : ℝ)) * m n i
def upperSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (1 / (n : ℝ)) * M n i

theorem gap1 (n i : ℕ) (hn : 0 < n) (hi : i < n) :
    m n i = Real.sqrt ((i : ℝ) / n) ∧
      M n i = Real.sqrt (((i : ℝ) + 1) / n) := by
  constructor <;> rfl

theorem gap2 (n : ℕ) (hn : 0 < n) :
    lowerSum n =
      ∑ i ∈ Finset.range n, (1 / (n : ℝ)) * Real.sqrt ((i : ℝ) / n) := by
  rfl

theorem gap3 (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ Finset.range n, (1 / (n : ℝ)) * Real.sqrt ((i : ℝ) / n)) =
      (1 / (n : ℝ)) * ∑ i ∈ Finset.range n, Real.sqrt ((i : ℝ) / n) := by
  rw [Finset.mul_sum]

theorem gap4 (n : ℕ) (hn : 0 < n) :
    lowerSum n =
      (1 / (n : ℝ)) * ∑ i ∈ Finset.range n, Real.sqrt ((i : ℝ) / n) := by
  calc
    lowerSum n =
        ∑ i ∈ Finset.range n, (1 / (n : ℝ)) * Real.sqrt ((i : ℝ) / n) := gap2 n hn
    _ = (1 / (n : ℝ)) * ∑ i ∈ Finset.range n,
        Real.sqrt ((i : ℝ) / n) := gap3 n hn

theorem gap5 (n : ℕ) (hn : 0 < n) :
    upperSum n =
      ∑ i ∈ Finset.range n,
        (1 / (n : ℝ)) * Real.sqrt (((i : ℝ) + 1) / n) := by
  rfl

theorem gap6 (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ Finset.range n,
        (1 / (n : ℝ)) * Real.sqrt (((i : ℝ) + 1) / n)) =
      (1 / (n : ℝ)) * ∑ i ∈ Finset.range n,
        Real.sqrt (((i : ℝ) + 1) / n) := by
  rw [Finset.mul_sum]

theorem gap7 (n : ℕ) (hn : 0 < n) :
    upperSum n =
      (1 / (n : ℝ)) * ∑ i ∈ Finset.range n,
        Real.sqrt (((i : ℝ) + 1) / n) := by
  calc
    upperSum n =
        ∑ i ∈ Finset.range n,
          (1 / (n : ℝ)) * Real.sqrt (((i : ℝ) + 1) / n) := gap5 n hn
    _ = (1 / (n : ℝ)) * ∑ i ∈ Finset.range n,
        Real.sqrt (((i : ℝ) + 1) / n) := gap6 n hn

end
end ProofGap.Exercise2182_2
