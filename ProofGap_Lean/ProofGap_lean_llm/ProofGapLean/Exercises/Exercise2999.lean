import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise2999

noncomputable section

def term (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * (n : ℝ) /
    (Nat.factorial (2 * n + 1) : ℝ)

def splitTerm (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / 2 *
    (1 / (Nat.factorial (2 * n) : ℝ) -
      1 / (Nat.factorial (2 * n + 1) : ℝ))

def seriesSum : ℝ :=
  ∑' n : ℕ, term n

def evenFactorialSeries : ℝ :=
  ∑' n : ℕ,
    (-1 : ℝ) ^ n / (Nat.factorial (2 * n) : ℝ)

def oddFactorialSeries : ℝ :=
  ∑' n : ℕ,
    (-1 : ℝ) ^ n / (Nat.factorial (2 * n + 1) : ℝ)

private theorem factorialSeries_hasSum :
    HasSum
        (fun n : ℕ =>
          (-1 : ℝ) ^ n / (Nat.factorial (2 * n) : ℝ))
        (Real.cos 1) ∧
      HasSum
        (fun n : ℕ =>
          (-1 : ℝ) ^ n / (Nat.factorial (2 * n + 1) : ℝ))
        (Real.sin 1) := by
  constructor
  · simpa using Real.hasSum_cos 1
  · simpa using Real.hasSum_sin 1

theorem gap1 :
    -(1 / (Nat.factorial 3 : ℝ)) =
      -(1 / 2) *
        (1 / (Nat.factorial 2 : ℝ) -
          1 / (Nat.factorial 3 : ℝ)) := by
  norm_num

theorem gap2 :
    2 / (Nat.factorial 5 : ℝ) =
      1 / 2 *
        (1 / (Nat.factorial 4 : ℝ) -
          1 / (Nat.factorial 5 : ℝ)) := by
  norm_num

theorem gap3 :
    ∀ n : ℕ, term n = splitTerm n := by
  intro n
  unfold term splitTerm
  have hEven : (Nat.factorial (2 * n) : ℝ) ≠ 0 := by
    positivity
  have hOdd : (Nat.factorial (2 * n + 1) : ℝ) ≠ 0 := by
    positivity
  field_simp [hEven, hOdd] <;>
    norm_num [Nat.factorial_succ] <;>
    ring

theorem gap4 :
    seriesSum =
      1 / 2 * (evenFactorialSeries - oddFactorialSeries) := by
  have hSplit :
      HasSum splitTerm
        (1 / 2 * (Real.cos 1 - Real.sin 1)) := by
    refine ((factorialSeries_hasSum.1.sub factorialSeries_hasSum.2).mul_left
      (1 / 2 : ℝ)).congr ?_
    intro n
    unfold splitTerm
    ring
  calc
    seriesSum = ∑' n : ℕ, splitTerm n := by
      unfold seriesSum
      rw [show term = splitTerm from funext gap3]
    _ = 1 / 2 * (Real.cos 1 - Real.sin 1) := hSplit.tsum_eq
    _ = 1 / 2 * (evenFactorialSeries - oddFactorialSeries) := by
      unfold evenFactorialSeries oddFactorialSeries
      rw [factorialSeries_hasSum.1.tsum_eq,
        factorialSeries_hasSum.2.tsum_eq]

theorem gap5 :
    seriesSum =
      1 / 2 * (evenFactorialSeries - oddFactorialSeries) := by
  exact gap4

theorem gap6 :
    1 / 2 * (evenFactorialSeries - oddFactorialSeries) =
      1 / 2 * (Real.cos 1 - Real.sin 1) := by
  unfold evenFactorialSeries oddFactorialSeries
  rw [factorialSeries_hasSum.1.tsum_eq,
    factorialSeries_hasSum.2.tsum_eq]

theorem gap7 :
    seriesSum = 1 / 2 * (Real.cos 1 - Real.sin 1) := by
  calc
    seriesSum = 1 / 2 * (evenFactorialSeries - oddFactorialSeries) := gap4
    _ = 1 / 2 * (Real.cos 1 - Real.sin 1) := gap6

end

end ProofGap.Exercise2999
