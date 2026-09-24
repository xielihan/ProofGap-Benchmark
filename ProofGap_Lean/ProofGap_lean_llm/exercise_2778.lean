import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology
open Filter

namespace Exercise2778

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

def ClosedInterval : Set ℝ := Set.Icc 0 (2 * Real.pi)
def IntGeTwo : Set ℤ := {n | 2 ≤ n}
def PosNatSet : Set ℕ := {n | 0 < n}
def UniformConvergentSeriesOn (a : ℤ -> ℝ -> ℝ) (domain : Set ℝ) (S : ℝ -> ℝ) : Prop :=
  TendstoUniformlyOn (fun N x => ∑ k ∈ Finset.Icc (2:ℤ) N, a k x) S atTop domain

-- exercise: exercise_2778

theorem proof_gap_exercise_2778_1 (a s : ℤ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℤ)
  (h5 : ∀ n x, x ∈ (Set.univ : Set ℝ) ∧ n ∈ (Set.univ : Set ℤ) ∧ x ∈ ClosedInterval ∧ n ≥ 2 -> a n x = ((-1:ℝ)^n.natAbs) /. ((n : ℝ) + Real.sin x))
  (h6 : ∀ n x, x ∈ (Set.univ : Set ℝ) ∧ n ∈ (Set.univ : Set ℤ) ∧ x ∈ ClosedInterval ∧ n ≥ 2 -> s n x = ∑ k ∈ Finset.Icc (2:ℤ) n, a k x)
  : ∀ x, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ 2 * Real.pi -> MonotoneOn (fun n : ℤ => 1 /. ((n : ℝ) + Real.sin x)) IntGeTwo := by
  sorry

theorem proof_gap_exercise_2778_2 (a s : ℤ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℤ)
  (h7 : ∀ x, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ 2 * Real.pi -> MonotoneOn (fun n : ℤ => 1 /. ((n : ℝ) + Real.sin x)) IntGeTwo)
  : ∀ x, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ 2 * Real.pi -> ∀ n, n ∈ (Set.univ : Set ℤ) ∧ n ≥ 2 -> 0 < (1 /. ((n : ℝ) + Real.sin x)) ∧ (1 /. ((n : ℝ) + Real.sin x)) < (1 /. ((n : ℝ) - 1)) := by
  sorry

theorem proof_gap_exercise_2778_3 (a s : ℤ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℤ)
  (h8 : ∀ x, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ 2 * Real.pi -> ∀ n, n ∈ (Set.univ : Set ℤ) ∧ n ≥ 2 -> 0 < (1 /. ((n : ℝ) + Real.sin x)) ∧ (1 /. ((n : ℝ) + Real.sin x)) < (1 /. ((n : ℝ) - 1)))
  : ∀ x, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ 2 * Real.pi -> Tendsto (fun n : ℕ => 1 /. (((n + 2 : ℕ) : ℝ) + Real.sin x)) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_2778_4 (a s : ℤ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℤ)
  : ∀ n, n ∈ (Set.univ : Set ℕ) ∧ n ∈ PosNatSet -> |∑ k ∈ Finset.Icc 1 n, ((-1:ℝ)^k)| ≤ 1 := by
  sorry

theorem proof_gap_exercise_2778_5 (a s : ℤ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℤ)
  (h7 : ∀ x, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ 2 * Real.pi -> MonotoneOn (fun n : ℤ => 1 /. ((n : ℝ) + Real.sin x)) IntGeTwo)
  (h9 : ∀ x, x ∈ (Set.univ : Set ℝ) ∧ 0 ≤ x ∧ x ≤ 2 * Real.pi -> Tendsto (fun n : ℕ => 1 /. (((n + 2 : ℕ) : ℝ) + Real.sin x)) atTop (𝓝 0))
  (h10 : ∀ n, n ∈ (Set.univ : Set ℕ) ∧ n ∈ PosNatSet -> |∑ k ∈ Finset.Icc 1 n, ((-1:ℝ)^k)| ≤ 1)
  : UniformConvergentSeriesOn a ClosedInterval S := by
  sorry

theorem proof_gap_exercise_2778_6 (a s : ℤ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℤ)
  (h11 : UniformConvergentSeriesOn a ClosedInterval S)
  : UniformConvergentSeriesOn a ClosedInterval S := by
  sorry

end Exercise2778
