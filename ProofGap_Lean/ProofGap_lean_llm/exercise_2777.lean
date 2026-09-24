import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology
open Filter

namespace Exercise2777

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

def PosRealSet : Set ℝ := {x | 0 < x}
def PosNatSet : Set ℕ := {n | 0 < n}
def UniformConvergentSeriesOn (a : ℕ -> ℝ -> ℝ) (domain : Set ℝ) (S : ℝ -> ℝ) : Prop :=
  TendstoUniformlyOn (fun N x => ∑ k ∈ Finset.Icc 1 N, a k x) S atTop domain

-- exercise: exercise_2777

theorem proof_gap_exercise_2777_1 (a s : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  (h5 : ∀ n x, n ∈ (Set.univ : Set ℕ) ∧ x ∈ (Set.univ : Set ℝ) ∧ n ∈ PosNatSet ∧ x ∈ PosRealSet -> a n x = ((-1:ℝ)^n) /. (x + n))
  (h6 : ∀ n x, n ∈ (Set.univ : Set ℕ) ∧ x ∈ (Set.univ : Set ℝ) ∧ n ∈ PosNatSet ∧ x ∈ PosRealSet -> s n x = ∑ k ∈ Finset.Icc 1 n, a k x)
  : ∀ n, n ∈ (Set.univ : Set ℕ) ∧ n ∈ PosNatSet -> |∑ k ∈ Finset.Icc 1 n, ((-1:ℝ)^k)| ≤ 1 := by
  sorry

theorem proof_gap_exercise_2777_2 (a s : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  (h7 : ∀ n, n ∈ (Set.univ : Set ℕ) ∧ n ∈ PosNatSet -> |∑ k ∈ Finset.Icc 1 n, ((-1:ℝ)^k)| ≤ 1)
  : ∀ x, x ∈ (Set.univ : Set ℝ) ∧ 0 < x -> ∀ n, n ∈ (Set.univ : Set ℕ) ∧ n ∈ PosNatSet -> (1 /. ((n : ℝ) + x)) < (1 /. n) := by
  sorry

theorem proof_gap_exercise_2777_3 (a s : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  (h8 : ∀ x, x ∈ (Set.univ : Set ℝ) ∧ 0 < x -> ∀ n, n ∈ (Set.univ : Set ℕ) ∧ n ∈ PosNatSet -> (1 /. ((n : ℝ) + x)) < (1 /. n))
  : ∀ x, x ∈ (Set.univ : Set ℝ) ∧ 0 < x -> MonotoneOn (fun n : ℕ => 1 /. ((n : ℝ) + x)) (Set.univ : Set ℕ) := by
  sorry

theorem proof_gap_exercise_2777_4 (a s : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  (h9 : ∀ x, x ∈ (Set.univ : Set ℝ) ∧ 0 < x -> MonotoneOn (fun n : ℕ => 1 /. ((n : ℝ) + x)) (Set.univ : Set ℕ))
  : ∀ x, x ∈ (Set.univ : Set ℝ) ∧ 0 < x -> Tendsto (fun n : ℕ => 1 /. ((n : ℝ) + x)) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_2777_5 (a s : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  (h7 : ∀ n, n ∈ (Set.univ : Set ℕ) ∧ n ∈ PosNatSet -> |∑ k ∈ Finset.Icc 1 n, ((-1:ℝ)^k)| ≤ 1)
  (h9 : ∀ x, x ∈ (Set.univ : Set ℝ) ∧ 0 < x -> MonotoneOn (fun n : ℕ => 1 /. ((n : ℝ) + x)) (Set.univ : Set ℕ))
  (h10 : ∀ x, x ∈ (Set.univ : Set ℝ) ∧ 0 < x -> Tendsto (fun n : ℕ => 1 /. ((n : ℝ) + x)) atTop (𝓝 0))
  : UniformConvergentSeriesOn a PosRealSet S := by
  sorry

theorem proof_gap_exercise_2777_6 (a s : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  (h11 : UniformConvergentSeriesOn a PosRealSet S)
  : UniformConvergentSeriesOn a PosRealSet S := by
  sorry

end Exercise2777
