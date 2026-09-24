import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology
open Filter

namespace Exercise2779

def ClosedTen : Set ℝ := Set.Icc (-10) 10
def PosNatSet : Set ℕ := {n | 0 < n}
noncomputable def cbrtDen (n : ℕ) (x : ℝ) : ℝ := Real.rpow ((n:ℝ)^2 + Real.exp x) ((1:ℝ) / 3)
def UniformConvergentSeriesOn (a : ℕ -> ℝ -> ℝ) (domain : Set ℝ) (S : ℝ -> ℝ) : Prop :=
  TendstoUniformlyOn (fun N x => ∑ k ∈ Finset.Icc 1 N, a k x) S atTop domain

-- exercise: exercise_2779

theorem proof_gap_exercise_2779_1 (a b s : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  (h6 : ∀ n x, n ∈ (Set.univ : Set ℕ) ∧ x ∈ (Set.univ : Set ℝ) ∧ n ∈ PosNatSet ∧ x ∈ ClosedTen -> b n x = 1 / cbrtDen n x)
  (h7 : ∀ n x, n ∈ (Set.univ : Set ℕ) ∧ x ∈ (Set.univ : Set ℝ) ∧ n ∈ PosNatSet ∧ x ∈ ClosedTen -> a n x = ((-1:ℝ)^((n * (n - 1)) / 2)) / cbrtDen n x)
  (h8 : ∀ n x, n ∈ (Set.univ : Set ℕ) ∧ x ∈ (Set.univ : Set ℝ) ∧ n ∈ PosNatSet ∧ x ∈ ClosedTen -> s n x = ∑ k ∈ Finset.Icc 1 n, a k x)
  : ∀ n, n ∈ (Set.univ : Set ℕ) ∧ n ∈ PosNatSet -> |∑ k ∈ Finset.Icc 1 n, ((-1:ℝ)^((k * (k - 1)) / 2))| ≤ 2 := by
  sorry

theorem proof_gap_exercise_2779_2 (a b s : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  (h9 : ∀ n, n ∈ (Set.univ : Set ℕ) ∧ n ∈ PosNatSet -> |∑ k ∈ Finset.Icc 1 n, ((-1:ℝ)^((k * (k - 1)) / 2))| ≤ 2)
  : ∀ x, x ∈ (Set.univ : Set ℝ) ∧ |x| ≤ 10 -> ∀ n, n ∈ (Set.univ : Set ℕ) ∧ n ∈ PosNatSet -> 1 / cbrtDen n x > 1 / cbrtDen (n + 1) x := by
  sorry

theorem proof_gap_exercise_2779_3 (a b s : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  (h10 : ∀ x, x ∈ (Set.univ : Set ℝ) ∧ |x| ≤ 10 -> ∀ n, n ∈ (Set.univ : Set ℕ) ∧ n ∈ PosNatSet -> 1 / cbrtDen n x > 1 / cbrtDen (n + 1) x)
  : ∀ x, x ∈ (Set.univ : Set ℝ) ∧ |x| ≤ 10 -> MonotoneOn (fun n : ℕ => b n x) (Set.univ : Set ℕ) := by
  sorry

theorem proof_gap_exercise_2779_4 (a b s : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  (h11 : ∀ x, x ∈ (Set.univ : Set ℝ) ∧ |x| ≤ 10 -> MonotoneOn (fun n : ℕ => b n x) (Set.univ : Set ℕ))
  : ∀ x, x ∈ (Set.univ : Set ℝ) ∧ |x| ≤ 10 -> ∀ n, n ∈ (Set.univ : Set ℕ) ∧ n ∈ PosNatSet -> b n x < 1 / (Real.rpow ((n:ℝ)^2) ((1:ℝ) / 3)) := by
  sorry

theorem proof_gap_exercise_2779_5 (a b s : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  (h12 : ∀ x, x ∈ (Set.univ : Set ℝ) ∧ |x| ≤ 10 -> ∀ n, n ∈ (Set.univ : Set ℕ) ∧ n ∈ PosNatSet -> b n x < 1 / (Real.rpow ((n:ℝ)^2) ((1:ℝ) / 3)))
  : ∀ x, x ∈ (Set.univ : Set ℝ) ∧ |x| ≤ 10 -> Tendsto (fun n : ℕ => b n x) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_2779_6 (a b s : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  (h9 : ∀ n, n ∈ (Set.univ : Set ℕ) ∧ n ∈ PosNatSet -> |∑ k ∈ Finset.Icc 1 n, ((-1:ℝ)^((k * (k - 1)) / 2))| ≤ 2)
  (h11 : ∀ x, x ∈ (Set.univ : Set ℝ) ∧ |x| ≤ 10 -> MonotoneOn (fun n : ℕ => b n x) (Set.univ : Set ℕ))
  (h13 : ∀ x, x ∈ (Set.univ : Set ℝ) ∧ |x| ≤ 10 -> Tendsto (fun n : ℕ => b n x) atTop (𝓝 0))
  : UniformConvergentSeriesOn a ClosedTen S := by
  sorry

theorem proof_gap_exercise_2779_7 (a b s : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  (h14 : UniformConvergentSeriesOn a ClosedTen S)
  : UniformConvergentSeriesOn a ClosedTen S := by
  sorry

end Exercise2779
