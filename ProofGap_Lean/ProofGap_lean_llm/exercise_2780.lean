import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology
open Filter

namespace Exercise2780

def PosNatSet : Set ℕ := {n | 0 < n}
def UniformConvergentSeriesOn (a : ℕ -> ℝ -> ℝ) (domain : Set ℝ) (S : ℝ -> ℝ) : Prop :=
  TendstoUniformlyOn (fun N x => ∑ k ∈ Finset.Icc 1 N, a k x) S atTop domain

-- exercise: exercise_2780

theorem proof_gap_exercise_2780_1 (a s : ℕ -> ℝ -> ℝ) (S : ℝ)
  : ∀ n, n ∈ (Set.univ : Set ℕ) ∧ n ∈ PosNatSet -> |∑ k ∈ Finset.Icc 1 n, Real.cos ((2 * (k:ℝ) * Real.pi) / 3)| ≤ 1 / |Real.sin (Real.pi / 3)| ∧ 1 / |Real.sin (Real.pi / 3)| = 2 / Real.sqrt 3 := by
  sorry

theorem proof_gap_exercise_2780_2 (a s : ℕ -> ℝ -> ℝ) (S : ℝ)
  (h4 : ∀ n, n ∈ (Set.univ : Set ℕ) ∧ n ∈ PosNatSet -> |∑ k ∈ Finset.Icc 1 n, Real.cos ((2 * (k:ℝ) * Real.pi) / 3)| ≤ 1 / |Real.sin (Real.pi / 3)| ∧ 1 / |Real.sin (Real.pi / 3)| = 2 / Real.sqrt 3)
  : ∀ x, x ∈ (Set.univ : Set ℝ) -> MonotoneOn (fun n : ℕ => 1 / Real.sqrt ((n:ℝ)^2 + x^2)) PosNatSet := by
  sorry

theorem proof_gap_exercise_2780_3 (a s : ℕ -> ℝ -> ℝ) (S : ℝ)
  (h5 : ∀ x, x ∈ (Set.univ : Set ℝ) -> MonotoneOn (fun n : ℕ => 1 / Real.sqrt ((n:ℝ)^2 + x^2)) PosNatSet)
  : ∀ x, x ∈ (Set.univ : Set ℝ) -> ∀ n, n ∈ (Set.univ : Set ℕ) ∧ n ∈ PosNatSet -> 1 / Real.sqrt ((n:ℝ)^2 + x^2) ≤ 1 / n := by
  sorry

theorem proof_gap_exercise_2780_4 (a s : ℕ -> ℝ -> ℝ) (S : ℝ)
  (h6 : ∀ x, x ∈ (Set.univ : Set ℝ) -> ∀ n, n ∈ (Set.univ : Set ℕ) ∧ n ∈ PosNatSet -> 1 / Real.sqrt ((n:ℝ)^2 + x^2) ≤ 1 / n)
  : ∀ x, x ∈ (Set.univ : Set ℝ) -> Tendsto (fun n : ℕ => 1 / Real.sqrt ((n:ℝ)^2 + x^2)) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_2780_5 (a s : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ)
  (h4 : ∀ n, n ∈ (Set.univ : Set ℕ) ∧ n ∈ PosNatSet -> |∑ k ∈ Finset.Icc 1 n, Real.cos ((2 * (k:ℝ) * Real.pi) / 3)| ≤ 1 / |Real.sin (Real.pi / 3)| ∧ 1 / |Real.sin (Real.pi / 3)| = 2 / Real.sqrt 3)
  (h5 : ∀ x, x ∈ (Set.univ : Set ℝ) -> MonotoneOn (fun n : ℕ => 1 / Real.sqrt ((n:ℝ)^2 + x^2)) PosNatSet)
  (h7 : ∀ x, x ∈ (Set.univ : Set ℝ) -> Tendsto (fun n : ℕ => 1 / Real.sqrt ((n:ℝ)^2 + x^2)) atTop (𝓝 0))
  : UniformConvergentSeriesOn a (Set.univ : Set ℝ) S := by
  sorry

theorem proof_gap_exercise_2780_6 (a s : ℕ -> ℝ -> ℝ) (S0 : ℝ)
  : ∀ (a s : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ), (∀ n x, n ∈ (Set.univ : Set ℕ) ∧ n ∈ PosNatSet ∧ x ∈ (Set.univ : Set ℝ) -> a n x = Real.cos ((2 * (n:ℝ) * Real.pi) / 3) / Real.sqrt ((n:ℝ)^2 + x^2)) ∧ (∀ n x, n ∈ (Set.univ : Set ℕ) ∧ n ∈ PosNatSet ∧ x ∈ (Set.univ : Set ℝ) -> s n x = ∑ k ∈ Finset.Icc 1 n, a k x) -> UniformConvergentSeriesOn a (Set.univ : Set ℝ) S := by
  sorry

end Exercise2780
