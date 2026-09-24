import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology
open Filter

namespace Exercise2776

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

def PosRealSet : Set ℝ := {x | 0 < x}
def PosNatSet : Set ℕ := {n | 0 < n}

def UniformConvergentSeriesOn (u : ℕ -> ℝ -> ℝ) (domain : Set ℝ) (S : ℝ -> ℝ) : Prop :=
  TendstoUniformlyOn (fun N x => ∑ k ∈ Finset.Icc 1 N, u k x) S atTop domain

noncomputable def term (n : ℕ) (x : ℝ) : ℝ := (2:ℝ)^n * Real.sin (1 /. ((3:ℝ)^n * x))
noncomputable def majorant (n : ℕ) (x : ℝ) : ℝ := (1 /. x) * ((2:ℝ) /. 3)^n

-- exercise: exercise_2776
-- source: sum n=1..infty of 2^n sin(1/(3^n x)) converges on (0,+infty), not uniformly.

theorem proof_gap_exercise_2776_1
  (u : ℕ -> ℝ -> ℝ) (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  (h5 : ∀ n x, n ∈ (Set.univ : Set ℕ) ∧ x ∈ (Set.univ : Set ℝ) ∧ n ∈ PosNatSet ∧ x ∈ PosRealSet -> u n x = term n x)
  (h6 : ∀ n x, n ∈ (Set.univ : Set ℕ) ∧ x ∈ (Set.univ : Set ℝ) ∧ n ∈ PosNatSet ∧ x ∈ PosRealSet -> S_n n x = ∑ k ∈ Finset.Icc 1 n, u k x)
  : ∀ n, n ∈ (Set.univ : Set ℕ) -> ∀ x, x ∈ (Set.univ : Set ℝ) ∧ n ∈ PosNatSet ∧ x ∈ PosRealSet -> |u n x| ≤ (2:ℝ)^n * (1 /. ((3:ℝ)^n * x)) := by
  sorry

theorem proof_gap_exercise_2776_2 (u : ℕ -> ℝ -> ℝ) (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  : ∀ n, n ∈ (Set.univ : Set ℕ) -> ∀ x, x ∈ (Set.univ : Set ℝ) ∧ n ∈ PosNatSet ∧ x ∈ PosRealSet -> (2:ℝ)^n * (1 /. ((3:ℝ)^n * x)) = majorant n x := by
  sorry

theorem proof_gap_exercise_2776_3 (u : ℕ -> ℝ -> ℝ) (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  (h7 : ∀ n, n ∈ (Set.univ : Set ℕ) -> ∀ x, x ∈ (Set.univ : Set ℝ) ∧ n ∈ PosNatSet ∧ x ∈ PosRealSet -> |u n x| ≤ (2:ℝ)^n * (1 /. ((3:ℝ)^n * x)))
  (h8 : ∀ n, n ∈ (Set.univ : Set ℕ) -> ∀ x, x ∈ (Set.univ : Set ℝ) ∧ n ∈ PosNatSet ∧ x ∈ PosRealSet -> (2:ℝ)^n * (1 /. ((3:ℝ)^n * x)) = majorant n x)
  : ∀ n, n ∈ (Set.univ : Set ℕ) -> ∀ x, x ∈ (Set.univ : Set ℝ) ∧ n ∈ PosNatSet ∧ x ∈ PosRealSet -> |u n x| ≤ majorant n x := by
  sorry

theorem proof_gap_exercise_2776_4 (u : ℕ -> ℝ -> ℝ) (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  : ∀ n, n ∈ (Set.univ : Set ℕ) -> ∀ x, x ∈ (Set.univ : Set ℝ) ∧ n ∈ PosNatSet ∧ x ∈ PosRealSet -> Summable (fun m : ℕ => if 1 ≤ m then majorant m x else 0) := by
  sorry

theorem proof_gap_exercise_2776_5 (u : ℕ -> ℝ -> ℝ) (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  : ∀ n, n ∈ (Set.univ : Set ℕ) -> ∀ x, x ∈ (Set.univ : Set ℝ) ∧ n ∈ PosNatSet ∧ x ∈ PosRealSet -> Summable (fun m : ℕ => if 1 ≤ m then ‖term m x‖ else 0) := by
  sorry

theorem proof_gap_exercise_2776_6 (u : ℕ -> ℝ -> ℝ) (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  : ∀ x, x ∈ (Set.univ : Set ℝ) ∧ x ∈ PosRealSet -> Summable (fun m : ℕ => if 1 ≤ m then term m x else 0) := by
  sorry

theorem proof_gap_exercise_2776_7 (u : ℕ -> ℝ -> ℝ) (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ UniformConvergentSeriesOn u PosRealSet S ∧ ε = 1 -> ∃ N : ℕ, N ∈ (Set.univ : Set ℕ) ∧ N ∈ PosNatSet ∧ (∀ n p x, n ∈ (Set.univ : Set ℕ) ∧ p ∈ (Set.univ : Set ℕ) ∧ x ∈ (Set.univ : Set ℝ) ∧ n ∈ PosNatSet ∧ p ∈ PosNatSet ∧ x ∈ PosRealSet ∧ n ≥ N -> |∑ k ∈ Finset.Icc (n + 1) (n + p), u k x| < ε) := by
  sorry

theorem proof_gap_exercise_2776_8 (u : ℕ -> ℝ -> ℝ) (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) -> ∀ N : ℕ, N ∈ (Set.univ : Set ℕ) -> ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) -> ∀ p : ℕ, p ∈ (Set.univ : Set ℕ) ∧ UniformConvergentSeriesOn u PosRealSet S ∧ ε = 1 ∧ n = N ∧ p = 1 -> ∀ x, x ∈ (Set.univ : Set ℝ) ∧ x ∈ PosRealSet -> |u (N + 1) x| < 1 := by
  sorry

theorem proof_gap_exercise_2776_9 (u : ℕ -> ℝ -> ℝ) (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) -> ∀ N : ℕ, N ∈ (Set.univ : Set ℕ) -> ∃ x0 : ℝ, x0 ∈ (Set.univ : Set ℝ) ∧ (UniformConvergentSeriesOn u PosRealSet S -> ε = 1 -> (x0 = 2 /. ((3:ℝ)^(N + 1) * Real.pi)) -> x0 ∈ PosRealSet) := by
  sorry

theorem proof_gap_exercise_2776_10 (u : ℕ -> ℝ -> ℝ) (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) -> ∀ N : ℕ, N ∈ (Set.univ : Set ℕ) -> ∃ x0 : ℝ, x0 ∈ (Set.univ : Set ℝ) ∧ (UniformConvergentSeriesOn u PosRealSet S -> ε = 1 -> (x0 = 2 /. ((3:ℝ)^(N + 1) * Real.pi)) -> |u (N + 1) x0| < 1) := by
  sorry

theorem proof_gap_exercise_2776_11 (u : ℕ -> ℝ -> ℝ) (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) -> ∀ N : ℕ, N ∈ (Set.univ : Set ℕ) -> ∃ x0 : ℝ, x0 ∈ (Set.univ : Set ℝ) ∧ (UniformConvergentSeriesOn u PosRealSet S -> ε = 1 -> (x0 = 2 /. ((3:ℝ)^(N + 1) * Real.pi)) -> u (N + 1) x0 = term (N + 1) x0) := by
  sorry

theorem proof_gap_exercise_2776_12 (u : ℕ -> ℝ -> ℝ) (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) -> ∀ N : ℕ, N ∈ (Set.univ : Set ℕ) -> ∃ x0 : ℝ, x0 ∈ (Set.univ : Set ℝ) ∧ (UniformConvergentSeriesOn u PosRealSet S -> ε = 1 -> (x0 = 2 /. ((3:ℝ)^(N + 1) * Real.pi)) -> term (N + 1) x0 = (2:ℝ)^(N + 1) * Real.sin (Real.pi /. 2)) := by
  sorry

theorem proof_gap_exercise_2776_13 (u : ℕ -> ℝ -> ℝ) (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) -> ∀ N : ℕ, N ∈ (Set.univ : Set ℕ) -> ∃ x0 : ℝ, x0 ∈ (Set.univ : Set ℝ) ∧ (UniformConvergentSeriesOn u PosRealSet S -> ε = 1 -> (x0 = 2 /. ((3:ℝ)^(N + 1) * Real.pi)) -> (2:ℝ)^(N + 1) * Real.sin (Real.pi /. 2) = (2:ℝ)^(N + 1)) := by
  sorry

theorem proof_gap_exercise_2776_14 (u : ℕ -> ℝ -> ℝ) (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) -> ∀ N : ℕ, N ∈ (Set.univ : Set ℕ) -> ∃ x0 : ℝ, x0 ∈ (Set.univ : Set ℝ) ∧ (UniformConvergentSeriesOn u PosRealSet S -> ε = 1 -> (x0 = 2 /. ((3:ℝ)^(N + 1) * Real.pi)) -> (2:ℝ)^(N + 1) > 1) := by
  sorry

theorem proof_gap_exercise_2776_15 (u : ℕ -> ℝ -> ℝ) (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) -> ∀ N : ℕ, N ∈ (Set.univ : Set ℕ) -> ∃ x0 : ℝ, x0 ∈ (Set.univ : Set ℝ) ∧ (UniformConvergentSeriesOn u PosRealSet S -> ε = 1 -> (x0 = 2 /. ((3:ℝ)^(N + 1) * Real.pi)) -> u (N + 1) x0 > 1) := by
  sorry

theorem proof_gap_exercise_2776_16 (u : ℕ -> ℝ -> ℝ) (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) -> ∀ N : ℕ, N ∈ (Set.univ : Set ℕ) -> ∃ x0 : ℝ, x0 ∈ (Set.univ : Set ℝ) ∧ (UniformConvergentSeriesOn u PosRealSet S -> ε = 1 -> (x0 = 2 /. ((3:ℝ)^(N + 1) * Real.pi)) -> False) := by
  sorry

theorem proof_gap_exercise_2776_17 (u : ℕ -> ℝ -> ℝ) (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  : ¬ UniformConvergentSeriesOn u PosRealSet S := by
  sorry

theorem proof_gap_exercise_2776_18 (u : ℕ -> ℝ -> ℝ) (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  : ∀ x, x ∈ (Set.univ : Set ℝ) ∧ x ∈ PosRealSet -> Summable (fun m : ℕ => if 1 ≤ m then term m x else 0) := by
  sorry

theorem proof_gap_exercise_2776_19 (u : ℕ -> ℝ -> ℝ) (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  : ¬ UniformConvergentSeriesOn u PosRealSet S := by
  sorry

theorem proof_gap_exercise_2776_20 (u : ℕ -> ℝ -> ℝ) (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
  : (∀ x, x ∈ (Set.univ : Set ℝ) ∧ x ∈ PosRealSet -> Summable (fun m : ℕ => if 1 ≤ m then term m x else 0)) ∧ ¬ UniformConvergentSeriesOn u PosRealSet S := by
  sorry

end Exercise2776
