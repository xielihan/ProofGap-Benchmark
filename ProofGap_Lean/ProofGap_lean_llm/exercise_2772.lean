import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

def ConvergentSeries (a : ℕ -> ℝ) : Prop := Summable a
def AbsoluteConvergentSeries (a : ℕ -> ℝ) : Prop := Summable (fun n => ‖a n‖)
def UniformConvergent (F : ℕ -> ℝ -> ℝ) (s : Set ℝ) (g : ℝ -> ℝ) : Prop :=
  TendstoUniformlyOn F g atTop s
def PosRealSet : Set ℝ := {x | 0 < x}

-- exercise: exercise_2772

theorem proof_gap_exercise_2772_1
    (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
    (h3 : k ∈ (Set.univ : Set ℕ))
    (h4 : ∀ n x, n ∈ (Set.univ : Set ℕ) ∧ x ∈ (Set.univ : Set ℝ) ∧ n ∈ {m : ℕ | 0 < m} ∧ x ∈ PosRealSet →
      S_n n x = ∑ j ∈ Finset.Icc 1 n, 1 /. ((x + (j : ℝ)) * (x + (j : ℝ) + 1))) :
    ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) →
      ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ n ∈ {m : ℕ | 0 < m} ∧ x ∈ PosRealSet →
        |1 /. ((x + (n : ℝ)) * (x + (n : ℝ) + 1))| < 1 /. ((n : ℝ) ^ 2) := by
  sorry

theorem proof_gap_exercise_2772_2
    (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ) (k : ℕ)
    (h5 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) →
      ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ n ∈ {m : ℕ | 0 < m} ∧ x ∈ PosRealSet →
        |1 /. ((x + (n : ℝ)) * (x + (n : ℝ) + 1))| < 1 /. ((n : ℝ) ^ 2)) :
    ConvergentSeries (fun n : ℕ => if 1 ≤ n then 1 /. ((n : ℝ) ^ 2) else 0) := by
  sorry

theorem proof_gap_exercise_2772_3
    (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ)
    (h5 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) →
      ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ n ∈ {m : ℕ | 0 < m} ∧ x ∈ PosRealSet →
        |1 /. ((x + (n : ℝ)) * (x + (n : ℝ) + 1))| < 1 /. ((n : ℝ) ^ 2))
    (h6 : ConvergentSeries (fun n : ℕ => if 1 ≤ n then 1 /. ((n : ℝ) ^ 2) else 0)) :
    ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ PosRealSet →
      AbsoluteConvergentSeries (fun n : ℕ => if 1 ≤ n then 1 /. ((x + (n : ℝ)) * (x + (n : ℝ) + 1)) else 0) := by
  sorry

theorem proof_gap_exercise_2772_4
    (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ)
    (h5 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) →
      ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ n ∈ {m : ℕ | 0 < m} ∧ x ∈ PosRealSet →
        |1 /. ((x + (n : ℝ)) * (x + (n : ℝ) + 1))| < 1 /. ((n : ℝ) ^ 2))
    (h6 : ConvergentSeries (fun n : ℕ => if 1 ≤ n then 1 /. ((n : ℝ) ^ 2) else 0))
    (h7 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ PosRealSet →
      AbsoluteConvergentSeries (fun n : ℕ => if 1 ≤ n then 1 /. ((x + (n : ℝ)) * (x + (n : ℝ) + 1)) else 0)) :
    UniformConvergent S_n PosRealSet S := by
  sorry

theorem proof_gap_exercise_2772_5
    (S_n : ℕ -> ℝ -> ℝ) (S : ℝ -> ℝ)
    (h7 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ PosRealSet →
      AbsoluteConvergentSeries (fun n : ℕ => if 1 ≤ n then 1 /. ((x + (n : ℝ)) * (x + (n : ℝ) + 1)) else 0))
    (h8 : UniformConvergent S_n PosRealSet S) :
    (∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ PosRealSet →
      AbsoluteConvergentSeries (fun n : ℕ => if 1 ≤ n then 1 /. ((x + (n : ℝ)) * (x + (n : ℝ) + 1)) else 0)) ∧
      UniformConvergent S_n PosRealSet S := by
  sorry
