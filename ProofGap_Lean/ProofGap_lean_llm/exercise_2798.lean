import Mathlib

attribute [local instance] Classical.propDecidable

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

-- exercise: exercise_2798

noncomputable def thetaTerm (n : ℤ) (x : ℝ) : ℝ :=
  Real.exp (-(Real.pi * ((n : ℝ) ^ (2 : ℕ)) * x))

noncomputable def thetaPosTerm (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-(Real.pi * ((n : ℝ) ^ (2 : ℕ)) * x))

noncomputable def thetaDeriTerm (n : ℕ) (x : ℝ) : ℝ :=
  Real.pi * ((n : ℝ) ^ (2 : ℕ)) * Real.exp (-(Real.pi * ((n : ℝ) ^ (2 : ℕ)) * x))

noncomputable def thetaHigherTerm (k n : ℕ) (x : ℝ) : ℝ :=
  (Real.pi * ((n : ℝ) ^ (2 : ℕ))) ^ k * Real.exp (-(Real.pi * ((n : ℝ) ^ (2 : ℕ)) * x))

def theta_base (theta : ℝ -> ℝ) (u : ℤ × ℝ -> ℝ) : Prop :=
  (∀ x : ℝ, 0 < x -> theta x = tsum (fun n : ℤ => thetaTerm n x)) ∧
  (∀ n : ℤ, ∀ x : ℝ, 0 < x -> u (n, x) = thetaTerm n x)

def thetaDefinedAt (theta : ℝ -> ℝ) (x : ℝ) : Prop :=
  0 < x ∧ Summable (fun n : ℤ => thetaTerm n x) ∧ theta x = tsum (fun n : ℤ => thetaTerm n x)

def thetaDefinedOn (theta : ℝ -> ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, thetaDefinedAt theta x

noncomputable def thetaDeriv (theta : ℝ -> ℝ) (k : ℕ) : ℝ -> ℝ :=
  iteratedDeriv k theta

theorem proof_gap_exercise_2798_1 (theta : ℝ -> ℝ) (u : ℤ × ℝ -> ℝ)
  (hbase : theta_base theta u) :
  ∀ n : ℕ, 0 < n -> ∀ x : ℝ, 0 < x -> u (-(n : ℤ), x) = u ((n : ℤ), x) := by
  sorry

theorem proof_gap_exercise_2798_2 (theta : ℝ -> ℝ) (u : ℤ × ℝ -> ℝ)
  (hbase : theta_base theta u)
  (h1 : ∀ n : ℕ, 0 < n -> ∀ x : ℝ, 0 < x -> u (-(n : ℤ), x) = u ((n : ℤ), x)) :
  ∀ n : ℕ, 0 < n -> ∀ x : ℝ, 0 < x ->
    theta x = 1 + 2 * tsum (fun m : ℕ => thetaPosTerm (m + 1) x) := by
  sorry

theorem proof_gap_exercise_2798_3 (theta : ℝ -> ℝ) (u : ℤ × ℝ -> ℝ)
  (hbase : theta_base theta u) :
  ∀ n : ℕ, 0 < n -> ∀ x : ℝ, 0 < x -> 0 < Real.exp (-((n : ℝ) ^ (2 : ℕ) * x)) := by
  sorry

theorem proof_gap_exercise_2798_4 (theta : ℝ -> ℝ) (u : ℤ × ℝ -> ℝ)
  (hbase : theta_base theta u) :
  ∀ n : ℕ, 0 < n -> ∀ x : ℝ, 0 < x -> Real.exp (-((n : ℝ) ^ (2 : ℕ) * x)) < 1 /. (((n : ℝ) ^ (2 : ℕ)) * x) := by
  sorry

theorem proof_gap_exercise_2798_5 (theta : ℝ -> ℝ) (u : ℤ × ℝ -> ℝ)
  (hbase : theta_base theta u) :
  ∀ n : ℕ, 0 < n -> ∀ x : ℝ, 0 < x -> 0 < 1 /. (((n : ℝ) ^ (2 : ℕ)) * x) := by
  sorry

theorem proof_gap_exercise_2798_6 (theta : ℝ -> ℝ) (u : ℤ × ℝ -> ℝ)
  (hbase : theta_base theta u) :
  ∀ x : ℝ, 0 < x -> Summable (fun n : ℕ => 1 /. ((((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * x)) := by
  sorry

theorem proof_gap_exercise_2798_7 (theta : ℝ -> ℝ) (u : ℤ × ℝ -> ℝ)
  (hbase : theta_base theta u) :
  ∀ x : ℝ, 0 < x -> Summable (fun n : ℕ => thetaPosTerm (n + 1) x) := by
  sorry

theorem proof_gap_exercise_2798_8 (theta : ℝ -> ℝ) (u : ℤ × ℝ -> ℝ)
  (hbase : theta_base theta u) :
  ∀ x : ℝ, 0 < x -> thetaDefinedAt theta x := by
  sorry

theorem proof_gap_exercise_2798_9 (theta : ℝ -> ℝ) (u : ℤ × ℝ -> ℝ)
  (hbase : theta_base theta u) :
  ∀ ε : ℝ, 0 < ε -> ∀ x : ℝ, ε ≤ x -> ∀ n : ℕ, 0 < n -> 0 < thetaDeriTerm n x := by
  sorry

theorem proof_gap_exercise_2798_10 (theta : ℝ -> ℝ) (u : ℤ × ℝ -> ℝ)
  (hbase : theta_base theta u) :
  ∀ ε : ℝ, 0 < ε -> ∀ x : ℝ, ε ≤ x -> ∀ n : ℕ, 0 < n -> thetaDeriTerm n x ≤ thetaDeriTerm n ε := by
  sorry

theorem proof_gap_exercise_2798_11 (theta : ℝ -> ℝ) (u : ℤ × ℝ -> ℝ)
  (hbase : theta_base theta u) :
  ∀ ε : ℝ, 0 < ε -> ∀ x : ℝ, ε ≤ x -> ∀ n : ℕ, 0 < n -> thetaDeriTerm n ε < 1 /. (((n : ℝ) ^ (2 : ℕ)) * ε) := by
  sorry

theorem proof_gap_exercise_2798_12 (theta : ℝ -> ℝ) (u : ℤ × ℝ -> ℝ)
  (hbase : theta_base theta u) :
  ∀ ε : ℝ, 0 < ε -> ∀ x : ℝ, ε ≤ x -> ∀ n : ℕ, 0 < n -> 0 < 1 /. (((n : ℝ) ^ (2 : ℕ)) * ε) := by
  sorry

theorem proof_gap_exercise_2798_13 (theta : ℝ -> ℝ) (u : ℤ × ℝ -> ℝ)
  (hbase : theta_base theta u) :
  ∀ ε : ℝ, 0 < ε -> Summable (fun n : ℕ => 1 /. ((((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * ε)) := by
  sorry

theorem proof_gap_exercise_2798_14 (theta : ℝ -> ℝ) (u : ℤ × ℝ -> ℝ)
  (hbase : theta_base theta u) :
  ∀ ε : ℝ, 0 < ε ->
    TendstoUniformlyOn (fun n x => thetaDeriTerm (n + 1) x)
      (fun x => tsum (fun n : ℕ => thetaDeriTerm (n + 1) x)) atTop (Set.Ici ε) := by
  sorry

theorem proof_gap_exercise_2798_15 (theta : ℝ -> ℝ) (u : ℤ × ℝ -> ℝ)
  (hbase : theta_base theta u) :
  ∀ ε : ℝ, 0 < ε -> ∀ n : ℕ, 0 < n -> ContinuousOn (fun x : ℝ => thetaDeriTerm n x) (Set.Ici ε) := by
  sorry

theorem proof_gap_exercise_2798_16 (theta : ℝ -> ℝ) (u : ℤ × ℝ -> ℝ)
  (hbase : theta_base theta u) :
  ∀ ε : ℝ, 0 < ε -> ContDiffOn ℝ 1 theta (Set.Ici ε) := by
  sorry

theorem proof_gap_exercise_2798_17 (theta : ℝ -> ℝ) (u : ℤ × ℝ -> ℝ)
  (hbase : theta_base theta u) :
  ∀ ε : ℝ, 0 < ε -> ∀ x : ℝ, x ∈ Set.Ici ε ->
    deriv theta x = -(tsum (fun n : ℤ => Real.pi * ((n : ℝ) ^ (2 : ℕ)) * thetaTerm n x)) := by
  sorry

theorem proof_gap_exercise_2798_18 (theta : ℝ -> ℝ) (u : ℤ × ℝ -> ℝ)
  (hbase : theta_base theta u) :
  ContDiffOn ℝ 1 theta (Set.Ioi 0) := by
  sorry

theorem proof_gap_exercise_2798_19 (theta : ℝ -> ℝ) (u : ℤ × ℝ -> ℝ)
  (hbase : theta_base theta u) :
  ∀ k : ℕ, 0 < k -> ∀ ε : ℝ, 0 < ε -> ∀ x : ℝ, x ∈ Set.Ici ε -> ∀ n : ℕ, 0 < n ->
    0 < thetaHigherTerm k n x := by
  sorry

theorem proof_gap_exercise_2798_20 (theta : ℝ -> ℝ) (u : ℤ × ℝ -> ℝ)
  (hbase : theta_base theta u) :
  ∀ k : ℕ, 0 < k -> ∀ ε : ℝ, 0 < ε -> ∀ x : ℝ, x ∈ Set.Ici ε -> ∀ n : ℕ, 0 < n ->
    thetaHigherTerm k n x < 1 /. (((n : ℝ) ^ (2 : ℕ)) * ε) := by
  sorry

theorem proof_gap_exercise_2798_21 (theta : ℝ -> ℝ) (u : ℤ × ℝ -> ℝ)
  (hbase : theta_base theta u) :
  ∀ k : ℕ, 0 < k -> ∀ ε : ℝ, 0 < ε -> ∀ x : ℝ, x ∈ Set.Ici ε -> ∀ n : ℕ, 0 < n ->
    0 < 1 /. (((n : ℝ) ^ (2 : ℕ)) * ε) := by
  sorry

theorem proof_gap_exercise_2798_22 (theta : ℝ -> ℝ) (u : ℤ × ℝ -> ℝ)
  (hbase : theta_base theta u) :
  ∀ k : ℕ, 0 < k -> ∀ ε : ℝ, 0 < ε ->
    TendstoUniformlyOn (fun n x => thetaHigherTerm k (n + 1) x)
      (fun x => tsum (fun n : ℕ => thetaHigherTerm k (n + 1) x)) atTop (Set.Ici ε) := by
  sorry

theorem proof_gap_exercise_2798_23 (theta : ℝ -> ℝ) (u : ℤ × ℝ -> ℝ)
  (hbase : theta_base theta u) :
  ∀ k : ℕ, 0 < k -> DifferentiableOn ℝ (thetaDeriv theta k) (Set.Ioi 0) := by
  sorry

theorem proof_gap_exercise_2798_24 (theta : ℝ -> ℝ) (u : ℤ × ℝ -> ℝ)
  (hbase : theta_base theta u) :
  ∀ k : ℕ, 0 < k -> ContinuousOn (thetaDeriv theta k) (Set.Ioi 0) := by
  sorry

theorem proof_gap_exercise_2798_25 (theta : ℝ -> ℝ) (u : ℤ × ℝ -> ℝ)
  (hbase : theta_base theta u) :
  ContDiffOn ℝ ⊤ theta (Set.Ioi 0) := by
  sorry

theorem proof_gap_exercise_2798_26 (theta : ℝ -> ℝ) (u : ℤ × ℝ -> ℝ)
  (hbase : theta_base theta u) :
  thetaDefinedOn theta (Set.Ioi 0) ∧ ContDiffOn ℝ ⊤ theta (Set.Ioi 0) := by
  sorry
