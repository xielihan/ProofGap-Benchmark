import Mathlib

open scoped Topology
open Filter

theorem proof_gap_exercise_2751_3_1
  (f : ℕ × ℝ -> ℝ) (g : ℝ -> ℝ) (eps : ℝ)
  (h1 : eps ∈ (Set.univ : Set ℝ)) (h2 : eps ∈ {x : ℝ | 0 < x})
  (h3 : forall (x : ℝ) (n : ℕ), (((x ∈ (Set.univ : Set ℝ)) ∧ (n ∈ (Set.univ : Set ℕ))) ∧ (n ∈ {n : ℕ | 0 < n}) ∧ (x ≥ 1 + eps)) → f (n, x) = (x ^ n) / (1 + x ^ n))
  (h4 : forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 1 + eps)) → g x = 1)
  : forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 1 + eps)) → Tendsto (fun n : ℕ => f (n, x)) atTop (𝓝 1) := by
  sorry

theorem proof_gap_exercise_2751_3_2
  (f : ℕ × ℝ -> ℝ) (g : ℝ -> ℝ) (eps : ℝ)
  (h1 : eps ∈ (Set.univ : Set ℝ)) (h2 : eps ∈ {x : ℝ | 0 < x})
  (h3 : forall (x : ℝ) (n : ℕ), (((x ∈ (Set.univ : Set ℝ)) ∧ (n ∈ (Set.univ : Set ℕ))) ∧ (n ∈ {n : ℕ | 0 < n}) ∧ (x ≥ 1 + eps)) → f (n, x) = (x ^ n) / (1 + x ^ n))
  (h4 : forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 1 + eps)) → g x = 1)
  (h5 : forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 1 + eps)) → Tendsto (fun n : ℕ => f (n, x)) atTop (𝓝 1))
  : forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 1 + eps)) → g x = 1 := by
  sorry

theorem proof_gap_exercise_2751_3_3
  (f : ℕ × ℝ -> ℝ) (g : ℝ -> ℝ) (eps : ℝ)
  (h1 : eps ∈ (Set.univ : Set ℝ)) (h2 : eps ∈ {x : ℝ | 0 < x})
  (h3 : forall (x : ℝ) (n : ℕ), (((x ∈ (Set.univ : Set ℝ)) ∧ (n ∈ (Set.univ : Set ℕ))) ∧ (n ∈ {n : ℕ | 0 < n}) ∧ (x ≥ 1 + eps)) → f (n, x) = (x ^ n) / (1 + x ^ n))
  (h4 h6 : forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 1 + eps)) → g x = 1)
  (h5 : forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 1 + eps)) → Tendsto (fun n : ℕ => f (n, x)) atTop (𝓝 1))
  : forall (n : ℕ) (x : ℝ), (((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ {n : ℕ | 0 < n}) ∧ (x ≥ 1 + eps)) → |f (n, x) - g x| = 1 / (1 + x ^ n) := by
  sorry

theorem proof_gap_exercise_2751_3_4
  (f : ℕ × ℝ -> ℝ) (g : ℝ -> ℝ) (eps : ℝ)
  (h1 : eps ∈ (Set.univ : Set ℝ)) (h2 : eps ∈ {x : ℝ | 0 < x})
  : forall (x : ℝ) (n : ℕ), (((x ∈ (Set.univ : Set ℝ)) ∧ (n ∈ (Set.univ : Set ℕ))) ∧ (x ≥ 1 + eps) ∧ (n ∈ {n : ℕ | 0 < n})) → 1 / (1 + x ^ n) < 1 / ((1 + eps) ^ n) := by
  sorry

theorem proof_gap_exercise_2751_3_5
  (f : ℕ × ℝ -> ℝ) (g : ℝ -> ℝ) (eps : ℝ)
  (h1 : forall (n : ℕ) (x : ℝ), (((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ {n : ℕ | 0 < n}) ∧ (x ≥ 1 + eps)) → |f (n, x) - g x| = 1 / (1 + x ^ n))
  (h2 : forall (x : ℝ) (n : ℕ), (((x ∈ (Set.univ : Set ℝ)) ∧ (n ∈ (Set.univ : Set ℕ))) ∧ (x ≥ 1 + eps) ∧ (n ∈ {n : ℕ | 0 < n})) → 1 / (1 + x ^ n) < 1 / ((1 + eps) ^ n))
  : forall (n : ℕ) (x : ℝ), (((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ {n : ℕ | 0 < n}) ∧ (x ≥ 1 + eps)) → |f (n, x) - g x| < 1 / ((1 + eps) ^ n) := by
  sorry

theorem proof_gap_exercise_2751_3_6
  (f : ℕ × ℝ -> ℝ) (g : ℝ -> ℝ) (eps : ℝ)
  (h1 : forall (n : ℕ) (x : ℝ), (((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ {n : ℕ | 0 < n}) ∧ (x ≥ 1 + eps)) → |f (n, x) - g x| < 1 / ((1 + eps) ^ n))
  : forall (n : ℕ) (x : ℝ), (((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ {n : ℕ | 0 < n}) ∧ (x ≥ 1 + eps)) → forall (eps' : ℝ), (((eps' ∈ (Set.univ : Set ℝ)) ∧ eps' > 0) ∧ 1 / ((1 + eps) ^ n) < eps') → |f (n, x) - g x| < eps' := by
  sorry

theorem proof_gap_exercise_2751_3_7
  (eps : ℝ)
  : forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ {n : ℕ | 0 < n})) → forall (eps' : ℝ), (((eps' ∈ (Set.univ : Set ℝ)) ∧ eps' > 0) ∧ (n : ℝ) > (Real.log (1 / eps')) / (Real.log (1 + eps))) → 1 / ((1 + eps) ^ n) < eps' := by
  sorry

theorem proof_gap_exercise_2751_3_8
  (f : ℕ × ℝ -> ℝ) (g : ℝ -> ℝ) (eps : ℝ)
  (h1 : forall (n : ℕ) (x : ℝ), (((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ {n : ℕ | 0 < n}) ∧ (x ≥ 1 + eps)) → forall (eps' : ℝ), (((eps' ∈ (Set.univ : Set ℝ)) ∧ eps' > 0) ∧ 1 / ((1 + eps) ^ n) < eps') → |f (n, x) - g x| < eps')
  (h2 : forall (n : ℕ), ((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ {n : ℕ | 0 < n})) → forall (eps' : ℝ), (((eps' ∈ (Set.univ : Set ℝ)) ∧ eps' > 0) ∧ (n : ℝ) > (Real.log (1 / eps')) / (Real.log (1 + eps))) → 1 / ((1 + eps) ^ n) < eps')
  : forall (n : ℕ) (x : ℝ), (((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ {n : ℕ | 0 < n}) ∧ (x ≥ 1 + eps)) → forall (eps' : ℝ), (((eps' ∈ (Set.univ : Set ℝ)) ∧ eps' > 0) ∧ (n : ℝ) > (Real.log (1 / eps')) / (Real.log (1 + eps))) → |f (n, x) - g x| < eps' := by
  sorry

theorem proof_gap_exercise_2751_3_9
  (eps : ℝ)
  : forall (eps' : ℝ), ((eps' ∈ (Set.univ : Set ℝ)) ∧ eps' > 0) → exists (N : ℕ), (N ∈ (Set.univ : Set ℕ)) ∧ N = Int.toNat ⌊(Real.log (1 / eps')) / (Real.log (1 + eps))⌋ := by
  sorry

theorem proof_gap_exercise_2751_3_10
  (f : ℕ × ℝ -> ℝ) (g : ℝ -> ℝ) (eps : ℝ)
  (h1 : forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) ∧ (x ≥ 1 + eps)) → g x = 1)
  : forall (n : ℕ) (N : ℕ) (x : ℝ), (((n ∈ (Set.univ : Set ℕ)) ∧ (N ∈ (Set.univ : Set ℕ))) ∧ (x ∈ (Set.univ : Set ℝ))) → forall (eps' : ℝ), (((((eps' ∈ (Set.univ : Set ℝ)) ∧ eps' > 0) ∧ n > N) ∧ (n ∈ {n : ℕ | 0 < n})) ∧ x ≥ 1 + eps) → |f (n, x) - g x| = |f (n, x) - 1| := by
  sorry

theorem proof_gap_exercise_2751_3_11
  (f : ℕ × ℝ -> ℝ) (g : ℝ -> ℝ) (eps : ℝ)
  (h1 : forall (n : ℕ) (x : ℝ), (((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ {n : ℕ | 0 < n}) ∧ (x ≥ 1 + eps)) → forall (eps' : ℝ), (((eps' ∈ (Set.univ : Set ℝ)) ∧ eps' > 0) ∧ (n : ℝ) > (Real.log (1 / eps')) / (Real.log (1 + eps))) → |f (n, x) - g x| < eps')
  : forall (n : ℕ) (N : ℕ) (x : ℝ), (((n ∈ (Set.univ : Set ℕ)) ∧ (N ∈ (Set.univ : Set ℕ))) ∧ (x ∈ (Set.univ : Set ℝ))) → forall (eps' : ℝ), (((((eps' ∈ (Set.univ : Set ℝ)) ∧ eps' > 0) ∧ n > N) ∧ (n ∈ {n : ℕ | 0 < n})) ∧ x ≥ 1 + eps) → |f (n, x) - 1| < eps' := by
  sorry

theorem proof_gap_exercise_2751_3_12
  (f : ℕ × ℝ -> ℝ) (g : ℝ -> ℝ) (eps : ℝ)
  (h1 : forall (n : ℕ) (N : ℕ) (x : ℝ), (((n ∈ (Set.univ : Set ℕ)) ∧ (N ∈ (Set.univ : Set ℕ))) ∧ (x ∈ (Set.univ : Set ℝ))) → forall (eps' : ℝ), (((((eps' ∈ (Set.univ : Set ℝ)) ∧ eps' > 0) ∧ n > N) ∧ (n ∈ {n : ℕ | 0 < n})) ∧ x ≥ 1 + eps) → |f (n, x) - g x| = |f (n, x) - 1|)
  (h2 : forall (n : ℕ) (N : ℕ) (x : ℝ), (((n ∈ (Set.univ : Set ℕ)) ∧ (N ∈ (Set.univ : Set ℕ))) ∧ (x ∈ (Set.univ : Set ℝ))) → forall (eps' : ℝ), (((((eps' ∈ (Set.univ : Set ℝ)) ∧ eps' > 0) ∧ n > N) ∧ (n ∈ {n : ℕ | 0 < n})) ∧ x ≥ 1 + eps) → |f (n, x) - 1| < eps')
  : forall (n : ℕ) (N : ℕ) (x : ℝ), (((n ∈ (Set.univ : Set ℕ)) ∧ (N ∈ (Set.univ : Set ℕ))) ∧ (x ∈ (Set.univ : Set ℝ))) → forall (eps' : ℝ), (((((eps' ∈ (Set.univ : Set ℝ)) ∧ eps' > 0) ∧ n > N) ∧ (n ∈ {n : ℕ | 0 < n})) ∧ x ≥ 1 + eps) → |f (n, x) - g x| < eps' := by
  sorry

theorem proof_gap_exercise_2751_3_13
  (f : ℕ × ℝ -> ℝ) (g : ℝ -> ℝ) (eps : ℝ)
  (h1 : forall (eps' : ℝ), ((eps' ∈ (Set.univ : Set ℝ)) ∧ eps' > 0) → exists (N : ℕ), (N ∈ (Set.univ : Set ℕ)) ∧ N = Int.toNat ⌊(Real.log (1 / eps')) / (Real.log (1 + eps))⌋)
  (h2 : forall (n : ℕ) (N : ℕ) (x : ℝ), (((n ∈ (Set.univ : Set ℕ)) ∧ (N ∈ (Set.univ : Set ℕ))) ∧ (x ∈ (Set.univ : Set ℝ))) → forall (eps' : ℝ), (((((eps' ∈ (Set.univ : Set ℝ)) ∧ eps' > 0) ∧ n > N) ∧ (n ∈ {n : ℕ | 0 < n})) ∧ x ≥ 1 + eps) → |f (n, x) - g x| < eps')
  : TendstoUniformlyOn (fun n x => f (n, x)) g Filter.atTop (Set.Ici (1 + eps)) := by
  sorry

theorem proof_gap_exercise_2751_3_14
  (f : ℕ × ℝ -> ℝ) (g : ℝ -> ℝ) (eps : ℝ)
  (h1 : TendstoUniformlyOn (fun n x => f (n, x)) g Filter.atTop (Set.Ici (1 + eps)))
  : TendstoUniformlyOn (fun n x => f (n, x)) g Filter.atTop (Set.Ici (1 + eps)) := by
  sorry
