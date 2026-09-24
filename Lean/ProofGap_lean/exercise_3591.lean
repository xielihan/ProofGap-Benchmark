import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat

open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

open scoped RealInnerProductSpace

noncomputable def lpFunDeri {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (f g : E -> ℝ) : E -> ℝ :=
  fun x => (inner ℝ (gradient f x) (gradient g x)) /. (‖gradient g x‖ ^ 2)

def lpLeftDifferentiable (f : ℝ -> ℝ) : Prop :=
  ∀ x, DifferentiableWithinAt ℝ f (Set.Iio x) x

def lpRightDifferentiable (f : ℝ -> ℝ) : Prop :=
  ∀ x, DifferentiableWithinAt ℝ f (Set.Ioi x) x

def lpLeftDifferentiableOn (f : ℝ -> ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, DifferentiableWithinAt ℝ f (s ∩ Set.Iio x) x

def lpRightDifferentiableOn (f : ℝ -> ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, DifferentiableWithinAt ℝ f (s ∩ Set.Ioi x) x

def lpMaximumPoints {α β : Type*} [Preorder β] (f : α -> β) : Set α :=
  {x | ∀ y, f y ≤ f x}

def lpMinimumPoints {α β : Type*} [Preorder β] (f : α -> β) : Set α :=
  {x | ∀ y, f x ≤ f y}

def lpMaximumPointsOn {α β : Type*} [Preorder β] (f : α -> β) (s : Set α) : Set α :=
  {x | x ∈ s ∧ ∀ y ∈ s, f y ≤ f x}

def lpMinimumPointsOn {α β : Type*} [Preorder β] (f : α -> β) (s : Set α) : Set α :=
  {x | x ∈ s ∧ ∀ y ∈ s, f x ≤ f y}

noncomputable def lpRadiusOfConvergence {𝕜 : Type*} [NormedField 𝕜] (a : ℕ -> 𝕜) : ENNReal :=
  ⨆ (r : NNReal), ⨆ (_h : Summable (fun n : ℕ => ‖a n‖ * (r : ℝ) ^ n)), (r : ENNReal)

-- exercise: exercise_3591

theorem proof_gap_exercise_3591_1
  (f : (ℝ × ℝ -> ℝ))
  (Delta : (ℝ × ℝ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h : ℝ)
  (k : ℝ)
  (h1 : U ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : y ∈ (Set.univ : Set ℝ))
  (h4 : h ∈ (Set.univ : Set ℝ))
  (h5 : k ∈ (Set.univ : Set ℝ))
  (h6 : (x, y) ∈ U)
  (h7 : ((x + h), y) ∈ U)
  (h8 : (x, (y + k)) ∈ U)
  (h9 : ((x + h), (y + k)) ∈ U)
  (h10 : (forall (a : ℝ) (b : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (b ∈ (Set.univ : Set ℝ))) ∧ ((a, b) ∈ U)) → ((Delta (a, b)) = ((((f ((a + h), (b + k))) - (f ((a + h), b))) - (f (a, (b + k)))) + (f (a, b)))))))
  : (f ((x + h), (y + k))) = ((((f (x, y)) + (h * (iteratedDeriv 1 (fun t => f (t, y)) x))) + (k * (iteratedDeriv 1 (fun t => f (x, t)) y))) + (∑' n, if (2 : ℕ) ≤ n then (∑ m ∈ Finset.Icc (0 : ℕ) n, ((((h ^ m) * (k ^ (n - m))) /. ((m)! * ((n - m))!)) * (iteratedDeriv (n - m) (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv m (fun t => f (t, p.2)) p.1)) (x, t)) y))) else 0)) := by
  sorry

theorem proof_gap_exercise_3591_2
  (f : (ℝ × ℝ -> ℝ))
  (Delta : (ℝ × ℝ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h : ℝ)
  (k : ℝ)
  (h1 : U ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : y ∈ (Set.univ : Set ℝ))
  (h4 : h ∈ (Set.univ : Set ℝ))
  (h5 : k ∈ (Set.univ : Set ℝ))
  (h6 : (x, y) ∈ U)
  (h7 : ((x + h), y) ∈ U)
  (h8 : (x, (y + k)) ∈ U)
  (h9 : ((x + h), (y + k)) ∈ U)
  (h10 : (forall (a : ℝ) (b : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (b ∈ (Set.univ : Set ℝ))) ∧ ((a, b) ∈ U)) → ((Delta (a, b)) = ((((f ((a + h), (b + k))) - (f ((a + h), b))) - (f (a, (b + k)))) + (f (a, b)))))))
  (h11 : (f ((x + h), (y + k))) = ((((f (x, y)) + (h * (iteratedDeriv 1 (fun t => f (t, y)) x))) + (k * (iteratedDeriv 1 (fun t => f (x, t)) y))) + (∑' n, if (2 : ℕ) ≤ n then (∑ m ∈ Finset.Icc (0 : ℕ) n, ((((h ^ m) * (k ^ (n - m))) /. ((m)! * ((n - m))!)) * (iteratedDeriv (n - m) (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv m (fun t => f (t, p.2)) p.1)) (x, t)) y))) else 0)))
  : (f ((x + h), y)) = ((f (x, y)) + (∑' n, if (1 : ℕ) ≤ n then (((h ^ n) /. (n)!) * (iteratedDeriv n (fun t => f (t, y)) x)) else 0)) := by
  sorry

theorem proof_gap_exercise_3591_3
  (f : (ℝ × ℝ -> ℝ))
  (Delta : (ℝ × ℝ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h : ℝ)
  (k : ℝ)
  (h1 : U ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : y ∈ (Set.univ : Set ℝ))
  (h4 : h ∈ (Set.univ : Set ℝ))
  (h5 : k ∈ (Set.univ : Set ℝ))
  (h6 : (x, y) ∈ U)
  (h7 : ((x + h), y) ∈ U)
  (h8 : (x, (y + k)) ∈ U)
  (h9 : ((x + h), (y + k)) ∈ U)
  (h10 : (forall (a : ℝ) (b : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (b ∈ (Set.univ : Set ℝ))) ∧ ((a, b) ∈ U)) → ((Delta (a, b)) = ((((f ((a + h), (b + k))) - (f ((a + h), b))) - (f (a, (b + k)))) + (f (a, b)))))))
  (h11 : (f ((x + h), (y + k))) = ((((f (x, y)) + (h * (iteratedDeriv 1 (fun t => f (t, y)) x))) + (k * (iteratedDeriv 1 (fun t => f (x, t)) y))) + (∑' n, if (2 : ℕ) ≤ n then (∑ m ∈ Finset.Icc (0 : ℕ) n, ((((h ^ m) * (k ^ (n - m))) /. ((m)! * ((n - m))!)) * (iteratedDeriv (n - m) (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv m (fun t => f (t, p.2)) p.1)) (x, t)) y))) else 0)))
  (h12 : (f ((x + h), y)) = ((f (x, y)) + (∑' n, if (1 : ℕ) ≤ n then (((h ^ n) /. (n)!) * (iteratedDeriv n (fun t => f (t, y)) x)) else 0)))
  : (f (x, (y + k))) = ((f (x, y)) + (∑' n, if (1 : ℕ) ≤ n then (((k ^ n) /. (n)!) * (iteratedDeriv n (fun t => f (x, t)) y)) else 0)) := by
  sorry

theorem proof_gap_exercise_3591_4
  (f : (ℝ × ℝ -> ℝ))
  (Delta : (ℝ × ℝ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h : ℝ)
  (k : ℝ)
  (h1 : U ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : y ∈ (Set.univ : Set ℝ))
  (h4 : h ∈ (Set.univ : Set ℝ))
  (h5 : k ∈ (Set.univ : Set ℝ))
  (h6 : (x, y) ∈ U)
  (h7 : ((x + h), y) ∈ U)
  (h8 : (x, (y + k)) ∈ U)
  (h9 : ((x + h), (y + k)) ∈ U)
  (h10 : (forall (a : ℝ) (b : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (b ∈ (Set.univ : Set ℝ))) ∧ ((a, b) ∈ U)) → ((Delta (a, b)) = ((((f ((a + h), (b + k))) - (f ((a + h), b))) - (f (a, (b + k)))) + (f (a, b)))))))
  (h11 : (f ((x + h), (y + k))) = ((((f (x, y)) + (h * (iteratedDeriv 1 (fun t => f (t, y)) x))) + (k * (iteratedDeriv 1 (fun t => f (x, t)) y))) + (∑' n, if (2 : ℕ) ≤ n then (∑ m ∈ Finset.Icc (0 : ℕ) n, ((((h ^ m) * (k ^ (n - m))) /. ((m)! * ((n - m))!)) * (iteratedDeriv (n - m) (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv m (fun t => f (t, p.2)) p.1)) (x, t)) y))) else 0)))
  (h12 : (f ((x + h), y)) = ((f (x, y)) + (∑' n, if (1 : ℕ) ≤ n then (((h ^ n) /. (n)!) * (iteratedDeriv n (fun t => f (t, y)) x)) else 0)))
  (h13 : (f (x, (y + k))) = ((f (x, y)) + (∑' n, if (1 : ℕ) ≤ n then (((k ^ n) /. (n)!) * (iteratedDeriv n (fun t => f (x, t)) y)) else 0)))
  : (Delta (x, y)) = (∑' n, if (2 : ℕ) ≤ n then (∑ m ∈ Finset.Icc (1 : ℕ) (n - 1), ((((h ^ m) * (k ^ (n - m))) /. ((m)! * ((n - m))!)) * (iteratedDeriv (n - m) (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv m (fun t => f (t, p.2)) p.1)) (x, t)) y))) else 0) := by
  sorry

theorem proof_gap_exercise_3591_5
  (f : (ℝ × ℝ -> ℝ))
  (Delta : (ℝ × ℝ -> ℝ))
  (x : ℝ)
  (y : ℝ)
  (h : ℝ)
  (k : ℝ)
  (h1 : U ⊆ ((Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ)))
  (h2 : x ∈ (Set.univ : Set ℝ))
  (h3 : y ∈ (Set.univ : Set ℝ))
  (h4 : h ∈ (Set.univ : Set ℝ))
  (h5 : k ∈ (Set.univ : Set ℝ))
  (h6 : (x, y) ∈ U)
  (h7 : ((x + h), y) ∈ U)
  (h8 : (x, (y + k)) ∈ U)
  (h9 : ((x + h), (y + k)) ∈ U)
  (h10 : (forall (a : ℝ) (b : ℝ), ((((a ∈ (Set.univ : Set ℝ)) ∧ (b ∈ (Set.univ : Set ℝ))) ∧ ((a, b) ∈ U)) → ((Delta (a, b)) = ((((f ((a + h), (b + k))) - (f ((a + h), b))) - (f (a, (b + k)))) + (f (a, b)))))))
  (h11 : (f ((x + h), (y + k))) = ((((f (x, y)) + (h * (iteratedDeriv 1 (fun t => f (t, y)) x))) + (k * (iteratedDeriv 1 (fun t => f (x, t)) y))) + (∑' n, if (2 : ℕ) ≤ n then (∑ m ∈ Finset.Icc (0 : ℕ) n, ((((h ^ m) * (k ^ (n - m))) /. ((m)! * ((n - m))!)) * (iteratedDeriv (n - m) (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv m (fun t => f (t, p.2)) p.1)) (x, t)) y))) else 0)))
  (h12 : (f ((x + h), y)) = ((f (x, y)) + (∑' n, if (1 : ℕ) ≤ n then (((h ^ n) /. (n)!) * (iteratedDeriv n (fun t => f (t, y)) x)) else 0)))
  (h13 : (f (x, (y + k))) = ((f (x, y)) + (∑' n, if (1 : ℕ) ≤ n then (((k ^ n) /. (n)!) * (iteratedDeriv n (fun t => f (x, t)) y)) else 0)))
  (h14 : (Delta (x, y)) = (∑' n, if (2 : ℕ) ≤ n then (∑ m ∈ Finset.Icc (1 : ℕ) (n - 1), ((((h ^ m) * (k ^ (n - m))) /. ((m)! * ((n - m))!)) * (iteratedDeriv (n - m) (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv m (fun t => f (t, p.2)) p.1)) (x, t)) y))) else 0))
  : (Delta (x, y)) = ((h * k) * ((iteratedDeriv 1 (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv 1 (fun t => f (t, p.2)) p.1)) (x, t)) y) + (∑' n, if (3 : ℕ) ≤ n then (∑ m ∈ Finset.Icc (1 : ℕ) (n - 1), ((((h ^ (m - 1)) * (k ^ ((n - m) - 1))) /. ((m)! * ((n - m))!)) * (iteratedDeriv (n - m) (fun t => (fun (p : ℝ × ℝ) => (iteratedDeriv m (fun t => f (t, p.2)) p.1)) (x, t)) y))) else 0))) := by
  sorry
