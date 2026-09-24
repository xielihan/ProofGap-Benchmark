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

-- exercise: exercise_1601

theorem proof_gap_exercise_1601_1
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (R : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((x t) = (a * (t - (Real.sin t)))))))
  (h4 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((y t) = (a * (1 - (Real.cos t)))))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((lpFunDeri y x) t) = ((a * (Real.sin t)) /. (a * (1 - (Real.cos t))))))) := by
  sorry

theorem proof_gap_exercise_1601_2
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (R : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((x t) = (a * (t - (Real.sin t)))))))
  (h4 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((y t) = (a * (1 - (Real.cos t)))))))
  (h5 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((lpFunDeri y x) t) = ((a * (Real.sin t)) /. (a * (1 - (Real.cos t))))))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((a * (Real.sin t)) /. (a * (1 - (Real.cos t)))) = ((1 : ℝ) /. (Real.tan (t /. 2)))))) := by
  sorry

theorem proof_gap_exercise_1601_3
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (R : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((x t) = (a * (t - (Real.sin t)))))))
  (h4 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((y t) = (a * (1 - (Real.cos t)))))))
  (h5 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((lpFunDeri y x) t) = ((a * (Real.sin t)) /. (a * (1 - (Real.cos t))))))))
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((a * (Real.sin t)) /. (a * (1 - (Real.cos t)))) = ((1 : ℝ) /. (Real.tan (t /. 2)))))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((lpFunDeri y x) t) = ((1 : ℝ) /. (Real.tan (t /. 2)))))) := by
  sorry

theorem proof_gap_exercise_1601_4
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (R : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((x t) = (a * (t - (Real.sin t)))))))
  (h4 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((y t) = (a * (1 - (Real.cos t)))))))
  (h5 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((lpFunDeri y x) t) = ((a * (Real.sin t)) /. (a * (1 - (Real.cos t))))))))
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((a * (Real.sin t)) /. (a * (1 - (Real.cos t)))) = ((1 : ℝ) /. (Real.tan (t /. 2)))))))
  (h7 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((lpFunDeri y x) t) = ((1 : ℝ) /. (Real.tan (t /. 2)))))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((lpFunDeri (lpFunDeri y x) x) t) = ((-(1 /. (2 * ((Real.sin (t /. 2)) ^ (2 : ℕ))))) /. (a * (1 - (Real.cos t))))))) := by
  sorry

theorem proof_gap_exercise_1601_5
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (R : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((x t) = (a * (t - (Real.sin t)))))))
  (h4 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((y t) = (a * (1 - (Real.cos t)))))))
  (h5 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((lpFunDeri y x) t) = ((a * (Real.sin t)) /. (a * (1 - (Real.cos t))))))))
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((a * (Real.sin t)) /. (a * (1 - (Real.cos t)))) = ((1 : ℝ) /. (Real.tan (t /. 2)))))))
  (h7 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((lpFunDeri y x) t) = ((1 : ℝ) /. (Real.tan (t /. 2)))))))
  (h8 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((lpFunDeri (lpFunDeri y x) x) t) = ((-(1 /. (2 * ((Real.sin (t /. 2)) ^ (2 : ℕ))))) /. (a * (1 - (Real.cos t))))))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((-(1 /. (2 * ((Real.sin (t /. 2)) ^ (2 : ℕ))))) /. (a * (1 - (Real.cos t)))) = (-(1 /. ((4 * a) * ((Real.sin (t /. 2)) ^ (4 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_1601_6
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (R : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((x t) = (a * (t - (Real.sin t)))))))
  (h4 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((y t) = (a * (1 - (Real.cos t)))))))
  (h5 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((lpFunDeri y x) t) = ((a * (Real.sin t)) /. (a * (1 - (Real.cos t))))))))
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((a * (Real.sin t)) /. (a * (1 - (Real.cos t)))) = ((1 : ℝ) /. (Real.tan (t /. 2)))))))
  (h7 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((lpFunDeri y x) t) = ((1 : ℝ) /. (Real.tan (t /. 2)))))))
  (h8 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((lpFunDeri (lpFunDeri y x) x) t) = ((-(1 /. (2 * ((Real.sin (t /. 2)) ^ (2 : ℕ))))) /. (a * (1 - (Real.cos t))))))))
  (h9 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((-(1 /. (2 * ((Real.sin (t /. 2)) ^ (2 : ℕ))))) /. (a * (1 - (Real.cos t)))) = (-(1 /. ((4 * a) * ((Real.sin (t /. 2)) ^ (4 : ℕ)))))))))
  : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((lpFunDeri (lpFunDeri y x) x) t) = (-(1 /. ((4 * a) * ((Real.sin (t /. 2)) ^ (4 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_1601_7
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (R : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((x t) = (a * (t - (Real.sin t)))))))
  (h4 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((y t) = (a * (1 - (Real.cos t)))))))
  (h5 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((lpFunDeri y x) t) = ((a * (Real.sin t)) /. (a * (1 - (Real.cos t))))))))
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((a * (Real.sin t)) /. (a * (1 - (Real.cos t)))) = ((1 : ℝ) /. (Real.tan (t /. 2)))))))
  (h7 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((lpFunDeri y x) t) = ((1 : ℝ) /. (Real.tan (t /. 2)))))))
  (h8 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((lpFunDeri (lpFunDeri y x) x) t) = ((-(1 /. (2 * ((Real.sin (t /. 2)) ^ (2 : ℕ))))) /. (a * (1 - (Real.cos t))))))))
  (h9 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((-(1 /. (2 * ((Real.sin (t /. 2)) ^ (2 : ℕ))))) /. (a * (1 - (Real.cos t)))) = (-(1 /. ((4 * a) * ((Real.sin (t /. 2)) ^ (4 : ℕ)))))))))
  (h10 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((lpFunDeri (lpFunDeri y x) x) t) = (-(1 /. ((4 * a) * ((Real.sin (t /. 2)) ^ (4 : ℕ)))))))))
  : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((R t) = ((Real.rpow (1 + (((1 : ℝ) /. (Real.tan (t /. 2))) ^ (2 : ℕ))) (3 /. 2)) /. (1 /. ((4 * a) * ((Real.sin (t /. 2)) ^ (4 : ℕ)))))))) := by
  sorry

theorem proof_gap_exercise_1601_8
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (R : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((x t) = (a * (t - (Real.sin t)))))))
  (h4 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((y t) = (a * (1 - (Real.cos t)))))))
  (h5 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((lpFunDeri y x) t) = ((a * (Real.sin t)) /. (a * (1 - (Real.cos t))))))))
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((a * (Real.sin t)) /. (a * (1 - (Real.cos t)))) = ((1 : ℝ) /. (Real.tan (t /. 2)))))))
  (h7 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((lpFunDeri y x) t) = ((1 : ℝ) /. (Real.tan (t /. 2)))))))
  (h8 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((lpFunDeri (lpFunDeri y x) x) t) = ((-(1 /. (2 * ((Real.sin (t /. 2)) ^ (2 : ℕ))))) /. (a * (1 - (Real.cos t))))))))
  (h9 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((-(1 /. (2 * ((Real.sin (t /. 2)) ^ (2 : ℕ))))) /. (a * (1 - (Real.cos t)))) = (-(1 /. ((4 * a) * ((Real.sin (t /. 2)) ^ (4 : ℕ)))))))))
  (h10 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((lpFunDeri (lpFunDeri y x) x) t) = (-(1 /. ((4 * a) * ((Real.sin (t /. 2)) ^ (4 : ℕ)))))))))
  (h11 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((R t) = ((Real.rpow (1 + (((1 : ℝ) /. (Real.tan (t /. 2))) ^ (2 : ℕ))) (3 /. 2)) /. (1 /. ((4 * a) * ((Real.sin (t /. 2)) ^ (4 : ℕ)))))))))
  : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((R t) = ((4 * a) * |((Real.sin (t /. 2)))|)))) := by
  sorry

theorem proof_gap_exercise_1601_9
  (x : (ℝ -> ℝ))
  (y : (ℝ -> ℝ))
  (R : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((x t) = (a * (t - (Real.sin t)))))))
  (h4 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((y t) = (a * (1 - (Real.cos t)))))))
  (h5 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((lpFunDeri y x) t) = ((a * (Real.sin t)) /. (a * (1 - (Real.cos t))))))))
  (h6 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((a * (Real.sin t)) /. (a * (1 - (Real.cos t)))) = ((1 : ℝ) /. (Real.tan (t /. 2)))))))
  (h7 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((lpFunDeri y x) t) = ((1 : ℝ) /. (Real.tan (t /. 2)))))))
  (h8 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((lpFunDeri (lpFunDeri y x) x) t) = ((-(1 /. (2 * ((Real.sin (t /. 2)) ^ (2 : ℕ))))) /. (a * (1 - (Real.cos t))))))))
  (h9 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((-(1 /. (2 * ((Real.sin (t /. 2)) ^ (2 : ℕ))))) /. (a * (1 - (Real.cos t)))) = (-(1 /. ((4 * a) * ((Real.sin (t /. 2)) ^ (4 : ℕ)))))))))
  (h10 : (forall (t : ℝ), (((t ∈ (Set.univ : Set ℝ)) ∧ ((1 - (Real.cos t)) ≠ 0)) → (((lpFunDeri (lpFunDeri y x) x) t) = (-(1 /. ((4 * a) * ((Real.sin (t /. 2)) ^ (4 : ℕ)))))))))
  (h11 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((R t) = ((Real.rpow (1 + (((1 : ℝ) /. (Real.tan (t /. 2))) ^ (2 : ℕ))) (3 /. 2)) /. (1 /. ((4 * a) * ((Real.sin (t /. 2)) ^ (4 : ℕ)))))))))
  (h12 : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((R t) = ((4 * a) * |((Real.sin (t /. 2)))|)))))
  : (forall (t : ℝ), ((t ∈ (Set.univ : Set ℝ)) → ((R t) = (2 * (Real.rpow ((2 * a) * (y t)) (((2 : ℝ))⁻¹)))))) := by
  sorry
