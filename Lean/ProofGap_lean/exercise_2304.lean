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

-- exercise: exercise_2304

theorem proof_gap_exercise_2304_1
  (F : (ℝ -> ℝ))
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F x_1) = (∫ t in (0 : ℝ)..x_1, ((SignType.sign (Real.sin t) : ℝ) * (1 : ℝ)))))))
  : (forall (a : ℝ), ((a ∈ (Set.univ : Set ℝ)) → (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (a < b)) → (MeasureTheory.IntegrableOn (fun (t : ℝ) => (SignType.sign (Real.sin t) : ℝ)) (Set.Icc a b) MeasureTheory.volume))))) := by
  sorry

theorem proof_gap_exercise_2304_2
  (F : (ℝ -> ℝ))
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F x_1) = (∫ t in (0 : ℝ)..x_1, ((SignType.sign (Real.sin t) : ℝ) * (1 : ℝ)))))))
  (h4 : (forall (a : ℝ), ((a ∈ (Set.univ : Set ℝ)) → (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (a < b)) → (MeasureTheory.IntegrableOn (fun (t : ℝ) => (SignType.sign (Real.sin t) : ℝ)) (Set.Icc a b) MeasureTheory.volume))))))
  : Continuous F := by
  sorry

theorem proof_gap_exercise_2304_3
  (F : (ℝ -> ℝ))
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F x_1) = (∫ t in (0 : ℝ)..x_1, ((SignType.sign (Real.sin t) : ℝ) * (1 : ℝ)))))))
  (h4 : (forall (a : ℝ), ((a ∈ (Set.univ : Set ℝ)) → (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (a < b)) → (MeasureTheory.IntegrableOn (fun (t : ℝ) => (SignType.sign (Real.sin t) : ℝ)) (Set.Icc a b) MeasureTheory.volume))))))
  (h5 : Continuous F)
  : (exists (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((k * Real.pi) ≤ x)) ∧ (x < ((k + 1) * Real.pi))) ∧ (forall (k1 : ℤ), ((((k1 ∈ (Set.univ : Set ℤ)) ∧ ((k1 * Real.pi) ≤ x)) ∧ (x < ((k1 + 1) * Real.pi))) → (k1 = k))))) := by
  sorry

theorem proof_gap_exercise_2304_4
  (F : (ℝ -> ℝ))
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F x_1) = (∫ t in (0 : ℝ)..x_1, ((SignType.sign (Real.sin t) : ℝ) * (1 : ℝ)))))))
  (h4 : (forall (a : ℝ), ((a ∈ (Set.univ : Set ℝ)) → (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (a < b)) → (MeasureTheory.IntegrableOn (fun (t : ℝ) => (SignType.sign (Real.sin t) : ℝ)) (Set.Icc a b) MeasureTheory.volume))))))
  (h5 : Continuous F)
  (h6 : (exists (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((k * Real.pi) ≤ x)) ∧ (x < ((k + 1) * Real.pi))) ∧ (forall (k1 : ℤ), ((((k1 ∈ (Set.univ : Set ℤ)) ∧ ((k1 * Real.pi) ≤ x)) ∧ (x < ((k1 + 1) * Real.pi))) → (k1 = k))))))
  : (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((k * Real.pi) ≤ x)) ∧ (x < ((k + 1) * Real.pi))) → ((F x) = (∫ t in (0 : ℝ)..x, ((SignType.sign (Real.sin t) : ℝ) * (1 : ℝ)))))) := by
  sorry

theorem proof_gap_exercise_2304_5
  (F : (ℝ -> ℝ))
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F x_1) = (∫ t in (0 : ℝ)..x_1, ((SignType.sign (Real.sin t) : ℝ) * (1 : ℝ)))))))
  (h4 : (forall (a : ℝ), ((a ∈ (Set.univ : Set ℝ)) → (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (a < b)) → (MeasureTheory.IntegrableOn (fun (t : ℝ) => (SignType.sign (Real.sin t) : ℝ)) (Set.Icc a b) MeasureTheory.volume))))))
  (h5 : Continuous F)
  (h6 : (exists (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((k * Real.pi) ≤ x)) ∧ (x < ((k + 1) * Real.pi))) ∧ (forall (k1 : ℤ), ((((k1 ∈ (Set.univ : Set ℤ)) ∧ ((k1 * Real.pi) ≤ x)) ∧ (x < ((k1 + 1) * Real.pi))) → (k1 = k))))))
  (h7 : (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((k * Real.pi) ≤ x)) ∧ (x < ((k + 1) * Real.pi))) → ((F x) = (∫ t in (0 : ℝ)..x, ((SignType.sign (Real.sin t) : ℝ) * (1 : ℝ)))))))
  : (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((k * Real.pi) ≤ x)) ∧ (x < ((k + 1) * Real.pi))) → ((F x) = ((∫ t in (0 : ℝ)..((k * Real.pi) + (Real.pi /. 2)), ((SignType.sign (Real.sin t) : ℝ) * (1 : ℝ))) + (∫ t in ((k * Real.pi) + (Real.pi /. 2))..x, ((SignType.sign (Real.sin t) : ℝ) * (1 : ℝ))))))) := by
  sorry

theorem proof_gap_exercise_2304_6
  (F : (ℝ -> ℝ))
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F x_1) = (∫ t in (0 : ℝ)..x_1, ((SignType.sign (Real.sin t) : ℝ) * (1 : ℝ)))))))
  (h4 : (forall (a : ℝ), ((a ∈ (Set.univ : Set ℝ)) → (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (a < b)) → (MeasureTheory.IntegrableOn (fun (t : ℝ) => (SignType.sign (Real.sin t) : ℝ)) (Set.Icc a b) MeasureTheory.volume))))))
  (h5 : Continuous F)
  (h6 : (exists (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((k * Real.pi) ≤ x)) ∧ (x < ((k + 1) * Real.pi))) ∧ (forall (k1 : ℤ), ((((k1 ∈ (Set.univ : Set ℤ)) ∧ ((k1 * Real.pi) ≤ x)) ∧ (x < ((k1 + 1) * Real.pi))) → (k1 = k))))))
  (h7 : (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((k * Real.pi) ≤ x)) ∧ (x < ((k + 1) * Real.pi))) → ((F x) = (∫ t in (0 : ℝ)..x, ((SignType.sign (Real.sin t) : ℝ) * (1 : ℝ)))))))
  (h8 : (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((k * Real.pi) ≤ x)) ∧ (x < ((k + 1) * Real.pi))) → ((F x) = ((∫ t in (0 : ℝ)..((k * Real.pi) + (Real.pi /. 2)), ((SignType.sign (Real.sin t) : ℝ) * (1 : ℝ))) + (∫ t in ((k * Real.pi) + (Real.pi /. 2))..x, ((SignType.sign (Real.sin t) : ℝ) * (1 : ℝ))))))))
  (h9 : (Real.sin x) ≠ 0)
  : (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((k * Real.pi) ≤ x)) ∧ (x < ((k + 1) * Real.pi))) → ((F x) = ((Real.pi /. 2) + (∫ t in ((k * Real.pi) + (Real.pi /. 2))..x, (((Real.sin t) /. (Real.rpow (1 - ((Real.cos t) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))))))) := by
  sorry

theorem proof_gap_exercise_2304_7
  (F : (ℝ -> ℝ))
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F x_1) = (∫ t in (0 : ℝ)..x_1, ((SignType.sign (Real.sin t) : ℝ) * (1 : ℝ)))))))
  (h4 : (forall (a : ℝ), ((a ∈ (Set.univ : Set ℝ)) → (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (a < b)) → (MeasureTheory.IntegrableOn (fun (t : ℝ) => (SignType.sign (Real.sin t) : ℝ)) (Set.Icc a b) MeasureTheory.volume))))))
  (h5 : Continuous F)
  (h6 : (exists (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((k * Real.pi) ≤ x)) ∧ (x < ((k + 1) * Real.pi))) ∧ (forall (k1 : ℤ), ((((k1 ∈ (Set.univ : Set ℤ)) ∧ ((k1 * Real.pi) ≤ x)) ∧ (x < ((k1 + 1) * Real.pi))) → (k1 = k))))))
  (h7 : (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((k * Real.pi) ≤ x)) ∧ (x < ((k + 1) * Real.pi))) → ((F x) = (∫ t in (0 : ℝ)..x, ((SignType.sign (Real.sin t) : ℝ) * (1 : ℝ)))))))
  (h8 : (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((k * Real.pi) ≤ x)) ∧ (x < ((k + 1) * Real.pi))) → ((F x) = ((∫ t in (0 : ℝ)..((k * Real.pi) + (Real.pi /. 2)), ((SignType.sign (Real.sin t) : ℝ) * (1 : ℝ))) + (∫ t in ((k * Real.pi) + (Real.pi /. 2))..x, ((SignType.sign (Real.sin t) : ℝ) * (1 : ℝ))))))))
  (h9 : (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((k * Real.pi) ≤ x)) ∧ (x < ((k + 1) * Real.pi))) → ((F x) = ((Real.pi /. 2) + (∫ t in ((k * Real.pi) + (Real.pi /. 2))..x, (((Real.sin t) /. (Real.rpow (1 - ((Real.cos t) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))))))))
  (h10 : (Real.sin x) ≠ 0)
  : (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((k * Real.pi) ≤ x)) ∧ (x < ((k + 1) * Real.pi))) → ((F x) = (((Real.pi /. 2) + (Real.arccos (Real.cos x))) - ((Real.pi /. 2) + (Real.arccos (Real.cos ((k * Real.pi) + (Real.pi /. 2))))))))) := by
  sorry

theorem proof_gap_exercise_2304_8
  (F : (ℝ -> ℝ))
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F x_1) = (∫ t in (0 : ℝ)..x_1, ((SignType.sign (Real.sin t) : ℝ) * (1 : ℝ)))))))
  (h4 : (forall (a : ℝ), ((a ∈ (Set.univ : Set ℝ)) → (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (a < b)) → (MeasureTheory.IntegrableOn (fun (t : ℝ) => (SignType.sign (Real.sin t) : ℝ)) (Set.Icc a b) MeasureTheory.volume))))))
  (h5 : Continuous F)
  (h6 : (exists (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((k * Real.pi) ≤ x)) ∧ (x < ((k + 1) * Real.pi))) ∧ (forall (k1 : ℤ), ((((k1 ∈ (Set.univ : Set ℤ)) ∧ ((k1 * Real.pi) ≤ x)) ∧ (x < ((k1 + 1) * Real.pi))) → (k1 = k))))))
  (h7 : (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((k * Real.pi) ≤ x)) ∧ (x < ((k + 1) * Real.pi))) → ((F x) = (∫ t in (0 : ℝ)..x, ((SignType.sign (Real.sin t) : ℝ) * (1 : ℝ)))))))
  (h8 : (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((k * Real.pi) ≤ x)) ∧ (x < ((k + 1) * Real.pi))) → ((F x) = ((∫ t in (0 : ℝ)..((k * Real.pi) + (Real.pi /. 2)), ((SignType.sign (Real.sin t) : ℝ) * (1 : ℝ))) + (∫ t in ((k * Real.pi) + (Real.pi /. 2))..x, ((SignType.sign (Real.sin t) : ℝ) * (1 : ℝ))))))))
  (h9 : (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((k * Real.pi) ≤ x)) ∧ (x < ((k + 1) * Real.pi))) → ((F x) = ((Real.pi /. 2) + (∫ t in ((k * Real.pi) + (Real.pi /. 2))..x, (((Real.sin t) /. (Real.rpow (1 - ((Real.cos t) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))))))))
  (h10 : (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((k * Real.pi) ≤ x)) ∧ (x < ((k + 1) * Real.pi))) → ((F x) = (((Real.pi /. 2) + (Real.arccos (Real.cos x))) - ((Real.pi /. 2) + (Real.arccos (Real.cos ((k * Real.pi) + (Real.pi /. 2))))))))))
  (h11 : (Real.sin x) ≠ 0)
  : (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((k * Real.pi) ≤ x)) ∧ (x < ((k + 1) * Real.pi))) → ((F x) = (Real.arccos (Real.cos x))))) := by
  sorry

theorem proof_gap_exercise_2304_9
  (F : (ℝ -> ℝ))
  (x : ℝ)
  (C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F x_1) = (∫ t in (0 : ℝ)..x_1, ((SignType.sign (Real.sin t) : ℝ) * (1 : ℝ)))))))
  (h4 : (forall (a : ℝ), ((a ∈ (Set.univ : Set ℝ)) → (forall (b : ℝ), (((b ∈ (Set.univ : Set ℝ)) ∧ (a < b)) → (MeasureTheory.IntegrableOn (fun (t : ℝ) => (SignType.sign (Real.sin t) : ℝ)) (Set.Icc a b) MeasureTheory.volume))))))
  (h5 : Continuous F)
  (h6 : (exists (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((k * Real.pi) ≤ x)) ∧ (x < ((k + 1) * Real.pi))) ∧ (forall (k1 : ℤ), ((((k1 ∈ (Set.univ : Set ℤ)) ∧ ((k1 * Real.pi) ≤ x)) ∧ (x < ((k1 + 1) * Real.pi))) → (k1 = k))))))
  (h7 : (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((k * Real.pi) ≤ x)) ∧ (x < ((k + 1) * Real.pi))) → ((F x) = (∫ t in (0 : ℝ)..x, ((SignType.sign (Real.sin t) : ℝ) * (1 : ℝ)))))))
  (h8 : (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((k * Real.pi) ≤ x)) ∧ (x < ((k + 1) * Real.pi))) → ((F x) = ((∫ t in (0 : ℝ)..((k * Real.pi) + (Real.pi /. 2)), ((SignType.sign (Real.sin t) : ℝ) * (1 : ℝ))) + (∫ t in ((k * Real.pi) + (Real.pi /. 2))..x, ((SignType.sign (Real.sin t) : ℝ) * (1 : ℝ))))))))
  (h9 : (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((k * Real.pi) ≤ x)) ∧ (x < ((k + 1) * Real.pi))) → ((F x) = ((Real.pi /. 2) + (∫ t in ((k * Real.pi) + (Real.pi /. 2))..x, (((Real.sin t) /. (Real.rpow (1 - ((Real.cos t) ^ (2 : ℕ))) (((2 : ℝ))⁻¹))) * (1 : ℝ))))))))
  (h10 : (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((k * Real.pi) ≤ x)) ∧ (x < ((k + 1) * Real.pi))) → ((F x) = (((Real.pi /. 2) + (Real.arccos (Real.cos x))) - ((Real.pi /. 2) + (Real.arccos (Real.cos ((k * Real.pi) + (Real.pi /. 2))))))))))
  (h11 : (forall (k : ℤ), ((((k ∈ (Set.univ : Set ℤ)) ∧ ((k * Real.pi) ≤ x)) ∧ (x < ((k + 1) * Real.pi))) → ((F x) = (Real.arccos (Real.cos x))))))
  (h12 : (Real.sin x) ≠ 0)
  : ({F_2 : (ℝ -> ℝ) | (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((iteratedDeriv 1 (fun t_1 => F_2 t_1) x_1) = ((SignType.sign (Real.sin x_1) : ℝ) * (iteratedDeriv 1 (fun t_1 => t_1) x_1)))))}) = ({F_3 : (ℝ -> ℝ) | (exists (C_1 : ℝ), ((C_1 ∈ (Set.univ : Set ℝ)) ∧ (forall (x_1 : ℝ), ((x_1 ∈ (Set.univ : Set ℝ)) → ((F_3 x_1) = ((Real.arccos (Real.cos x_1)) + C_1))))))}) := by
  sorry
