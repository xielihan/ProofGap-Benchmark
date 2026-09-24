import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat

open Filter

open scoped RealInnerProductSpace

noncomputable def lpFunDeri {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (f g : E -> ℝ) : E -> ℝ :=
  fun x => (inner ℝ (gradient f x) (gradient g x)) / (‖gradient g x‖ ^ 2)

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

-- exercise: exercise_2781

theorem proof_gap_exercise_2781_1
  (a : (ℕ × ℝ -> ℝ))
  (s : (ℕ × ℝ -> ℝ))
  (S : ℝ)
  (h1 : S ∈ (Set.univ : Set ℝ))
  : (forall (x : ℝ) (m : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℤ))) ∧ (x = ((2 * m) * Real.pi))) ∧ (0 <= m)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (1 : ℕ) n, ((Real.sin x) * (Real.sin (k * x)))) = 0))))) := by
  sorry

theorem proof_gap_exercise_2781_2
  (a : (ℕ × ℝ -> ℝ))
  (s : (ℕ × ℝ -> ℝ))
  (S : ℝ)
  (h1 : S ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ) (m : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℤ))) ∧ (x = ((2 * m) * Real.pi))) ∧ (0 <= m)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (1 : ℕ) n, ((Real.sin x) * (Real.sin (k * x)))) = 0))))))
  : (forall (x : ℝ) (m : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℤ))) ∧ (x ≠ ((2 * m) * Real.pi))) ∧ (0 <= m)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((((|((∑ k ∈ Finset.Icc (1 : ℕ) n, ((Real.sin x) * (Real.sin (k * x)))))| = (|((Real.sin x))| * |((∑ k ∈ Finset.Icc (1 : ℕ) n, (Real.sin (k * x))))|)) ∧ ((|((Real.sin x))| * |((∑ k ∈ Finset.Icc (1 : ℕ) n, (Real.sin (k * x))))|) ≤ (|((Real.sin x))| * (1 / |((Real.sin (x / 2)))|)))) ∧ ((|((Real.sin x))| * (1 / |((Real.sin (x / 2)))|)) = (2 * |((Real.cos (x / 2)))|))) ∧ ((2 * |((Real.cos (x / 2)))|) ≤ 2)))))) := by
  sorry

theorem proof_gap_exercise_2781_3
  (a : (ℕ × ℝ -> ℝ))
  (s : (ℕ × ℝ -> ℝ))
  (S : ℝ)
  (h1 : S ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ) (m : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℤ))) ∧ (x = ((2 * m) * Real.pi))) ∧ (0 <= m)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (1 : ℕ) n, ((Real.sin x) * (Real.sin (k * x)))) = 0))))))
  (h3 : (forall (x : ℝ) (m : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℤ))) ∧ (x ≠ ((2 * m) * Real.pi))) ∧ (0 <= m)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((((|((∑ k ∈ Finset.Icc (1 : ℕ) n, ((Real.sin x) * (Real.sin (k * x)))))| = (|((Real.sin x))| * |((∑ k ∈ Finset.Icc (1 : ℕ) n, (Real.sin (k * x))))|)) ∧ ((|((Real.sin x))| * |((∑ k ∈ Finset.Icc (1 : ℕ) n, (Real.sin (k * x))))|) ≤ (|((Real.sin x))| * (1 / |((Real.sin (x / 2)))|)))) ∧ ((|((Real.sin x))| * (1 / |((Real.sin (x / 2)))|)) = (2 * |((Real.cos (x / 2)))|))) ∧ ((2 * |((Real.cos (x / 2)))|) ≤ 2)))))))
  : (forall (x : ℝ) (n : ℕ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n ∈ (Set.univ : Set ℕ))) ∧ (x ∈ ({x_1 : ℝ | 0 <= x_1}))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|((∑ k ∈ Finset.Icc (1 : ℕ) n, ((Real.sin x) * (Real.sin (k * x)))))| ≤ 2))) := by
  sorry

theorem proof_gap_exercise_2781_4
  (a : (ℕ × ℝ -> ℝ))
  (s : (ℕ × ℝ -> ℝ))
  (S : ℝ)
  (h1 : S ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ) (m : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℤ))) ∧ (x = ((2 * m) * Real.pi))) ∧ (0 <= m)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (1 : ℕ) n, ((Real.sin x) * (Real.sin (k * x)))) = 0))))))
  (h3 : (forall (x : ℝ) (m : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℤ))) ∧ (x ≠ ((2 * m) * Real.pi))) ∧ (0 <= m)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((((|((∑ k ∈ Finset.Icc (1 : ℕ) n, ((Real.sin x) * (Real.sin (k * x)))))| = (|((Real.sin x))| * |((∑ k ∈ Finset.Icc (1 : ℕ) n, (Real.sin (k * x))))|)) ∧ ((|((Real.sin x))| * |((∑ k ∈ Finset.Icc (1 : ℕ) n, (Real.sin (k * x))))|) ≤ (|((Real.sin x))| * (1 / |((Real.sin (x / 2)))|)))) ∧ ((|((Real.sin x))| * (1 / |((Real.sin (x / 2)))|)) = (2 * |((Real.cos (x / 2)))|))) ∧ ((2 * |((Real.cos (x / 2)))|) ≤ 2)))))))
  (h4 : (forall (x : ℝ) (n : ℕ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n ∈ (Set.univ : Set ℕ))) ∧ (x ∈ ({x_1 : ℝ | 0 <= x_1}))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|((∑ k ∈ Finset.Icc (1 : ℕ) n, ((Real.sin x) * (Real.sin (k * x)))))| ≤ 2))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 <= x_1}))) → (Antitone (fun (n : ℕ) => (1 / (Real.rpow (n + x) (((2 : ℝ))⁻¹))))))) := by
  sorry

theorem proof_gap_exercise_2781_5
  (a : (ℕ × ℝ -> ℝ))
  (s : (ℕ × ℝ -> ℝ))
  (S : ℝ)
  (h1 : S ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ) (m : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℤ))) ∧ (x = ((2 * m) * Real.pi))) ∧ (0 <= m)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (1 : ℕ) n, ((Real.sin x) * (Real.sin (k * x)))) = 0))))))
  (h3 : (forall (x : ℝ) (m : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℤ))) ∧ (x ≠ ((2 * m) * Real.pi))) ∧ (0 <= m)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((((|((∑ k ∈ Finset.Icc (1 : ℕ) n, ((Real.sin x) * (Real.sin (k * x)))))| = (|((Real.sin x))| * |((∑ k ∈ Finset.Icc (1 : ℕ) n, (Real.sin (k * x))))|)) ∧ ((|((Real.sin x))| * |((∑ k ∈ Finset.Icc (1 : ℕ) n, (Real.sin (k * x))))|) ≤ (|((Real.sin x))| * (1 / |((Real.sin (x / 2)))|)))) ∧ ((|((Real.sin x))| * (1 / |((Real.sin (x / 2)))|)) = (2 * |((Real.cos (x / 2)))|))) ∧ ((2 * |((Real.cos (x / 2)))|) ≤ 2)))))))
  (h4 : (forall (x : ℝ) (n : ℕ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n ∈ (Set.univ : Set ℕ))) ∧ (x ∈ ({x_1 : ℝ | 0 <= x_1}))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|((∑ k ∈ Finset.Icc (1 : ℕ) n, ((Real.sin x) * (Real.sin (k * x)))))| ≤ 2))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 <= x_1}))) → (Antitone (fun (n : ℕ) => (1 / (Real.rpow (n + x) (((2 : ℝ))⁻¹))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 <= x_1}))) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 / (Real.rpow (n + x) (((2 : ℝ))⁻¹))) ≤ (1 / (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)))))))) := by
  sorry

theorem proof_gap_exercise_2781_6
  (a : (ℕ × ℝ -> ℝ))
  (s : (ℕ × ℝ -> ℝ))
  (S : ℝ)
  (h1 : S ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ) (m : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℤ))) ∧ (x = ((2 * m) * Real.pi))) ∧ (0 <= m)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (1 : ℕ) n, ((Real.sin x) * (Real.sin (k * x)))) = 0))))))
  (h3 : (forall (x : ℝ) (m : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℤ))) ∧ (x ≠ ((2 * m) * Real.pi))) ∧ (0 <= m)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((((|((∑ k ∈ Finset.Icc (1 : ℕ) n, ((Real.sin x) * (Real.sin (k * x)))))| = (|((Real.sin x))| * |((∑ k ∈ Finset.Icc (1 : ℕ) n, (Real.sin (k * x))))|)) ∧ ((|((Real.sin x))| * |((∑ k ∈ Finset.Icc (1 : ℕ) n, (Real.sin (k * x))))|) ≤ (|((Real.sin x))| * (1 / |((Real.sin (x / 2)))|)))) ∧ ((|((Real.sin x))| * (1 / |((Real.sin (x / 2)))|)) = (2 * |((Real.cos (x / 2)))|))) ∧ ((2 * |((Real.cos (x / 2)))|) ≤ 2)))))))
  (h4 : (forall (x : ℝ) (n : ℕ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n ∈ (Set.univ : Set ℕ))) ∧ (x ∈ ({x_1 : ℝ | 0 <= x_1}))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|((∑ k ∈ Finset.Icc (1 : ℕ) n, ((Real.sin x) * (Real.sin (k * x)))))| ≤ 2))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 <= x_1}))) → (Antitone (fun (n : ℕ) => (1 / (Real.rpow (n + x) (((2 : ℝ))⁻¹))))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 <= x_1}))) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 / (Real.rpow (n + x) (((2 : ℝ))⁻¹))) ≤ (1 / (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)))))))))
  : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 <= x_1}))) → (Tendsto (fun n : ℕ => (1 / (Real.rpow (n + x) (((2 : ℝ))⁻¹)))) atTop (𝓝 0)))) := by
  sorry

theorem proof_gap_exercise_2781_7
  (a : (ℕ × ℝ -> ℝ))
  (s : (ℕ × ℝ -> ℝ))
  (S : ℝ)
  (h1 : S ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ) (m : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℤ))) ∧ (x = ((2 * m) * Real.pi))) ∧ (0 <= m)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (1 : ℕ) n, ((Real.sin x) * (Real.sin (k * x)))) = 0))))))
  (h3 : (forall (x : ℝ) (m : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℤ))) ∧ (x ≠ ((2 * m) * Real.pi))) ∧ (0 <= m)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((((|((∑ k ∈ Finset.Icc (1 : ℕ) n, ((Real.sin x) * (Real.sin (k * x)))))| = (|((Real.sin x))| * |((∑ k ∈ Finset.Icc (1 : ℕ) n, (Real.sin (k * x))))|)) ∧ ((|((Real.sin x))| * |((∑ k ∈ Finset.Icc (1 : ℕ) n, (Real.sin (k * x))))|) ≤ (|((Real.sin x))| * (1 / |((Real.sin (x / 2)))|)))) ∧ ((|((Real.sin x))| * (1 / |((Real.sin (x / 2)))|)) = (2 * |((Real.cos (x / 2)))|))) ∧ ((2 * |((Real.cos (x / 2)))|) ≤ 2)))))))
  (h4 : (forall (x : ℝ) (n : ℕ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n ∈ (Set.univ : Set ℕ))) ∧ (x ∈ ({x_1 : ℝ | 0 <= x_1}))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|((∑ k ∈ Finset.Icc (1 : ℕ) n, ((Real.sin x) * (Real.sin (k * x)))))| ≤ 2))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 <= x_1}))) → (Antitone (fun (n : ℕ) => (1 / (Real.rpow (n + x) (((2 : ℝ))⁻¹))))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 <= x_1}))) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 / (Real.rpow (n + x) (((2 : ℝ))⁻¹))) ≤ (1 / (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)))))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 <= x_1}))) → (Tendsto (fun n : ℕ => (1 / (Real.rpow (n + x) (((2 : ℝ))⁻¹)))) atTop (𝓝 0)))))
  : TendstoUniformlyOn (fun n x => s (n, x)) (fun _ => S) Filter.atTop ({x_1 : ℝ | 0 <= x_1}) := by
  sorry

theorem proof_gap_exercise_2781_8
  (a : (ℕ × ℝ -> ℝ))
  (s : (ℕ × ℝ -> ℝ))
  (S : ℝ)
  (h1 : S ∈ (Set.univ : Set ℝ))
  (h2 : (forall (x : ℝ) (m : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℤ))) ∧ (x = ((2 * m) * Real.pi))) ∧ (0 <= m)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((∑ k ∈ Finset.Icc (1 : ℕ) n, ((Real.sin x) * (Real.sin (k * x)))) = 0))))))
  (h3 : (forall (x : ℝ) (m : ℤ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (m ∈ (Set.univ : Set ℤ))) ∧ (x ≠ ((2 * m) * Real.pi))) ∧ (0 <= m)) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((((|((∑ k ∈ Finset.Icc (1 : ℕ) n, ((Real.sin x) * (Real.sin (k * x)))))| = (|((Real.sin x))| * |((∑ k ∈ Finset.Icc (1 : ℕ) n, (Real.sin (k * x))))|)) ∧ ((|((Real.sin x))| * |((∑ k ∈ Finset.Icc (1 : ℕ) n, (Real.sin (k * x))))|) ≤ (|((Real.sin x))| * (1 / |((Real.sin (x / 2)))|)))) ∧ ((|((Real.sin x))| * (1 / |((Real.sin (x / 2)))|)) = (2 * |((Real.cos (x / 2)))|))) ∧ ((2 * |((Real.cos (x / 2)))|) ≤ 2)))))))
  (h4 : (forall (x : ℝ) (n : ℕ), (((((x ∈ (Set.univ : Set ℝ)) ∧ (n ∈ (Set.univ : Set ℕ))) ∧ (x ∈ ({x_1 : ℝ | 0 <= x_1}))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → (|((∑ k ∈ Finset.Icc (1 : ℕ) n, ((Real.sin x) * (Real.sin (k * x)))))| ≤ 2))))
  (h5 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 <= x_1}))) → (Antitone (fun (n : ℕ) => (1 / (Real.rpow (n + x) (((2 : ℝ))⁻¹))))))))
  (h6 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 <= x_1}))) → (forall (n : ℕ), (((n ∈ (Set.univ : Set ℕ)) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) → ((1 / (Real.rpow (n + x) (((2 : ℝ))⁻¹))) ≤ (1 / (Real.rpow (n : ℝ) (((2 : ℝ))⁻¹)))))))))
  (h7 : (forall (x : ℝ), (((x ∈ (Set.univ : Set ℝ)) ∧ (x ∈ ({x_1 : ℝ | 0 <= x_1}))) → (Tendsto (fun n : ℕ => (1 / (Real.rpow (n + x) (((2 : ℝ))⁻¹)))) atTop (𝓝 0)))))
  (h8 : TendstoUniformlyOn (fun n x => s (n, x)) (fun _ => S) Filter.atTop ({x_1 : ℝ | 0 <= x_1}))
  : (forall (a_1 : (ℕ × ℝ -> ℝ)) (s_1 : (ℕ × ℝ -> ℝ)) (S_1 : ℝ), ((((True ∧ (S_1 ∈ (Set.univ : Set ℝ))) ∧ (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ ({x_1 : ℝ | 0 <= x_1}))) → ((a_1 (n, x)) = (((Real.sin x) * (Real.sin (n * x))) / (Real.rpow (n + x) (((2 : ℝ))⁻¹))))))) ∧ (forall (n : ℕ) (x : ℝ), (((((n ∈ (Set.univ : Set ℕ)) ∧ (x ∈ (Set.univ : Set ℝ))) ∧ (n ∈ ({n_1 : ℕ | 0 < n_1}))) ∧ (x ∈ ({x_1 : ℝ | 0 <= x_1}))) → ((s_1 (n, x)) = (∑ k ∈ Finset.Icc (1 : ℕ) n, (a_1 (k, x))))))) → (TendstoUniformlyOn (fun n x => s_1 (n, x)) (fun _ => S_1) Filter.atTop ({x_1 : ℝ | 0 <= x_1})))) := by
  sorry
