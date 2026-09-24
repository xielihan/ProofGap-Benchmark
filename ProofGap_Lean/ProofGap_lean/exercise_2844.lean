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

-- exercise: exercise_2844

theorem proof_gap_exercise_2844_1
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : a ≠ 1)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (Real.rpow a x)))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (Real.exp (x * (Real.log a)))))) := by
  sorry

theorem proof_gap_exercise_2844_2
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : a ≠ 1)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (Real.rpow a x)))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (Real.exp (x * (Real.log a)))))))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (∑' n, if (0 : ℕ) ≤ n then ((((Real.log a) ^ n) /. (n)!) * (x ^ n)) else 0)))) := by
  sorry

theorem proof_gap_exercise_2844_3
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : a ≠ 1)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (Real.rpow a x)))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (Real.exp (x * (Real.log a)))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (∑' n, if (0 : ℕ) ≤ n then ((((Real.log a) ^ n) /. (n)!) * (x ^ n)) else 0)))))
  : (∃ L : ℝ, Tendsto (fun n : ℕ => (1 /. (Real.rpow ((n)! : ℝ) ((n)⁻¹)))) atTop (𝓝 L) ∧ (Tendsto (fun n : ℕ => (Real.rpow |(((Real.rpow (Real.log a) n) /. (n)!))| ((n)⁻¹))) atTop (𝓝 (|((Real.log a))| * atTop.limUnder (fun n : ℕ => (1 /. (Real.rpow ((n)! : ℝ) ((n)⁻¹)))))))) := by
  sorry

theorem proof_gap_exercise_2844_4
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : a ≠ 1)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (Real.rpow a x)))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (Real.exp (x * (Real.log a)))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (∑' n, if (0 : ℕ) ≤ n then ((((Real.log a) ^ n) /. (n)!) * (x ^ n)) else 0)))))
  (h7 : Tendsto (fun n : ℕ => (Real.rpow |(((Real.rpow (Real.log a) n) /. (n)!))| ((n)⁻¹))) atTop (𝓝 (|((Real.log a))| * atTop.limUnder (fun n : ℕ => (1 /. (Real.rpow ((n)! : ℝ) ((n)⁻¹)))))))
  (h8 : ∃ L : ℝ, Tendsto (fun n : ℕ => (1 /. (Real.rpow ((n)! : ℝ) ((n)⁻¹)))) atTop (𝓝 L))
  : (|((Real.log a))| * atTop.limUnder (fun n : ℕ => (1 /. (Real.rpow ((n)! : ℝ) ((n)⁻¹))))) = 0 := by
  sorry

theorem proof_gap_exercise_2844_5
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : a ≠ 1)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (Real.rpow a x)))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (Real.exp (x * (Real.log a)))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (∑' n, if (0 : ℕ) ≤ n then ((((Real.log a) ^ n) /. (n)!) * (x ^ n)) else 0)))))
  (h7 : Tendsto (fun n : ℕ => (Real.rpow |(((Real.rpow (Real.log a) n) /. (n)!))| ((n)⁻¹))) atTop (𝓝 (|((Real.log a))| * atTop.limUnder (fun n : ℕ => (1 /. (Real.rpow ((n)! : ℝ) ((n)⁻¹)))))))
  (h8 : (|((Real.log a))| * atTop.limUnder (fun n : ℕ => (1 /. (Real.rpow ((n)! : ℝ) ((n)⁻¹))))) = 0)
  (h9 : ∃ L : ℝ, Tendsto (fun n : ℕ => (1 /. (Real.rpow ((n)! : ℝ) ((n)⁻¹)))) atTop (𝓝 L))
  : Tendsto (fun n : ℕ => (Real.rpow |(((Real.rpow (Real.log a) n) /. (n)!))| ((n)⁻¹))) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_2844_6
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : a ≠ 1)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (Real.rpow a x)))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (Real.exp (x * (Real.log a)))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (∑' n, if (0 : ℕ) ≤ n then ((((Real.log a) ^ n) /. (n)!) * (x ^ n)) else 0)))))
  (h7 : Tendsto (fun n : ℕ => (Real.rpow |(((Real.rpow (Real.log a) n) /. (n)!))| ((n)⁻¹))) atTop (𝓝 (|((Real.log a))| * atTop.limUnder (fun n : ℕ => (1 /. (Real.rpow ((n)! : ℝ) ((n)⁻¹)))))))
  (h8 : (|((Real.log a))| * atTop.limUnder (fun n : ℕ => (1 /. (Real.rpow ((n)! : ℝ) ((n)⁻¹))))) = 0)
  (h9 : Tendsto (fun n : ℕ => (Real.rpow |(((Real.rpow (Real.log a) n) /. (n)!))| ((n)⁻¹))) atTop (𝓝 0))
  (h10 : ∃ L : ℝ, Tendsto (fun n : ℕ => (1 /. (Real.rpow ((n)! : ℝ) ((n)⁻¹)))) atTop (𝓝 L))
  : ((lpRadiusOfConvergence (fun (n : ℕ) => (((Real.log a) ^ n) /. (n)!))) : EReal) = ⊤ := by
  sorry

theorem proof_gap_exercise_2844_7
  (f : (ℝ -> ℝ))
  (a : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : a > 0)
  (h3 : a ≠ 1)
  (h4 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (Real.rpow a x)))))
  (h5 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (Real.exp (x * (Real.log a)))))))
  (h6 : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (∑' n, if (0 : ℕ) ≤ n then ((((Real.log a) ^ n) /. (n)!) * (x ^ n)) else 0)))))
  (h7 : Tendsto (fun n : ℕ => (Real.rpow |(((Real.rpow (Real.log a) n) /. (n)!))| ((n)⁻¹))) atTop (𝓝 (|((Real.log a))| * atTop.limUnder (fun n : ℕ => (1 /. (Real.rpow ((n)! : ℝ) ((n)⁻¹)))))))
  (h8 : (|((Real.log a))| * atTop.limUnder (fun n : ℕ => (1 /. (Real.rpow ((n)! : ℝ) ((n)⁻¹))))) = 0)
  (h9 : Tendsto (fun n : ℕ => (Real.rpow |(((Real.rpow (Real.log a) n) /. (n)!))| ((n)⁻¹))) atTop (𝓝 0))
  (h10 : ((lpRadiusOfConvergence (fun (n : ℕ) => (((Real.log a) ^ n) /. (n)!))) : EReal) = ⊤)
  (h11 : ∃ L : ℝ, Tendsto (fun n : ℕ => (1 /. (Real.rpow ((n)! : ℝ) ((n)⁻¹)))) atTop (𝓝 L))
  : (forall (x : ℝ), ((x ∈ (Set.univ : Set ℝ)) → ((f x) = (∑' n, if (0 : ℕ) ≤ n then ((((Real.log a) ^ n) /. (n)!) * (x ^ n)) else 0)))) := by
  sorry
