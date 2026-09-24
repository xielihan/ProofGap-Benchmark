import Mathlib

set_option linter.style.longLine false

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

def lpUniformConvergentOn (F : ℕ × ℝ -> ℝ) (s : Set ℝ) (g : ℝ -> ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n > N -> 0 < n -> ∀ x : ℝ, x ∈ s -> |F (n, x) - g x| < ε

def lpC1On (f : ℝ -> ℝ) (s : Set ℝ) : Prop := ContDiffOn ℝ 1 f s
def lpContinuousOn (f : ℝ -> ℝ) (s : Set ℝ) : Prop := ContinuousOn f s
def lpUniformContinuousOn (f : ℝ -> ℝ) (s : Set ℝ) : Prop := UniformContinuousOn f s
noncomputable def lpDeriv (f : ℝ -> ℝ) : ℝ -> ℝ := fun x => deriv f x

-- exercise: exercise_2765

theorem proof_gap_exercise_2765_1
  (f : ℝ -> ℝ) (F : ℕ × ℝ -> ℝ) (a b α β αp βp : ℝ)
  (hab : a < b) (haα : a < α) (hαβ : α < β) (hβb : β < b)
  (hf : lpC1On f (Set.Ioo a b))
  (hF : ∀ (n : ℕ) (x : ℝ), 0 < n ∧ x ∈ Set.Ioo a (b - 1 /. n) -> F (n, x) = (n : ℝ) * (f (x + 1 /. n) - f x))
  (hαp : αp = (α + a) / 2) (hβp : βp = (β + b) / 2) : a < αp := by
  sorry

theorem proof_gap_exercise_2765_2
  (f : ℝ -> ℝ) (F : ℕ × ℝ -> ℝ) (a b α β αp βp : ℝ)
  (hab : a < b) (haα : a < α) (hαβ : α < β) (hβb : β < b)
  (hf : lpC1On f (Set.Ioo a b)) (hF : ∀ (n : ℕ) (x : ℝ), 0 < n ∧ x ∈ Set.Ioo a (b - 1 /. n) -> F (n, x) = (n : ℝ) * (f (x + 1 /. n) - f x))
  (hαp : αp = (α + a) / 2) (hβp : βp = (β + b) / 2) (h1 : a < αp) : αp < α := by
  sorry

theorem proof_gap_exercise_2765_3
  (f : ℝ -> ℝ) (F : ℕ × ℝ -> ℝ) (a b α β αp βp : ℝ)
  (hab : a < b) (haα : a < α) (hαβ : α < β) (hβb : β < b)
  (hf : lpC1On f (Set.Ioo a b)) (hF : ∀ (n : ℕ) (x : ℝ), 0 < n ∧ x ∈ Set.Ioo a (b - 1 /. n) -> F (n, x) = (n : ℝ) * (f (x + 1 /. n) - f x))
  (hαp : αp = (α + a) / 2) (hβp : βp = (β + b) / 2) (h1 : a < αp) (h2 : αp < α) : α < β := by
  sorry

theorem proof_gap_exercise_2765_4
  (f : ℝ -> ℝ) (F : ℕ × ℝ -> ℝ) (a b α β αp βp : ℝ)
  (hab : a < b) (haα : a < α) (hαβ : α < β) (hβb : β < b)
  (hf : lpC1On f (Set.Ioo a b)) (hF : ∀ (n : ℕ) (x : ℝ), 0 < n ∧ x ∈ Set.Ioo a (b - 1 /. n) -> F (n, x) = (n : ℝ) * (f (x + 1 /. n) - f x))
  (hαp : αp = (α + a) / 2) (hβp : βp = (β + b) / 2) (h1 : a < αp) (h2 : αp < α) (h3 : α < β) : β < βp := by
  sorry

theorem proof_gap_exercise_2765_5
  (f : ℝ -> ℝ) (F : ℕ × ℝ -> ℝ) (a b α β αp βp : ℝ)
  (hab : a < b) (haα : a < α) (hαβ : α < β) (hβb : β < b)
  (hf : lpC1On f (Set.Ioo a b)) (hF : ∀ (n : ℕ) (x : ℝ), 0 < n ∧ x ∈ Set.Ioo a (b - 1 /. n) -> F (n, x) = (n : ℝ) * (f (x + 1 /. n) - f x))
  (hαp : αp = (α + a) / 2) (hβp : βp = (β + b) / 2) (h1 : a < αp) (h2 : αp < α) (h3 : α < β) (h4 : β < βp) : βp < b := by
  sorry

theorem proof_gap_exercise_2765_6
  (f : ℝ -> ℝ) (F : ℕ × ℝ -> ℝ) (a b α β αp βp : ℝ)
  (hab : a < b) (haα : a < α) (hαβ : α < β) (hβb : β < b) (hf : lpC1On f (Set.Ioo a b))
  (hF : ∀ (n : ℕ) (x : ℝ), 0 < n ∧ x ∈ Set.Ioo a (b - 1 /. n) -> F (n, x) = (n : ℝ) * (f (x + 1 /. n) - f x))
  (hαp : αp = (α + a) / 2) (hβp : βp = (β + b) / 2) (h1 : a < αp) (h2 : αp < α) (h3 : α < β) (h4 : β < βp) (h5 : βp < b)
  : lpContinuousOn (lpDeriv f) (Set.Icc αp βp) := by
  sorry

theorem proof_gap_exercise_2765_7
  (f : ℝ -> ℝ) (F : ℕ × ℝ -> ℝ) (a b α β αp βp : ℝ)
  (hab : a < b) (haα : a < α) (hαβ : α < β) (hβb : β < b) (hf : lpC1On f (Set.Ioo a b))
  (hF : ∀ (n : ℕ) (x : ℝ), 0 < n ∧ x ∈ Set.Ioo a (b - 1 /. n) -> F (n, x) = (n : ℝ) * (f (x + 1 /. n) - f x))
  (hαp : αp = (α + a) / 2) (hβp : βp = (β + b) / 2) (h1 : a < αp) (h2 : αp < α) (h3 : α < β) (h4 : β < βp) (h5 : βp < b)
  (h6 : lpContinuousOn (lpDeriv f) (Set.Icc αp βp))
  : lpUniformContinuousOn (lpDeriv f) (Set.Icc αp βp) := by
  sorry

theorem proof_gap_exercise_2765_8
  (f : ℝ -> ℝ) (F : ℕ × ℝ -> ℝ) (a b α β αp βp : ℝ)
  (hab : a < b) (haα : a < α) (hαβ : α < β) (hβb : β < b) (hf : lpC1On f (Set.Ioo a b))
  (hF : ∀ (n : ℕ) (x : ℝ), 0 < n ∧ x ∈ Set.Ioo a (b - 1 /. n) -> F (n, x) = (n : ℝ) * (f (x + 1 /. n) - f x))
  (hαp : αp = (α + a) / 2) (hβp : βp = (β + b) / 2) (h6 : lpContinuousOn (lpDeriv f) (Set.Icc αp βp)) (h7 : lpUniformContinuousOn (lpDeriv f) (Set.Icc αp βp))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x ∈ Set.Icc α β ∧ 0 < n ->
      ∃ θ : ℝ, θ ∈ (Set.univ : Set ℝ) ∧ 0 < θ ∧ θ < 1 ∧ F (n, x) = lpDeriv f (x + θ /. n) := by
  sorry

theorem proof_gap_exercise_2765_9
  (f : ℝ -> ℝ) (F : ℕ × ℝ -> ℝ) (a b α β αp βp : ℝ)
  (h7 : lpUniformContinuousOn (lpDeriv f) (Set.Icc αp βp))
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 -> ∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧
      ∀ (xp aq bq xpp : ℝ), xp ∈ (Set.univ : Set ℝ) ∧ aq ∈ (Set.univ : Set ℝ) ∧ bq ∈ (Set.univ : Set ℝ) ∧ xpp ∈ (Set.univ : Set ℝ) ∧
        xp ∈ Set.Icc aq bq ∧ xpp ∈ Set.Icc aq bq ∧ |xp - xpp| < δ -> |lpDeriv f xp - lpDeriv f xpp| < ε := by
  sorry

theorem proof_gap_exercise_2765_10
  (f : ℝ -> ℝ) (F : ℕ × ℝ -> ℝ) (a b α β αp βp : ℝ)
  (h9 : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 -> ∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧ ∀ (xp aq bq xpp : ℝ), xp ∈ Set.Icc aq bq ∧ xpp ∈ Set.Icc aq bq ∧ |xp - xpp| < δ -> |lpDeriv f xp - lpDeriv f xpp| < ε)
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 -> ∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧ ∃ N : ℕ, N ∈ (Set.univ : Set ℕ) ∧ N = Int.toNat (Int.floor (1 / δ) + 1) ∧ ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n > N ∧ 0 < n -> (1 /. n) < δ := by
  sorry

theorem proof_gap_exercise_2765_11
  (f : ℝ -> ℝ) (F : ℕ × ℝ -> ℝ) (a b α β αp βp : ℝ)
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 -> ∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧ ∃ N : ℕ, N ∈ (Set.univ : Set ℕ) ∧ N = Int.toNat (Int.floor (1 / δ) + 1) ∧ ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n > N ∧ 0 < n -> ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc α β -> ∃ θ : ℝ, θ ∈ (Set.univ : Set ℝ) ∧ 0 < θ ∧ θ < 1 ∧ x ∈ Set.Icc αp βp ∧ (x + (θ /. n)) ∈ Set.Icc αp βp := by
  sorry

theorem proof_gap_exercise_2765_12
  (f : ℝ -> ℝ) (F : ℕ × ℝ -> ℝ) (a b α β αp βp : ℝ)
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 -> ∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧ ∃ N : ℕ, N ∈ (Set.univ : Set ℕ) ∧ N = Int.toNat (Int.floor (1 / δ) + 1) ∧ ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n > N ∧ 0 < n -> ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc α β -> ∃ θ : ℝ, θ ∈ (Set.univ : Set ℝ) ∧ 0 < θ ∧ θ < 1 ∧ |F (n, x) - lpDeriv f x| = |lpDeriv f (x + (θ /. n)) - lpDeriv f x| ∧ |lpDeriv f (x + (θ /. n)) - lpDeriv f x| < ε := by
  sorry

theorem proof_gap_exercise_2765_13
  (f : ℝ -> ℝ) (F : ℕ × ℝ -> ℝ) (a b α β αp βp : ℝ)
  (h12 : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 -> ∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧ ∃ N : ℕ, N ∈ (Set.univ : Set ℕ) ∧ N = Int.toNat (Int.floor (1 / δ) + 1) ∧ ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n > N ∧ 0 < n -> ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc α β -> ∃ θ : ℝ, θ ∈ (Set.univ : Set ℝ) ∧ 0 < θ ∧ θ < 1 ∧ |F (n, x) - lpDeriv f x| = |lpDeriv f (x + (θ /. n)) - lpDeriv f x| ∧ |lpDeriv f (x + (θ /. n)) - lpDeriv f x| < ε)
  : lpUniformConvergentOn F (Set.Icc α β) (lpDeriv f) := by
  sorry

theorem proof_gap_exercise_2765_14
  (f : ℝ -> ℝ) (F : ℕ × ℝ -> ℝ) (a b α β αp βp : ℝ)
  (h13 : lpUniformConvergentOn F (Set.Icc α β) (lpDeriv f))
  : lpUniformConvergentOn F (Set.Icc α β) (lpDeriv f) := by
  sorry
