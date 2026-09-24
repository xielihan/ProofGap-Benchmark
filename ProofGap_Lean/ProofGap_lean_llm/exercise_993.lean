import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable def FunDeri (f : ℝ → ℝ) (_i _j : ℕ) : ℝ → ℝ := deriv f
def BoundedFunc (g : ℝ → ℝ) : Prop := ∃ C : ℝ, ∀ x : ℝ, |g x| ≤ C
def BoundedFuncOn (g : ℝ → ℝ) (s : Set ℝ) : Prop := ∃ C : ℝ, ∀ x ∈ s, |g x| ≤ C
def DiffableFuncAt (f : ℝ → ℝ) (x : ℝ) : Prop := DifferentiableAt ℝ f x

-- exercise: exercise_993

theorem proof_gap_exercise_993_1
  (f : ℝ → ℝ)
  (n m : ℝ)
  (hn : n ∈ (Set.univ : Set ℝ))
  (hm : m ∈ (Set.univ : Set ℝ))
  (hmpos : m > 0)
  (hf_ne : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 → f x = |x| ^ n * Real.sin ((1 : ℝ) /. (|x| ^ m)))
  (hf0 : f 0 = 0)
  : ∀ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 →
      ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 ∧ x ∈ Set.Ioo (-δ) δ ∧ δ > 0 →
        FunDeri f 1 1 x =
          n * |x| ^ (n - 1) * (|x| /. x) * Real.sin ((1 : ℝ) /. (|x| ^ m)) -
          (m /. (|x| ^ (m + 1))) * (|x| /. x) * |x| ^ n * Real.cos ((1 : ℝ) /. (|x| ^ m)) := by
  sorry

theorem proof_gap_exercise_993_2
  (f : ℝ → ℝ)
  (n m : ℝ)
  (hn : n ∈ (Set.univ : Set ℝ))
  (hm : m ∈ (Set.univ : Set ℝ))
  (hmpos : m > 0)
  (hf_ne : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 → f x = |x| ^ n * Real.sin ((1 : ℝ) /. (|x| ^ m)))
  (hf0 : f 0 = 0)
  (h7 : ∀ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 →
      ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 ∧ x ∈ Set.Ioo (-δ) δ ∧ δ > 0 →
        FunDeri f 1 1 x =
          n * |x| ^ (n - 1) * (|x| /. x) * Real.sin ((1 : ℝ) /. (|x| ^ m)) -
          (m /. (|x| ^ (m + 1))) * (|x| /. x) * |x| ^ n * Real.cos ((1 : ℝ) /. (|x| ^ m)))
  : ∀ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 →
      ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 ∧ x ∈ Set.Ioo (-δ) δ ∧ δ > 0 →
        FunDeri f 1 1 x =
          (|x| /. x) * (n * |x| ^ (n - 1) * Real.sin ((1 : ℝ) /. (|x| ^ m)) -
            m * |x| ^ (n - (m + 1)) * Real.cos ((1 : ℝ) /. (|x| ^ m))) := by
  sorry

theorem proof_gap_exercise_993_3
  (f : ℝ → ℝ)
  (n m : ℝ)
  (hmpos : m > 0)
  (hf_ne : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 → f x = |x| ^ n * Real.sin ((1 : ℝ) /. (|x| ^ m)))
  (hf0 : f 0 = 0)
  (h7 : ∀ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 →
      ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 ∧ x ∈ Set.Ioo (-δ) δ ∧ δ > 0 →
        FunDeri f 1 1 x =
          n * |x| ^ (n - 1) * (|x| /. x) * Real.sin ((1 : ℝ) /. (|x| ^ m)) -
          (m /. (|x| ^ (m + 1))) * (|x| /. x) * |x| ^ n * Real.cos ((1 : ℝ) /. (|x| ^ m)))
  (h8 : ∀ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 →
      ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 ∧ x ∈ Set.Ioo (-δ) δ ∧ δ > 0 →
        FunDeri f 1 1 x =
          (|x| /. x) * (n * |x| ^ (n - 1) * Real.sin ((1 : ℝ) /. (|x| ^ m)) -
            m * |x| ^ (n - (m + 1)) * Real.cos ((1 : ℝ) /. (|x| ^ m))))
  : BoundedFunc (fun x : ℝ => |x| /. x) := by
  sorry

theorem proof_gap_exercise_993_4
  (f : ℝ → ℝ)
  (n m : ℝ)
  (hmpos : m > 0)
  (h9 : BoundedFunc (fun x : ℝ => |x| /. x))
  : BoundedFunc (fun x : ℝ => Real.sin ((1 : ℝ) /. (|x| ^ m))) := by
  sorry

theorem proof_gap_exercise_993_5
  (f : ℝ → ℝ)
  (n m : ℝ)
  (hmpos : m > 0)
  (h9 : BoundedFunc (fun x : ℝ => |x| /. x))
  (h10 : BoundedFunc (fun x : ℝ => Real.sin ((1 : ℝ) /. (|x| ^ m))))
  : BoundedFunc (fun x : ℝ => Real.cos ((1 : ℝ) /. (|x| ^ m))) := by
  sorry

theorem proof_gap_exercise_993_6
  (f : ℝ → ℝ)
  (n m : ℝ)
  (hmpos : m > 0)
  (hf_ne : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 → f x = |x| ^ n * Real.sin ((1 : ℝ) /. (|x| ^ m)))
  (hf0 : f 0 = 0)
  (h8 : ∀ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 →
      ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 ∧ x ∈ Set.Ioo (-δ) δ ∧ δ > 0 →
        FunDeri f 1 1 x =
          (|x| /. x) * (n * |x| ^ (n - 1) * Real.sin ((1 : ℝ) /. (|x| ^ m)) -
            m * |x| ^ (n - (m + 1)) * Real.cos ((1 : ℝ) /. (|x| ^ m))))
  (h9 : BoundedFunc (fun x : ℝ => |x| /. x))
  (h10 : BoundedFunc (fun x : ℝ => Real.sin ((1 : ℝ) /. (|x| ^ m)))
  )
  (h11 : BoundedFunc (fun x : ℝ => Real.cos ((1 : ℝ) /. (|x| ^ m))))
  : n ≥ m + 1 → ∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧ BoundedFuncOn (FunDeri f 1 1) (Set.Ioo (-δ) δ) := by
  sorry

theorem proof_gap_exercise_993_7
  (f : ℝ → ℝ)
  (n m : ℝ)
  (hmpos : m > 0)
  (hf_ne : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 → f x = |x| ^ n * Real.sin ((1 : ℝ) /. (|x| ^ m)))
  (hf0 : f 0 = 0)
  (h12 : n ≥ m + 1 → ∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧ BoundedFuncOn (FunDeri f 1 1) (Set.Ioo (-δ) δ))
  : n ≥ m + 1 → FunDeri f 1 1 0 = 0 := by
  sorry

theorem proof_gap_exercise_993_8
  (f : ℝ → ℝ)
  (n m : ℝ)
  (hmpos : m > 0)
  (hf_ne : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 → f x = |x| ^ n * Real.sin ((1 : ℝ) /. (|x| ^ m)))
  (hf0 : f 0 = 0)
  (h13 : n ≥ m + 1 → FunDeri f 1 1 0 = 0)
  : n < m + 1 → ∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧ ¬ BoundedFuncOn (FunDeri f 1 1) (Set.Ioo (-δ) δ) := by
  sorry

theorem proof_gap_exercise_993_9
  (f : ℝ → ℝ)
  (n m : ℝ)
  (hmpos : m > 0)
  (hf_ne : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 → f x = |x| ^ n * Real.sin ((1 : ℝ) /. (|x| ^ m)))
  (hf0 : f 0 = 0)
  (h14 : n < m + 1 → ∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧ ¬ BoundedFuncOn (FunDeri f 1 1) (Set.Ioo (-δ) δ))
  : n > 1 → DiffableFuncAt f 0 := by
  sorry

theorem proof_gap_exercise_993_10
  (f : ℝ → ℝ)
  (n m : ℝ)
  (hn : n ∈ (Set.univ : Set ℝ))
  (hm : m ∈ (Set.univ : Set ℝ))
  (hmpos : m > 0)
  (hf_ne : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 → f x = |x| ^ n * Real.sin ((1 : ℝ) /. (|x| ^ m)))
  (hf0 : f 0 = 0)
  (h12 : n ≥ m + 1 → ∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧ BoundedFuncOn (FunDeri f 1 1) (Set.Ioo (-δ) δ))
  (h14 : n < m + 1 → ∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧ ¬ BoundedFuncOn (FunDeri f 1 1) (Set.Ioo (-δ) δ))
  (h15 : n > 1 → DiffableFuncAt f 0)
  : ∃ n₁ : ℝ, n₁ ∈ (Set.univ : Set ℝ) ∧
      ∃ n₂ : ℝ, n₂ ∈ (Set.univ : Set ℝ) ∧
        ((n₁ ∈ {t : ℝ | t ≥ m + 1}) ∧ (n₂ ∈ {t : ℝ | 1 < t ∧ t < m + 1}) ↔
          (∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧ BoundedFuncOn (FunDeri f 1 1) (Set.Ioo (-δ) δ)) ∧
          (∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧ ¬ BoundedFuncOn (FunDeri f 1 1) (Set.Ioo (-δ) δ) ∧ DiffableFuncAt f 0)) := by
  sorry
