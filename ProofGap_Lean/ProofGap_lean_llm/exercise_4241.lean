import Mathlib

set_option linter.style.longLine false

open scoped Real

noncomputable abbrev frac (x y : ℝ) : ℝ := x / y
noncomputable abbrev sqrtn (_n : ℝ) (x : ℝ) : ℝ := Real.sqrt x
axiom diff : (ℝ → ℝ) → ℝ
axiom ScalarCurveInt2 : Set (ℝ × ℝ) → (ℝ × ℝ → ℝ) → ℝ → ℝ
axiom DefInt : ℝ → ℝ → (ℝ → ℝ) → ℝ → ℝ

-- exercise: exercise_4241

theorem proof_gap_exercise_4241_1
  (C : Set (ℝ × ℝ)) (a b s t M : ℝ) (x y : ℝ → ℝ) (rho : ℝ × ℝ → ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a > 0) (hb : b ∈ (Set.univ : Set ℝ) ∧ b > 0)
  (hC : C = {p | ∃ t, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 2 * Real.pi ∧ p = (x t, y t)})
  (hx : ∀ t, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 2 * Real.pi → x t = a * Real.cos t)
  (hy : ∀ t, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 2 * Real.pi → y t = b * Real.sin t)
  (hrho : ∀ x y, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) → rho (x, y) = |y|)
  : M = ScalarCurveInt2 C (fun p => |p.2|) (diff (fun _ => s)) := by
  sorry

theorem proof_gap_exercise_4241_2
  (C : Set (ℝ × ℝ)) (a b s t M : ℝ) (x y : ℝ → ℝ) (rho : ℝ × ℝ → ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a > 0) (hb : b ∈ (Set.univ : Set ℝ) ∧ b > 0)
  (hM : M = ScalarCurveInt2 C (fun p => |p.2|) (diff (fun _ => s)))
  : ∀ t, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 2 * Real.pi →
      diff (fun _ => s) = sqrtn 2 (a ^ (2 : ℕ) * Real.sin t ^ (2 : ℕ) + b ^ (2 : ℕ) * Real.cos t ^ (2 : ℕ)) *
        diff (fun t => t) := by
  sorry

theorem proof_gap_exercise_4241_3
  (C : Set (ℝ × ℝ)) (a b s t M : ℝ) (x y : ℝ → ℝ) (rho : ℝ × ℝ → ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a > 0) (hb : b ∈ (Set.univ : Set ℝ) ∧ b > 0)
  (hds : ∀ t, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 2 * Real.pi →
      diff (fun _ => s) = sqrtn 2 (a ^ (2 : ℕ) * Real.sin t ^ (2 : ℕ) + b ^ (2 : ℕ) * Real.cos t ^ (2 : ℕ)) * diff (fun t => t))
  : a > b → ∃ eps, eps ∈ (Set.univ : Set ℝ) ∧ eps = frac (sqrtn 2 (a ^ (2 : ℕ) - b ^ (2 : ℕ))) a ∧
      (∀ t, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 2 * Real.pi →
        diff (fun _ => s) = a * sqrtn 2 (1 - eps ^ (2 : ℕ) * Real.cos t ^ (2 : ℕ)) * diff (fun t => t)) := by
  sorry

theorem proof_gap_exercise_4241_4
  (C : Set (ℝ × ℝ)) (a b s t M : ℝ) (x y : ℝ → ℝ) (rho : ℝ × ℝ → ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a > 0) (hb : b ∈ (Set.univ : Set ℝ) ∧ b > 0)
  (hcase : a > b → ∃ eps, eps ∈ (Set.univ : Set ℝ) ∧ eps = frac (sqrtn 2 (a ^ (2 : ℕ) - b ^ (2 : ℕ))) a ∧
      (∀ t, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 2 * Real.pi →
        diff (fun _ => s) = a * sqrtn 2 (1 - eps ^ (2 : ℕ) * Real.cos t ^ (2 : ℕ)) * diff (fun t => t)))
  : a > b → ∃ eps, eps ∈ (Set.univ : Set ℝ) ∧ eps = frac (sqrtn 2 (a ^ (2 : ℕ) - b ^ (2 : ℕ))) a ∧
      M = DefInt 0 Real.pi (fun t => a * b * Real.sin t * sqrtn 2 (1 - eps ^ (2 : ℕ) * Real.cos t ^ (2 : ℕ))) (diff (fun t => t)) +
          DefInt Real.pi (2 * Real.pi) (fun t => a * (-b) * Real.sin t * sqrtn 2 (1 - eps ^ (2 : ℕ) * Real.cos t ^ (2 : ℕ))) (diff (fun t => t)) := by
  sorry

theorem proof_gap_exercise_4241_5
  (C : Set (ℝ × ℝ)) (a b s t M : ℝ) (x y : ℝ → ℝ) (rho : ℝ × ℝ → ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a > 0) (hb : b ∈ (Set.univ : Set ℝ) ∧ b > 0)
  (hsplit : a > b → ∃ eps, eps ∈ (Set.univ : Set ℝ) ∧ eps = frac (sqrtn 2 (a ^ (2 : ℕ) - b ^ (2 : ℕ))) a ∧
      M = DefInt 0 Real.pi (fun t => a * b * Real.sin t * sqrtn 2 (1 - eps ^ (2 : ℕ) * Real.cos t ^ (2 : ℕ))) (diff (fun t => t)) +
          DefInt Real.pi (2 * Real.pi) (fun t => a * (-b) * Real.sin t * sqrtn 2 (1 - eps ^ (2 : ℕ) * Real.cos t ^ (2 : ℕ))) (diff (fun t => t)))
  : a > b → ∃ eps, eps ∈ (Set.univ : Set ℝ) ∧ eps = frac (sqrtn 2 (a ^ (2 : ℕ) - b ^ (2 : ℕ))) a ∧
      M = 4 * a * b * DefInt 0 1 (fun u => sqrtn 2 (1 - eps ^ (2 : ℕ) * u ^ (2 : ℕ))) (diff (fun u => u)) := by
  sorry

theorem proof_gap_exercise_4241_6
  (C : Set (ℝ × ℝ)) (a b s t M : ℝ) (x y : ℝ → ℝ) (rho : ℝ × ℝ → ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a > 0) (hb : b ∈ (Set.univ : Set ℝ) ∧ b > 0)
  (hreduced : a > b → ∃ eps, eps ∈ (Set.univ : Set ℝ) ∧ eps = frac (sqrtn 2 (a ^ (2 : ℕ) - b ^ (2 : ℕ))) a ∧
      M = 4 * a * b * DefInt 0 1 (fun u => sqrtn 2 (1 - eps ^ (2 : ℕ) * u ^ (2 : ℕ))) (diff (fun u => u)))
  : a > b → ∃ eps, eps ∈ (Set.univ : Set ℝ) ∧ eps = frac (sqrtn 2 (a ^ (2 : ℕ) - b ^ (2 : ℕ))) a ∧
      M = 2 * b ^ (2 : ℕ) + 2 * a * b * frac (Real.arcsin eps) eps := by
  sorry

theorem proof_gap_exercise_4241_7
  (C : Set (ℝ × ℝ)) (a b s t M : ℝ) (x y : ℝ → ℝ) (rho : ℝ × ℝ → ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a > 0) (hb : b ∈ (Set.univ : Set ℝ) ∧ b > 0)
  (hds : ∀ t, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 2 * Real.pi →
      diff (fun _ => s) = sqrtn 2 (a ^ (2 : ℕ) * Real.sin t ^ (2 : ℕ) + b ^ (2 : ℕ) * Real.cos t ^ (2 : ℕ)) * diff (fun t => t))
  : a < b → ∃ eps1, eps1 ∈ (Set.univ : Set ℝ) ∧ eps1 = frac (sqrtn 2 (b ^ (2 : ℕ) - a ^ (2 : ℕ))) a ∧
      (∀ t, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 2 * Real.pi →
        diff (fun _ => s) = a * sqrtn 2 (1 + eps1 ^ (2 : ℕ) * Real.cos t ^ (2 : ℕ)) * diff (fun t => t)) := by
  sorry

theorem proof_gap_exercise_4241_8
  (C : Set (ℝ × ℝ)) (a b s t M : ℝ) (x y : ℝ → ℝ) (rho : ℝ × ℝ → ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a > 0) (hb : b ∈ (Set.univ : Set ℝ) ∧ b > 0)
  (hcase : a < b → ∃ eps1, eps1 ∈ (Set.univ : Set ℝ) ∧ eps1 = frac (sqrtn 2 (b ^ (2 : ℕ) - a ^ (2 : ℕ))) a ∧
      (∀ t, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 2 * Real.pi →
        diff (fun _ => s) = a * sqrtn 2 (1 + eps1 ^ (2 : ℕ) * Real.cos t ^ (2 : ℕ)) * diff (fun t => t)))
  : a < b → ∃ eps1, eps1 ∈ (Set.univ : Set ℝ) ∧ eps1 = frac (sqrtn 2 (b ^ (2 : ℕ) - a ^ (2 : ℕ))) a ∧
      M = 4 * a * b * DefInt 0 1 (fun u => sqrtn 2 (1 + eps1 ^ (2 : ℕ) * u ^ (2 : ℕ))) (diff (fun u => u)) := by
  sorry

theorem proof_gap_exercise_4241_9
  (C : Set (ℝ × ℝ)) (a b s t M : ℝ) (x y : ℝ → ℝ) (rho : ℝ × ℝ → ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a > 0) (hb : b ∈ (Set.univ : Set ℝ) ∧ b > 0)
  (hreduced : a < b → ∃ eps1, eps1 ∈ (Set.univ : Set ℝ) ∧ eps1 = frac (sqrtn 2 (b ^ (2 : ℕ) - a ^ (2 : ℕ))) a ∧
      M = 4 * a * b * DefInt 0 1 (fun u => sqrtn 2 (1 + eps1 ^ (2 : ℕ) * u ^ (2 : ℕ))) (diff (fun u => u)))
  : a < b → ∃ eps1, eps1 ∈ (Set.univ : Set ℝ) ∧ eps1 = frac (sqrtn 2 (b ^ (2 : ℕ) - a ^ (2 : ℕ))) a ∧
      M = 2 * b ^ (2 : ℕ) + 2 * a * b * frac (Real.log (eps1 + sqrtn 2 (1 + eps1 ^ (2 : ℕ)))) eps1 := by
  sorry

theorem proof_gap_exercise_4241_10
  (C : Set (ℝ × ℝ)) (a b s t M : ℝ) (x y : ℝ → ℝ) (rho : ℝ × ℝ → ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a > 0) (hb : b ∈ (Set.univ : Set ℝ) ∧ b > 0)
  : a = b → ∀ t, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 2 * Real.pi →
      diff (fun _ => s) = a * diff (fun t => t) := by
  sorry

theorem proof_gap_exercise_4241_11
  (C : Set (ℝ × ℝ)) (a b s t M : ℝ) (x y : ℝ → ℝ) (rho : ℝ × ℝ → ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a > 0) (hb : b ∈ (Set.univ : Set ℝ) ∧ b > 0)
  (hcircle : a = b → ∀ t, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 2 * Real.pi →
      diff (fun _ => s) = a * diff (fun t => t))
  : a = b → M = DefInt 0 Real.pi (fun t => a ^ (2 : ℕ) * Real.sin t) (diff (fun t => t)) +
      DefInt Real.pi (2 * Real.pi) (fun t => (-a) * Real.sin t * a) (diff (fun t => t)) := by
  sorry

theorem proof_gap_exercise_4241_12
  (C : Set (ℝ × ℝ)) (a b s t M : ℝ) (x y : ℝ → ℝ) (rho : ℝ × ℝ → ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a > 0) (hb : b ∈ (Set.univ : Set ℝ) ∧ b > 0)
  (hcircleInt : a = b → M = DefInt 0 Real.pi (fun t => a ^ (2 : ℕ) * Real.sin t) (diff (fun t => t)) +
      DefInt Real.pi (2 * Real.pi) (fun t => (-a) * Real.sin t * a) (diff (fun t => t)))
  : a = b → M = 4 * a ^ (2 : ℕ) := by
  sorry

theorem proof_gap_exercise_4241_13
  (C : Set (ℝ × ℝ)) (a b s t M : ℝ) (x y : ℝ → ℝ) (rho : ℝ × ℝ → ℝ)
  (ha : a ∈ (Set.univ : Set ℝ) ∧ a > 0) (hb : b ∈ (Set.univ : Set ℝ) ∧ b > 0)
  (hgt : a > b → ∃ eps, eps ∈ (Set.univ : Set ℝ) ∧ eps = frac (sqrtn 2 (a ^ (2 : ℕ) - b ^ (2 : ℕ))) a ∧
      M = 2 * b ^ (2 : ℕ) + 2 * a * b * frac (Real.arcsin eps) eps)
  (hlt : a < b → ∃ eps1, eps1 ∈ (Set.univ : Set ℝ) ∧ eps1 = frac (sqrtn 2 (b ^ (2 : ℕ) - a ^ (2 : ℕ))) a ∧
      M = 2 * b ^ (2 : ℕ) + 2 * a * b * frac (Real.log (eps1 + sqrtn 2 (1 + eps1 ^ (2 : ℕ)))) eps1)
  (heq : a = b → M = 4 * a ^ (2 : ℕ))
  : M =
      (if a > b then
        2 * b ^ (2 : ℕ) + 2 * a * b *
          frac (Real.arcsin (frac (sqrtn 2 (a ^ (2 : ℕ) - b ^ (2 : ℕ))) a))
            (frac (sqrtn 2 (a ^ (2 : ℕ) - b ^ (2 : ℕ))) a)
      else if a < b then
        2 * b ^ (2 : ℕ) + 2 * a * b *
          frac (Real.log (frac (sqrtn 2 (b ^ (2 : ℕ) - a ^ (2 : ℕ))) a +
            sqrtn 2 (1 + (frac (sqrtn 2 (b ^ (2 : ℕ) - a ^ (2 : ℕ))) a) ^ (2 : ℕ))))
            (frac (sqrtn 2 (b ^ (2 : ℕ) - a ^ (2 : ℕ))) a)
      else
        4 * a ^ (2 : ℕ)) := by
  sorry
