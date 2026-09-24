import Mathlib

/- exercise_3331, gaps 1-4. -/

noncomputable section

def DiffableFunc (φ : ℝ → ℝ) : Prop := ContDiff ℝ 1 φ

noncomputable def partialDeriv (z : ℝ → ℝ → ℝ) (coord order : Nat) : ℝ → ℝ → ℝ :=
  Nat.iterate
    (fun g x y => fderiv ℝ (fun p : ℝ × ℝ => g p.1 p.2) (x, y)
      (if coord = 1 then (1, 0) else (0, 1)))
    order z

noncomputable def compDeriv3331 (φ : ℝ → ℝ) (_u : ℝ → ℝ → ℝ) (order : Nat) : ℝ → ℝ :=
  Nat.iterate deriv order φ

theorem proof_gap_exercise_3331_1
    (z : ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hz : ∀ x y : ℝ, z x y = x + φ (x * y))
    (hφ : DiffableFunc φ) :
    ∀ x : ℝ, ∀ y : ℝ,
      partialDeriv z 1 1 x y =
        1 + y * compDeriv3331 φ (fun x y => x * y) 1 (x * y) := by
  sorry

theorem proof_gap_exercise_3331_2
    (z : ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hz : ∀ x y : ℝ, z x y = x + φ (x * y))
    (hφ : DiffableFunc φ)
    (h1 : ∀ x : ℝ, ∀ y : ℝ,
      partialDeriv z 1 1 x y =
        1 + y * compDeriv3331 φ (fun x y => x * y) 1 (x * y)) :
    ∀ x : ℝ, ∀ y : ℝ,
      partialDeriv z 2 1 x y =
        x * compDeriv3331 φ (fun x y => x * y) 1 (x * y) := by
  sorry

theorem proof_gap_exercise_3331_3
    (z : ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hz : ∀ x y : ℝ, z x y = x + φ (x * y))
    (hφ : DiffableFunc φ)
    (h1 : ∀ x : ℝ, ∀ y : ℝ,
      partialDeriv z 1 1 x y =
        1 + y * compDeriv3331 φ (fun x y => x * y) 1 (x * y))
    (h2 : ∀ x : ℝ, ∀ y : ℝ,
      partialDeriv z 2 1 x y =
        x * compDeriv3331 φ (fun x y => x * y) 1 (x * y)) :
    ∀ x : ℝ, ∀ y : ℝ,
      x * partialDeriv z 1 1 x y - y * partialDeriv z 2 1 x y = x := by
  sorry

theorem proof_gap_exercise_3331_4
    (z : ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hz : ∀ x y : ℝ, z x y = x + φ (x * y))
    (hφ : DiffableFunc φ)
    (h1 : ∀ x : ℝ, ∀ y : ℝ,
      partialDeriv z 1 1 x y =
        1 + y * compDeriv3331 φ (fun x y => x * y) 1 (x * y))
    (h2 : ∀ x : ℝ, ∀ y : ℝ,
      partialDeriv z 2 1 x y =
        x * compDeriv3331 φ (fun x y => x * y) 1 (x * y))
    (h3 : ∀ x : ℝ, ∀ y : ℝ,
      x * partialDeriv z 1 1 x y - y * partialDeriv z 2 1 x y = x) :
    ∀ x : ℝ, ∀ y : ℝ,
      x * partialDeriv z 1 1 x y - y * partialDeriv z 2 1 x y = x := by
  sorry
