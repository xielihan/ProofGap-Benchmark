import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat

-- exercise: exercise_3303

noncomputable abbrev P3 := ℝ × ℝ × ℝ

noncomputable def pd1 (f : P3 -> ℝ) (i : Fin 3) (p : P3) : ℝ :=
  match i with
  | ⟨0, _⟩ => iteratedDeriv 1 (fun t : ℝ => f (t, p.2.1, p.2.2)) p.1
  | ⟨1, _⟩ => iteratedDeriv 1 (fun t : ℝ => f (p.1, t, p.2.2)) p.2.1
  | _ => iteratedDeriv 1 (fun t : ℝ => f (p.1, p.2.1, t)) p.2.2

noncomputable def weightedRadialOp (a b c dx dy dz : ℝ) (g : P3 -> ℝ) : P3 -> ℝ :=
  fun p => a * dx * pd1 g ⟨0, by decide⟩ p +
    b * dy * pd1 g ⟨1, by decide⟩ p +
    c * dz * pd1 g ⟨2, by decide⟩ p

noncomputable def iterateOp (n : ℕ) (T : (P3 -> ℝ) -> P3 -> ℝ) (g : P3 -> ℝ) : P3 -> ℝ :=
  Nat.iterate T n g

theorem proof_gap_exercise_3303_1
  (a b c x y z ξ η ζ dx dy dz : ℝ)
  (f u : P3 -> ℝ)
  (D : Set P3)
  (n : ℕ)
  (hn : 0 < n)
  (hD : D ⊆ Set.univ)
  (hp : (a * x, b * y, c * z) ∈ D)
  (hf : ContDiffOn ℝ (n : ℕ∞) f D)
  (hu : ∀ x y z : ℝ, (a * x, b * y, c * z) ∈ D -> u (x, y, z) = f (a * x, b * y, c * z))
  (hξ : ξ = a * x)
  (hη : η = b * y)
  (hζ : ζ = c * z)
  : iterateOp n (weightedRadialOp a b c dx dy dz) f (ξ, η, ζ) =
      iterateOp n (weightedRadialOp a b c dx dy dz) f (a * x, b * y, c * z) := by
  sorry
