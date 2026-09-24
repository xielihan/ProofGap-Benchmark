import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat

-- exercise: exercise_3304

noncomputable abbrev P3 := ℝ × ℝ × ℝ

noncomputable def pd1 (f : P3 -> ℝ) (i : Fin 3) (p : P3) : ℝ :=
  match i with
  | ⟨0, _⟩ => iteratedDeriv 1 (fun t : ℝ => f (t, p.2.1, p.2.2)) p.1
  | ⟨1, _⟩ => iteratedDeriv 1 (fun t : ℝ => f (p.1, t, p.2.2)) p.2.1
  | _ => iteratedDeriv 1 (fun t : ℝ => f (p.1, p.2.1, t)) p.2.2

noncomputable def affineOpFirst
    (a1 b1 c1 a2 b2 c2 a3 b3 c3 dx dy dz : ℝ) (g : P3 -> ℝ) : P3 -> ℝ :=
  fun p =>
    (a1 * dx + b1 * dy + c1 * dz) * pd1 g ⟨0, by decide⟩ p +
    (a2 * dx + b2 * dy + c2 * dz) * pd1 g ⟨1, by decide⟩ p +
    (a3 * dx + b3 * dy + c3 * dz) * pd1 g ⟨2, by decide⟩ p

noncomputable def affineOpCollected
    (a1 b1 c1 a2 b2 c2 a3 b3 c3 dx dy dz : ℝ) (g : P3 -> ℝ) : P3 -> ℝ :=
  fun p =>
    dx * (a1 * pd1 g ⟨0, by decide⟩ p + a2 * pd1 g ⟨1, by decide⟩ p + a3 * pd1 g ⟨2, by decide⟩ p) +
    dy * (b1 * pd1 g ⟨0, by decide⟩ p + b2 * pd1 g ⟨1, by decide⟩ p + b3 * pd1 g ⟨2, by decide⟩ p) +
    dz * (c1 * pd1 g ⟨0, by decide⟩ p + c2 * pd1 g ⟨1, by decide⟩ p + c3 * pd1 g ⟨2, by decide⟩ p)

noncomputable def iterateOp (n : ℕ) (T : (P3 -> ℝ) -> P3 -> ℝ) (g : P3 -> ℝ) : P3 -> ℝ :=
  Nat.iterate T n g

theorem proof_gap_exercise_3304_1
  (a1 b1 c1 a2 b2 c2 a3 b3 c3 x y z ξ η ζ dx dy dz : ℝ)
  (f u : P3 -> ℝ)
  (n : ℕ)
  (hn : 0 < n)
  (hf : ContDiff ℝ (n : ℕ∞) f)
  (hu : ∀ x y z : ℝ,
    u (x, y, z) =
      f (a1 * x + b1 * y + c1 * z, a2 * x + b2 * y + c2 * z, a3 * x + b3 * y + c3 * z))
  (hξ : ξ = a1 * x + b1 * y + c1 * z)
  (hη : η = a2 * x + b2 * y + c2 * z)
  (hζ : ζ = a3 * x + b3 * y + c3 * z)
  : iterateOp n (affineOpFirst a1 b1 c1 a2 b2 c2 a3 b3 c3 dx dy dz) f (ξ, η, ζ) =
      iterateOp n (affineOpFirst a1 b1 c1 a2 b2 c2 a3 b3 c3 dx dy dz) f
        (a1 * x + b1 * y + c1 * z, a2 * x + b2 * y + c2 * z, a3 * x + b3 * y + c3 * z) := by
  sorry

theorem proof_gap_exercise_3304_2
  (a1 b1 c1 a2 b2 c2 a3 b3 c3 x y z ξ η ζ dx dy dz : ℝ)
  (f u : P3 -> ℝ)
  (n : ℕ)
  (hn : 0 < n)
  (hf : ContDiff ℝ (n : ℕ∞) f)
  (hu : ∀ x y z : ℝ,
    u (x, y, z) =
      f (a1 * x + b1 * y + c1 * z, a2 * x + b2 * y + c2 * z, a3 * x + b3 * y + c3 * z))
  (hξ : ξ = a1 * x + b1 * y + c1 * z)
  (hη : η = a2 * x + b2 * y + c2 * z)
  (hζ : ζ = a3 * x + b3 * y + c3 * z)
  (hfirst : iterateOp n (affineOpFirst a1 b1 c1 a2 b2 c2 a3 b3 c3 dx dy dz) f (ξ, η, ζ) =
      iterateOp n (affineOpFirst a1 b1 c1 a2 b2 c2 a3 b3 c3 dx dy dz) f
        (a1 * x + b1 * y + c1 * z, a2 * x + b2 * y + c2 * z, a3 * x + b3 * y + c3 * z))
  : iterateOp n (affineOpCollected a1 b1 c1 a2 b2 c2 a3 b3 c3 dx dy dz) f (ξ, η, ζ) =
      iterateOp n (affineOpCollected a1 b1 c1 a2 b2 c2 a3 b3 c3 dx dy dz) f
        (a1 * x + b1 * y + c1 * z, a2 * x + b2 * y + c2 * z, a3 * x + b3 * y + c3 * z) := by
  sorry
