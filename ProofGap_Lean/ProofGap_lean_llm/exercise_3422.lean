import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology

namespace exercise_3422

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable abbrev pd2 (Φ : ℝ -> ℝ -> ℝ) (i : Nat) (u v : ℝ) : ℝ :=
  match i with
  | 1 => iteratedDeriv 1 (fun s => Φ s v) u
  | _ => iteratedDeriv 1 (fun s => Φ u s) v

noncomputable abbrev zₓ (z : ℝ -> ℝ -> ℝ) (x y : ℝ) : ℝ := iteratedDeriv 1 (fun s => z s y) x
noncomputable abbrev zᵧ (z : ℝ -> ℝ -> ℝ) (x y : ℝ) : ℝ := iteratedDeriv 1 (fun s => z x s) y
noncomputable abbrev dot3 (p q : ℝ × ℝ × ℝ) : ℝ := p.1 * q.1 + p.2.1 * q.2.1 + p.2.2 * q.2.2

def lineThrough (x₀ y₀ z₀ x₂ y₂ z₂ : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {P | ((P.1 - x₀) /. (x₂ - x₀)) = ((P.2.1 - y₀) /. (y₂ - y₀)) ∧
       ((P.2.1 - y₀) /. (y₂ - y₀)) = ((P.2.2 - z₀) /. (z₂ - z₀))}

variable
  (Φ : ℝ -> ℝ -> ℝ) (z : ℝ -> ℝ -> ℝ)
  (x₀ y₀ z₀ : ℝ) (Surface₂ : Set (ℝ × ℝ × ℝ))
  (ConeWithVertex : ℝ × ℝ × ℝ -> Set (ℝ × ℝ × ℝ)) (P₀ : ℝ × ℝ × ℝ)
  (hΦ : Differentiable ℝ (fun p : ℝ × ℝ => Φ p.1 p.2))
  (hzero : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ z x y ≠ z₀ -> Φ ((x - x₀) /. (z x y - z₀)) ((y - y₀) /. (z x y - z₀)) = 0)
  (hzdiff : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) -> DifferentiableAt ℝ (fun p : ℝ × ℝ => z p.1 p.2) (x, y))

noncomputable abbrev den (x y : ℝ) : ℝ :=
  (x - x₀) * pd2 Φ 1 ((x - x₀) /. (z x y - z₀)) ((y - y₀) /. (z x y - z₀)) +
    (y - y₀) * pd2 Φ 2 ((x - x₀) /. (z x y - z₀)) ((y - y₀) /. (z x y - z₀))

-- Exercise 3422, gap 1
theorem proof_gap_exercise_3422_1 :
    ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ->
      ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ z x y ≠ z₀ ->
        pd2 Φ 1 ((x - x₀) /. (z x y - z₀)) ((y - y₀) /. (z x y - z₀)) *
          ((z x y - z₀ - (x - x₀) * zₓ z x y) /. ((z x y - z₀) ^ 2)) -
        pd2 Φ 2 ((x - x₀) /. (z x y - z₀)) ((y - y₀) /. (z x y - z₀)) *
          (((y - y₀) * zₓ z x y) /. ((z x y - z₀) ^ 2)) = 0 := by
  sorry

-- Exercise 3422, gap 2
theorem proof_gap_exercise_3422_2
    (h12 : True) :
    ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ->
      ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ z x y ≠ z₀ ->
        -pd2 Φ 1 ((x - x₀) /. (z x y - z₀)) ((y - y₀) /. (z x y - z₀)) *
          (((x - x₀) * zᵧ z x y) /. ((z x y - z₀) ^ 2)) +
        pd2 Φ 2 ((x - x₀) /. (z x y - z₀)) ((y - y₀) /. (z x y - z₀)) *
          ((z x y - z₀ - (y - y₀) * zᵧ z x y) /. ((z x y - z₀) ^ 2)) = 0 := by
  sorry

-- Exercise 3422, gap 3
theorem proof_gap_exercise_3422_3
    (h12 h13 : True) :
    ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ->
      ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ z x y ≠ z₀ ∧ den Φ z x₀ y₀ z₀ x y ≠ 0 ->
        zₓ z x y = ((z x y - z₀) * pd2 Φ 1 ((x - x₀) /. (z x y - z₀)) ((y - y₀) /. (z x y - z₀))) /. den Φ z x₀ y₀ z₀ x y := by
  sorry

-- Exercise 3422, gap 4
theorem proof_gap_exercise_3422_4
    (h14 : True) :
    ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ->
      ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ z x y ≠ z₀ ∧ den Φ z x₀ y₀ z₀ x y ≠ 0 ->
        zᵧ z x y = ((z x y - z₀) * pd2 Φ 2 ((x - x₀) /. (z x y - z₀)) ((y - y₀) /. (z x y - z₀))) /. den Φ z x₀ y₀ z₀ x y := by
  sorry

-- Exercise 3422, gap 5
theorem proof_gap_exercise_3422_5
    (h14 h15 : True) :
    ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ->
      ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ z x y ≠ z₀ ∧ den Φ z x₀ y₀ z₀ x y ≠ 0 ->
        (x - x₀) * zₓ z x y + (y - y₀) * zᵧ z x y = z x y - z₀ := by
  sorry

-- Exercise 3422, gap 6
theorem proof_gap_exercise_3422_6
    (h16 : True) :
    ∀ x₂ y₂ z₂ : ℝ, x₂ ∈ (Set.univ : Set ℝ) ∧ y₂ ∈ (Set.univ : Set ℝ) ∧ z₂ ∈ (Set.univ : Set ℝ) ->
      ∀ P₂ : ℝ × ℝ × ℝ, P₂ ∈ (Set.univ : Set (ℝ × ℝ × ℝ)) ∧ P₂ = (x₂, y₂, z₂) ->
        dot3 (zₓ z x₂ y₂, zᵧ z x₂ y₂, -1) (x₂ - x₀, y₂ - y₀, z₂ - z₀) = 0 := by
  sorry

-- Exercise 3422, gap 7
theorem proof_gap_exercise_3422_7
    (h17 : True) :
    ∀ x₂ y₂ z₂ x y : ℝ,
      x₂ ∈ (Set.univ : Set ℝ) ∧ y₂ ∈ (Set.univ : Set ℝ) ∧ z₂ ∈ (Set.univ : Set ℝ) ∧ x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ->
        ∀ P₂ : ℝ × ℝ × ℝ, P₂ ∈ (Set.univ : Set (ℝ × ℝ × ℝ)) ∧ P₂ = (x₂, y₂, z₂) ->
          ∀ P : ℝ × ℝ × ℝ, P ∈ (Set.univ : Set (ℝ × ℝ × ℝ)) ∧ P ∈ lineThrough x₀ y₀ z₀ x₂ y₂ z₂ ->
            Φ ((P.1 - x₀) /. (P.2.2 - z₀)) ((P.2.1 - y₀) /. (P.2.2 - z₀)) = 0 := by
  sorry

-- Exercise 3422, gap 8
theorem proof_gap_exercise_3422_8
    (h18 : True) :
    Surface₂ = ConeWithVertex P₀ := by
  sorry

-- Exercise 3422, gap 9
theorem proof_gap_exercise_3422_9
    (h19 : Surface₂ = ConeWithVertex P₀) :
    ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ z x y ≠ z₀ ->
      (x - x₀) * zₓ z x y + (y - y₀) * zᵧ z x y = z x y - z₀ := by
  sorry

end exercise_3422
