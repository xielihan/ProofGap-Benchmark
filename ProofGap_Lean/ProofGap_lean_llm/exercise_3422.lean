import Mathlib

set_option linter.style.longLine false

open scoped Topology

namespace exercise_3422

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable abbrev pd2 (Phi : ℝ -> ℝ -> ℝ) (i : Nat) (u v : ℝ) : ℝ :=
  match i with
  | 1 => iteratedDeriv 1 (fun s => Phi s v) u
  | _ => iteratedDeriv 1 (fun s => Phi u s) v

noncomputable abbrev zₓ (z : ℝ -> ℝ -> ℝ) (x y : ℝ) : ℝ := iteratedDeriv 1 (fun s => z s y) x
noncomputable abbrev zᵧ (z : ℝ -> ℝ -> ℝ) (x y : ℝ) : ℝ := iteratedDeriv 1 (fun s => z x s) y

noncomputable abbrev dot3 (p q : ℝ × ℝ × ℝ) : ℝ :=
  p.1 * q.1 + p.2.1 * q.2.1 + p.2.2 * q.2.2

def lineThrough (x₀ y₀ z₀ x₂ y₂ z₂ : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {P | ((P.1 - x₀) /. (x₂ - x₀)) = ((P.2.1 - y₀) /. (y₂ - y₀)) ∧
       ((P.2.1 - y₀) /. (y₂ - y₀)) = ((P.2.2 - z₀) /. (z₂ - z₀))}

def graphSurface (Phi z : ℝ -> ℝ -> ℝ) (x₀ y₀ z₀ : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {P | ∃ x y : ℝ, P = (x, y, z x y) ∧ z x y ≠ z₀ ∧
    Phi ((x - x₀) /. (z x y - z₀)) ((y - y₀) /. (z x y - z₀)) = 0}

noncomputable abbrev den (Phi z : ℝ -> ℝ -> ℝ) (x₀ y₀ z₀ x y : ℝ) : ℝ :=
  (x - x₀) * pd2 Phi 1 ((x - x₀) /. (z x y - z₀)) ((y - y₀) /. (z x y - z₀)) +
    (y - y₀) * pd2 Phi 2 ((x - x₀) /. (z x y - z₀)) ((y - y₀) /. (z x y - z₀))

variable
  (Phi z : ℝ -> ℝ -> ℝ) (x₀ y₀ z₀ : ℝ)
  (Surface₂ : Set (ℝ × ℝ × ℝ))
  (ConeWithVertex : ℝ × ℝ × ℝ -> Set (ℝ × ℝ × ℝ)) (P₀ : ℝ × ℝ × ℝ)
  (hP₀ : P₀ = (x₀, y₀, z₀))
  (hSurface : Surface₂ = graphSurface Phi z x₀ y₀ z₀)
  (hPhi : Differentiable ℝ (fun p : ℝ × ℝ => Phi p.1 p.2))
  (hzero : ∀ x y : ℝ, z x y ≠ z₀ ->
    Phi ((x - x₀) /. (z x y - z₀)) ((y - y₀) /. (z x y - z₀)) = 0)
  (hzdiff : ∀ x y : ℝ, DifferentiableAt ℝ (fun p : ℝ × ℝ => z p.1 p.2) (x, y))

theorem proof_gap_exercise_3422_1 :
    ∀ x y : ℝ, z x y ≠ z₀ ->
      pd2 Phi 1 ((x - x₀) /. (z x y - z₀)) ((y - y₀) /. (z x y - z₀)) *
          ((z x y - z₀ - (x - x₀) * zₓ z x y) /. ((z x y - z₀) ^ 2)) -
        pd2 Phi 2 ((x - x₀) /. (z x y - z₀)) ((y - y₀) /. (z x y - z₀)) *
          (((y - y₀) * zₓ z x y) /. ((z x y - z₀) ^ 2)) = 0 := by
  sorry

theorem proof_gap_exercise_3422_2
    (h12 : ∀ x y : ℝ, z x y ≠ z₀ ->
      pd2 Phi 1 ((x - x₀) /. (z x y - z₀)) ((y - y₀) /. (z x y - z₀)) *
          ((z x y - z₀ - (x - x₀) * zₓ z x y) /. ((z x y - z₀) ^ 2)) -
        pd2 Phi 2 ((x - x₀) /. (z x y - z₀)) ((y - y₀) /. (z x y - z₀)) *
          (((y - y₀) * zₓ z x y) /. ((z x y - z₀) ^ 2)) = 0) :
    ∀ x y : ℝ, z x y ≠ z₀ ->
      -pd2 Phi 1 ((x - x₀) /. (z x y - z₀)) ((y - y₀) /. (z x y - z₀)) *
          (((x - x₀) * zᵧ z x y) /. ((z x y - z₀) ^ 2)) +
        pd2 Phi 2 ((x - x₀) /. (z x y - z₀)) ((y - y₀) /. (z x y - z₀)) *
          ((z x y - z₀ - (y - y₀) * zᵧ z x y) /. ((z x y - z₀) ^ 2)) = 0 := by
  sorry

theorem proof_gap_exercise_3422_3
    (h12 : ∀ x y : ℝ, z x y ≠ z₀ ->
      pd2 Phi 1 ((x - x₀) /. (z x y - z₀)) ((y - y₀) /. (z x y - z₀)) *
          ((z x y - z₀ - (x - x₀) * zₓ z x y) /. ((z x y - z₀) ^ 2)) -
        pd2 Phi 2 ((x - x₀) /. (z x y - z₀)) ((y - y₀) /. (z x y - z₀)) *
          (((y - y₀) * zₓ z x y) /. ((z x y - z₀) ^ 2)) = 0)
    (h13 : ∀ x y : ℝ, z x y ≠ z₀ ->
      -pd2 Phi 1 ((x - x₀) /. (z x y - z₀)) ((y - y₀) /. (z x y - z₀)) *
          (((x - x₀) * zᵧ z x y) /. ((z x y - z₀) ^ 2)) +
        pd2 Phi 2 ((x - x₀) /. (z x y - z₀)) ((y - y₀) /. (z x y - z₀)) *
          ((z x y - z₀ - (y - y₀) * zᵧ z x y) /. ((z x y - z₀) ^ 2)) = 0) :
    ∀ x y : ℝ, z x y ≠ z₀ -> den Phi z x₀ y₀ z₀ x y ≠ 0 ->
      zₓ z x y =
        ((z x y - z₀) * pd2 Phi 1 ((x - x₀) /. (z x y - z₀)) ((y - y₀) /. (z x y - z₀))) /.
          den Phi z x₀ y₀ z₀ x y := by
  sorry

theorem proof_gap_exercise_3422_4
    (h14 : ∀ x y : ℝ, z x y ≠ z₀ -> den Phi z x₀ y₀ z₀ x y ≠ 0 ->
      zₓ z x y =
        ((z x y - z₀) * pd2 Phi 1 ((x - x₀) /. (z x y - z₀)) ((y - y₀) /. (z x y - z₀))) /.
          den Phi z x₀ y₀ z₀ x y) :
    ∀ x y : ℝ, z x y ≠ z₀ -> den Phi z x₀ y₀ z₀ x y ≠ 0 ->
      zᵧ z x y =
        ((z x y - z₀) * pd2 Phi 2 ((x - x₀) /. (z x y - z₀)) ((y - y₀) /. (z x y - z₀))) /.
          den Phi z x₀ y₀ z₀ x y := by
  sorry

theorem proof_gap_exercise_3422_5
    (h14 : ∀ x y : ℝ, z x y ≠ z₀ -> den Phi z x₀ y₀ z₀ x y ≠ 0 ->
      zₓ z x y =
        ((z x y - z₀) * pd2 Phi 1 ((x - x₀) /. (z x y - z₀)) ((y - y₀) /. (z x y - z₀))) /.
          den Phi z x₀ y₀ z₀ x y)
    (h15 : ∀ x y : ℝ, z x y ≠ z₀ -> den Phi z x₀ y₀ z₀ x y ≠ 0 ->
      zᵧ z x y =
        ((z x y - z₀) * pd2 Phi 2 ((x - x₀) /. (z x y - z₀)) ((y - y₀) /. (z x y - z₀))) /.
          den Phi z x₀ y₀ z₀ x y) :
    ∀ x y : ℝ, z x y ≠ z₀ -> den Phi z x₀ y₀ z₀ x y ≠ 0 ->
      (x - x₀) * zₓ z x y + (y - y₀) * zᵧ z x y = z x y - z₀ := by
  sorry

theorem proof_gap_exercise_3422_6
    (h16 : ∀ x y : ℝ, z x y ≠ z₀ -> den Phi z x₀ y₀ z₀ x y ≠ 0 ->
      (x - x₀) * zₓ z x y + (y - y₀) * zᵧ z x y = z x y - z₀) :
    ∀ x₂ y₂ z₂ : ℝ, ∀ P₂ : ℝ × ℝ × ℝ, P₂ = (x₂, y₂, z₂) ->
      dot3 (zₓ z x₂ y₂, zᵧ z x₂ y₂, -1) (x₂ - x₀, y₂ - y₀, z₂ - z₀) = 0 := by
  sorry

theorem proof_gap_exercise_3422_7
    (h17 : ∀ x₂ y₂ z₂ : ℝ, ∀ P₂ : ℝ × ℝ × ℝ, P₂ = (x₂, y₂, z₂) ->
      dot3 (zₓ z x₂ y₂, zᵧ z x₂ y₂, -1) (x₂ - x₀, y₂ - y₀, z₂ - z₀) = 0) :
    ∀ x₂ y₂ z₂ x y : ℝ, ∀ P₂ : ℝ × ℝ × ℝ, P₂ = (x₂, y₂, z₂) ->
      ∀ P : ℝ × ℝ × ℝ, P ∈ lineThrough x₀ y₀ z₀ x₂ y₂ z₂ ->
        Phi ((P.1 - x₀) /. (P.2.2 - z₀)) ((P.2.1 - y₀) /. (P.2.2 - z₀)) = 0 := by
  sorry

theorem proof_gap_exercise_3422_8
    (h18 : ∀ x₂ y₂ z₂ x y : ℝ, ∀ P₂ : ℝ × ℝ × ℝ, P₂ = (x₂, y₂, z₂) ->
      ∀ P : ℝ × ℝ × ℝ, P ∈ lineThrough x₀ y₀ z₀ x₂ y₂ z₂ ->
        Phi ((P.1 - x₀) /. (P.2.2 - z₀)) ((P.2.1 - y₀) /. (P.2.2 - z₀)) = 0) :
    Surface₂ = ConeWithVertex P₀ := by
  sorry

theorem proof_gap_exercise_3422_9
    (h19 : Surface₂ = ConeWithVertex P₀) :
    ∀ x y : ℝ, z x y ≠ z₀ ->
      (x - x₀) * zₓ z x y + (y - y₀) * zᵧ z x y = z x y - z₀ := by
  sorry

end exercise_3422
