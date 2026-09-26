import Mathlib

set_option linter.style.longLine false

open scoped Topology

namespace exercise_3421

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable abbrev pd2 (Phi : ℝ -> ℝ -> ℝ) (i : Nat) (u v : ℝ) : ℝ :=
  match i with
  | 1 => iteratedDeriv 1 (fun s => Phi s v) u
  | _ => iteratedDeriv 1 (fun s => Phi u s) v

noncomputable abbrev zₓ (z : ℝ -> ℝ -> ℝ) (x y : ℝ) : ℝ :=
  iteratedDeriv 1 (fun s => z s y) x

noncomputable abbrev zᵧ (z : ℝ -> ℝ -> ℝ) (x y : ℝ) : ℝ :=
  iteratedDeriv 1 (fun s => z x s) y

noncomputable abbrev dot3 (p q : ℝ × ℝ × ℝ) : ℝ :=
  p.1 * q.1 + p.2.1 * q.2.1 + p.2.2 * q.2.2

def surface (Phi z : ℝ -> ℝ -> ℝ) (a b : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {P | ∃ x y : ℝ, P = (x, y, z x y) ∧ Phi (x - a * z x y) (y - b * z x y) = 0}

def ruledLine (a b : ℝ) (z : ℝ -> ℝ -> ℝ) (x₁ y₁ : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {P | ∃ l : ℝ, P = (x₁ + a * l, y₁ + b * l, z x₁ y₁ + l)}

variable
  (Phi z : ℝ -> ℝ -> ℝ) (a b : ℝ) (S : Set (ℝ × ℝ × ℝ))
  (hPhi : Differentiable ℝ (fun p : ℝ × ℝ => Phi p.1 p.2))
  (hzero : ∀ x y : ℝ, Phi (x - a * z x y) (y - b * z x y) = 0)
  (hden : ∀ x y : ℝ,
    a * pd2 Phi 1 (x - a * z x y) (y - b * z x y) +
      b * pd2 Phi 2 (x - a * z x y) (y - b * z x y) ≠ 0)
  (hSdef : S = surface Phi z a b)

theorem proof_gap_exercise_3421_1 :
    ∀ x y : ℝ,
      pd2 Phi 1 (x - a * z x y) (y - b * z x y) * (1 - a * zₓ z x y) -
        b * pd2 Phi 2 (x - a * z x y) (y - b * z x y) * zₓ z x y = 0 := by
  sorry

theorem proof_gap_exercise_3421_2
    (h10 : ∀ x y : ℝ,
      pd2 Phi 1 (x - a * z x y) (y - b * z x y) * (1 - a * zₓ z x y) -
        b * pd2 Phi 2 (x - a * z x y) (y - b * z x y) * zₓ z x y = 0) :
    ∀ x y : ℝ,
      -a * pd2 Phi 1 (x - a * z x y) (y - b * z x y) * zᵧ z x y +
        pd2 Phi 2 (x - a * z x y) (y - b * z x y) * (1 - b * zᵧ z x y) = 0 := by
  sorry

theorem proof_gap_exercise_3421_3
    (h10 : ∀ x y : ℝ,
      pd2 Phi 1 (x - a * z x y) (y - b * z x y) * (1 - a * zₓ z x y) -
        b * pd2 Phi 2 (x - a * z x y) (y - b * z x y) * zₓ z x y = 0)
    (h11 : ∀ x y : ℝ,
      -a * pd2 Phi 1 (x - a * z x y) (y - b * z x y) * zᵧ z x y +
        pd2 Phi 2 (x - a * z x y) (y - b * z x y) * (1 - b * zᵧ z x y) = 0) :
    ∀ x y : ℝ,
      zₓ z x y = pd2 Phi 1 (x - a * z x y) (y - b * z x y) /.
        (a * pd2 Phi 1 (x - a * z x y) (y - b * z x y) +
          b * pd2 Phi 2 (x - a * z x y) (y - b * z x y)) := by
  sorry

theorem proof_gap_exercise_3421_4
    (h12 : ∀ x y : ℝ,
      zₓ z x y = pd2 Phi 1 (x - a * z x y) (y - b * z x y) /.
        (a * pd2 Phi 1 (x - a * z x y) (y - b * z x y) +
          b * pd2 Phi 2 (x - a * z x y) (y - b * z x y))) :
    ∀ x y : ℝ,
      zᵧ z x y = pd2 Phi 2 (x - a * z x y) (y - b * z x y) /.
        (a * pd2 Phi 1 (x - a * z x y) (y - b * z x y) +
          b * pd2 Phi 2 (x - a * z x y) (y - b * z x y)) := by
  sorry

theorem proof_gap_exercise_3421_5
    (h12 : ∀ x y : ℝ,
      zₓ z x y = pd2 Phi 1 (x - a * z x y) (y - b * z x y) /.
        (a * pd2 Phi 1 (x - a * z x y) (y - b * z x y) +
          b * pd2 Phi 2 (x - a * z x y) (y - b * z x y)))
    (h13 : ∀ x y : ℝ,
      zᵧ z x y = pd2 Phi 2 (x - a * z x y) (y - b * z x y) /.
        (a * pd2 Phi 1 (x - a * z x y) (y - b * z x y) +
          b * pd2 Phi 2 (x - a * z x y) (y - b * z x y))) :
    ∀ x y : ℝ, a * zₓ z x y + b * zᵧ z x y = 1 := by
  sorry

theorem proof_gap_exercise_3421_6
    (h14 : ∀ x y : ℝ, a * zₓ z x y + b * zᵧ z x y = 1) :
    ∀ x₁ y₁ : ℝ, (x₁, y₁, z x₁ y₁) ∈ S ->
      dot3 (zₓ z x₁ y₁, zᵧ z x₁ y₁, -1) (a, b, 1) = 0 := by
  sorry

theorem proof_gap_exercise_3421_7
    (h15 : ∀ x₁ y₁ : ℝ, (x₁, y₁, z x₁ y₁) ∈ S ->
      dot3 (zₓ z x₁ y₁, zᵧ z x₁ y₁, -1) (a, b, 1) = 0) :
    ∀ x₁ y₁ : ℝ, (x₁, y₁, z x₁ y₁) ∈ S ->
      ∀ l : ℝ,
        Phi (x₁ + a * l - a * (z x₁ y₁ + l)) (y₁ + b * l - b * (z x₁ y₁ + l)) =
          Phi (x₁ - a * z x₁ y₁) (y₁ - b * z x₁ y₁) ∧
        Phi (x₁ - a * z x₁ y₁) (y₁ - b * z x₁ y₁) = 0 := by
  sorry

theorem proof_gap_exercise_3421_8
    (h16 : ∀ x₁ y₁ : ℝ, (x₁, y₁, z x₁ y₁) ∈ S -> ∀ l : ℝ,
      Phi (x₁ + a * l - a * (z x₁ y₁ + l)) (y₁ + b * l - b * (z x₁ y₁ + l)) =
        Phi (x₁ - a * z x₁ y₁) (y₁ - b * z x₁ y₁) ∧
      Phi (x₁ - a * z x₁ y₁) (y₁ - b * z x₁ y₁) = 0) :
    ∀ x₁ y₁ : ℝ, (x₁, y₁, z x₁ y₁) ∈ S -> ruledLine a b z x₁ y₁ ⊆ S := by
  sorry

theorem proof_gap_exercise_3421_9
    (h17 : ∀ x₁ y₁ : ℝ, (x₁, y₁, z x₁ y₁) ∈ S -> ruledLine a b z x₁ y₁ ⊆ S) :
    ∀ x y : ℝ, a * zₓ z x y + b * zᵧ z x y = 1 := by
  sorry

theorem proof_gap_exercise_3421_10
    (h18 : ∀ x y : ℝ, a * zₓ z x y + b * zᵧ z x y = 1) :
    ∀ x₁ y₁ : ℝ, (x₁, y₁, z x₁ y₁) ∈ S -> ruledLine a b z x₁ y₁ ⊆ S := by
  sorry

theorem proof_gap_exercise_3421_11
    (h18 : ∀ x y : ℝ, a * zₓ z x y + b * zᵧ z x y = 1)
    (h19 : ∀ x₁ y₁ : ℝ, (x₁, y₁, z x₁ y₁) ∈ S -> ruledLine a b z x₁ y₁ ⊆ S) :
    ∀ x y : ℝ,
      a * zₓ z x y + b * zᵧ z x y = 1 ∧
      (∀ x₁ y₁ : ℝ, (x₁, y₁, z x₁ y₁) ∈ S -> ruledLine a b z x₁ y₁ ⊆ S) := by
  sorry

end exercise_3421
