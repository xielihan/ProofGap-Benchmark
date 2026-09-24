import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology

namespace exercise_3417

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable abbrev pd4 (f : ℝ -> ℝ -> ℝ -> ℝ -> ℝ) (i : Nat) (x y z t : ℝ) : ℝ :=
  match i with
  | 1 => iteratedDeriv 1 (fun s => f s y z t) x
  | 2 => iteratedDeriv 1 (fun s => f x s z t) y
  | 3 => iteratedDeriv 1 (fun s => f x y s t) z
  | _ => iteratedDeriv 1 (fun s => f x y z s) t

noncomputable abbrev pd3 (g : ℝ -> ℝ -> ℝ -> ℝ) (i : Nat) (y z t : ℝ) : ℝ :=
  match i with
  | 2 => iteratedDeriv 1 (fun s => g s z t) y
  | 3 => iteratedDeriv 1 (fun s => g y s t) z
  | _ => iteratedDeriv 1 (fun s => g y z s) t

noncomputable abbrev pd2 (h : ℝ -> ℝ -> ℝ) (i : Nat) (z t : ℝ) : ℝ :=
  match i with
  | 3 => iteratedDeriv 1 (fun s => h s t) z
  | _ => iteratedDeriv 1 (fun s => h z s) t

noncomputable abbrev d_y (r : ℝ -> ℝ) (y : ℝ) : ℝ := iteratedDeriv 1 r y
noncomputable abbrev d_xy (u : ℝ -> ℝ -> ℝ) (x y : ℝ) : ℝ := iteratedDeriv 1 (fun s => u s y) x + iteratedDeriv 1 (fun s => u x s) y

variable
  (u : ℝ -> ℝ -> ℝ) (f : ℝ -> ℝ -> ℝ -> ℝ -> ℝ)
  (g : ℝ -> ℝ -> ℝ -> ℝ) (h : ℝ -> ℝ -> ℝ)
  (z t : ℝ -> ℝ) (I₁ I₂ : ℝ -> ℝ -> ℝ -> ℝ)
  (hu : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) -> u x y = f x y (z y) (t y))
  (hg : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) -> g y (z y) (t y) = 0)
  (hh : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) -> h (z y) (t y) = 0)
  (hf : ContDiff ℝ (1 : ℕ∞) (fun p : ℝ × ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2.1 p.2.2.2))
  (hgdiff : ContDiff ℝ (1 : ℕ∞) (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2))
  (hhdiff : ContDiff ℝ (1 : ℕ∞) (fun p : ℝ × ℝ => h p.1 p.2))
  (hI₁ : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) -> I₁ y (z y) (t y) = pd3 g 3 y (z y) (t y) * pd2 h 4 (z y) (t y) - pd3 g 4 y (z y) (t y) * pd2 h 3 (z y) (t y))
  (hI₁ne : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) -> I₁ y (z y) (t y) ≠ 0)
  (hI₂ : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) -> I₂ y (z y) (t y) = pd2 h 3 (z y) (t y) * pd4 f 4 x y (z y) (t y) - pd2 h 4 (z y) (t y) * pd4 f 3 x y (z y) (t y))

-- Exercise 3417, gap 1
theorem proof_gap_exercise_3417_1 :
    ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ->
      d_xy u x y =
        pd4 f 1 x y (z y) (t y) * iteratedDeriv 1 (fun s : ℝ => s) x +
        pd4 f 2 x y (z y) (t y) * iteratedDeriv 1 (fun s : ℝ => s) y +
        pd4 f 3 x y (z y) (t y) * d_y z y +
        pd4 f 4 x y (z y) (t y) * d_y t y := by
  sorry

-- Exercise 3417, gap 2
theorem proof_gap_exercise_3417_2
    (h18 : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ->
      d_xy u x y = pd4 f 1 x y (z y) (t y) * iteratedDeriv 1 (fun s : ℝ => s) x +
        pd4 f 2 x y (z y) (t y) * iteratedDeriv 1 (fun s : ℝ => s) y +
        pd4 f 3 x y (z y) (t y) * d_y z y + pd4 f 4 x y (z y) (t y) * d_y t y) :
    ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ->
      0 = pd3 g 2 y (z y) (t y) * iteratedDeriv 1 (fun s : ℝ => s) y +
          pd3 g 3 y (z y) (t y) * d_y z y +
          pd3 g 4 y (z y) (t y) * d_y t y := by
  sorry

-- Exercise 3417, gap 3
theorem proof_gap_exercise_3417_3
    (h18 : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) -> True)
    (h19 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) -> True) :
    ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ->
      0 = pd2 h 3 (z y) (t y) * d_y z y + pd2 h 4 (z y) (t y) * d_y t y := by
  sorry

-- Exercise 3417, gap 4
theorem proof_gap_exercise_3417_4
    (h18 : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) -> True)
    (h19 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) -> True)
    (h20 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) -> True) :
    ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ->
      d_y z y = (-(pd3 g 2 y (z y) (t y)) * pd2 h 4 (z y) (t y)) /. I₁ y (z y) (t y) *
        iteratedDeriv 1 (fun s : ℝ => s) y := by
  sorry

-- Exercise 3417, gap 5
theorem proof_gap_exercise_3417_5
    (h21 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) -> d_y z y = (-(pd3 g 2 y (z y) (t y)) * pd2 h 4 (z y) (t y)) /. I₁ y (z y) (t y) * iteratedDeriv 1 (fun s : ℝ => s) y) :
    ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ->
      d_y t y = (pd3 g 2 y (z y) (t y) * pd2 h 3 (z y) (t y)) /. I₁ y (z y) (t y) *
        iteratedDeriv 1 (fun s : ℝ => s) y := by
  sorry

-- Exercise 3417, gap 6
theorem proof_gap_exercise_3417_6
    (h21 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) -> d_y z y = (-(pd3 g 2 y (z y) (t y)) * pd2 h 4 (z y) (t y)) /. I₁ y (z y) (t y) * iteratedDeriv 1 (fun s : ℝ => s) y)
    (h22 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) -> d_y t y = (pd3 g 2 y (z y) (t y) * pd2 h 3 (z y) (t y)) /. I₁ y (z y) (t y) * iteratedDeriv 1 (fun s : ℝ => s) y) :
    ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ->
      d_xy u x y =
        pd4 f 1 x y (z y) (t y) * iteratedDeriv 1 (fun s : ℝ => s) x +
        pd4 f 2 x y (z y) (t y) * iteratedDeriv 1 (fun s : ℝ => s) y -
        (pd3 g 2 y (z y) (t y) /. I₁ y (z y) (t y)) *
          (pd4 f 3 x y (z y) (t y) * pd2 h 4 (z y) (t y) -
           pd4 f 4 x y (z y) (t y) * pd2 h 3 (z y) (t y)) *
        iteratedDeriv 1 (fun s : ℝ => s) y := by
  sorry

-- Exercise 3417, gap 7
theorem proof_gap_exercise_3417_7
    (h23 : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) -> True) :
    ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ->
      iteratedDeriv 1 (fun s => u s y) x = pd4 f 1 x y (z y) (t y) := by
  sorry

-- Exercise 3417, gap 8
theorem proof_gap_exercise_3417_8
    (h23 : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) -> True)
    (h24 : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) -> iteratedDeriv 1 (fun s => u s y) x = pd4 f 1 x y (z y) (t y)) :
    ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ->
      iteratedDeriv 1 (fun s => u x s) y =
        pd4 f 2 x y (z y) (t y) + pd3 g 2 y (z y) (t y) * (I₂ y (z y) (t y) /. I₁ y (z y) (t y)) := by
  sorry

end exercise_3417
