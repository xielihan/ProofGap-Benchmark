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
  (hu : ∀ x y : ℝ, u x y = f x y (z y) (t y))
  (hg : ∀ y : ℝ, g y (z y) (t y) = 0)
  (hh : ∀ y : ℝ, h (z y) (t y) = 0)
  (hf : ContDiff ℝ (1 : ℕ∞) (fun p : ℝ × ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2.1 p.2.2.2))
  (hgdiff : ContDiff ℝ (1 : ℕ∞) (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2))
  (hhdiff : ContDiff ℝ (1 : ℕ∞) (fun p : ℝ × ℝ => h p.1 p.2))
  (hI₁ : ∀ y : ℝ, I₁ y (z y) (t y) = pd3 g 3 y (z y) (t y) * pd2 h 4 (z y) (t y) - pd3 g 4 y (z y) (t y) * pd2 h 3 (z y) (t y))
  (hI₁ne : ∀ y : ℝ, I₁ y (z y) (t y) ≠ 0)
  (hI₂ : ∀ x y : ℝ, I₂ y (z y) (t y) = pd2 h 3 (z y) (t y) * pd4 f 4 x y (z y) (t y) - pd2 h 4 (z y) (t y) * pd4 f 3 x y (z y) (t y))

-- Source: proofgap/exercise_3417/1.txt
theorem proof_gap_exercise_3417_1 :
    ∀ x y : ℝ,
      d_xy u x y =
        pd4 f 1 x y (z y) (t y) * iteratedDeriv 1 (fun s : ℝ => s) x +
        pd4 f 2 x y (z y) (t y) * iteratedDeriv 1 (fun s : ℝ => s) y +
        pd4 f 3 x y (z y) (t y) * d_y z y +
        pd4 f 4 x y (z y) (t y) * d_y t y := by
  sorry

-- Source: proofgap/exercise_3417/2.txt
theorem proof_gap_exercise_3417_2
    (h18 : ∀ x y : ℝ,
      d_xy u x y = pd4 f 1 x y (z y) (t y) * iteratedDeriv 1 (fun s : ℝ => s) x +
        pd4 f 2 x y (z y) (t y) * iteratedDeriv 1 (fun s : ℝ => s) y +
        pd4 f 3 x y (z y) (t y) * d_y z y + pd4 f 4 x y (z y) (t y) * d_y t y) :
    ∀ y : ℝ,
      0 = pd3 g 2 y (z y) (t y) * iteratedDeriv 1 (fun s : ℝ => s) y +
          pd3 g 3 y (z y) (t y) * d_y z y +
          pd3 g 4 y (z y) (t y) * d_y t y := by
  sorry

-- Source: proofgap/exercise_3417/3.txt
theorem proof_gap_exercise_3417_3
    (h18 : ∀ x y : ℝ,
      d_xy u x y =
        pd4 f 1 x y (z y) (t y) * iteratedDeriv 1 (fun s : ℝ => s) x +
        pd4 f 2 x y (z y) (t y) * iteratedDeriv 1 (fun s : ℝ => s) y +
        pd4 f 3 x y (z y) (t y) * d_y z y +
        pd4 f 4 x y (z y) (t y) * d_y t y)
    (h19 : ∀ y : ℝ,
      0 = pd3 g 2 y (z y) (t y) * iteratedDeriv 1 (fun s : ℝ => s) y +
          pd3 g 3 y (z y) (t y) * d_y z y +
          pd3 g 4 y (z y) (t y) * d_y t y) :
    ∀ y : ℝ,
      0 = pd2 h 3 (z y) (t y) * d_y z y + pd2 h 4 (z y) (t y) * d_y t y := by
  sorry

-- Source: proofgap/exercise_3417/4.txt
theorem proof_gap_exercise_3417_4
    (h18 : ∀ x y : ℝ,
      d_xy u x y =
        pd4 f 1 x y (z y) (t y) * iteratedDeriv 1 (fun s : ℝ => s) x +
        pd4 f 2 x y (z y) (t y) * iteratedDeriv 1 (fun s : ℝ => s) y +
        pd4 f 3 x y (z y) (t y) * d_y z y +
        pd4 f 4 x y (z y) (t y) * d_y t y)
    (h19 : ∀ y : ℝ,
      0 = pd3 g 2 y (z y) (t y) * iteratedDeriv 1 (fun s : ℝ => s) y +
          pd3 g 3 y (z y) (t y) * d_y z y +
          pd3 g 4 y (z y) (t y) * d_y t y)
    (h20 : ∀ y : ℝ,
      0 = pd2 h 3 (z y) (t y) * d_y z y + pd2 h 4 (z y) (t y) * d_y t y) :
    ∀ y : ℝ,
      d_y z y = (-(pd3 g 2 y (z y) (t y)) * pd2 h 4 (z y) (t y)) /. I₁ y (z y) (t y) *
        iteratedDeriv 1 (fun s : ℝ => s) y := by
  sorry

-- Source: proofgap/exercise_3417/5.txt
theorem proof_gap_exercise_3417_5
    (h21 : ∀ y : ℝ, d_y z y = (-(pd3 g 2 y (z y) (t y)) * pd2 h 4 (z y) (t y)) /. I₁ y (z y) (t y) * iteratedDeriv 1 (fun s : ℝ => s) y) :
    ∀ y : ℝ,
      d_y t y = (pd3 g 2 y (z y) (t y) * pd2 h 3 (z y) (t y)) /. I₁ y (z y) (t y) *
        iteratedDeriv 1 (fun s : ℝ => s) y := by
  sorry

-- Source: proofgap/exercise_3417/6.txt
theorem proof_gap_exercise_3417_6
    (h21 : ∀ y : ℝ, d_y z y = (-(pd3 g 2 y (z y) (t y)) * pd2 h 4 (z y) (t y)) /. I₁ y (z y) (t y) * iteratedDeriv 1 (fun s : ℝ => s) y)
    (h22 : ∀ y : ℝ, d_y t y = (pd3 g 2 y (z y) (t y) * pd2 h 3 (z y) (t y)) /. I₁ y (z y) (t y) * iteratedDeriv 1 (fun s : ℝ => s) y) :
    ∀ x y : ℝ,
      d_xy u x y =
        pd4 f 1 x y (z y) (t y) * iteratedDeriv 1 (fun s : ℝ => s) x +
        pd4 f 2 x y (z y) (t y) * iteratedDeriv 1 (fun s : ℝ => s) y -
        (pd3 g 2 y (z y) (t y) /. I₁ y (z y) (t y)) *
          (pd4 f 3 x y (z y) (t y) * pd2 h 4 (z y) (t y) -
           pd4 f 4 x y (z y) (t y) * pd2 h 3 (z y) (t y)) *
        iteratedDeriv 1 (fun s : ℝ => s) y := by
  sorry

-- Source: proofgap/exercise_3417/7.txt
theorem proof_gap_exercise_3417_7
    (h23 : ∀ x y : ℝ,
      d_xy u x y =
        pd4 f 1 x y (z y) (t y) * iteratedDeriv 1 (fun s : ℝ => s) x +
        pd4 f 2 x y (z y) (t y) * iteratedDeriv 1 (fun s : ℝ => s) y -
        (pd3 g 2 y (z y) (t y) /. I₁ y (z y) (t y)) *
          (pd4 f 3 x y (z y) (t y) * pd2 h 4 (z y) (t y) -
           pd4 f 4 x y (z y) (t y) * pd2 h 3 (z y) (t y)) *
        iteratedDeriv 1 (fun s : ℝ => s) y) :
    ∀ x y : ℝ,
      iteratedDeriv 1 (fun s => u s y) x = pd4 f 1 x y (z y) (t y) := by
  sorry

-- Source: proofgap/exercise_3417/8.txt
theorem proof_gap_exercise_3417_8
    (h23 : ∀ x y : ℝ,
      d_xy u x y =
        pd4 f 1 x y (z y) (t y) * iteratedDeriv 1 (fun s : ℝ => s) x +
        pd4 f 2 x y (z y) (t y) * iteratedDeriv 1 (fun s : ℝ => s) y -
        (pd3 g 2 y (z y) (t y) /. I₁ y (z y) (t y)) *
          (pd4 f 3 x y (z y) (t y) * pd2 h 4 (z y) (t y) -
           pd4 f 4 x y (z y) (t y) * pd2 h 3 (z y) (t y)) *
        iteratedDeriv 1 (fun s : ℝ => s) y)
    (h24 : ∀ x y : ℝ, iteratedDeriv 1 (fun s => u s y) x = pd4 f 1 x y (z y) (t y)) :
    ∀ x y : ℝ,
      iteratedDeriv 1 (fun s => u x s) y =
        pd4 f 2 x y (z y) (t y) + pd3 g 2 y (z y) (t y) * (I₂ y (z y) (t y) /. I₁ y (z y) (t y)) := by
  sorry

end exercise_3417
