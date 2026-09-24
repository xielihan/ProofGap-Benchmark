import Mathlib

set_option linter.style.longLine false

noncomputable section

local notation:70 x:71 " /. " y:71 => ((x : ℝ) / (y : ℝ))

abbrev Region3 := Set (ℝ × ℝ × ℝ)

noncomputable def VolumeInt (_s : Region3) (_dω : ℝ) : ℝ := 0
noncomputable def DefInt (a b : ℝ) (f : ℝ → ℝ) : ℝ := ∫ x in a..b, f x
noncomputable def diff {α : Type*} (_x : α) : ℝ := 1

-- exercise: exercise_4114
-- source: x^2/a^2+y^2/b^2+z^4/c^4≤1, a,b,c>0.

def Omega4114Original (a b c : ℝ) : Region3 :=
  {p | (p.1 ^ 2 /. a ^ 2) + (p.2.1 ^ 2 /. b ^ 2) + (p.2.2 ^ 4 /. c ^ 4) ≤ 1}

def Omega4114Cyl (c : ℝ) : Region3 :=
  {p | 0 ≤ p.2.1 ∧ p.2.1 ≤ 2 * Real.pi ∧ 0 ≤ p.1 ∧ p.1 ≤ 1 ∧
       -c * (1 - p.1 ^ 2) ^ (1 /. 4) ≤ p.2.2 ∧ p.2.2 ≤ c * (1 - p.1 ^ 2) ^ (1 /. 4)}

def Int4114 (a b c : ℝ) : ℝ :=
  DefInt 0 (2 * Real.pi) (fun φ =>
    DefInt 0 1 (fun r => a * b * r * DefInt (-c * (1 - r ^ 2) ^ (1 /. 4)) (c * (1 - r ^ 2) ^ (1 /. 4)) (fun z => diff z) * diff r) * diff φ)

def Red4114 (a b c : ℝ) : ℝ :=
  4 * Real.pi * a * b * c * DefInt 0 1 (fun r => r * (1 - r ^ 2) ^ (1 /. 4) * diff r)

theorem proof_gap_exercise_4114_1
  (a b c : ℝ) (Ω : Region3) (x y : ℝ × ℝ → ℝ)
  (ha : a > 0) (hb : b > 0) (hc : c > 0)
  (hΩ : ∀ X Y Z : ℝ, Ω = Omega4114Original a b c)
  (hx : ∀ r φ : ℝ, x (r, φ) = a * r * Real.cos φ)
  (hy : ∀ r φ : ℝ, y (r, φ) = b * r * Real.sin φ) :
  Ω = Omega4114Cyl c := by
  sorry

theorem proof_gap_exercise_4114_2
  (a b c : ℝ) (Ω : Region3) (x y : ℝ × ℝ → ℝ)
  (ha : a > 0) (hb : b > 0) (hc : c > 0)
  (hΩ : ∀ X Y Z : ℝ, Ω = Omega4114Original a b c)
  (hx : ∀ r φ : ℝ, x (r, φ) = a * r * Real.cos φ)
  (hy : ∀ r φ : ℝ, y (r, φ) = b * r * Real.sin φ)
  (h10 : Ω = Omega4114Cyl c) :
  ∃ I : ℝ, ∀ r : ℝ, |I| = a * b * r := by
  sorry

theorem proof_gap_exercise_4114_3
  (a b c ω : ℝ) (Ω : Region3) (x y : ℝ × ℝ → ℝ)
  (ha : a > 0) (hb : b > 0) (hc : c > 0)
  (hΩ : ∀ X Y Z : ℝ, Ω = Omega4114Original a b c)
  (hx : ∀ r φ : ℝ, x (r, φ) = a * r * Real.cos φ)
  (hy : ∀ r φ : ℝ, y (r, φ) = b * r * Real.sin φ)
  (h10 : Ω = Omega4114Cyl c)
  (h11 : ∃ I : ℝ, ∀ r : ℝ, |I| = a * b * r) :
  VolumeInt Ω (diff ω) = Int4114 a b c := by
  sorry

theorem proof_gap_exercise_4114_4
  (a b c ω : ℝ) (Ω : Region3) (x y : ℝ × ℝ → ℝ)
  (ha : a > 0) (hb : b > 0) (hc : c > 0)
  (hΩ : ∀ X Y Z : ℝ, Ω = Omega4114Original a b c)
  (hx : ∀ r φ : ℝ, x (r, φ) = a * r * Real.cos φ)
  (hy : ∀ r φ : ℝ, y (r, φ) = b * r * Real.sin φ)
  (h10 : Ω = Omega4114Cyl c) (h11 : ∃ I : ℝ, ∀ r : ℝ, |I| = a * b * r)
  (h12 : VolumeInt Ω (diff ω) = Int4114 a b c) :
  Int4114 a b c = Red4114 a b c := by
  sorry

theorem proof_gap_exercise_4114_5
  (a b c ω : ℝ) (Ω : Region3) (x y : ℝ × ℝ → ℝ)
  (ha : a > 0) (hb : b > 0) (hc : c > 0)
  (hΩ : ∀ X Y Z : ℝ, Ω = Omega4114Original a b c)
  (hx : ∀ r φ : ℝ, x (r, φ) = a * r * Real.cos φ)
  (hy : ∀ r φ : ℝ, y (r, φ) = b * r * Real.sin φ)
  (h10 : Ω = Omega4114Cyl c) (h11 : ∃ I : ℝ, ∀ r : ℝ, |I| = a * b * r)
  (h12 : VolumeInt Ω (diff ω) = Int4114 a b c) (h13 : Int4114 a b c = Red4114 a b c) :
  VolumeInt Ω (diff ω) = Red4114 a b c := by
  sorry

theorem proof_gap_exercise_4114_6
  (a b c ω : ℝ) (Ω : Region3) (x y : ℝ × ℝ → ℝ)
  (ha : a > 0) (hb : b > 0) (hc : c > 0)
  (hΩ : ∀ X Y Z : ℝ, Ω = Omega4114Original a b c)
  (hx : ∀ r φ : ℝ, x (r, φ) = a * r * Real.cos φ)
  (hy : ∀ r φ : ℝ, y (r, φ) = b * r * Real.sin φ)
  (h10 : Ω = Omega4114Cyl c) (h11 : ∃ I : ℝ, ∀ r : ℝ, |I| = a * b * r)
  (h12 : VolumeInt Ω (diff ω) = Int4114 a b c) (h13 : Int4114 a b c = Red4114 a b c)
  (h14 : VolumeInt Ω (diff ω) = Red4114 a b c) :
  Red4114 a b c = (8 /. 5) * Real.pi * a * b * c := by
  sorry
