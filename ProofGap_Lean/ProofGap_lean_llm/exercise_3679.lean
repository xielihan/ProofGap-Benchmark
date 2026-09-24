import Mathlib

noncomputable section
open Classical Real

abbrev Point2 := ℝ × ℝ
abbrev Point3 := (ℝ × ℝ) × ℝ
def u3679 (p : Point3) : ℝ := p.1.1 + p.1.2 + p.2
def S3679 : Set Point3 := {p | p.1.1 ^ 2 + p.1.2 ^ 2 ≤ p.2 ∧ p.2 ≤ 1}
def g3679 (p : Point2) : ℝ := u3679 ((p.1, p.2), p.1 ^ 2 + p.2 ^ 2)
def top3679 (p : Point2) : ℝ := u3679 ((p.1, p.2), 1)
def F3679 (p : Point2) (lam : ℝ) : ℝ := p.1 + p.2 + 1 + lam * (p.1 ^ 2 + p.2 ^ 2 - 1)
axiom grad3 : (Point3 → ℝ) → Point3 → Point3
axiom grad2 : (Point2 → ℝ) → Point2 → Point2
axiom FunDeri2 : (Point2 → ℝ) → ℕ → ℕ → Point2 → ℝ
axiom FunDeri3 : (Point2 → ℝ → ℝ) → ℕ → ℕ → Point2 → ℝ → ℝ
def MaximumPointOn (f : Point3 → ℝ) (S : Set Point3) : Set Point3 :=
  {p | p ∈ S ∧ ∀ q ∈ S, f q ≤ f p}
def MinimumPointOn (f : Point3 → ℝ) (S : Set Point3) : Set Point3 :=
  {p | p ∈ S ∧ ∀ q ∈ S, f p ≤ f q}
def ImageOn (f : Point3 → ℝ) (S : Set Point3) : Set ℝ := f '' S

-- Exercise 3679, gap 1
theorem proof_gap_exercise_3679_1 :
    ∀ x y z : ℝ, x ^ 2 + y ^ 2 < z ∧ z < 1 → grad3 u3679 ((x, y), z) ≠ ((0, 0), 0) := by
  sorry

-- Exercise 3679, gap 2
theorem proof_gap_exercise_3679_2
    (hint : ∀ x y z : ℝ, x ^ 2 + y ^ 2 < z ∧ z < 1 → grad3 u3679 ((x, y), z) ≠ ((0, 0), 0)) :
    ∀ x y : ℝ, x ^ 2 + y ^ 2 < 1 → grad2 top3679 (x, y) ≠ (0, 0) := by
  sorry

-- Exercise 3679, gap 3
theorem proof_gap_exercise_3679_3 :
    ∀ x y : ℝ, x ^ 2 + y ^ 2 ≤ 1 → u3679 ((x, y), x ^ 2 + y ^ 2) = x + y + x ^ 2 + y ^ 2 := by
  sorry

-- Exercise 3679, gap 4
theorem proof_gap_exercise_3679_4 :
    ∀ x y : ℝ, FunDeri2 g3679 1 1 (x, y) = 1 + 2 * x := by
  sorry

-- Exercise 3679, gap 5
theorem proof_gap_exercise_3679_5
    (hx : ∀ x y : ℝ, FunDeri2 g3679 1 1 (x, y) = 1 + 2 * x) :
    ∀ x y : ℝ, FunDeri2 g3679 2 1 (x, y) = 1 + 2 * y := by
  sorry

-- Exercise 3679, gap 6
theorem proof_gap_exercise_3679_6 :
    (((-1 / 2, -1 / 2), 1 / 2) : Point3) ∈ S3679 := by
  sorry

-- Exercise 3679, gap 7
theorem proof_gap_exercise_3679_7 :
    u3679 ((-1 / 2, -1 / 2), 1 / 2) = -1 / 2 := by
  sorry

-- Exercise 3679, gap 8
theorem proof_gap_exercise_3679_8 :
    ∀ x y lam : ℝ, FunDeri3 F3679 1 1 (x, y) lam = 1 + 2 * lam * x := by
  sorry

-- Exercise 3679, gap 9
theorem proof_gap_exercise_3679_9
    (hFx : ∀ x y lam : ℝ, FunDeri3 F3679 1 1 (x, y) lam = 1 + 2 * lam * x) :
    ∀ x y lam : ℝ, FunDeri3 F3679 2 1 (x, y) lam = 1 + 2 * lam * y := by
  sorry

-- Exercise 3679, gap 10
theorem proof_gap_exercise_3679_10 :
    (((1 / sqrt 2, 1 / sqrt 2), 1) : Point3) ∈ S3679 := by
  sorry

-- Exercise 3679, gap 11
theorem proof_gap_exercise_3679_11 :
    u3679 ((1 / sqrt 2, 1 / sqrt 2), 1) = 1 + sqrt 2 := by
  sorry

-- Exercise 3679, gap 12
theorem proof_gap_exercise_3679_12 :
    (((-1 / sqrt 2, -1 / sqrt 2), 1) : Point3) ∈ S3679 := by
  sorry

-- Exercise 3679, gap 13
theorem proof_gap_exercise_3679_13 :
    u3679 ((-1 / sqrt 2, -1 / sqrt 2), 1) = 1 - sqrt 2 := by
  sorry

-- Exercise 3679, gap 14
theorem proof_gap_exercise_3679_14 :
    MaximumPointOn u3679 S3679 = ({((1 / sqrt 2, 1 / sqrt 2), 1)} : Set Point3) := by
  sorry

-- Exercise 3679, gap 15
theorem proof_gap_exercise_3679_15
    (hmax : MaximumPointOn u3679 S3679 = ({((1 / sqrt 2, 1 / sqrt 2), 1)} : Set Point3)) :
    MinimumPointOn u3679 S3679 = ({((-1 / 2, -1 / 2), 1 / 2)} : Set Point3) := by
  sorry

-- Exercise 3679, gap 16
theorem proof_gap_exercise_3679_16
    (hmax : MaximumPointOn u3679 S3679 = ({((1 / sqrt 2, 1 / sqrt 2), 1)} : Set Point3))
    (hmin : MinimumPointOn u3679 S3679 = ({((-1 / 2, -1 / 2), 1 / 2)} : Set Point3)) :
    (sSup (ImageOn u3679 S3679), sInf (ImageOn u3679 S3679)) = (1 + sqrt 2, -1 / 2) := by
  sorry
