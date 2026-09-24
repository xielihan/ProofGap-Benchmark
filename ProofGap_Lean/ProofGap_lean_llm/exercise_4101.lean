import Mathlib

noncomputable section

namespace Exercise4101

abbrev Point3 := ℝ × ℝ × ℝ
def pt (x y z : ℝ) : Point3 := (x, y, z)

variable (VolumeInt : Set Point3 → (Point3 → ℝ) → ℝ)
variable (DefInt : ℝ → ℝ → (ℝ → ℝ) → ℝ)
variable {V : Set Point3}

def iter1 (DefInt : ℝ → ℝ → (ℝ → ℝ) → ℝ) : ℝ :=
  DefInt 0 1 (fun x => DefInt (x ^ 2) x
    (fun y => DefInt (x ^ 2 + y ^ 2) (2 * x ^ 2 + 2 * y ^ 2) (fun _z => 1)))
def iter2 (DefInt : ℝ → ℝ → (ℝ → ℝ) → ℝ) : ℝ :=
  DefInt 0 1 (fun x => DefInt (x ^ 2) x (fun y => x ^ 2 + y ^ 2))
def iter3 (DefInt : ℝ → ℝ → (ℝ → ℝ) → ℝ) : ℝ :=
  DefInt 0 1 (fun x => (4 / 3) * x ^ 3 - x ^ 4 - (1 / 3) * x ^ 6)
def antiderivEval : ℝ := (1 / 3) * 1 ^ 4 - (1 / 5) * 1 ^ 5 - (1 / 21) * 1 ^ 7

-- Exercise 4101, gap 1
theorem proof_gap_exercise_4101_1
    (hV : ∀ x y z : ℝ, x ∈ Set.Icc 0 1 → x ^ 2 ≤ y → y ≤ x →
      x ^ 2 + y ^ 2 ≤ z → z ≤ 2 * x ^ 2 + 2 * y ^ 2 → pt x y z ∈ V) :
    VolumeInt V (fun _p => 1) = iter1 DefInt := by
  sorry

-- Exercise 4101, gap 2
theorem proof_gap_exercise_4101_2
    (h1 : VolumeInt V (fun _p => 1) = iter1 DefInt) :
    iter1 DefInt = iter2 DefInt := by
  sorry

-- Exercise 4101, gap 3
theorem proof_gap_exercise_4101_3
    (h2 : iter1 DefInt = iter2 DefInt) :
    iter2 DefInt = iter3 DefInt := by
  sorry

-- Exercise 4101, gap 4
theorem proof_gap_exercise_4101_4 :
    iter3 DefInt = antiderivEval := by
  sorry

-- Exercise 4101, gap 5
theorem proof_gap_exercise_4101_5 :
    antiderivEval = (3 / 35 : ℝ) := by
  sorry

-- Exercise 4101, gap 6
theorem proof_gap_exercise_4101_6
    (h1 : VolumeInt V (fun _p => 1) = iter1 DefInt)
    (h2 : iter1 DefInt = iter2 DefInt)
    (h3 : iter2 DefInt = iter3 DefInt)
    (h4 : iter3 DefInt = antiderivEval)
    (h5 : antiderivEval = (3 / 35 : ℝ)) :
    VolumeInt V (fun _p => 1) = (3 / 35 : ℝ) := by
  sorry

end Exercise4101
