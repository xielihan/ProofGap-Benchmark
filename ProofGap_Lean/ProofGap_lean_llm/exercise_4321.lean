import Mathlib

set_option linter.style.longLine false

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable def curveIntegral4321 (C : Set (ℝ × ℝ)) (form : ℝ) : ℝ := 0
noncomputable def areaIntegral4321 (D : Set (ℝ × ℝ)) (f : ℝ) : ℝ := 0
noncomputable def partial4321 (f : ℝ × ℝ -> ℝ) (i k : ℕ) (p : ℝ × ℝ) : ℝ := 0
noncomputable def inside4321 (C : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := Set.univ
noncomputable def imageRatio4321 (D : Set (ℝ × ℝ)) (fromXY : Bool) : ℝ := 0
noncomputable def sgn4321 (x : ℝ) : ℝ := if x > 0 then 1 else if x = 0 then 0 else -1

noncomputable def ellipse4321 (X Y : ℝ × ℝ -> ℝ) (r : ℝ) : Set (ℝ × ℝ) :=
  {p | X p ^ 2 + Y p ^ 2 = r ^ 2}

noncomputable def disk4321 (r : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2 ^ 2 ≤ r ^ 2}

-- exercise: exercise_4321

theorem proof_gap_exercise_4321_1
  (a b c d I r : ℝ) (C Cp : Set (ℝ × ℝ)) (X Y P Q : ℝ × ℝ -> ℝ)
  (hr : r > 0) (hdet : a * d - b * c ≠ 0)
  (hX : ∀ x y : ℝ, X (x, y) = a * x + b * y)
  (hY : ∀ x y : ℝ, Y (x, y) = c * x + d * y)
  (h0C : (0, 0) ∉ C) (hinside : (0, 0) ∈ inside4321 C)
  : ∀ x y : ℝ, X (x, y) ^ 2 + Y (x, y) ^ 2 = 0 ↔ (x, y) = (0, 0) := by
  sorry

theorem proof_gap_exercise_4321_2
  (a b c d I r : ℝ) (C Cp : Set (ℝ × ℝ)) (X Y P Q : ℝ × ℝ -> ℝ)
  (hr : r > 0) (hdet : a * d - b * c ≠ 0)
  (hX : ∀ x y : ℝ, X (x, y) = a * x + b * y)
  (hY : ∀ x y : ℝ, Y (x, y) = c * x + d * y)
  (hzero : ∀ x y : ℝ, X (x, y) ^ 2 + Y (x, y) ^ 2 = 0 ↔ (x, y) = (0, 0))
  : curveIntegral4321 C 2 = curveIntegral4321 C ((a * d - b * c) * 2) := by
  sorry

theorem proof_gap_exercise_4321_3
  (a b c d I r : ℝ) (C Cp : Set (ℝ × ℝ)) (X Y P Q : ℝ × ℝ -> ℝ)
  (hr : r > 0) (hdet : a * d - b * c ≠ 0)
  (hX : ∀ x y : ℝ, X (x, y) = a * x + b * y)
  (hY : ∀ x y : ℝ, Y (x, y) = c * x + d * y)
  (hform : curveIntegral4321 C 2 = curveIntegral4321 C ((a * d - b * c) * 2))
  (hP : P = fun p => -(((a * d - b * c) * p.2) /. ((a * p.1 + b * p.2) ^ 2 + (c * p.1 + d * p.2) ^ 2)))
  (hQ : Q = fun p => ((a * d - b * c) * p.1) /. ((a * p.1 + b * p.2) ^ 2 + (c * p.1 + d * p.2) ^ 2))
  : I = (1 /. (2 * Real.pi)) * curveIntegral4321 C 3 := by
  sorry

theorem proof_gap_exercise_4321_4
  (a b c d I r : ℝ) (C Cp : Set (ℝ × ℝ)) (X Y P Q : ℝ × ℝ -> ℝ)
  (hr : r > 0) (hdet : a * d - b * c ≠ 0)
  (hP : P = fun p => -(((a * d - b * c) * p.2) /. ((a * p.1 + b * p.2) ^ 2 + (c * p.1 + d * p.2) ^ 2)))
  (hQ : Q = fun p => ((a * d - b * c) * p.1) /. ((a * p.1 + b * p.2) ^ 2 + (c * p.1 + d * p.2) ^ 2))
  (hI : I = (1 /. (2 * Real.pi)) * curveIntegral4321 C 3)
  : I = (1 /. (2 * Real.pi)) * curveIntegral4321 C 4 := by
  sorry

theorem proof_gap_exercise_4321_5
  (a b c d I r : ℝ) (C Cp : Set (ℝ × ℝ)) (X Y P Q : ℝ × ℝ -> ℝ)
  (hr : r > 0) (hdet : a * d - b * c ≠ 0)
  (hP : P = fun p => -(((a * d - b * c) * p.2) /. ((a * p.1 + b * p.2) ^ 2 + (c * p.1 + d * p.2) ^ 2)))
  (hQ : Q = fun p => ((a * d - b * c) * p.1) /. ((a * p.1 + b * p.2) ^ 2 + (c * p.1 + d * p.2) ^ 2))
  : ∀ p : ℝ × ℝ, partial4321 Q 1 1 p = partial4321 P 2 1 p := by
  sorry

theorem proof_gap_exercise_4321_6
  (a b c d I r : ℝ) (C Cp : Set (ℝ × ℝ)) (X Y P Q : ℝ × ℝ -> ℝ)
  (hr : r > 0) (hdet : a * d - b * c ≠ 0)
  (hder : ∀ p : ℝ × ℝ, partial4321 Q 1 1 p = partial4321 P 2 1 p)
  : curveIntegral4321 C 4 = curveIntegral4321 Cp 4 := by
  sorry

theorem proof_gap_exercise_4321_7
  (a b c d I r : ℝ) (C Cp : Set (ℝ × ℝ)) (X Y P Q : ℝ × ℝ -> ℝ)
  (hr : r > 0) (hdet : a * d - b * c ≠ 0)
  (hI : I = (1 /. (2 * Real.pi)) * curveIntegral4321 C 3)
  (hgreen : curveIntegral4321 C 4 = curveIntegral4321 Cp 4)
  : Cp = ellipse4321 X Y r -> I = (1 /. (2 * Real.pi)) * curveIntegral4321 Cp 3 := by
  sorry

theorem proof_gap_exercise_4321_8
  (a b c d I r : ℝ) (C Cp : Set (ℝ × ℝ)) (X Y P Q : ℝ × ℝ -> ℝ)
  (hr : r > 0) (hdet : a * d - b * c ≠ 0)
  (h7 : Cp = ellipse4321 X Y r -> I = (1 /. (2 * Real.pi)) * curveIntegral4321 Cp 3)
  : Cp = ellipse4321 X Y r -> I = (1 /. (2 * Real.pi * r ^ 2)) * curveIntegral4321 Cp 5 := by
  sorry

theorem proof_gap_exercise_4321_9
  (a b c d I r : ℝ) (C Cp : Set (ℝ × ℝ)) (X Y P Q : ℝ × ℝ -> ℝ)
  (hr : r > 0) (hdet : a * d - b * c ≠ 0)
  (h8 : Cp = ellipse4321 X Y r -> I = (1 /. (2 * Real.pi * r ^ 2)) * curveIntegral4321 Cp 5)
  : Cp = ellipse4321 X Y r -> I = ((a * d - b * c) /. (2 * Real.pi * r ^ 2)) * curveIntegral4321 Cp 6 := by
  sorry

theorem proof_gap_exercise_4321_10
  (a b c d I r : ℝ) (C Cp : Set (ℝ × ℝ)) (X Y P Q : ℝ × ℝ -> ℝ)
  (hr : r > 0) (hdet : a * d - b * c ≠ 0)
  (h9 : Cp = ellipse4321 X Y r -> I = ((a * d - b * c) /. (2 * Real.pi * r ^ 2)) * curveIntegral4321 Cp 6)
  : Cp = ellipse4321 X Y r -> I = ((a * d - b * c) /. (Real.pi * r ^ 2)) * areaIntegral4321 (disk4321 r) 1 := by
  sorry

theorem proof_gap_exercise_4321_11
  (a b c d I r : ℝ) (C Cp D : Set (ℝ × ℝ)) (X Y P Q : ℝ × ℝ -> ℝ)
  (hr : r > 0) (hdet : a * d - b * c ≠ 0)
  : D ⊆ Set.univ -> Cp = ellipse4321 X Y r -> imageRatio4321 D false = a * d - b * c := by
  sorry

theorem proof_gap_exercise_4321_12
  (a b c d I r : ℝ) (C Cp D : Set (ℝ × ℝ)) (X Y P Q : ℝ × ℝ -> ℝ)
  (hr : r > 0) (hdet : a * d - b * c ≠ 0)
  (hjac : D ⊆ Set.univ -> Cp = ellipse4321 X Y r -> imageRatio4321 D false = a * d - b * c)
  : D ⊆ Set.univ -> Cp = ellipse4321 X Y r -> imageRatio4321 D true = 1 /. (a * d - b * c) := by
  sorry

theorem proof_gap_exercise_4321_13
  (a b c d I r : ℝ) (C Cp : Set (ℝ × ℝ)) (X Y P Q : ℝ × ℝ -> ℝ)
  (hr : r > 0) (hdet : a * d - b * c ≠ 0)
  (h10 : Cp = ellipse4321 X Y r -> I = ((a * d - b * c) /. (Real.pi * r ^ 2)) * areaIntegral4321 (disk4321 r) 1)
  : Cp = ellipse4321 X Y r ->
      I = ((a * d - b * c) /. (Real.pi * r ^ 2)) *
        areaIntegral4321 (disk4321 r) (1 /. |a * d - b * c|) := by
  sorry

theorem proof_gap_exercise_4321_14
  (a b c d I r : ℝ) (C Cp : Set (ℝ × ℝ)) (X Y P Q : ℝ × ℝ -> ℝ)
  (hr : r > 0) (hdet : a * d - b * c ≠ 0)
  (h13 : Cp = ellipse4321 X Y r ->
      I = ((a * d - b * c) /. (Real.pi * r ^ 2)) *
        areaIntegral4321 (disk4321 r) (1 /. |a * d - b * c|))
  : Cp = ellipse4321 X Y r ->
      I = ((a * d - b * c) /. (Real.pi * r ^ 2)) * (1 /. |a * d - b * c|) * Real.pi * r ^ 2 := by
  sorry

theorem proof_gap_exercise_4321_15
  (a b c d I r : ℝ) (C Cp : Set (ℝ × ℝ)) (X Y P Q : ℝ × ℝ -> ℝ)
  (hr : r > 0) (hdet : a * d - b * c ≠ 0)
  (h14 : Cp = ellipse4321 X Y r ->
      I = ((a * d - b * c) /. (Real.pi * r ^ 2)) * (1 /. |a * d - b * c|) * Real.pi * r ^ 2)
  : I = sgn4321 (a * d - b * c) := by
  sorry
