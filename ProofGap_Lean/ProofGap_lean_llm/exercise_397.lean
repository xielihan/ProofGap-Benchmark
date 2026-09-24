import Mathlib

/-- Oscillation on a real set, following predicate explanation Thm 227. -/
noncomputable def exercise397OscillationOn (f : ℝ → ℝ) (s : Set ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ s, ∃ y ∈ s, r = |f x - f y|}


/- Exercise 397, gap 1
PROOF GAP @1
ASSUM:
1. f : RealSet → RealSet
2. `ω_{1}` ∈ RealSet
3. `ω_{2}` ∈ RealSet
4. `ω_{3}` ∈ RealSet
5. `ω_{4}` ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ f(x) = x^{2}
7. OscillationOn(f, IntervalLoRo(1, 3)) = 8
8. `ω_{1}` = 8
GOAL:
`ω_{1}` = OscillationOn(f, IntervalLoRo(1, 3))

METHOD:
-/

theorem proof_gap_exercise_397_1
  (f : ℝ → ℝ) (ω1 ω2 ω3 ω4 : ℝ)
  (h2 : ω1 ∈ (Set.univ : Set ℝ))
  (h3 : ω2 ∈ (Set.univ : Set ℝ))
  (h4 : ω3 ∈ (Set.univ : Set ℝ))
  (h5 : ω4 ∈ (Set.univ : Set ℝ))
  (h6 : ∀ (x : ℝ), x ∈ (Set.univ : Set ℝ) → f x = x ^ (2 : ℕ))
  (h7 : exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)) = (8 : ℝ))
  (h8 : ω1 = (8 : ℝ))
  : ω1 = exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)) := by
  sorry


/- Exercise 397, gap 2
PROOF GAP @2
ASSUM:
1. f : RealSet → RealSet
2. `ω_{1}` ∈ RealSet
3. `ω_{2}` ∈ RealSet
4. `ω_{3}` ∈ RealSet
5. `ω_{4}` ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ f(x) = x^{2}
7. `ω_{1}` = OscillationOn(f, IntervalLoRo(1, 3))

GOAL:
OscillationOn(f, IntervalLoRo(1, 3)) = 9 - 1

METHOD:
-/

theorem proof_gap_exercise_397_2
  (f : ℝ → ℝ) (ω1 ω2 ω3 ω4 : ℝ)
  (h2 : ω1 ∈ (Set.univ : Set ℝ))
  (h3 : ω2 ∈ (Set.univ : Set ℝ))
  (h4 : ω3 ∈ (Set.univ : Set ℝ))
  (h5 : ω4 ∈ (Set.univ : Set ℝ))
  (h6 : ∀ (x : ℝ), x ∈ (Set.univ : Set ℝ) → f x = x ^ (2 : ℕ))
  (h7 : ω1 = exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)))
  : exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)) = (9 : ℝ) - (1 : ℝ) := by
  sorry


/- Exercise 397, gap 3
PROOF GAP @3
ASSUM:
1. f : RealSet → RealSet
2. `ω_{1}` ∈ RealSet
3. `ω_{2}` ∈ RealSet
4. `ω_{3}` ∈ RealSet
5. `ω_{4}` ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ f(x) = x^{2}
7. `ω_{1}` = OscillationOn(f, IntervalLoRo(1, 3))
8. OscillationOn(f, IntervalLoRo(1, 3)) = 9 - 1

GOAL:
9 - 1 = 8

METHOD:
-/

theorem proof_gap_exercise_397_3
  (f : ℝ → ℝ) (ω1 ω2 ω3 ω4 : ℝ)
  (h2 : ω1 ∈ (Set.univ : Set ℝ))
  (h3 : ω2 ∈ (Set.univ : Set ℝ))
  (h4 : ω3 ∈ (Set.univ : Set ℝ))
  (h5 : ω4 ∈ (Set.univ : Set ℝ))
  (h6 : ∀ (x : ℝ), x ∈ (Set.univ : Set ℝ) → f x = x ^ (2 : ℕ))
  (h7 : ω1 = exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)))
  (h8 : exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)) = (9 : ℝ) - (1 : ℝ))
  : (9 : ℝ) - (1 : ℝ) = (8 : ℝ) := by
  sorry


/- Exercise 397, gap 4
PROOF GAP @4
ASSUM:
1. f : RealSet → RealSet
2. `ω_{1}` ∈ RealSet
3. `ω_{2}` ∈ RealSet
4. `ω_{3}` ∈ RealSet
5. `ω_{4}` ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ f(x) = x^{2}
7. `ω_{1}` = OscillationOn(f, IntervalLoRo(1, 3))
8. OscillationOn(f, IntervalLoRo(1, 3)) = 9 - 1
9. 9 - 1 = 8

GOAL:
`ω_{1}` = 8

METHOD:
-/

theorem proof_gap_exercise_397_4
  (f : ℝ → ℝ) (ω1 ω2 ω3 ω4 : ℝ)
  (h2 : ω1 ∈ (Set.univ : Set ℝ))
  (h3 : ω2 ∈ (Set.univ : Set ℝ))
  (h4 : ω3 ∈ (Set.univ : Set ℝ))
  (h5 : ω4 ∈ (Set.univ : Set ℝ))
  (h6 : ∀ (x : ℝ), x ∈ (Set.univ : Set ℝ) → f x = x ^ (2 : ℕ))
  (h7 : ω1 = exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)))
  (h8 : exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)) = (9 : ℝ) - (1 : ℝ))
  (h9 : (9 : ℝ) - (1 : ℝ) = (8 : ℝ))
  : ω1 = (8 : ℝ) := by
  sorry


/- Exercise 397, gap 5
PROOF GAP @5
ASSUM:
1. f : RealSet → RealSet
2. `ω_{1}` ∈ RealSet
3. `ω_{2}` ∈ RealSet
4. `ω_{3}` ∈ RealSet
5. `ω_{4}` ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ f(x) = x^{2}
7. `ω_{1}` = OscillationOn(f, IntervalLoRo(1, 3))
8. OscillationOn(f, IntervalLoRo(1, 3)) = 9 - 1
9. 9 - 1 = 8
10. `ω_{1}` = 8
11. OscillationOn(f, IntervalLoRo(1.9, 2.1)) = 0.8
12. `ω_{2}` = 0.8
GOAL:
`ω_{2}` = OscillationOn(f, IntervalLoRo(1.9, 2.1))

METHOD:
-/

theorem proof_gap_exercise_397_5
  (f : ℝ → ℝ) (ω1 ω2 ω3 ω4 : ℝ)
  (h2 : ω1 ∈ (Set.univ : Set ℝ))
  (h3 : ω2 ∈ (Set.univ : Set ℝ))
  (h4 : ω3 ∈ (Set.univ : Set ℝ))
  (h5 : ω4 ∈ (Set.univ : Set ℝ))
  (h6 : ∀ (x : ℝ), x ∈ (Set.univ : Set ℝ) → f x = x ^ (2 : ℕ))
  (h7 : ω1 = exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)))
  (h8 : exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)) = (9 : ℝ) - (1 : ℝ))
  (h9 : (9 : ℝ) - (1 : ℝ) = (8 : ℝ))
  (h10 : ω1 = (8 : ℝ))
  (h11 : exercise397OscillationOn f (Set.Ioo (1.9 : ℝ) (2.1 : ℝ)) = (0.8 : ℝ))
  (h12 : ω2 = (0.8 : ℝ))
  : ω2 = exercise397OscillationOn f (Set.Ioo (1.9 : ℝ) (2.1 : ℝ)) := by
  sorry


/- Exercise 397, gap 6
PROOF GAP @6
ASSUM:
1. f : RealSet → RealSet
2. `ω_{1}` ∈ RealSet
3. `ω_{2}` ∈ RealSet
4. `ω_{3}` ∈ RealSet
5. `ω_{4}` ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ f(x) = x^{2}
7. `ω_{1}` = OscillationOn(f, IntervalLoRo(1, 3))
8. OscillationOn(f, IntervalLoRo(1, 3)) = 9 - 1
9. 9 - 1 = 8
10. `ω_{1}` = 8
11. `ω_{2}` = OscillationOn(f, IntervalLoRo(1.9, 2.1))

GOAL:
OscillationOn(f, IntervalLoRo(1.9, 2.1)) = 2.1^{2} - 1.9^{2}

METHOD:
-/

theorem proof_gap_exercise_397_6
  (f : ℝ → ℝ) (ω1 ω2 ω3 ω4 : ℝ)
  (h2 : ω1 ∈ (Set.univ : Set ℝ))
  (h3 : ω2 ∈ (Set.univ : Set ℝ))
  (h4 : ω3 ∈ (Set.univ : Set ℝ))
  (h5 : ω4 ∈ (Set.univ : Set ℝ))
  (h6 : ∀ (x : ℝ), x ∈ (Set.univ : Set ℝ) → f x = x ^ (2 : ℕ))
  (h7 : ω1 = exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)))
  (h8 : exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)) = (9 : ℝ) - (1 : ℝ))
  (h9 : (9 : ℝ) - (1 : ℝ) = (8 : ℝ))
  (h10 : ω1 = (8 : ℝ))
  (h11 : ω2 = exercise397OscillationOn f (Set.Ioo (1.9 : ℝ) (2.1 : ℝ)))
  : exercise397OscillationOn f (Set.Ioo (1.9 : ℝ) (2.1 : ℝ)) = (2.1 : ℝ) ^ (2 : ℕ) - (1.9 : ℝ) ^ (2 : ℕ) := by
  sorry


/- Exercise 397, gap 7
PROOF GAP @7
ASSUM:
1. f : RealSet → RealSet
2. `ω_{1}` ∈ RealSet
3. `ω_{2}` ∈ RealSet
4. `ω_{3}` ∈ RealSet
5. `ω_{4}` ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ f(x) = x^{2}
7. `ω_{1}` = OscillationOn(f, IntervalLoRo(1, 3))
8. OscillationOn(f, IntervalLoRo(1, 3)) = 9 - 1
9. 9 - 1 = 8
10. `ω_{1}` = 8
11. `ω_{2}` = OscillationOn(f, IntervalLoRo(1.9, 2.1))
12. OscillationOn(f, IntervalLoRo(1.9, 2.1)) = 2.1^{2} - 1.9^{2}

GOAL:
2.1^{2} - 1.9^{2} = 0.8

METHOD:
-/

theorem proof_gap_exercise_397_7
  (f : ℝ → ℝ) (ω1 ω2 ω3 ω4 : ℝ)
  (h2 : ω1 ∈ (Set.univ : Set ℝ))
  (h3 : ω2 ∈ (Set.univ : Set ℝ))
  (h4 : ω3 ∈ (Set.univ : Set ℝ))
  (h5 : ω4 ∈ (Set.univ : Set ℝ))
  (h6 : ∀ (x : ℝ), x ∈ (Set.univ : Set ℝ) → f x = x ^ (2 : ℕ))
  (h7 : ω1 = exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)))
  (h8 : exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)) = (9 : ℝ) - (1 : ℝ))
  (h9 : (9 : ℝ) - (1 : ℝ) = (8 : ℝ))
  (h10 : ω1 = (8 : ℝ))
  (h11 : ω2 = exercise397OscillationOn f (Set.Ioo (1.9 : ℝ) (2.1 : ℝ)))
  (h12 : exercise397OscillationOn f (Set.Ioo (1.9 : ℝ) (2.1 : ℝ)) = (2.1 : ℝ) ^ (2 : ℕ) - (1.9 : ℝ) ^ (2 : ℕ))
  : (2.1 : ℝ) ^ (2 : ℕ) - (1.9 : ℝ) ^ (2 : ℕ) = (0.8 : ℝ) := by
  sorry


/- Exercise 397, gap 8
PROOF GAP @8
ASSUM:
1. f : RealSet → RealSet
2. `ω_{1}` ∈ RealSet
3. `ω_{2}` ∈ RealSet
4. `ω_{3}` ∈ RealSet
5. `ω_{4}` ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ f(x) = x^{2}
7. `ω_{1}` = OscillationOn(f, IntervalLoRo(1, 3))
8. OscillationOn(f, IntervalLoRo(1, 3)) = 9 - 1
9. 9 - 1 = 8
10. `ω_{1}` = 8
11. `ω_{2}` = OscillationOn(f, IntervalLoRo(1.9, 2.1))
12. OscillationOn(f, IntervalLoRo(1.9, 2.1)) = 2.1^{2} - 1.9^{2}
13. 2.1^{2} - 1.9^{2} = 0.8

GOAL:
`ω_{2}` = 0.8

METHOD:
-/

theorem proof_gap_exercise_397_8
  (f : ℝ → ℝ) (ω1 ω2 ω3 ω4 : ℝ)
  (h2 : ω1 ∈ (Set.univ : Set ℝ))
  (h3 : ω2 ∈ (Set.univ : Set ℝ))
  (h4 : ω3 ∈ (Set.univ : Set ℝ))
  (h5 : ω4 ∈ (Set.univ : Set ℝ))
  (h6 : ∀ (x : ℝ), x ∈ (Set.univ : Set ℝ) → f x = x ^ (2 : ℕ))
  (h7 : ω1 = exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)))
  (h8 : exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)) = (9 : ℝ) - (1 : ℝ))
  (h9 : (9 : ℝ) - (1 : ℝ) = (8 : ℝ))
  (h10 : ω1 = (8 : ℝ))
  (h11 : ω2 = exercise397OscillationOn f (Set.Ioo (1.9 : ℝ) (2.1 : ℝ)))
  (h12 : exercise397OscillationOn f (Set.Ioo (1.9 : ℝ) (2.1 : ℝ)) = (2.1 : ℝ) ^ (2 : ℕ) - (1.9 : ℝ) ^ (2 : ℕ))
  (h13 : (2.1 : ℝ) ^ (2 : ℕ) - (1.9 : ℝ) ^ (2 : ℕ) = (0.8 : ℝ))
  : ω2 = (0.8 : ℝ) := by
  sorry


/- Exercise 397, gap 9
PROOF GAP @9
ASSUM:
1. f : RealSet → RealSet
2. `ω_{1}` ∈ RealSet
3. `ω_{2}` ∈ RealSet
4. `ω_{3}` ∈ RealSet
5. `ω_{4}` ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ f(x) = x^{2}
7. `ω_{1}` = OscillationOn(f, IntervalLoRo(1, 3))
8. OscillationOn(f, IntervalLoRo(1, 3)) = 9 - 1
9. 9 - 1 = 8
10. `ω_{1}` = 8
11. `ω_{2}` = OscillationOn(f, IntervalLoRo(1.9, 2.1))
12. OscillationOn(f, IntervalLoRo(1.9, 2.1)) = 2.1^{2} - 1.9^{2}
13. 2.1^{2} - 1.9^{2} = 0.8
14. `ω_{2}` = 0.8
15. OscillationOn(f, IntervalLoRo(1.99, 2.01)) = 0.08
16. `ω_{3}` = 0.08
GOAL:
`ω_{3}` = OscillationOn(f, IntervalLoRo(1.99, 2.01))

METHOD:
-/

theorem proof_gap_exercise_397_9
  (f : ℝ → ℝ) (ω1 ω2 ω3 ω4 : ℝ)
  (h2 : ω1 ∈ (Set.univ : Set ℝ))
  (h3 : ω2 ∈ (Set.univ : Set ℝ))
  (h4 : ω3 ∈ (Set.univ : Set ℝ))
  (h5 : ω4 ∈ (Set.univ : Set ℝ))
  (h6 : ∀ (x : ℝ), x ∈ (Set.univ : Set ℝ) → f x = x ^ (2 : ℕ))
  (h7 : ω1 = exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)))
  (h8 : exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)) = (9 : ℝ) - (1 : ℝ))
  (h9 : (9 : ℝ) - (1 : ℝ) = (8 : ℝ))
  (h10 : ω1 = (8 : ℝ))
  (h11 : ω2 = exercise397OscillationOn f (Set.Ioo (1.9 : ℝ) (2.1 : ℝ)))
  (h12 : exercise397OscillationOn f (Set.Ioo (1.9 : ℝ) (2.1 : ℝ)) = (2.1 : ℝ) ^ (2 : ℕ) - (1.9 : ℝ) ^ (2 : ℕ))
  (h13 : (2.1 : ℝ) ^ (2 : ℕ) - (1.9 : ℝ) ^ (2 : ℕ) = (0.8 : ℝ))
  (h14 : ω2 = (0.8 : ℝ))
  (h15 : exercise397OscillationOn f (Set.Ioo (1.99 : ℝ) (2.01 : ℝ)) = (0.08 : ℝ))
  (h16 : ω3 = (0.08 : ℝ))
  : ω3 = exercise397OscillationOn f (Set.Ioo (1.99 : ℝ) (2.01 : ℝ)) := by
  sorry


/- Exercise 397, gap 10
PROOF GAP @10
ASSUM:
1. f : RealSet → RealSet
2. `ω_{1}` ∈ RealSet
3. `ω_{2}` ∈ RealSet
4. `ω_{3}` ∈ RealSet
5. `ω_{4}` ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ f(x) = x^{2}
7. `ω_{1}` = OscillationOn(f, IntervalLoRo(1, 3))
8. OscillationOn(f, IntervalLoRo(1, 3)) = 9 - 1
9. 9 - 1 = 8
10. `ω_{1}` = 8
11. `ω_{2}` = OscillationOn(f, IntervalLoRo(1.9, 2.1))
12. OscillationOn(f, IntervalLoRo(1.9, 2.1)) = 2.1^{2} - 1.9^{2}
13. 2.1^{2} - 1.9^{2} = 0.8
14. `ω_{2}` = 0.8
15. `ω_{3}` = OscillationOn(f, IntervalLoRo(1.99, 2.01))

GOAL:
OscillationOn(f, IntervalLoRo(1.99, 2.01)) = 2.01^{2} - 1.99^{2}

METHOD:
-/

theorem proof_gap_exercise_397_10
  (f : ℝ → ℝ) (ω1 ω2 ω3 ω4 : ℝ)
  (h2 : ω1 ∈ (Set.univ : Set ℝ))
  (h3 : ω2 ∈ (Set.univ : Set ℝ))
  (h4 : ω3 ∈ (Set.univ : Set ℝ))
  (h5 : ω4 ∈ (Set.univ : Set ℝ))
  (h6 : ∀ (x : ℝ), x ∈ (Set.univ : Set ℝ) → f x = x ^ (2 : ℕ))
  (h7 : ω1 = exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)))
  (h8 : exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)) = (9 : ℝ) - (1 : ℝ))
  (h9 : (9 : ℝ) - (1 : ℝ) = (8 : ℝ))
  (h10 : ω1 = (8 : ℝ))
  (h11 : ω2 = exercise397OscillationOn f (Set.Ioo (1.9 : ℝ) (2.1 : ℝ)))
  (h12 : exercise397OscillationOn f (Set.Ioo (1.9 : ℝ) (2.1 : ℝ)) = (2.1 : ℝ) ^ (2 : ℕ) - (1.9 : ℝ) ^ (2 : ℕ))
  (h13 : (2.1 : ℝ) ^ (2 : ℕ) - (1.9 : ℝ) ^ (2 : ℕ) = (0.8 : ℝ))
  (h14 : ω2 = (0.8 : ℝ))
  (h15 : ω3 = exercise397OscillationOn f (Set.Ioo (1.99 : ℝ) (2.01 : ℝ)))
  : exercise397OscillationOn f (Set.Ioo (1.99 : ℝ) (2.01 : ℝ)) = (2.01 : ℝ) ^ (2 : ℕ) - (1.99 : ℝ) ^ (2 : ℕ) := by
  sorry


/- Exercise 397, gap 11
PROOF GAP @11
ASSUM:
1. f : RealSet → RealSet
2. `ω_{1}` ∈ RealSet
3. `ω_{2}` ∈ RealSet
4. `ω_{3}` ∈ RealSet
5. `ω_{4}` ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ f(x) = x^{2}
7. `ω_{1}` = OscillationOn(f, IntervalLoRo(1, 3))
8. OscillationOn(f, IntervalLoRo(1, 3)) = 9 - 1
9. 9 - 1 = 8
10. `ω_{1}` = 8
11. `ω_{2}` = OscillationOn(f, IntervalLoRo(1.9, 2.1))
12. OscillationOn(f, IntervalLoRo(1.9, 2.1)) = 2.1^{2} - 1.9^{2}
13. 2.1^{2} - 1.9^{2} = 0.8
14. `ω_{2}` = 0.8
15. `ω_{3}` = OscillationOn(f, IntervalLoRo(1.99, 2.01))
16. OscillationOn(f, IntervalLoRo(1.99, 2.01)) = 2.01^{2} - 1.99^{2}

GOAL:
2.01^{2} - 1.99^{2} = 0.08

METHOD:
-/

theorem proof_gap_exercise_397_11
  (f : ℝ → ℝ) (ω1 ω2 ω3 ω4 : ℝ)
  (h2 : ω1 ∈ (Set.univ : Set ℝ))
  (h3 : ω2 ∈ (Set.univ : Set ℝ))
  (h4 : ω3 ∈ (Set.univ : Set ℝ))
  (h5 : ω4 ∈ (Set.univ : Set ℝ))
  (h6 : ∀ (x : ℝ), x ∈ (Set.univ : Set ℝ) → f x = x ^ (2 : ℕ))
  (h7 : ω1 = exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)))
  (h8 : exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)) = (9 : ℝ) - (1 : ℝ))
  (h9 : (9 : ℝ) - (1 : ℝ) = (8 : ℝ))
  (h10 : ω1 = (8 : ℝ))
  (h11 : ω2 = exercise397OscillationOn f (Set.Ioo (1.9 : ℝ) (2.1 : ℝ)))
  (h12 : exercise397OscillationOn f (Set.Ioo (1.9 : ℝ) (2.1 : ℝ)) = (2.1 : ℝ) ^ (2 : ℕ) - (1.9 : ℝ) ^ (2 : ℕ))
  (h13 : (2.1 : ℝ) ^ (2 : ℕ) - (1.9 : ℝ) ^ (2 : ℕ) = (0.8 : ℝ))
  (h14 : ω2 = (0.8 : ℝ))
  (h15 : ω3 = exercise397OscillationOn f (Set.Ioo (1.99 : ℝ) (2.01 : ℝ)))
  (h16 : exercise397OscillationOn f (Set.Ioo (1.99 : ℝ) (2.01 : ℝ)) = (2.01 : ℝ) ^ (2 : ℕ) - (1.99 : ℝ) ^ (2 : ℕ))
  : (2.01 : ℝ) ^ (2 : ℕ) - (1.99 : ℝ) ^ (2 : ℕ) = (0.08 : ℝ) := by
  sorry


/- Exercise 397, gap 12
PROOF GAP @12
ASSUM:
1. f : RealSet → RealSet
2. `ω_{1}` ∈ RealSet
3. `ω_{2}` ∈ RealSet
4. `ω_{3}` ∈ RealSet
5. `ω_{4}` ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ f(x) = x^{2}
7. `ω_{1}` = OscillationOn(f, IntervalLoRo(1, 3))
8. OscillationOn(f, IntervalLoRo(1, 3)) = 9 - 1
9. 9 - 1 = 8
10. `ω_{1}` = 8
11. `ω_{2}` = OscillationOn(f, IntervalLoRo(1.9, 2.1))
12. OscillationOn(f, IntervalLoRo(1.9, 2.1)) = 2.1^{2} - 1.9^{2}
13. 2.1^{2} - 1.9^{2} = 0.8
14. `ω_{2}` = 0.8
15. `ω_{3}` = OscillationOn(f, IntervalLoRo(1.99, 2.01))
16. OscillationOn(f, IntervalLoRo(1.99, 2.01)) = 2.01^{2} - 1.99^{2}
17. 2.01^{2} - 1.99^{2} = 0.08

GOAL:
`ω_{3}` = 0.08

METHOD:
-/

theorem proof_gap_exercise_397_12
  (f : ℝ → ℝ) (ω1 ω2 ω3 ω4 : ℝ)
  (h2 : ω1 ∈ (Set.univ : Set ℝ))
  (h3 : ω2 ∈ (Set.univ : Set ℝ))
  (h4 : ω3 ∈ (Set.univ : Set ℝ))
  (h5 : ω4 ∈ (Set.univ : Set ℝ))
  (h6 : ∀ (x : ℝ), x ∈ (Set.univ : Set ℝ) → f x = x ^ (2 : ℕ))
  (h7 : ω1 = exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)))
  (h8 : exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)) = (9 : ℝ) - (1 : ℝ))
  (h9 : (9 : ℝ) - (1 : ℝ) = (8 : ℝ))
  (h10 : ω1 = (8 : ℝ))
  (h11 : ω2 = exercise397OscillationOn f (Set.Ioo (1.9 : ℝ) (2.1 : ℝ)))
  (h12 : exercise397OscillationOn f (Set.Ioo (1.9 : ℝ) (2.1 : ℝ)) = (2.1 : ℝ) ^ (2 : ℕ) - (1.9 : ℝ) ^ (2 : ℕ))
  (h13 : (2.1 : ℝ) ^ (2 : ℕ) - (1.9 : ℝ) ^ (2 : ℕ) = (0.8 : ℝ))
  (h14 : ω2 = (0.8 : ℝ))
  (h15 : ω3 = exercise397OscillationOn f (Set.Ioo (1.99 : ℝ) (2.01 : ℝ)))
  (h16 : exercise397OscillationOn f (Set.Ioo (1.99 : ℝ) (2.01 : ℝ)) = (2.01 : ℝ) ^ (2 : ℕ) - (1.99 : ℝ) ^ (2 : ℕ))
  (h17 : (2.01 : ℝ) ^ (2 : ℕ) - (1.99 : ℝ) ^ (2 : ℕ) = (0.08 : ℝ))
  : ω3 = (0.08 : ℝ) := by
  sorry


/- Exercise 397, gap 13
PROOF GAP @13
ASSUM:
1. f : RealSet → RealSet
2. `ω_{1}` ∈ RealSet
3. `ω_{2}` ∈ RealSet
4. `ω_{3}` ∈ RealSet
5. `ω_{4}` ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ f(x) = x^{2}
7. `ω_{1}` = OscillationOn(f, IntervalLoRo(1, 3))
8. OscillationOn(f, IntervalLoRo(1, 3)) = 9 - 1
9. 9 - 1 = 8
10. `ω_{1}` = 8
11. `ω_{2}` = OscillationOn(f, IntervalLoRo(1.9, 2.1))
12. OscillationOn(f, IntervalLoRo(1.9, 2.1)) = 2.1^{2} - 1.9^{2}
13. 2.1^{2} - 1.9^{2} = 0.8
14. `ω_{2}` = 0.8
15. `ω_{3}` = OscillationOn(f, IntervalLoRo(1.99, 2.01))
16. OscillationOn(f, IntervalLoRo(1.99, 2.01)) = 2.01^{2} - 1.99^{2}
17. 2.01^{2} - 1.99^{2} = 0.08
18. `ω_{3}` = 0.08
19. OscillationOn(f, IntervalLoRo(1.999, 2.001)) = 0.008
20. `ω_{4}` = 0.008
GOAL:
`ω_{4}` = OscillationOn(f, IntervalLoRo(1.999, 2.001))

METHOD:
-/

theorem proof_gap_exercise_397_13
  (f : ℝ → ℝ) (ω1 ω2 ω3 ω4 : ℝ)
  (h2 : ω1 ∈ (Set.univ : Set ℝ))
  (h3 : ω2 ∈ (Set.univ : Set ℝ))
  (h4 : ω3 ∈ (Set.univ : Set ℝ))
  (h5 : ω4 ∈ (Set.univ : Set ℝ))
  (h6 : ∀ (x : ℝ), x ∈ (Set.univ : Set ℝ) → f x = x ^ (2 : ℕ))
  (h7 : ω1 = exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)))
  (h8 : exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)) = (9 : ℝ) - (1 : ℝ))
  (h9 : (9 : ℝ) - (1 : ℝ) = (8 : ℝ))
  (h10 : ω1 = (8 : ℝ))
  (h11 : ω2 = exercise397OscillationOn f (Set.Ioo (1.9 : ℝ) (2.1 : ℝ)))
  (h12 : exercise397OscillationOn f (Set.Ioo (1.9 : ℝ) (2.1 : ℝ)) = (2.1 : ℝ) ^ (2 : ℕ) - (1.9 : ℝ) ^ (2 : ℕ))
  (h13 : (2.1 : ℝ) ^ (2 : ℕ) - (1.9 : ℝ) ^ (2 : ℕ) = (0.8 : ℝ))
  (h14 : ω2 = (0.8 : ℝ))
  (h15 : ω3 = exercise397OscillationOn f (Set.Ioo (1.99 : ℝ) (2.01 : ℝ)))
  (h16 : exercise397OscillationOn f (Set.Ioo (1.99 : ℝ) (2.01 : ℝ)) = (2.01 : ℝ) ^ (2 : ℕ) - (1.99 : ℝ) ^ (2 : ℕ))
  (h17 : (2.01 : ℝ) ^ (2 : ℕ) - (1.99 : ℝ) ^ (2 : ℕ) = (0.08 : ℝ))
  (h18 : ω3 = (0.08 : ℝ))
  (h19 : exercise397OscillationOn f (Set.Ioo (1.999 : ℝ) (2.001 : ℝ)) = (0.008 : ℝ))
  (h20 : ω4 = (0.008 : ℝ))
  : ω4 = exercise397OscillationOn f (Set.Ioo (1.999 : ℝ) (2.001 : ℝ)) := by
  sorry


/- Exercise 397, gap 14
PROOF GAP @14
ASSUM:
1. f : RealSet → RealSet
2. `ω_{1}` ∈ RealSet
3. `ω_{2}` ∈ RealSet
4. `ω_{3}` ∈ RealSet
5. `ω_{4}` ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ f(x) = x^{2}
7. `ω_{1}` = OscillationOn(f, IntervalLoRo(1, 3))
8. OscillationOn(f, IntervalLoRo(1, 3)) = 9 - 1
9. 9 - 1 = 8
10. `ω_{1}` = 8
11. `ω_{2}` = OscillationOn(f, IntervalLoRo(1.9, 2.1))
12. OscillationOn(f, IntervalLoRo(1.9, 2.1)) = 2.1^{2} - 1.9^{2}
13. 2.1^{2} - 1.9^{2} = 0.8
14. `ω_{2}` = 0.8
15. `ω_{3}` = OscillationOn(f, IntervalLoRo(1.99, 2.01))
16. OscillationOn(f, IntervalLoRo(1.99, 2.01)) = 2.01^{2} - 1.99^{2}
17. 2.01^{2} - 1.99^{2} = 0.08
18. `ω_{3}` = 0.08
19. `ω_{4}` = OscillationOn(f, IntervalLoRo(1.999, 2.001))

GOAL:
OscillationOn(f, IntervalLoRo(1.999, 2.001)) = 2.001^{2} - 1.999^{2}

METHOD:
-/

theorem proof_gap_exercise_397_14
  (f : ℝ → ℝ) (ω1 ω2 ω3 ω4 : ℝ)
  (h2 : ω1 ∈ (Set.univ : Set ℝ))
  (h3 : ω2 ∈ (Set.univ : Set ℝ))
  (h4 : ω3 ∈ (Set.univ : Set ℝ))
  (h5 : ω4 ∈ (Set.univ : Set ℝ))
  (h6 : ∀ (x : ℝ), x ∈ (Set.univ : Set ℝ) → f x = x ^ (2 : ℕ))
  (h7 : ω1 = exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)))
  (h8 : exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)) = (9 : ℝ) - (1 : ℝ))
  (h9 : (9 : ℝ) - (1 : ℝ) = (8 : ℝ))
  (h10 : ω1 = (8 : ℝ))
  (h11 : ω2 = exercise397OscillationOn f (Set.Ioo (1.9 : ℝ) (2.1 : ℝ)))
  (h12 : exercise397OscillationOn f (Set.Ioo (1.9 : ℝ) (2.1 : ℝ)) = (2.1 : ℝ) ^ (2 : ℕ) - (1.9 : ℝ) ^ (2 : ℕ))
  (h13 : (2.1 : ℝ) ^ (2 : ℕ) - (1.9 : ℝ) ^ (2 : ℕ) = (0.8 : ℝ))
  (h14 : ω2 = (0.8 : ℝ))
  (h15 : ω3 = exercise397OscillationOn f (Set.Ioo (1.99 : ℝ) (2.01 : ℝ)))
  (h16 : exercise397OscillationOn f (Set.Ioo (1.99 : ℝ) (2.01 : ℝ)) = (2.01 : ℝ) ^ (2 : ℕ) - (1.99 : ℝ) ^ (2 : ℕ))
  (h17 : (2.01 : ℝ) ^ (2 : ℕ) - (1.99 : ℝ) ^ (2 : ℕ) = (0.08 : ℝ))
  (h18 : ω3 = (0.08 : ℝ))
  (h19 : ω4 = exercise397OscillationOn f (Set.Ioo (1.999 : ℝ) (2.001 : ℝ)))
  : exercise397OscillationOn f (Set.Ioo (1.999 : ℝ) (2.001 : ℝ)) = (2.001 : ℝ) ^ (2 : ℕ) - (1.999 : ℝ) ^ (2 : ℕ) := by
  sorry


/- Exercise 397, gap 15
PROOF GAP @15
ASSUM:
1. f : RealSet → RealSet
2. `ω_{1}` ∈ RealSet
3. `ω_{2}` ∈ RealSet
4. `ω_{3}` ∈ RealSet
5. `ω_{4}` ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ f(x) = x^{2}
7. `ω_{1}` = OscillationOn(f, IntervalLoRo(1, 3))
8. OscillationOn(f, IntervalLoRo(1, 3)) = 9 - 1
9. 9 - 1 = 8
10. `ω_{1}` = 8
11. `ω_{2}` = OscillationOn(f, IntervalLoRo(1.9, 2.1))
12. OscillationOn(f, IntervalLoRo(1.9, 2.1)) = 2.1^{2} - 1.9^{2}
13. 2.1^{2} - 1.9^{2} = 0.8
14. `ω_{2}` = 0.8
15. `ω_{3}` = OscillationOn(f, IntervalLoRo(1.99, 2.01))
16. OscillationOn(f, IntervalLoRo(1.99, 2.01)) = 2.01^{2} - 1.99^{2}
17. 2.01^{2} - 1.99^{2} = 0.08
18. `ω_{3}` = 0.08
19. `ω_{4}` = OscillationOn(f, IntervalLoRo(1.999, 2.001))
20. OscillationOn(f, IntervalLoRo(1.999, 2.001)) = 2.001^{2} - 1.999^{2}

GOAL:
2.001^{2} - 1.999^{2} = 0.008

METHOD:
-/

theorem proof_gap_exercise_397_15
  (f : ℝ → ℝ) (ω1 ω2 ω3 ω4 : ℝ)
  (h2 : ω1 ∈ (Set.univ : Set ℝ))
  (h3 : ω2 ∈ (Set.univ : Set ℝ))
  (h4 : ω3 ∈ (Set.univ : Set ℝ))
  (h5 : ω4 ∈ (Set.univ : Set ℝ))
  (h6 : ∀ (x : ℝ), x ∈ (Set.univ : Set ℝ) → f x = x ^ (2 : ℕ))
  (h7 : ω1 = exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)))
  (h8 : exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)) = (9 : ℝ) - (1 : ℝ))
  (h9 : (9 : ℝ) - (1 : ℝ) = (8 : ℝ))
  (h10 : ω1 = (8 : ℝ))
  (h11 : ω2 = exercise397OscillationOn f (Set.Ioo (1.9 : ℝ) (2.1 : ℝ)))
  (h12 : exercise397OscillationOn f (Set.Ioo (1.9 : ℝ) (2.1 : ℝ)) = (2.1 : ℝ) ^ (2 : ℕ) - (1.9 : ℝ) ^ (2 : ℕ))
  (h13 : (2.1 : ℝ) ^ (2 : ℕ) - (1.9 : ℝ) ^ (2 : ℕ) = (0.8 : ℝ))
  (h14 : ω2 = (0.8 : ℝ))
  (h15 : ω3 = exercise397OscillationOn f (Set.Ioo (1.99 : ℝ) (2.01 : ℝ)))
  (h16 : exercise397OscillationOn f (Set.Ioo (1.99 : ℝ) (2.01 : ℝ)) = (2.01 : ℝ) ^ (2 : ℕ) - (1.99 : ℝ) ^ (2 : ℕ))
  (h17 : (2.01 : ℝ) ^ (2 : ℕ) - (1.99 : ℝ) ^ (2 : ℕ) = (0.08 : ℝ))
  (h18 : ω3 = (0.08 : ℝ))
  (h19 : ω4 = exercise397OscillationOn f (Set.Ioo (1.999 : ℝ) (2.001 : ℝ)))
  (h20 : exercise397OscillationOn f (Set.Ioo (1.999 : ℝ) (2.001 : ℝ)) = (2.001 : ℝ) ^ (2 : ℕ) - (1.999 : ℝ) ^ (2 : ℕ))
  : (2.001 : ℝ) ^ (2 : ℕ) - (1.999 : ℝ) ^ (2 : ℕ) = (0.008 : ℝ) := by
  sorry


/- Exercise 397, gap 16
PROOF GAP @16
ASSUM:
1. f : RealSet → RealSet
2. `ω_{1}` ∈ RealSet
3. `ω_{2}` ∈ RealSet
4. `ω_{3}` ∈ RealSet
5. `ω_{4}` ∈ RealSet
6. forall (x), x ∈ RealSet ⇒ f(x) = x^{2}
7. `ω_{1}` = OscillationOn(f, IntervalLoRo(1, 3))
8. OscillationOn(f, IntervalLoRo(1, 3)) = 9 - 1
9. 9 - 1 = 8
10. `ω_{1}` = 8
11. `ω_{2}` = OscillationOn(f, IntervalLoRo(1.9, 2.1))
12. OscillationOn(f, IntervalLoRo(1.9, 2.1)) = 2.1^{2} - 1.9^{2}
13. 2.1^{2} - 1.9^{2} = 0.8
14. `ω_{2}` = 0.8
15. `ω_{3}` = OscillationOn(f, IntervalLoRo(1.99, 2.01))
16. OscillationOn(f, IntervalLoRo(1.99, 2.01)) = 2.01^{2} - 1.99^{2}
17. 2.01^{2} - 1.99^{2} = 0.08
18. `ω_{3}` = 0.08
19. `ω_{4}` = OscillationOn(f, IntervalLoRo(1.999, 2.001))
20. OscillationOn(f, IntervalLoRo(1.999, 2.001)) = 2.001^{2} - 1.999^{2}
21. 2.001^{2} - 1.999^{2} = 0.008

GOAL:
`ω_{4}` = 0.008

METHOD:
-/

theorem proof_gap_exercise_397_16
  (f : ℝ → ℝ) (ω1 ω2 ω3 ω4 : ℝ)
  (h2 : ω1 ∈ (Set.univ : Set ℝ))
  (h3 : ω2 ∈ (Set.univ : Set ℝ))
  (h4 : ω3 ∈ (Set.univ : Set ℝ))
  (h5 : ω4 ∈ (Set.univ : Set ℝ))
  (h6 : ∀ (x : ℝ), x ∈ (Set.univ : Set ℝ) → f x = x ^ (2 : ℕ))
  (h7 : ω1 = exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)))
  (h8 : exercise397OscillationOn f (Set.Ioo (1 : ℝ) (3 : ℝ)) = (9 : ℝ) - (1 : ℝ))
  (h9 : (9 : ℝ) - (1 : ℝ) = (8 : ℝ))
  (h10 : ω1 = (8 : ℝ))
  (h11 : ω2 = exercise397OscillationOn f (Set.Ioo (1.9 : ℝ) (2.1 : ℝ)))
  (h12 : exercise397OscillationOn f (Set.Ioo (1.9 : ℝ) (2.1 : ℝ)) = (2.1 : ℝ) ^ (2 : ℕ) - (1.9 : ℝ) ^ (2 : ℕ))
  (h13 : (2.1 : ℝ) ^ (2 : ℕ) - (1.9 : ℝ) ^ (2 : ℕ) = (0.8 : ℝ))
  (h14 : ω2 = (0.8 : ℝ))
  (h15 : ω3 = exercise397OscillationOn f (Set.Ioo (1.99 : ℝ) (2.01 : ℝ)))
  (h16 : exercise397OscillationOn f (Set.Ioo (1.99 : ℝ) (2.01 : ℝ)) = (2.01 : ℝ) ^ (2 : ℕ) - (1.99 : ℝ) ^ (2 : ℕ))
  (h17 : (2.01 : ℝ) ^ (2 : ℕ) - (1.99 : ℝ) ^ (2 : ℕ) = (0.08 : ℝ))
  (h18 : ω3 = (0.08 : ℝ))
  (h19 : ω4 = exercise397OscillationOn f (Set.Ioo (1.999 : ℝ) (2.001 : ℝ)))
  (h20 : exercise397OscillationOn f (Set.Ioo (1.999 : ℝ) (2.001 : ℝ)) = (2.001 : ℝ) ^ (2 : ℕ) - (1.999 : ℝ) ^ (2 : ℕ))
  (h21 : (2.001 : ℝ) ^ (2 : ℕ) - (1.999 : ℝ) ^ (2 : ℕ) = (0.008 : ℝ))
  : ω4 = (0.008 : ℝ) := by
  sorry
