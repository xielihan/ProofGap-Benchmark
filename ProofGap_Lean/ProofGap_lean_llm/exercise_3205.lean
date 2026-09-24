import Mathlib

set_option linter.style.longLine false

noncomputable section

-- exercise: exercise_3205

def ContinuousInXOn (f : ℝ × ℝ -> ℝ) (G : Set (ℝ × ℝ)) : Prop :=
  ∀ x y0 : ℝ, ContinuousOn (fun x' => f (x', y0)) {x' | (x', y0) ∈ G}

def UniformContinuousInYOn (f : ℝ × ℝ -> ℝ) (G : Set (ℝ × ℝ)) : Prop :=
  ∀ eps > 0, ∃ d1 > 0, ∀ x y' y'' : ℝ,
    (x, y') ∈ G -> (x, y'') ∈ G -> |y' - y''| < d1 ->
      |f (x, y') - f (x, y'')| < eps / 2

theorem proof_gap_exercise_3205_1
  (f : ℝ × ℝ -> ℝ) (G : Set (ℝ × ℝ))
  (hxin : ContinuousInXOn f G)
  (hyunif : UniformContinuousInYOn f G)
  : ∀ x0 y0 : ℝ, (x0, y0) ∈ G ->
      ∀ eps > 0, ∃ d1 > 0, ∀ x y' y'' : ℝ,
        (x, y') ∈ G -> (x, y'') ∈ G -> |y' - y''| < d1 ->
          |f (x, y') - f (x, y'')| < eps / 2 := by
  sorry

theorem proof_gap_exercise_3205_2
  (f : ℝ × ℝ -> ℝ) (G : Set (ℝ × ℝ))
  (hxin : ContinuousInXOn f G)
  (hyunif : UniformContinuousInYOn f G)
  (h1 : ∀ x0 y0 : ℝ, (x0, y0) ∈ G ->
      ∀ eps > 0, ∃ d1 > 0, ∀ x y' y'' : ℝ,
        (x, y') ∈ G -> (x, y'') ∈ G -> |y' - y''| < d1 ->
          |f (x, y') - f (x, y'')| < eps / 2)
  : ∀ x0 y0 : ℝ, (x0, y0) ∈ G ->
      ∀ eps > 0, ∃ d2 > 0, ∀ x : ℝ,
        |x - x0| < d2 -> (x, y0) ∈ G ->
          |f (x, y0) - f (x0, y0)| < eps / 2 := by
  sorry

theorem proof_gap_exercise_3205_3
  (f : ℝ × ℝ -> ℝ) (G : Set (ℝ × ℝ))
  (h2 : ∀ x0 y0 : ℝ, (x0, y0) ∈ G ->
      ∀ eps > 0, ∃ d2 > 0, ∀ x : ℝ,
        |x - x0| < d2 -> (x, y0) ∈ G ->
          |f (x, y0) - f (x0, y0)| < eps / 2)
  : ∀ x0 y0 d1 d2 x y : ℝ, (x0, y0) ∈ G ->
      ∀ eps delta : ℝ, eps > 0 -> delta = min d1 d2 ->
        (x, y) ∈ G -> dist (x, y) (x0, y0) < delta ->
          |x - x0| < delta := by
  sorry

theorem proof_gap_exercise_3205_4
  (f : ℝ × ℝ -> ℝ) (G : Set (ℝ × ℝ))
  (h3 : ∀ x0 y0 d1 d2 x y : ℝ, (x0, y0) ∈ G ->
      ∀ eps delta : ℝ, eps > 0 -> delta = min d1 d2 ->
        (x, y) ∈ G -> dist (x, y) (x0, y0) < delta ->
          |x - x0| < delta)
  : ∀ x0 y0 d1 d2 x y : ℝ, (x0, y0) ∈ G ->
      ∀ eps delta : ℝ, eps > 0 -> delta = min d1 d2 ->
        (x, y) ∈ G -> dist (x, y) (x0, y0) < delta ->
          delta ≤ d2 := by
  sorry

theorem proof_gap_exercise_3205_5
  (f : ℝ × ℝ -> ℝ) (G : Set (ℝ × ℝ))
  (h3 : ∀ x0 y0 d1 d2 x y : ℝ, (x0, y0) ∈ G ->
      ∀ eps delta : ℝ, eps > 0 -> delta = min d1 d2 ->
        (x, y) ∈ G -> dist (x, y) (x0, y0) < delta ->
          |x - x0| < delta)
  (h4 : ∀ x0 y0 d1 d2 x y : ℝ, (x0, y0) ∈ G ->
      ∀ eps delta : ℝ, eps > 0 -> delta = min d1 d2 ->
        (x, y) ∈ G -> dist (x, y) (x0, y0) < delta ->
          delta ≤ d2)
  : ∀ x0 y0 d1 d2 x y : ℝ, (x0, y0) ∈ G ->
      ∀ eps delta : ℝ, eps > 0 -> delta = min d1 d2 ->
        (x, y) ∈ G -> dist (x, y) (x0, y0) < delta ->
          |x - x0| < d2 := by
  sorry

theorem proof_gap_exercise_3205_6
  (f : ℝ × ℝ -> ℝ) (G : Set (ℝ × ℝ))
  : ∀ x0 y0 d1 d2 x y : ℝ, (x0, y0) ∈ G ->
      ∀ eps delta : ℝ, eps > 0 -> delta = min d1 d2 ->
        (x, y) ∈ G -> dist (x, y) (x0, y0) < delta ->
          |y - y0| < delta := by
  sorry

theorem proof_gap_exercise_3205_7
  (f : ℝ × ℝ -> ℝ) (G : Set (ℝ × ℝ))
  : ∀ x0 y0 d1 d2 x y : ℝ, (x0, y0) ∈ G ->
      ∀ eps delta : ℝ, eps > 0 -> delta = min d1 d2 ->
        (x, y) ∈ G -> dist (x, y) (x0, y0) < delta ->
          delta ≤ d1 := by
  sorry

theorem proof_gap_exercise_3205_8
  (f : ℝ × ℝ -> ℝ) (G : Set (ℝ × ℝ))
  (h6 : ∀ x0 y0 d1 d2 x y : ℝ, (x0, y0) ∈ G ->
      ∀ eps delta : ℝ, eps > 0 -> delta = min d1 d2 ->
        (x, y) ∈ G -> dist (x, y) (x0, y0) < delta ->
          |y - y0| < delta)
  (h7 : ∀ x0 y0 d1 d2 x y : ℝ, (x0, y0) ∈ G ->
      ∀ eps delta : ℝ, eps > 0 -> delta = min d1 d2 ->
        (x, y) ∈ G -> dist (x, y) (x0, y0) < delta ->
          delta ≤ d1)
  : ∀ x0 y0 d1 d2 x y : ℝ, (x0, y0) ∈ G ->
      ∀ eps delta : ℝ, eps > 0 -> delta = min d1 d2 ->
        (x, y) ∈ G -> dist (x, y) (x0, y0) < delta ->
          |y - y0| < d1 := by
  sorry

theorem proof_gap_exercise_3205_9
  (f : ℝ × ℝ -> ℝ) (G : Set (ℝ × ℝ))
  (hyunif : UniformContinuousInYOn f G)
  (h8 : ∀ x0 y0 d1 d2 x y : ℝ, (x0, y0) ∈ G ->
      ∀ eps delta : ℝ, eps > 0 -> delta = min d1 d2 ->
        (x, y) ∈ G -> dist (x, y) (x0, y0) < delta ->
          |y - y0| < d1)
  : ∀ x0 y0 d1 d2 x y : ℝ, (x0, y0) ∈ G -> (x, y0) ∈ G ->
      ∀ eps delta : ℝ, eps > 0 -> delta = min d1 d2 ->
        (x, y) ∈ G -> dist (x, y) (x0, y0) < delta ->
          |f (x, y) - f (x, y0)| < eps / 2 := by
  sorry

theorem proof_gap_exercise_3205_10
  (f : ℝ × ℝ -> ℝ) (G : Set (ℝ × ℝ))
  (h2 : ∀ x0 y0 : ℝ, (x0, y0) ∈ G ->
      ∀ eps > 0, ∃ d2 > 0, ∀ x : ℝ,
        |x - x0| < d2 -> (x, y0) ∈ G ->
          |f (x, y0) - f (x0, y0)| < eps / 2)
  (h5 : ∀ x0 y0 d1 d2 x y : ℝ, (x0, y0) ∈ G ->
      ∀ eps delta : ℝ, eps > 0 -> delta = min d1 d2 ->
        (x, y) ∈ G -> dist (x, y) (x0, y0) < delta ->
          |x - x0| < d2)
  : ∀ x0 y0 d1 d2 x y : ℝ, (x0, y0) ∈ G -> (x, y0) ∈ G ->
      ∀ eps delta : ℝ, eps > 0 -> delta = min d1 d2 ->
        (x, y) ∈ G -> dist (x, y) (x0, y0) < delta ->
          |f (x, y0) - f (x0, y0)| < eps / 2 := by
  sorry

theorem proof_gap_exercise_3205_11
  (f : ℝ × ℝ -> ℝ) (G : Set (ℝ × ℝ))
  : ∀ x0 y0 d1 d2 x y : ℝ, (x0, y0) ∈ G ->
      ∀ eps delta : ℝ, eps > 0 -> delta = min d1 d2 ->
        (x, y) ∈ G -> dist (x, y) (x0, y0) < delta ->
          |f (x, y) - f (x0, y0)| ≤
            |f (x, y) - f (x, y0)| + |f (x, y0) - f (x0, y0)| := by
  sorry

theorem proof_gap_exercise_3205_12
  (f : ℝ × ℝ -> ℝ) (G : Set (ℝ × ℝ))
  (h9 : ∀ x0 y0 d1 d2 x y : ℝ, (x0, y0) ∈ G -> (x, y0) ∈ G ->
      ∀ eps delta : ℝ, eps > 0 -> delta = min d1 d2 ->
        (x, y) ∈ G -> dist (x, y) (x0, y0) < delta ->
          |f (x, y) - f (x, y0)| < eps / 2)
  (h10 : ∀ x0 y0 d1 d2 x y : ℝ, (x0, y0) ∈ G -> (x, y0) ∈ G ->
      ∀ eps delta : ℝ, eps > 0 -> delta = min d1 d2 ->
        (x, y) ∈ G -> dist (x, y) (x0, y0) < delta ->
          |f (x, y0) - f (x0, y0)| < eps / 2)
  : ∀ x0 y0 d1 d2 x y : ℝ, (x0, y0) ∈ G -> (x, y0) ∈ G ->
      ∀ eps delta : ℝ, eps > 0 -> delta = min d1 d2 ->
        (x, y) ∈ G -> dist (x, y) (x0, y0) < delta ->
          |f (x, y) - f (x, y0)| + |f (x, y0) - f (x0, y0)| < eps / 2 + eps / 2 := by
  sorry

theorem proof_gap_exercise_3205_13
  (f : ℝ × ℝ -> ℝ) (G : Set (ℝ × ℝ))
  : ∀ x0 y0 d1 d2 x y : ℝ, (x0, y0) ∈ G ->
      ∀ eps delta : ℝ, eps > 0 -> delta = min d1 d2 ->
        (x, y) ∈ G -> dist (x, y) (x0, y0) < delta ->
          eps / 2 + eps / 2 = eps := by
  sorry

theorem proof_gap_exercise_3205_14
  (f : ℝ × ℝ -> ℝ) (G : Set (ℝ × ℝ))
  (h11 : ∀ x0 y0 d1 d2 x y : ℝ, (x0, y0) ∈ G ->
      ∀ eps delta : ℝ, eps > 0 -> delta = min d1 d2 ->
        (x, y) ∈ G -> dist (x, y) (x0, y0) < delta ->
          |f (x, y) - f (x0, y0)| ≤
            |f (x, y) - f (x, y0)| + |f (x, y0) - f (x0, y0)|)
  (h12 : ∀ x0 y0 d1 d2 x y : ℝ, (x0, y0) ∈ G -> (x, y0) ∈ G ->
      ∀ eps delta : ℝ, eps > 0 -> delta = min d1 d2 ->
        (x, y) ∈ G -> dist (x, y) (x0, y0) < delta ->
          |f (x, y) - f (x, y0)| + |f (x, y0) - f (x0, y0)| < eps / 2 + eps / 2)
  (h13 : ∀ x0 y0 d1 d2 x y : ℝ, (x0, y0) ∈ G ->
      ∀ eps delta : ℝ, eps > 0 -> delta = min d1 d2 ->
        (x, y) ∈ G -> dist (x, y) (x0, y0) < delta ->
          eps / 2 + eps / 2 = eps)
  : ∀ x0 y0 d1 d2 x y : ℝ, (x0, y0) ∈ G -> (x, y0) ∈ G ->
      ∀ eps delta : ℝ, eps > 0 -> delta = min d1 d2 ->
        (x, y) ∈ G -> dist (x, y) (x0, y0) < delta ->
          |f (x, y) - f (x0, y0)| < eps := by
  sorry

theorem proof_gap_exercise_3205_15
  (f : ℝ × ℝ -> ℝ) (G : Set (ℝ × ℝ))
  (h_point : ∀ x0 y0 : ℝ, (x0, y0) ∈ G ->
      ∀ eps > 0, ∃ delta > 0, ∀ x y : ℝ, (x, y) ∈ G ->
        dist (x, y) (x0, y0) < delta ->
          |f (x, y) - f (x0, y0)| < eps)
  : ContinuousOn f G := by
  sorry

