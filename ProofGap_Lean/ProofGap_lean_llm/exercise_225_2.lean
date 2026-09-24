import Mathlib

-- exercise: exercise_225_2
-- InverseFunc is modeled by Mathlib's choice-based inverse of y.
-- All evaluated arguments lie in y's image under the hypotheses.
-- The final bounded lambda is a function on the subtype of nonnegative reals;
-- equality there imposes no assertion about negative arguments.

-- Exercise 225_2, gap 1
-- SHA256: 68d606e4938bd54fc6f06c5f34677c3ebdc480b8fa570f6cf1d875600d2e2ea5
theorem proof_gap_exercise_225_2_1
    (y : ℝ → ℝ)
    (h_square : ∀ x : ℝ, 0 ≤ x → y x = x ^ (2 : ℕ))
    (h_injective : Function.Injective y) :
    ∀ x : ℝ, 0 ≤ x → Function.invFun y (y x) = x := by
  sorry

-- Exercise 225_2, gap 2
-- SHA256: 212fd7283ffece00a3dd97d634605e3d19a2c45f3ef7e2db5a169a6b3ff980e3
theorem proof_gap_exercise_225_2_2
    (y : ℝ → ℝ)
    (h_square : ∀ x : ℝ, 0 ≤ x → y x = x ^ (2 : ℕ))
    (h_inverse : ∀ x : ℝ, 0 ≤ x → Function.invFun y (y x) = x) :
    ∀ t : ℝ, 0 ≤ t → Function.invFun y t = Real.sqrt t := by
  sorry

-- Exercise 225_2, gap 3
-- SHA256: f1f8087810c4dc8c0dc01f2900cd0f40fac8ce39edaa98f3160486d4bc6594d0
theorem proof_gap_exercise_225_2_3
    (y : ℝ → ℝ)
    (h_square : ∀ x : ℝ, 0 ≤ x → y x = x ^ (2 : ℕ))
    (h_inverse : ∀ x : ℝ, 0 ≤ x → Function.invFun y (y x) = x)
    (h_sqrt : ∀ t : ℝ, 0 ≤ t → Function.invFun y t = Real.sqrt t) :
    (fun t : {t : ℝ // 0 ≤ t} => Function.invFun y t.val) =
      (fun t : {t : ℝ // 0 ≤ t} => Real.sqrt t.val) := by
  sorry
