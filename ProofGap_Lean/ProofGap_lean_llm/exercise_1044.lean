import Mathlib

set_option linter.style.longLine false

-- Function-selector derivative, as defined by the repository's lpFunDeri.
-- For real unary functions this is deriv f u / deriv g u (totalized at zero).
noncomputable def exercise1044FunDeri (f g : ℝ → ℝ) : ℝ → ℝ :=
  fun u => inner ℝ (gradient f u) (gradient g u) / ‖gradient g u‖ ^ 2

-- Domain of the graph of a total real function (Thm 220).
def exercise1044Dom (f : ℝ → ℝ) : Set ℝ :=
  {u | ∃ v : ℝ, f u = v}

/- Exercise 1044, gap 1
SHA-256: 8f7f1857cb5768b262a950331bb2c2b6c9a2bd68c98a235fa0bba41b539942ed
PROOF GAP @1
ASSUM:
1. x : RealSet → RealSet
2. y : RealSet → RealSet
3. F : RealSet → RealSet
4. a ∈ RealSet
5. a ≠ 0
6. forall (t), t ∈ RealSet ⇒ x(t) = a * (t - sin(t))
7. forall (t), t ∈ RealSet ⇒ y(t) = a * (1 - cos(t))
8. forall (t), t ∈ RealSet ∧ x(t) ∈ Dom(F) ⇒ y(t) = F(x(t))

GOAL:
forall (t), t ∈ RealSet ⇒ FunDeri(x, 1, 1)(t) = a * (1 - cos(t)) ∧ FunDeri(y, 1, 1)(t) = a * sin(t)

METHOD:

-/
theorem proof_gap_exercise_1044_1
  (x y F : ℝ → ℝ) (a : ℝ)
  (h4 : a ∈ (Set.univ : Set ℝ))
  (h5 : a ≠ 0)
  (h6 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) → x t = a * (t - Real.sin t))
  (h7 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) → y t = a * (1 - Real.cos t))
  (h8 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ x t ∈ exercise1044Dom F →
    y t = F (x t))
  : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) →
      deriv x t = a * (1 - Real.cos t) ∧ deriv y t = a * Real.sin t := by
  sorry

/- Exercise 1044, gap 2
SHA-256: 2cb38500080d9aa87b98ca5526bff61cbd48ce35cf386dafe1934335801e402e
PROOF GAP @2
ASSUM:
1. x : RealSet → RealSet
2. y : RealSet → RealSet
3. F : RealSet → RealSet
4. a ∈ RealSet
5. a ≠ 0
6. forall (t), t ∈ RealSet ⇒ x(t) = a * (t - sin(t))
7. forall (t), t ∈ RealSet ⇒ y(t) = a * (1 - cos(t))
8. forall (t), t ∈ RealSet ∧ x(t) ∈ Dom(F) ⇒ y(t) = F(x(t))
9. forall (t), t ∈ RealSet ⇒ FunDeri(x, 1, 1)(t) = a * (1 - cos(t)) ∧ FunDeri(y, 1, 1)(t) = a * sin(t)

GOAL:
forall (k), k ∈ IntegerSet ⇒ (forall (t), t ∈ RealSet ∧ t ≠ 2 * k * π ∧ k ∈ IntegerSet ⇒ FunDeri(F, x, 1)(x(t)) = frac(FunDeri(y, 1, 1)(t), FunDeri(x, 1, 1)(t)) ∧ frac(FunDeri(y, 1, 1)(t), FunDeri(x, 1, 1)(t)) = frac(a * sin(t), a * (1 - cos(t))) ∧ frac(a * sin(t), a * (1 - cos(t))) = cot(frac(t, 2)))

METHOD:

-/
theorem proof_gap_exercise_1044_2
  (x y F : ℝ → ℝ) (a : ℝ)
  (h4 : a ∈ (Set.univ : Set ℝ))
  (h5 : a ≠ 0)
  (h6 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) → x t = a * (t - Real.sin t))
  (h7 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) → y t = a * (1 - Real.cos t))
  (h8 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ x t ∈ exercise1044Dom F →
    y t = F (x t))
  (h9 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) →
    deriv x t = a * (1 - Real.cos t) ∧ deriv y t = a * Real.sin t)
  : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) →
      ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t ≠ 2 * (k : ℝ) * Real.pi ∧
        k ∈ (Set.univ : Set ℤ) →
      exercise1044FunDeri F x (x t) = deriv y t / deriv x t ∧
      deriv y t / deriv x t = (a * Real.sin t) / (a * (1 - Real.cos t)) ∧
      (a * Real.sin t) / (a * (1 - Real.cos t)) = 1 / Real.tan (t / 2) := by
  sorry
