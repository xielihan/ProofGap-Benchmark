import Mathlib

-- A real function with an explicit source domain and a total representative.
-- Ordinary derivatives follow the ambient limits in source Thm 277.
namespace Exercise1125

structure DomainFunction where
  domain : Set ℝ
  value : ℝ → ℝ

def graph (f : DomainFunction) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ f.domain ∧ p.2 = f.value p.1}

def dom (f : DomainFunction) : Set ℝ :=
  {t | ∃ z, (t, z) ∈ graph f}

-- Literal expansion of source Thm 286 (including n = k).
def sourceClassOn (f : ℝ → ℝ) (s : Set ℝ) (k : ℕ) : Prop :=
  (∀ n : ℕ, n ≤ k → ∀ x ∈ s, DifferentiableAt ℝ (iteratedDeriv n f) x) ∧
  (∀ x ∈ s, ContinuousAt (iteratedDeriv k f) x)

end Exercise1125

open Exercise1125

/- Exercise 1125, gap 1
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. f : RealSet → RealSet
3. I ⊆ RealSet
4. forall (t), t ∈ RealSet ⇒ (t ∈ Dom(f) ⇔ (exists (x), x ∈ RealSet ∧ x ∈ I ∧ t = x^{2}))
5. FuncOfClassKOn(f, Dom(f), 3)
6. forall (x), x ∈ RealSet ∧ x ∈ I ⇒ y(x) = f(x^{2})

GOAL:
forall (x), x ∈ RealSet ∧ x ∈ I ⇒ FunDeri(y, 1, 1)(x) = 2 * x * FunDeri(f, 1, 1)(x^{2})

METHOD:

-/
theorem proof_gap_exercise_1125_1
  (y : ℝ → ℝ) (f : DomainFunction) (I : Set ℝ)
  (hI : I ⊆ (Set.univ : Set ℝ))
  (hdom : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) →
    (t ∈ dom f ↔ ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I ∧ t = x ^ 2))
  (hclass : sourceClassOn f.value (dom f) 3)
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I → y x = f.value (x ^ 2))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I → iteratedDeriv 1 y x = 2 * x * iteratedDeriv 1 f.value (x ^ 2) := by
  sorry

/- Exercise 1125, gap 2
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. f : RealSet → RealSet
3. I ⊆ RealSet
4. forall (t), t ∈ RealSet ⇒ (t ∈ Dom(f) ⇔ (exists (x), x ∈ RealSet ∧ x ∈ I ∧ t = x^{2}))
5. FuncOfClassKOn(f, Dom(f), 3)
6. forall (x), x ∈ RealSet ∧ x ∈ I ⇒ y(x) = f(x^{2})
7. forall (x), x ∈ RealSet ∧ x ∈ I ⇒ FunDeri(y, 1, 1)(x) = 2 * x * FunDeri(f, 1, 1)(x^{2})

GOAL:
forall (x), x ∈ RealSet ∧ x ∈ I ⇒ FunDeri(y, 1, 2)(x) = 2 * FunDeri(f, 1, 1)(x^{2}) + 4 * x^{2} * FunDeri(f, 1, 2)(x^{2})

METHOD:

-/
theorem proof_gap_exercise_1125_2
  (y : ℝ → ℝ) (f : DomainFunction) (I : Set ℝ)
  (hI : I ⊆ (Set.univ : Set ℝ))
  (hdom : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) →
    (t ∈ dom f ↔ ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I ∧ t = x ^ 2))
  (hclass : sourceClassOn f.value (dom f) 3)
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I → y x = f.value (x ^ 2))
  (hfirst : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I → iteratedDeriv 1 y x = 2 * x * iteratedDeriv 1 f.value (x ^ 2))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I → iteratedDeriv 2 y x = 2 * iteratedDeriv 1 f.value (x ^ 2) + 4 * x ^ 2 * iteratedDeriv 2 f.value (x ^ 2) := by
  sorry

/- Exercise 1125, gap 3
PROOF GAP @3
ASSUM:
1. y : RealSet → RealSet
2. f : RealSet → RealSet
3. I ⊆ RealSet
4. forall (t), t ∈ RealSet ⇒ (t ∈ Dom(f) ⇔ (exists (x), x ∈ RealSet ∧ x ∈ I ∧ t = x^{2}))
5. FuncOfClassKOn(f, Dom(f), 3)
6. forall (x), x ∈ RealSet ∧ x ∈ I ⇒ y(x) = f(x^{2})
7. forall (x), x ∈ RealSet ∧ x ∈ I ⇒ FunDeri(y, 1, 1)(x) = 2 * x * FunDeri(f, 1, 1)(x^{2})
8. forall (x), x ∈ RealSet ∧ x ∈ I ⇒ FunDeri(y, 1, 2)(x) = 2 * FunDeri(f, 1, 1)(x^{2}) + 4 * x^{2} * FunDeri(f, 1, 2)(x^{2})

GOAL:
forall (x), x ∈ RealSet ∧ x ∈ I ⇒ FunDeri(y, 1, 3)(x) = 4 * x * FunDeri(f, 1, 2)(x^{2}) + 8 * x * FunDeri(f, 1, 2)(x^{2}) + 8 * x^{3} * FunDeri(f, 1, 3)(x^{2}) ∧ 4 * x * FunDeri(f, 1, 2)(x^{2}) + 8 * x * FunDeri(f, 1, 2)(x^{2}) + 8 * x^{3} * FunDeri(f, 1, 3)(x^{2}) = 12 * x * FunDeri(f, 1, 2)(x^{2}) + 8 * x^{3} * FunDeri(f, 1, 3)(x^{2})

METHOD:

-/
theorem proof_gap_exercise_1125_3
  (y : ℝ → ℝ) (f : DomainFunction) (I : Set ℝ)
  (hI : I ⊆ (Set.univ : Set ℝ))
  (hdom : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) →
    (t ∈ dom f ↔ ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I ∧ t = x ^ 2))
  (hclass : sourceClassOn f.value (dom f) 3)
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I → y x = f.value (x ^ 2))
  (hfirst : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I → iteratedDeriv 1 y x = 2 * x * iteratedDeriv 1 f.value (x ^ 2))
  (hsecond : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I → iteratedDeriv 2 y x = 2 * iteratedDeriv 1 f.value (x ^ 2) + 4 * x ^ 2 * iteratedDeriv 2 f.value (x ^ 2))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ I → iteratedDeriv 3 y x = 4 * x * iteratedDeriv 2 f.value (x ^ 2) + 8 * x * iteratedDeriv 2 f.value (x ^ 2) + 8 * x ^ 3 * iteratedDeriv 3 f.value (x ^ 2) ∧
    4 * x * iteratedDeriv 2 f.value (x ^ 2) + 8 * x * iteratedDeriv 2 f.value (x ^ 2) + 8 * x ^ 3 * iteratedDeriv 3 f.value (x ^ 2) = 12 * x * iteratedDeriv 2 f.value (x ^ 2) + 8 * x ^ 3 * iteratedDeriv 3 f.value (x ^ 2) := by
  sorry

