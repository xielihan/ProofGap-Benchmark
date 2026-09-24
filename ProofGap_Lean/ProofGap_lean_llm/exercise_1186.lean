import Mathlib

set_option linter.style.longLine false
open scoped RealInnerProductSpace

namespace Exercise1186

-- Thm 286, expanded using Thms 276 and 267: ambient pointwise derivatives.
-- The inclusive bound j ≤ n is deliberately retained from the source definition.
def ClassKOn (f : ℝ → ℝ) (I : Set ℝ) (n : ℕ) : Prop :=
  (∀ j : ℕ, j ≤ n → ∀ y ∈ I, DifferentiableAt ℝ (iteratedDeriv j f) y) ∧
  (∀ y ∈ I, ContinuousAt (iteratedDeriv n f) y)

-- Function-valued selector: iterate differentiation with respect to g.
-- Retain the source selector, even though it differs from the RNFL ordinary derivative.
noncomputable def relativeStep (g f : ℝ → ℝ) : ℝ → ℝ :=
  fun y => inner ℝ (gradient f y) (gradient g y) / (‖gradient g y‖ ^ 2)

noncomputable def relativeDeriv (f g : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  (relativeStep g)^[n] f

def Premises (n : ℕ) (a b x : ℝ) (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  I ⊆ Set.univ ∧ 0 < n ∧ a ∈ (Set.univ : Set ℝ) ∧
  b ∈ (Set.univ : Set ℝ) ∧ x ∈ (Set.univ : Set ℝ) ∧
  a * x + b ∈ I ∧ ClassKOn f I n

def Formula (f : ℝ → ℝ) (a b x : ℝ) (k : ℕ) : Prop :=
  iteratedDeriv k (fun t => f (a * t + b)) x =
    a ^ k * relativeDeriv f (fun y => a * y + b) k (a * x + b)

def Statement1 : Prop :=
  ∀ n : ℕ, ∀ a b x : ℝ, ∀ f : ℝ → ℝ, ∀ I : Set ℝ,
    Premises n a b x f I → iteratedDeriv 1 (fun y => a * y + b) x = a

def Statement2 : Prop :=
  ∀ n : ℕ, ∀ a b x : ℝ, ∀ f : ℝ → ℝ, ∀ I : Set ℝ,
    Premises n a b x f I → ∀ k : ℕ, 0 < k ∧ k ≤ n → Formula f a b x k

def Statement3 : Prop :=
  ∀ n : ℕ, ∀ a b x : ℝ, ∀ f : ℝ → ℝ, ∀ I : Set ℝ,
    Premises n a b x f I → Formula f a b x n

def Statement4 : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ) (n : ℕ) (a b x : ℝ),
    Premises n a b x f I → Formula f a b x n

end Exercise1186

open Exercise1186

/- Exercise 1186, gap 1
PROOF GAP @1
ASSUM:

GOAL:
forall (n), n ∈ NonNegIntegerSet ⇒ (forall (a), a ∈ RealSet ⇒ (forall (b), b ∈ RealSet ⇒ (forall (x), x ∈ RealSet ⇒ (forall (f), f : RealSet → RealSet ⇒ (forall (I), I ⊆ RealSet ∧ n ∈ PosIntegerSet ∧ a ∈ RealSet ∧ b ∈ RealSet ∧ x ∈ RealSet ∧ a * x + b ∈ I ∧ FuncOfClassKOn(f, I, n) ⇒ FunDeri(fun x [x ∈ RealSet] . a * x + b, 1, 1)(x) = a)))))

METHOD:

-/
theorem proof_gap_exercise_1186_1
  : Statement1 := by
  sorry

/- Exercise 1186, gap 2
PROOF GAP @2
ASSUM:
1. forall (n), n ∈ NonNegIntegerSet ⇒ (forall (a), a ∈ RealSet ⇒ (forall (b), b ∈ RealSet ⇒ (forall (x), x ∈ RealSet ⇒ (forall (f), f : RealSet → RealSet ⇒ (forall (I), I ⊆ RealSet ∧ n ∈ PosIntegerSet ∧ a ∈ RealSet ∧ b ∈ RealSet ∧ x ∈ RealSet ∧ a * x + b ∈ I ∧ FuncOfClassKOn(f, I, n) ⇒ FunDeri(fun x [x ∈ RealSet] . a * x + b, 1, 1)(x) = a)))))

GOAL:
forall (n), n ∈ NonNegIntegerSet ⇒ (forall (a), a ∈ RealSet ⇒ (forall (b), b ∈ RealSet ⇒ (forall (x), x ∈ RealSet ⇒ (forall (f), f : RealSet → RealSet ⇒ (forall (I), I ⊆ RealSet ∧ n ∈ PosIntegerSet ∧ a ∈ RealSet ∧ b ∈ RealSet ∧ x ∈ RealSet ∧ a * x + b ∈ I ∧ FuncOfClassKOn(f, I, n) ⇒ (forall (k), k ∈ NonNegIntegerSet ∧ k ∈ PosIntegerSet ∧ k ≤ n ⇒ FunDeri(fun t [t ∈ RealSet] . f(a * t + b), 1, k)(x) = a^{k} * FunDeri(f, fun x [x ∈ RealSet] . a * x + b, k)(a * x + b)))))))

METHOD:

-/
theorem proof_gap_exercise_1186_2
  (h1 : Statement1)
  : Statement2 := by
  sorry

/- Exercise 1186, gap 3
PROOF GAP @3
ASSUM:
1. forall (n), n ∈ NonNegIntegerSet ⇒ (forall (a), a ∈ RealSet ⇒ (forall (b), b ∈ RealSet ⇒ (forall (x), x ∈ RealSet ⇒ (forall (f), f : RealSet → RealSet ⇒ (forall (I), I ⊆ RealSet ∧ n ∈ PosIntegerSet ∧ a ∈ RealSet ∧ b ∈ RealSet ∧ x ∈ RealSet ∧ a * x + b ∈ I ∧ FuncOfClassKOn(f, I, n) ⇒ FunDeri(fun x [x ∈ RealSet] . a * x + b, 1, 1)(x) = a)))))
2. forall (n), n ∈ NonNegIntegerSet ⇒ (forall (a), a ∈ RealSet ⇒ (forall (b), b ∈ RealSet ⇒ (forall (x), x ∈ RealSet ⇒ (forall (f), f : RealSet → RealSet ⇒ (forall (I), I ⊆ RealSet ∧ n ∈ PosIntegerSet ∧ a ∈ RealSet ∧ b ∈ RealSet ∧ x ∈ RealSet ∧ a * x + b ∈ I ∧ FuncOfClassKOn(f, I, n) ⇒ (forall (k), k ∈ NonNegIntegerSet ∧ k ∈ PosIntegerSet ∧ k ≤ n ⇒ FunDeri(fun t [t ∈ RealSet] . f(a * t + b), 1, k)(x) = a^{k} * FunDeri(f, fun x [x ∈ RealSet] . a * x + b, k)(a * x + b)))))))

GOAL:
forall (n), n ∈ NonNegIntegerSet ⇒ (forall (a), a ∈ RealSet ⇒ (forall (b), b ∈ RealSet ⇒ (forall (x), x ∈ RealSet ⇒ (forall (f), f : RealSet → RealSet ⇒ (forall (I), I ⊆ RealSet ∧ n ∈ PosIntegerSet ∧ a ∈ RealSet ∧ b ∈ RealSet ∧ x ∈ RealSet ∧ a * x + b ∈ I ∧ FuncOfClassKOn(f, I, n) ⇒ FunDeri(fun t [t ∈ RealSet] . f(a * t + b), 1, n)(x) = a^{n} * FunDeri(f, fun x [x ∈ RealSet] . a * x + b, n)(a * x + b))))))

METHOD:

-/
theorem proof_gap_exercise_1186_3
  (h1 : Statement1)
  (h2 : Statement2)
  : Statement3 := by
  sorry

/- Exercise 1186, gap 4
PROOF GAP @4
ASSUM:
1. forall (n), n ∈ NonNegIntegerSet ⇒ (forall (a), a ∈ RealSet ⇒ (forall (b), b ∈ RealSet ⇒ (forall (x), x ∈ RealSet ⇒ (forall (f), f : RealSet → RealSet ⇒ (forall (I), I ⊆ RealSet ∧ n ∈ PosIntegerSet ∧ a ∈ RealSet ∧ b ∈ RealSet ∧ x ∈ RealSet ∧ a * x + b ∈ I ∧ FuncOfClassKOn(f, I, n) ⇒ FunDeri(fun x [x ∈ RealSet] . a * x + b, 1, 1)(x) = a)))))
2. forall (n), n ∈ NonNegIntegerSet ⇒ (forall (a), a ∈ RealSet ⇒ (forall (b), b ∈ RealSet ⇒ (forall (x), x ∈ RealSet ⇒ (forall (f), f : RealSet → RealSet ⇒ (forall (I), I ⊆ RealSet ∧ n ∈ PosIntegerSet ∧ a ∈ RealSet ∧ b ∈ RealSet ∧ x ∈ RealSet ∧ a * x + b ∈ I ∧ FuncOfClassKOn(f, I, n) ⇒ (forall (k), k ∈ NonNegIntegerSet ∧ k ∈ PosIntegerSet ∧ k ≤ n ⇒ FunDeri(fun t [t ∈ RealSet] . f(a * t + b), 1, k)(x) = a^{k} * FunDeri(f, fun x [x ∈ RealSet] . a * x + b, k)(a * x + b)))))))
3. forall (n), n ∈ NonNegIntegerSet ⇒ (forall (a), a ∈ RealSet ⇒ (forall (b), b ∈ RealSet ⇒ (forall (x), x ∈ RealSet ⇒ (forall (f), f : RealSet → RealSet ⇒ (forall (I), I ⊆ RealSet ∧ n ∈ PosIntegerSet ∧ a ∈ RealSet ∧ b ∈ RealSet ∧ x ∈ RealSet ∧ a * x + b ∈ I ∧ FuncOfClassKOn(f, I, n) ⇒ FunDeri(fun t [t ∈ RealSet] . f(a * t + b), 1, n)(x) = a^{n} * FunDeri(f, fun x [x ∈ RealSet] . a * x + b, n)(a * x + b))))))

GOAL:
forall (f) (I) (n) (a) (b) (x), f : RealSet → RealSet ∧ I ⊆ RealSet ∧ n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ∧ a ∈ RealSet ∧ b ∈ RealSet ∧ x ∈ RealSet ∧ a * x + b ∈ I ∧ FuncOfClassKOn(f, I, n) ⇒ FunDeri(fun t [t ∈ RealSet] . f(a * t + b), 1, n)(x) = a^{n} * FunDeri(f, fun x [x ∈ RealSet] . a * x + b, n)(a * x + b)

METHOD:

-/
theorem proof_gap_exercise_1186_4
  (h1 : Statement1)
  (h2 : Statement2)
  (h3 : Statement3)
  : Statement4 := by
  sorry

/- Exercise 1186, gap 5
PROOF GAP @5
ASSUM:
1. forall (n), n ∈ NonNegIntegerSet ⇒ (forall (a), a ∈ RealSet ⇒ (forall (b), b ∈ RealSet ⇒ (forall (x), x ∈ RealSet ⇒ (forall (f), f : RealSet → RealSet ⇒ (forall (I), I ⊆ RealSet ∧ n ∈ PosIntegerSet ∧ a ∈ RealSet ∧ b ∈ RealSet ∧ x ∈ RealSet ∧ a * x + b ∈ I ∧ FuncOfClassKOn(f, I, n) ⇒ FunDeri(fun x [x ∈ RealSet] . a * x + b, 1, 1)(x) = a)))))
2. forall (n), n ∈ NonNegIntegerSet ⇒ (forall (a), a ∈ RealSet ⇒ (forall (b), b ∈ RealSet ⇒ (forall (x), x ∈ RealSet ⇒ (forall (f), f : RealSet → RealSet ⇒ (forall (I), I ⊆ RealSet ∧ n ∈ PosIntegerSet ∧ a ∈ RealSet ∧ b ∈ RealSet ∧ x ∈ RealSet ∧ a * x + b ∈ I ∧ FuncOfClassKOn(f, I, n) ⇒ (forall (k), k ∈ NonNegIntegerSet ∧ k ∈ PosIntegerSet ∧ k ≤ n ⇒ FunDeri(fun t [t ∈ RealSet] . f(a * t + b), 1, k)(x) = a^{k} * FunDeri(f, fun x [x ∈ RealSet] . a * x + b, k)(a * x + b)))))))
3. forall (n), n ∈ NonNegIntegerSet ⇒ (forall (a), a ∈ RealSet ⇒ (forall (b), b ∈ RealSet ⇒ (forall (x), x ∈ RealSet ⇒ (forall (f), f : RealSet → RealSet ⇒ (forall (I), I ⊆ RealSet ∧ n ∈ PosIntegerSet ∧ a ∈ RealSet ∧ b ∈ RealSet ∧ x ∈ RealSet ∧ a * x + b ∈ I ∧ FuncOfClassKOn(f, I, n) ⇒ FunDeri(fun t [t ∈ RealSet] . f(a * t + b), 1, n)(x) = a^{n} * FunDeri(f, fun x [x ∈ RealSet] . a * x + b, n)(a * x + b))))))
4. forall (f) (I) (n) (a) (b) (x), f : RealSet → RealSet ∧ I ⊆ RealSet ∧ n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ∧ a ∈ RealSet ∧ b ∈ RealSet ∧ x ∈ RealSet ∧ a * x + b ∈ I ∧ FuncOfClassKOn(f, I, n) ⇒ FunDeri(fun t [t ∈ RealSet] . f(a * t + b), 1, n)(x) = a^{n} * FunDeri(f, fun x [x ∈ RealSet] . a * x + b, n)(a * x + b)

GOAL:
forall (f) (I) (n) (a) (b) (x), f : RealSet → RealSet ∧ I ⊆ RealSet ∧ n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ∧ a ∈ RealSet ∧ b ∈ RealSet ∧ x ∈ RealSet ∧ a * x + b ∈ I ∧ FuncOfClassKOn(f, I, n) ⇒ FunDeri(fun t [t ∈ RealSet] . f(a * t + b), 1, n)(x) = a^{n} * FunDeri(f, fun x [x ∈ RealSet] . a * x + b, n)(a * x + b)

METHOD:

-/
theorem proof_gap_exercise_1186_5
  (h1 : Statement1)
  (h2 : Statement2)
  (h3 : Statement3)
  (h4 : Statement4)
  : Statement4 := by
  sorry
