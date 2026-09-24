import Mathlib

open Filter
open scoped Topology

namespace Exercise694

-- A side oscillates when it has neither a finite nor an infinite limit.
def OscillatesAlong (y : ℝ → ℝ) (F : Filter ℝ) : Prop :=
  (¬ ∃ l : ℝ, Tendsto y F (𝓝 l)) ∧
  ¬ Tendsto y F atTop ∧ ¬ Tendsto y F atBot

-- For this bounded function this is also a second-kind discontinuity.
def OscillatorySingularPoint (y : ℝ → ℝ) (c : ℝ) : Prop :=
  ¬ ContinuousAt y c ∧
    (OscillatesAlong y (𝓝[<] c) ∨ OscillatesAlong y (𝓝[>] c))

def JumpSingularPoint (y : ℝ → ℝ) (c : ℝ) : Prop :=
  ¬ ContinuousAt y c ∧ ∃ l r : ℝ,
    Tendsto y (𝓝[<] c) (𝓝 l) ∧ Tendsto y (𝓝[>] c) (𝓝 r) ∧ l ≠ r

end Exercise694

open Exercise694

-- Exercise 694, gap 1
/-
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x ≠ 0 ⇒ y(x) = sgn(sin(frac(π, x)))

GOAL:
¬(exists (l), l ∈ RealSet ∧ lim_{ x → 0 } (y(x)) = l)

METHOD:

-/
theorem proof_gap_exercise_694_1
  (y : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 →
    y x = (SignType.sign (Real.sin (Real.pi / x)) : ℝ))
  : ¬ (∃ l : ℝ, l ∈ (Set.univ : Set ℝ) ∧ Tendsto y (𝓝[≠] (0 : ℝ)) (𝓝 l)) := by
  sorry

-- Exercise 694, gap 2
/-
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x ≠ 0 ⇒ y(x) = sgn(sin(frac(π, x)))
4. ¬(exists (l), l ∈ RealSet ∧ lim_{ x → 0 } (y(x)) = l)

GOAL:
OscillatorySingularPoint(y, 0)

METHOD:

-/
theorem proof_gap_exercise_694_2
  (y : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 →
    y x = (SignType.sign (Real.sin (Real.pi / x)) : ℝ))
  (h4 : ¬ (∃ l : ℝ, l ∈ (Set.univ : Set ℝ) ∧ Tendsto y (𝓝[≠] (0 : ℝ)) (𝓝 l)))
  : OscillatorySingularPoint y 0 := by
  sorry

-- Exercise 694, gap 3
/-
PROOF GAP @3
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x ≠ 0 ⇒ y(x) = sgn(sin(frac(π, x)))
4. ¬(exists (l), l ∈ RealSet ∧ lim_{ x → 0 } (y(x)) = l)
5. OscillatorySingularPoint(y, 0)

GOAL:
forall (k), k ∈ IntegerSet ∧ k ≠ 0 ⇒ lim_{ x → frac(1, k)^- } (y(x)) = (-1)^{k}

METHOD:

-/
theorem proof_gap_exercise_694_3
  (y : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 →
    y x = (SignType.sign (Real.sin (Real.pi / x)) : ℝ))
  (h4 : ¬ (∃ l : ℝ, l ∈ (Set.univ : Set ℝ) ∧ Tendsto y (𝓝[≠] (0 : ℝ)) (𝓝 l)))
  (h5 : OscillatorySingularPoint y 0)
  : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) ∧ k ≠ 0 →
    Tendsto y (𝓝[<] (1 / (k : ℝ))) (𝓝 ((-1 : ℝ) ^ k)) := by
  sorry

-- Exercise 694, gap 4
/-
PROOF GAP @4
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x ≠ 0 ⇒ y(x) = sgn(sin(frac(π, x)))
4. ¬(exists (l), l ∈ RealSet ∧ lim_{ x → 0 } (y(x)) = l)
5. OscillatorySingularPoint(y, 0)
6. forall (k), k ∈ IntegerSet ∧ k ≠ 0 ⇒ lim_{ x → frac(1, k)^- } (y(x)) = (-1)^{k}

GOAL:
forall (k), k ∈ IntegerSet ∧ k ≠ 0 ⇒ lim_{ x → frac(1, k)^+ } (y(x)) = (-1)^{k - 1}

METHOD:

-/
theorem proof_gap_exercise_694_4
  (y : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 →
    y x = (SignType.sign (Real.sin (Real.pi / x)) : ℝ))
  (h4 : ¬ (∃ l : ℝ, l ∈ (Set.univ : Set ℝ) ∧ Tendsto y (𝓝[≠] (0 : ℝ)) (𝓝 l)))
  (h5 : OscillatorySingularPoint y 0)
  (h6 : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) ∧ k ≠ 0 →
    Tendsto y (𝓝[<] (1 / (k : ℝ))) (𝓝 ((-1 : ℝ) ^ k)))
  : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) ∧ k ≠ 0 →
    Tendsto y (𝓝[>] (1 / (k : ℝ))) (𝓝 ((-1 : ℝ) ^ (k - 1))) := by
  sorry

-- Exercise 694, gap 5
/-
PROOF GAP @5
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x ≠ 0 ⇒ y(x) = sgn(sin(frac(π, x)))
4. ¬(exists (l), l ∈ RealSet ∧ lim_{ x → 0 } (y(x)) = l)
5. OscillatorySingularPoint(y, 0)
6. forall (k), k ∈ IntegerSet ∧ k ≠ 0 ⇒ lim_{ x → frac(1, k)^- } (y(x)) = (-1)^{k}
7. forall (k), k ∈ IntegerSet ∧ k ≠ 0 ⇒ lim_{ x → frac(1, k)^+ } (y(x)) = (-1)^{k - 1}

GOAL:
forall (k), k ∈ IntegerSet ∧ k ≠ 0 ⇒ JumpSingularPoint(y, frac(1, k))

METHOD:

-/
theorem proof_gap_exercise_694_5
  (y : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 →
    y x = (SignType.sign (Real.sin (Real.pi / x)) : ℝ))
  (h4 : ¬ (∃ l : ℝ, l ∈ (Set.univ : Set ℝ) ∧ Tendsto y (𝓝[≠] (0 : ℝ)) (𝓝 l)))
  (h5 : OscillatorySingularPoint y 0)
  (h6 : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) ∧ k ≠ 0 →
    Tendsto y (𝓝[<] (1 / (k : ℝ))) (𝓝 ((-1 : ℝ) ^ k)))
  (h7 : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) ∧ k ≠ 0 →
    Tendsto y (𝓝[>] (1 / (k : ℝ))) (𝓝 ((-1 : ℝ) ^ (k - 1))))
  : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) ∧ k ≠ 0 →
    JumpSingularPoint y (1 / (k : ℝ)) := by
  sorry

-- Exercise 694, gap 6
/-
PROOF GAP @6
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x ≠ 0 ⇒ y(x) = sgn(sin(frac(π, x)))
4. ¬(exists (l), l ∈ RealSet ∧ lim_{ x → 0 } (y(x)) = l)
5. OscillatorySingularPoint(y, 0)
6. forall (k), k ∈ IntegerSet ∧ k ≠ 0 ⇒ lim_{ x → frac(1, k)^- } (y(x)) = (-1)^{k}
7. forall (k), k ∈ IntegerSet ∧ k ≠ 0 ⇒ lim_{ x → frac(1, k)^+ } (y(x)) = (-1)^{k - 1}
8. forall (k), k ∈ IntegerSet ∧ k ≠ 0 ⇒ JumpSingularPoint(y, frac(1, k))

GOAL:
a ∈ { 0 } ∪ { frac(1, k) | k ∈ IntegerSet, k ≠ 0 } ⇔ ¬ContinuousFuncAt(y, a)

METHOD:

-/
theorem proof_gap_exercise_694_6
  (y : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 →
    y x = (SignType.sign (Real.sin (Real.pi / x)) : ℝ))
  (h4 : ¬ (∃ l : ℝ, l ∈ (Set.univ : Set ℝ) ∧ Tendsto y (𝓝[≠] (0 : ℝ)) (𝓝 l)))
  (h5 : OscillatorySingularPoint y 0)
  (h6 : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) ∧ k ≠ 0 →
    Tendsto y (𝓝[<] (1 / (k : ℝ))) (𝓝 ((-1 : ℝ) ^ k)))
  (h7 : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) ∧ k ≠ 0 →
    Tendsto y (𝓝[>] (1 / (k : ℝ))) (𝓝 ((-1 : ℝ) ^ (k - 1))))
  (h8 : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) ∧ k ≠ 0 →
    JumpSingularPoint y (1 / (k : ℝ)))
  : a ∈ ({0} : Set ℝ) ∪
    {x : ℝ | ∃ k : ℤ, k ∈ (Set.univ : Set ℤ) ∧ k ≠ 0 ∧ x = 1 / (k : ℝ)}
    ↔ ¬ ContinuousAt y a := by
  sorry

