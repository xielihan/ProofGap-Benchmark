import Mathlib

open Filter
open scoped Topology

namespace Exercise2361

noncomputable def integrand (p x : ℝ) : ℝ := Real.rpow x (p - 1) * Real.exp (-x)
noncomputable def lower (p a : ℝ) : ℝ := ∫ x in a..(1 : ℝ), integrand p x
noncomputable def upper (p b : ℝ) : ℝ := ∫ x in (1 : ℝ)..b, integrand p x
noncomputable def whole (p : ℝ) (ab : ℝ × ℝ) : ℝ :=
  ∫ x in ab.1..ab.2, integrand p x

def LowerHas (p L : ℝ) : Prop := Tendsto (lower p) (𝓝[>] (0 : ℝ)) (𝓝 L)
def UpperHas (p L : ℝ) : Prop := Tendsto (upper p) atTop (𝓝 L)
-- Independent endpoint limits: this is not a principal value.
def WholeHas (p L : ℝ) : Prop :=
  Tendsto (whole p) ((𝓝[>] (0 : ℝ)) ×ˢ (atTop : Filter ℝ)) (𝓝 L)
def LowerConverges (p : ℝ) : Prop := ∃ L : ℝ, LowerHas p L
def UpperConverges (p : ℝ) : Prop := ∃ L : ℝ, UpperHas p L
def WholeConverges (p : ℝ) : Prop := ∃ L : ℝ, WholeHas p L
-- Equality of defined finite improper integrals, with their values explicit.
def Split (p : ℝ) : Prop :=
  ∃ I A B : ℝ, WholeHas p I ∧ LowerHas p A ∧ UpperHas p B ∧ I = A + B

def NearZero (p : ℝ) : Prop :=
  Tendsto (fun x : ℝ => Real.rpow x (1 - p) * Real.rpow x (p - 1) * Real.exp (-x))
    (𝓝[>] (0 : ℝ)) (𝓝 1)
noncomputable def weighted (p x : ℝ) : ℝ := x ^ (2 : ℕ) * Real.rpow x (p - 1) * Real.exp (-x)
noncomputable def quotient (p x : ℝ) : ℝ := Real.rpow x (p + 1) / Real.exp x
-- Equality of two finite limits means that both tend to a common real value.
def EqualLimits (p : ℝ) : Prop :=
  ∃ L : ℝ, Tendsto (weighted p) atTop (𝓝 L) ∧ Tendsto (quotient p) atTop (𝓝 L)

end Exercise2361
open Exercise2361

/- Exercise 2361, gap 1
PROOF GAP @1
ASSUM:
1. p ∈ RealSet
2. p > 0

GOAL:
forall (x), x ∈ RealSet ⇒ DefInt(0, +∞, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)) = DefInt(0, 1, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)) + DefInt(1, +∞, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x))

METHOD:

-/
theorem proof_gap_exercise_2361_1
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : p > 0)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → Split p := by
  sorry

/- Exercise 2361, gap 2
PROOF GAP @2
ASSUM:
1. p ∈ RealSet
2. forall (x), x ∈ RealSet ⇒ DefInt(0, +∞, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)) = DefInt(0, 1, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)) + DefInt(1, +∞, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x))
3. p > 0

GOAL:
lim_{ x → 0^+ } (x^{1 - p} * x^{p - 1} * e^{-x}) = 1

METHOD:

-/
theorem proof_gap_exercise_2361_2
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → Split p)
  (h3 : p > 0)
  : NearZero p := by
  sorry

/- Exercise 2361, gap 3
PROOF GAP @3
ASSUM:
1. p ∈ RealSet
2. forall (x), x ∈ RealSet ⇒ DefInt(0, +∞, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)) = DefInt(0, 1, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)) + DefInt(1, +∞, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x))
3. lim_{ x → 0^+ } (x^{1 - p} * x^{p - 1} * e^{-x}) = 1
4. p > 0

GOAL:
forall (x), x ∈ RealSet ∧ p > 0 ⇒ ConvergentSeries(DefInt(0, 1, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)))

METHOD:
[@method 根据 "广义积分比较判别法" @]
-/
theorem proof_gap_exercise_2361_3
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → Split p)
  (h3 : NearZero p)
  (h4 : p > 0)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p > 0 → LowerConverges p := by
  sorry

/- Exercise 2361, gap 4
PROOF GAP @4
ASSUM:
1. p ∈ RealSet
2. forall (x), x ∈ RealSet ⇒ DefInt(0, +∞, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)) = DefInt(0, 1, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)) + DefInt(1, +∞, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x))
3. lim_{ x → 0^+ } (x^{1 - p} * x^{p - 1} * e^{-x}) = 1
4. forall (x), x ∈ RealSet ∧ p > 0 ⇒ ConvergentSeries(DefInt(0, 1, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)))
5. p > 0

GOAL:
lim_{ x → +∞ } (x^{2} * x^{p - 1} * e^{-x}) = lim_{ x → +∞ } (frac(x^{p + 1}, e^{x}))

METHOD:

-/
theorem proof_gap_exercise_2361_4
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → Split p)
  (h3 : NearZero p)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p > 0 → LowerConverges p)
  (h5 : p > 0)
  : EqualLimits p := by
  sorry

/- Exercise 2361, gap 5
PROOF GAP @5
ASSUM:
1. p ∈ RealSet
2. forall (x), x ∈ RealSet ⇒ DefInt(0, +∞, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)) = DefInt(0, 1, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)) + DefInt(1, +∞, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x))
3. lim_{ x → 0^+ } (x^{1 - p} * x^{p - 1} * e^{-x}) = 1
4. forall (x), x ∈ RealSet ∧ p > 0 ⇒ ConvergentSeries(DefInt(0, 1, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)))
5. lim_{ x → +∞ } (x^{2} * x^{p - 1} * e^{-x}) = lim_{ x → +∞ } (frac(x^{p + 1}, e^{x}))
6. p > 0

GOAL:
lim_{ x → +∞ } (frac(x^{p + 1}, e^{x})) = 0

METHOD:

-/
theorem proof_gap_exercise_2361_5
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → Split p)
  (h3 : NearZero p)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p > 0 → LowerConverges p)
  (h5 : EqualLimits p)
  (h6 : p > 0)
  : Tendsto (quotient p) atTop (𝓝 0) := by
  sorry

/- Exercise 2361, gap 6
PROOF GAP @6
ASSUM:
1. p ∈ RealSet
2. forall (x), x ∈ RealSet ⇒ DefInt(0, +∞, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)) = DefInt(0, 1, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)) + DefInt(1, +∞, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x))
3. lim_{ x → 0^+ } (x^{1 - p} * x^{p - 1} * e^{-x}) = 1
4. forall (x), x ∈ RealSet ∧ p > 0 ⇒ ConvergentSeries(DefInt(0, 1, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)))
5. lim_{ x → +∞ } (x^{2} * x^{p - 1} * e^{-x}) = lim_{ x → +∞ } (frac(x^{p + 1}, e^{x}))
6. lim_{ x → +∞ } (frac(x^{p + 1}, e^{x})) = 0

GOAL:
lim_{ x → +∞ } (x^{2} * x^{p - 1} * e^{-x}) = 0

METHOD:

-/
theorem proof_gap_exercise_2361_6
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → Split p)
  (h3 : NearZero p)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p > 0 → LowerConverges p)
  (h5 : EqualLimits p)
  (h6 : Tendsto (quotient p) atTop (𝓝 0))
  : Tendsto (weighted p) atTop (𝓝 0) := by
  sorry

/- Exercise 2361, gap 7
PROOF GAP @7
ASSUM:
1. p ∈ RealSet
2. forall (x), x ∈ RealSet ⇒ DefInt(0, +∞, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)) = DefInt(0, 1, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)) + DefInt(1, +∞, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x))
3. lim_{ x → 0^+ } (x^{1 - p} * x^{p - 1} * e^{-x}) = 1
4. forall (x), x ∈ RealSet ∧ p > 0 ⇒ ConvergentSeries(DefInt(0, 1, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)))
5. lim_{ x → +∞ } (x^{2} * x^{p - 1} * e^{-x}) = lim_{ x → +∞ } (frac(x^{p + 1}, e^{x}))
6. lim_{ x → +∞ } (frac(x^{p + 1}, e^{x})) = 0
7. lim_{ x → +∞ } (x^{2} * x^{p - 1} * e^{-x}) = 0

GOAL:
forall (p), p ∈ RealSet ⇒ (forall (x), x ∈ RealSet ⇒ ConvergentSeries(DefInt(1, +∞, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x))))

METHOD:
[@method 根据 "广义积分比较判别法" @]
-/
theorem proof_gap_exercise_2361_7
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → Split p)
  (h3 : NearZero p)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p > 0 → LowerConverges p)
  (h5 : EqualLimits p)
  (h6 : Tendsto (quotient p) atTop (𝓝 0))
  (h7 : Tendsto (weighted p) atTop (𝓝 0))
  : ∀ q : ℝ, q ∈ (Set.univ : Set ℝ) → ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → UpperConverges q := by
  sorry

/- Exercise 2361, gap 8
PROOF GAP @8
ASSUM:
1. p ∈ RealSet
2. forall (x), x ∈ RealSet ⇒ DefInt(0, +∞, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)) = DefInt(0, 1, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)) + DefInt(1, +∞, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x))
3. lim_{ x → 0^+ } (x^{1 - p} * x^{p - 1} * e^{-x}) = 1
4. forall (x), x ∈ RealSet ∧ p > 0 ⇒ ConvergentSeries(DefInt(0, 1, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)))
5. lim_{ x → +∞ } (x^{2} * x^{p - 1} * e^{-x}) = lim_{ x → +∞ } (frac(x^{p + 1}, e^{x}))
6. lim_{ x → +∞ } (frac(x^{p + 1}, e^{x})) = 0
7. lim_{ x → +∞ } (x^{2} * x^{p - 1} * e^{-x}) = 0
8. forall (p), p ∈ RealSet ⇒ (forall (x), x ∈ RealSet ⇒ ConvergentSeries(DefInt(1, +∞, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x))))
9. p > 0

GOAL:
forall (x), x ∈ RealSet ∧ p > 0 ⇒ ConvergentSeries(DefInt(0, +∞, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)))

METHOD:

-/
theorem proof_gap_exercise_2361_8
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → Split p)
  (h3 : NearZero p)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p > 0 → LowerConverges p)
  (h5 : EqualLimits p)
  (h6 : Tendsto (quotient p) atTop (𝓝 0))
  (h7 : Tendsto (weighted p) atTop (𝓝 0))
  (h8 : ∀ q : ℝ, q ∈ (Set.univ : Set ℝ) → ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → UpperConverges q)
  (h9 : p > 0)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p > 0 → WholeConverges p := by
  sorry

/- Exercise 2361, gap 9
PROOF GAP @9
ASSUM:
1. p ∈ RealSet
2. forall (x), x ∈ RealSet ⇒ DefInt(0, +∞, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)) = DefInt(0, 1, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)) + DefInt(1, +∞, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x))
3. lim_{ x → 0^+ } (x^{1 - p} * x^{p - 1} * e^{-x}) = 1
4. forall (x), x ∈ RealSet ∧ p > 0 ⇒ ConvergentSeries(DefInt(0, 1, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)))
5. lim_{ x → +∞ } (x^{2} * x^{p - 1} * e^{-x}) = lim_{ x → +∞ } (frac(x^{p + 1}, e^{x}))
6. lim_{ x → +∞ } (frac(x^{p + 1}, e^{x})) = 0
7. lim_{ x → +∞ } (x^{2} * x^{p - 1} * e^{-x}) = 0
8. forall (p), p ∈ RealSet ⇒ (forall (x), x ∈ RealSet ⇒ ConvergentSeries(DefInt(1, +∞, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x))))
9. forall (x), x ∈ RealSet ∧ p > 0 ⇒ ConvergentSeries(DefInt(0, +∞, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)))
10. p > 0

GOAL:
forall (x), x ∈ RealSet ∧ p ≤ 0 ⇒ DivergentSeries(DefInt(0, +∞, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)))

METHOD:

-/
theorem proof_gap_exercise_2361_9
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → Split p)
  (h3 : NearZero p)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p > 0 → LowerConverges p)
  (h5 : EqualLimits p)
  (h6 : Tendsto (quotient p) atTop (𝓝 0))
  (h7 : Tendsto (weighted p) atTop (𝓝 0))
  (h8 : ∀ q : ℝ, q ∈ (Set.univ : Set ℝ) → ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → UpperConverges q)
  (h9 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p > 0 → WholeConverges p)
  (h10 : p > 0)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p ≤ 0 → ¬ WholeConverges p := by
  sorry

/- Exercise 2361, gap 10
PROOF GAP @10
ASSUM:
1. p ∈ RealSet
2. forall (x), x ∈ RealSet ⇒ DefInt(0, +∞, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)) = DefInt(0, 1, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)) + DefInt(1, +∞, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x))
3. lim_{ x → 0^+ } (x^{1 - p} * x^{p - 1} * e^{-x}) = 1
4. forall (x), x ∈ RealSet ∧ p > 0 ⇒ ConvergentSeries(DefInt(0, 1, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)))
5. lim_{ x → +∞ } (x^{2} * x^{p - 1} * e^{-x}) = lim_{ x → +∞ } (frac(x^{p + 1}, e^{x}))
6. lim_{ x → +∞ } (frac(x^{p + 1}, e^{x})) = 0
7. lim_{ x → +∞ } (x^{2} * x^{p - 1} * e^{-x}) = 0
8. forall (p), p ∈ RealSet ⇒ (forall (x), x ∈ RealSet ⇒ ConvergentSeries(DefInt(1, +∞, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x))))
9. forall (x), x ∈ RealSet ∧ p > 0 ⇒ ConvergentSeries(DefInt(0, +∞, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)))
10. forall (x), x ∈ RealSet ∧ p ≤ 0 ⇒ DivergentSeries(DefInt(0, +∞, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x)))

GOAL:
forall (x), x ∈ RealSet ⇒ (p ∈ PosRealSet ⇔ ConvergentSeries(DefInt(0, +∞, x^{p - 1} * e^{-x} * diff(fun x [x ∈ RealSet] . x))))

METHOD:

-/
theorem proof_gap_exercise_2361_10
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → Split p)
  (h3 : NearZero p)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p > 0 → LowerConverges p)
  (h5 : EqualLimits p)
  (h6 : Tendsto (quotient p) atTop (𝓝 0))
  (h7 : Tendsto (weighted p) atTop (𝓝 0))
  (h8 : ∀ q : ℝ, q ∈ (Set.univ : Set ℝ) → ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → UpperConverges q)
  (h9 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p > 0 → WholeConverges p)
  (h10 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p ≤ 0 → ¬ WholeConverges p)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → (p ∈ {r : ℝ | 0 < r} ↔ WholeConverges p) := by
  sorry

