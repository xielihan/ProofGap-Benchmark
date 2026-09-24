import Mathlib

open Filter
open scoped Topology

namespace Exercise688

-- Equality of two finite punctured limits includes their existence.
def SameLimit (f g : ℝ → ℝ) (a : ℝ) : Prop :=
  ∃ L : ℝ, Tendsto f (𝓝[≠] a) (𝓝 L) ∧ Tendsto g (𝓝[≠] a) (𝓝 L)

-- For the total real functions in the gaps, a removable singularity is
-- a discontinuity with an existing finite punctured limit.
def RemovableSingularPoint (f : ℝ → ℝ) (a : ℝ) : Prop :=
  (¬ ContinuousAt f a) ∧ ∃ L : ℝ, Tendsto f (𝓝[≠] a) (𝓝 L)

end Exercise688

/- Exercise 688, gap 1
SHA-256: 541b907baba2826282beed5cc9208ec298e9edada080651f56f7a97b6f0c39bc
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ 1 + x^{3} ≠ 0 ⇒ y(x) = frac(1 + x, 1 + x^{3})

GOAL:
forall (x), x ∈ RealSet ⇒ 1 + x^{3} = (1 + x) * (x^{2} - x + 1)

METHOD:

-/
theorem proof_gap_exercise_688_1
  (y : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 1 + x ^ 3 ≠ 0 →
    y x = (1 + x) / (1 + x ^ 3))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → 1 + x ^ 3 = (1 + x) * (x ^ 2 - x + 1) := by
  sorry

/- Exercise 688, gap 2
SHA-256: d9cacdf0ed72a1e79ead2718e10b901fc4a1248ed7646c7984077553126bbed2
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ 1 + x^{3} ≠ 0 ⇒ y(x) = frac(1 + x, 1 + x^{3})
4. forall (x), x ∈ RealSet ⇒ 1 + x^{3} = (1 + x) * (x^{2} - x + 1)

GOAL:
lim_{ x → -1 } (y(x)) = lim_{ x → -1 } (frac(1, x^{2} - x + 1))

METHOD:

-/
theorem proof_gap_exercise_688_2
  (y : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 1 + x ^ 3 ≠ 0 →
    y x = (1 + x) / (1 + x ^ 3))
  (hfactor : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → 1 + x ^ 3 = (1 + x) * (x ^ 2 - x + 1))
  : Exercise688.SameLimit y (fun x : ℝ => 1 / (x ^ 2 - x + 1)) (-1) := by
  sorry

/- Exercise 688, gap 3
SHA-256: 3d6142c8550bc28025c806a0a14f499cb87fc7667706879e564fbf32a1e192cb
PROOF GAP @3
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ 1 + x^{3} ≠ 0 ⇒ y(x) = frac(1 + x, 1 + x^{3})
4. forall (x), x ∈ RealSet ⇒ 1 + x^{3} = (1 + x) * (x^{2} - x + 1)
5. lim_{ x → -1 } (y(x)) = lim_{ x → -1 } (frac(1, x^{2} - x + 1))

GOAL:
lim_{ x → -1 } (frac(1, x^{2} - x + 1)) = frac(1, 3)

METHOD:

-/
theorem proof_gap_exercise_688_3
  (y : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 1 + x ^ 3 ≠ 0 →
    y x = (1 + x) / (1 + x ^ 3))
  (hfactor : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → 1 + x ^ 3 = (1 + x) * (x ^ 2 - x + 1))
  (hequal : Exercise688.SameLimit y (fun x : ℝ => 1 / (x ^ 2 - x + 1)) (-1))
  : Tendsto (fun x : ℝ => 1 / (x ^ 2 - x + 1)) (𝓝[≠] (-1)) (𝓝 (1 / 3 : ℝ)) := by
  sorry

/- Exercise 688, gap 4
SHA-256: 823b1946ad1919fa7f57eb5955bc62c4b0a0868cc9f61c9e1bf1ba529a1a65be
PROOF GAP @4
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ 1 + x^{3} ≠ 0 ⇒ y(x) = frac(1 + x, 1 + x^{3})
4. forall (x), x ∈ RealSet ⇒ 1 + x^{3} = (1 + x) * (x^{2} - x + 1)
5. lim_{ x → -1 } (y(x)) = lim_{ x → -1 } (frac(1, x^{2} - x + 1))
6. lim_{ x → -1 } (frac(1, x^{2} - x + 1)) = frac(1, 3)

GOAL:
lim_{ x → -1 } (y(x)) = frac(1, 3)

METHOD:

-/
theorem proof_gap_exercise_688_4
  (y : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 1 + x ^ 3 ≠ 0 →
    y x = (1 + x) / (1 + x ^ 3))
  (hfactor : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → 1 + x ^ 3 = (1 + x) * (x ^ 2 - x + 1))
  (hequal : Exercise688.SameLimit y (fun x : ℝ => 1 / (x ^ 2 - x + 1)) (-1))
  (hlimq : Tendsto (fun x : ℝ => 1 / (x ^ 2 - x + 1)) (𝓝[≠] (-1)) (𝓝 (1 / 3 : ℝ)))
  : Tendsto y (𝓝[≠] (-1)) (𝓝 (1 / 3 : ℝ)) := by
  sorry

/- Exercise 688, gap 5
SHA-256: ba5257f9b9ceb31e0f591a18d003ca2c7a6fe6b047d5c6e8937f332fa66309f8
PROOF GAP @5
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ 1 + x^{3} ≠ 0 ⇒ y(x) = frac(1 + x, 1 + x^{3})
4. forall (x), x ∈ RealSet ⇒ 1 + x^{3} = (1 + x) * (x^{2} - x + 1)
5. lim_{ x → -1 } (y(x)) = lim_{ x → -1 } (frac(1, x^{2} - x + 1))
6. lim_{ x → -1 } (frac(1, x^{2} - x + 1)) = frac(1, 3)
7. lim_{ x → -1 } (y(x)) = frac(1, 3)
8. y(-1) ≠ frac(1, 3)
GOAL:
RemovableSingularPoint(y, -1)

METHOD:

-/
theorem proof_gap_exercise_688_5
  (y : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 1 + x ^ 3 ≠ 0 →
    y x = (1 + x) / (1 + x ^ 3))
  (hfactor : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → 1 + x ^ 3 = (1 + x) * (x ^ 2 - x + 1))
  (hequal : Exercise688.SameLimit y (fun x : ℝ => 1 / (x ^ 2 - x + 1)) (-1))
  (hlimq : Tendsto (fun x : ℝ => 1 / (x ^ 2 - x + 1)) (𝓝[≠] (-1)) (𝓝 (1 / 3 : ℝ)))
  (hlimy : Tendsto y (𝓝[≠] (-1)) (𝓝 (1 / 3 : ℝ)))
  (hne : y (-1) ≠ (1 / 3 : ℝ))
  : Exercise688.RemovableSingularPoint y (-1) := by
  sorry

/- Exercise 688, gap 6
SHA-256: f60232c896d917eb188e2f2826129b2cbc58461a12ff749fc88ada27f63c56b2
PROOF GAP @6
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ 1 + x^{3} ≠ 0 ⇒ y(x) = frac(1 + x, 1 + x^{3})
4. forall (x), x ∈ RealSet ⇒ 1 + x^{3} = (1 + x) * (x^{2} - x + 1)
5. lim_{ x → -1 } (y(x)) = lim_{ x → -1 } (frac(1, x^{2} - x + 1))
6. lim_{ x → -1 } (frac(1, x^{2} - x + 1)) = frac(1, 3)
7. lim_{ x → -1 } (y(x)) = frac(1, 3)
8. RemovableSingularPoint(y, -1)

GOAL:
a ∈ { -1 } ⇔ ¬ContinuousFuncAt(y, a)

METHOD:

-/
theorem proof_gap_exercise_688_6
  (y : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (hy : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ 1 + x ^ 3 ≠ 0 →
    y x = (1 + x) / (1 + x ^ 3))
  (hfactor : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → 1 + x ^ 3 = (1 + x) * (x ^ 2 - x + 1))
  (hequal : Exercise688.SameLimit y (fun x : ℝ => 1 / (x ^ 2 - x + 1)) (-1))
  (hlimq : Tendsto (fun x : ℝ => 1 / (x ^ 2 - x + 1)) (𝓝[≠] (-1)) (𝓝 (1 / 3 : ℝ)))
  (hlimy : Tendsto y (𝓝[≠] (-1)) (𝓝 (1 / 3 : ℝ)))
  (hremovable : Exercise688.RemovableSingularPoint y (-1))
  : a ∈ ({-1} : Set ℝ) ↔ ¬ ContinuousAt y a := by
  sorry

