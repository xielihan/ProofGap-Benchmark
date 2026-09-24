import Mathlib

open Filter
open scoped Topology
namespace Exercise607
attribute [local instance] Classical.propDecidable

def IsRat (x : ℝ) : Prop := ∃ r : ℚ, (r : ℝ) = x

def PhiSpec (φ : ℝ → ℝ) : Prop :=
  (∀ (x : ℝ) (p q : ℤ), IsRat x ∧ 0 < q ∧ Int.gcd p q = 1 ∧
    x = (p : ℝ) / (q : ℝ) → φ x = 1 / (q : ℝ)) ∧
  (∀ x : ℝ, ¬ IsRat x → φ x = 0)

-- Gaps 3–5 retain the signed-denominator rule from the original prose.
-- The branch value uses the same p,q as x=p/q, for every such representation.
-- This source rule is inconsistent: 1=1/1=(-1)/(-1) would give φ(1)=1 and -1.
-- We preserve that source error; no positivity convention or witness is selected.
def SignedPhiSpec (φ : ℝ → ℝ) : Prop :=
  (∀ (x : ℝ) (p q : ℤ), q ≠ 0 ∧ Int.gcd p q = 1 ∧
    x = (p : ℝ) / (q : ℝ) → φ x = 1 / (q : ℝ)) ∧
  (∀ x : ℝ, ¬ IsRat x → φ x = 0)

-- Exercise 607, gap 1
/-
PROOF GAP @1
ASSUM:
1. (forall (x) (p) (q), x ∈ RationalSet ∧ p ∈ IntegerSet ∧ q ∈ PosIntegerSet ∧ gcd(p, q) = 1 ∧ x = frac(p, q) ⇒ φ(x) = frac(1, q)) ∧ (forall (x), x ∈ RealSet ∧ x ∉ RationalSet ⇒ φ(x) = 0)
2. ψ = (fun x [x ∈ RealSet] . cases{ 1 if x ≠ 0; 0 if x = 0 })

GOAL:
lim_{ x → 0 } (φ(x)) = 0

METHOD:

-/
theorem proof_gap_exercise_607_1
  (φ ψ : ℝ → ℝ)
  (h1 : PhiSpec φ)
  (h2 : ψ = (fun x : ℝ => if x ≠ 0 then 1 else 0))
  : Tendsto φ (𝓝[≠] 0) (𝓝 0) := by
  sorry

-- Exercise 607, gap 2
/-
PROOF GAP @2
ASSUM:
1. (forall (x) (p) (q), x ∈ RationalSet ∧ p ∈ IntegerSet ∧ q ∈ PosIntegerSet ∧ gcd(p, q) = 1 ∧ x = frac(p, q) ⇒ φ(x) = frac(1, q)) ∧ (forall (x), x ∈ RealSet ∧ x ∉ RationalSet ⇒ φ(x) = 0)
2. ψ = (fun x [x ∈ RealSet] . cases{ 1 if x ≠ 0; 0 if x = 0 })
3. lim_{ x → 0 } (φ(x)) = 0

GOAL:
lim_{ x → 0 } (ψ(x)) = 1

METHOD:

-/
theorem proof_gap_exercise_607_2
  (φ ψ : ℝ → ℝ)
  (h1 : PhiSpec φ)
  (h2 : ψ = (fun x : ℝ => if x ≠ 0 then 1 else 0))
  (h3 : Tendsto φ (𝓝[≠] 0) (𝓝 0))
  : Tendsto ψ (𝓝[≠] 0) (𝓝 1) := by
  sorry

-- Exercise 607, gap 3
/-
PROOF GAP @3
ASSUM:
1. φ = (fun x [x ∈ RealSet] . cases{ frac(1, q) if exists (p) (q), p ∈ IntegerSet ∧ q ∈ IntegerSet ∧ q ≠ 0 ∧ gcd(p, q) = 1 ∧ x = frac(p, q); 0 if x ∈ RealSet ∧ x ∉ RationalSet })
2. ψ = (fun x [x ∈ RealSet] . cases{ 1 if x ≠ 0; 0 if x = 0 })
3. lim_{ x → 0 } (φ(x)) = 0
4. lim_{ x → 0 } (ψ(x)) = 1
5. u = (fun n [n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet] . frac(sqrtn(2, 2), n))
6. v = (fun n [n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet] . frac(1, n))

GOAL:
forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ u(n) ∈ RealSet ∧ u(n) ∉ RationalSet ∧ v(n) ∈ RationalSet

METHOD:

-/
theorem proof_gap_exercise_607_3
  (φ ψ : ℝ → ℝ)
  (u v : ℕ → ℝ)
  (h1 : SignedPhiSpec φ)
  (h2 : ψ = (fun x : ℝ => if x ≠ 0 then 1 else 0))
  (h3 : Tendsto φ (𝓝[≠] 0) (𝓝 0))
  (h4 : Tendsto ψ (𝓝[≠] 0) (𝓝 1))
  (h5 : ∀ n : ℕ, 0 < n → u n = Real.sqrt 2 / (n : ℝ))
  (h6 : ∀ n : ℕ, 0 < n → v n = 1 / (n : ℝ))
  : ∀ n : ℕ, 0 < n → ¬ IsRat (u n) ∧ IsRat (v n) := by
  sorry

-- Exercise 607, gap 4
/-
PROOF GAP @4
ASSUM:
1. φ = (fun x [x ∈ RealSet] . cases{ frac(1, q) if exists (p) (q), p ∈ IntegerSet ∧ q ∈ IntegerSet ∧ q ≠ 0 ∧ gcd(p, q) = 1 ∧ x = frac(p, q); 0 if x ∈ RealSet ∧ x ∉ RationalSet })
2. ψ = (fun x [x ∈ RealSet] . cases{ 1 if x ≠ 0; 0 if x = 0 })
3. lim_{ x → 0 } (φ(x)) = 0
4. lim_{ x → 0 } (ψ(x)) = 1
5. u = (fun n [n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet] . frac(sqrtn(2, 2), n))
6. v = (fun n [n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet] . frac(1, n))
7. forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ u(n) ∈ RealSet ∧ u(n) ∉ RationalSet ∧ v(n) ∈ RationalSet

GOAL:
seqlim_{ n → +∞ } (u(n)) = 0

METHOD:

-/
theorem proof_gap_exercise_607_4
  (φ ψ : ℝ → ℝ)
  (u v : ℕ → ℝ)
  (h1 : SignedPhiSpec φ)
  (h2 : ψ = (fun x : ℝ => if x ≠ 0 then 1 else 0))
  (h3 : Tendsto φ (𝓝[≠] 0) (𝓝 0))
  (h4 : Tendsto ψ (𝓝[≠] 0) (𝓝 1))
  (h5 : ∀ n : ℕ, 0 < n → u n = Real.sqrt 2 / (n : ℝ))
  (h6 : ∀ n : ℕ, 0 < n → v n = 1 / (n : ℝ))
  (h7 : ∀ n : ℕ, 0 < n → ¬ IsRat (u n) ∧ IsRat (v n))
  : Tendsto u atTop (𝓝 0) := by
  sorry

-- Exercise 607, gap 5
/-
PROOF GAP @5
ASSUM:
1. φ = (fun x [x ∈ RealSet] . cases{ frac(1, q) if exists (p) (q), p ∈ IntegerSet ∧ q ∈ IntegerSet ∧ q ≠ 0 ∧ gcd(p, q) = 1 ∧ x = frac(p, q); 0 if x ∈ RealSet ∧ x ∉ RationalSet })
2. ψ = (fun x [x ∈ RealSet] . cases{ 1 if x ≠ 0; 0 if x = 0 })
3. lim_{ x → 0 } (φ(x)) = 0
4. lim_{ x → 0 } (ψ(x)) = 1
5. u = (fun n [n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet] . frac(sqrtn(2, 2), n))
6. v = (fun n [n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet] . frac(1, n))
7. forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ u(n) ∈ RealSet ∧ u(n) ∉ RationalSet ∧ v(n) ∈ RationalSet
8. seqlim_{ n → +∞ } (u(n)) = 0

GOAL:
seqlim_{ n → +∞ } (v(n)) = 0

METHOD:

-/
theorem proof_gap_exercise_607_5
  (φ ψ : ℝ → ℝ)
  (u v : ℕ → ℝ)
  (h1 : SignedPhiSpec φ)
  (h2 : ψ = (fun x : ℝ => if x ≠ 0 then 1 else 0))
  (h3 : Tendsto φ (𝓝[≠] 0) (𝓝 0))
  (h4 : Tendsto ψ (𝓝[≠] 0) (𝓝 1))
  (h5 : ∀ n : ℕ, 0 < n → u n = Real.sqrt 2 / (n : ℝ))
  (h6 : ∀ n : ℕ, 0 < n → v n = 1 / (n : ℝ))
  (h7 : ∀ n : ℕ, 0 < n → ¬ IsRat (u n) ∧ IsRat (v n))
  (h8 : Tendsto u atTop (𝓝 0))
  : Tendsto v atTop (𝓝 0) := by
  sorry

-- Exercise 607, gap 6
/-
PROOF GAP @6
ASSUM:
1. (forall (x) (p) (q), x ∈ RationalSet ∧ p ∈ IntegerSet ∧ q ∈ PosIntegerSet ∧ gcd(p, q) = 1 ∧ x = frac(p, q) ⇒ φ(x) = frac(1, q)) ∧ (forall (x), x ∈ RealSet ∧ x ∉ RationalSet ⇒ φ(x) = 0)
2. ψ = (fun x [x ∈ RealSet] . cases{ 1 if x ≠ 0; 0 if x = 0 })
3. lim_{ x → 0 } (φ(x)) = 0
4. lim_{ x → 0 } (ψ(x)) = 1
5. u = (fun n [n ∈ PosIntegerSet] . frac(sqrtn(2, 2), n))
6. v = (fun n [n ∈ PosIntegerSet] . frac(1, n))
7. forall (n), n ∈ PosIntegerSet ⇒ u(n) ∈ RealSet ∧ u(n) ∉ RationalSet ∧ v(n) ∈ RationalSet
8. seqlim_{ n → +∞ } (u(n)) = 0
9. seqlim_{ n → +∞ } (v(n)) = 0

GOAL:
forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ φ(u(n)) = 0 ∧ ψ(φ(u(n))) = 0

METHOD:

-/
theorem proof_gap_exercise_607_6
  (φ ψ : ℝ → ℝ)
  (u v : ℕ → ℝ)
  (h1 : PhiSpec φ)
  (h2 : ψ = (fun x : ℝ => if x ≠ 0 then 1 else 0))
  (h3 : Tendsto φ (𝓝[≠] 0) (𝓝 0))
  (h4 : Tendsto ψ (𝓝[≠] 0) (𝓝 1))
  (h5 : ∀ n : ℕ, 0 < n → u n = Real.sqrt 2 / (n : ℝ))
  (h6 : ∀ n : ℕ, 0 < n → v n = 1 / (n : ℝ))
  (h7 : ∀ n : ℕ, 0 < n → ¬ IsRat (u n) ∧ IsRat (v n))
  (h8 : Tendsto u atTop (𝓝 0))
  (h9 : Tendsto v atTop (𝓝 0))
  : ∀ n : ℕ, 0 < n → φ (u n) = 0 ∧ ψ (φ (u n)) = 0 := by
  sorry

-- Exercise 607, gap 7
/-
PROOF GAP @7
ASSUM:
1. (forall (x) (p) (q), x ∈ RationalSet ∧ p ∈ IntegerSet ∧ q ∈ PosIntegerSet ∧ gcd(p, q) = 1 ∧ x = frac(p, q) ⇒ φ(x) = frac(1, q)) ∧ (forall (x), x ∈ RealSet ∧ x ∉ RationalSet ⇒ φ(x) = 0)
2. ψ = (fun x [x ∈ RealSet] . cases{ 1 if x ≠ 0; 0 if x = 0 })
3. lim_{ x → 0 } (φ(x)) = 0
4. lim_{ x → 0 } (ψ(x)) = 1
5. u = (fun n [n ∈ PosIntegerSet] . frac(sqrtn(2, 2), n))
6. v = (fun n [n ∈ PosIntegerSet] . frac(1, n))
7. forall (n), n ∈ PosIntegerSet ⇒ u(n) ∈ RealSet ∧ u(n) ∉ RationalSet ∧ v(n) ∈ RationalSet
8. seqlim_{ n → +∞ } (u(n)) = 0
9. seqlim_{ n → +∞ } (v(n)) = 0
10. forall (n), n ∈ PosIntegerSet ⇒ φ(u(n)) = 0 ∧ ψ(φ(u(n))) = 0

GOAL:
forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ φ(v(n)) ≠ 0 ∧ ψ(φ(v(n))) = 1

METHOD:

-/
theorem proof_gap_exercise_607_7
  (φ ψ : ℝ → ℝ)
  (u v : ℕ → ℝ)
  (h1 : PhiSpec φ)
  (h2 : ψ = (fun x : ℝ => if x ≠ 0 then 1 else 0))
  (h3 : Tendsto φ (𝓝[≠] 0) (𝓝 0))
  (h4 : Tendsto ψ (𝓝[≠] 0) (𝓝 1))
  (h5 : ∀ n : ℕ, 0 < n → u n = Real.sqrt 2 / (n : ℝ))
  (h6 : ∀ n : ℕ, 0 < n → v n = 1 / (n : ℝ))
  (h7 : ∀ n : ℕ, 0 < n → ¬ IsRat (u n) ∧ IsRat (v n))
  (h8 : Tendsto u atTop (𝓝 0))
  (h9 : Tendsto v atTop (𝓝 0))
  (h10 : ∀ n : ℕ, 0 < n → φ (u n) = 0 ∧ ψ (φ (u n)) = 0)
  : ∀ n : ℕ, 0 < n → φ (v n) ≠ 0 ∧ ψ (φ (v n)) = 1 := by
  sorry

-- Exercise 607, gap 8
/-
PROOF GAP @8
ASSUM:
1. (forall (x) (p) (q), x ∈ RationalSet ∧ p ∈ IntegerSet ∧ q ∈ PosIntegerSet ∧ gcd(p, q) = 1 ∧ x = frac(p, q) ⇒ φ(x) = frac(1, q)) ∧ (forall (x), x ∈ RealSet ∧ x ∉ RationalSet ⇒ φ(x) = 0)
2. ψ = (fun x [x ∈ RealSet] . cases{ 1 if x ≠ 0; 0 if x = 0 })
3. lim_{ x → 0 } (φ(x)) = 0
4. lim_{ x → 0 } (ψ(x)) = 1
5. u = (fun n [n ∈ PosIntegerSet] . frac(sqrtn(2, 2), n))
6. v = (fun n [n ∈ PosIntegerSet] . frac(1, n))
7. forall (n), n ∈ PosIntegerSet ⇒ u(n) ∈ RealSet ∧ u(n) ∉ RationalSet ∧ v(n) ∈ RationalSet
8. seqlim_{ n → +∞ } (u(n)) = 0
9. seqlim_{ n → +∞ } (v(n)) = 0
10. forall (n), n ∈ PosIntegerSet ⇒ φ(u(n)) = 0 ∧ ψ(φ(u(n))) = 0
11. forall (n), n ∈ PosIntegerSet ⇒ φ(v(n)) ≠ 0 ∧ ψ(φ(v(n))) = 1

GOAL:
¬(exists (L), L ∈ RealSet ∧ lim_{ x → 0 } (ψ(φ(x))) = L)

METHOD:

-/
theorem proof_gap_exercise_607_8
  (φ ψ : ℝ → ℝ)
  (u v : ℕ → ℝ)
  (h1 : PhiSpec φ)
  (h2 : ψ = (fun x : ℝ => if x ≠ 0 then 1 else 0))
  (h3 : Tendsto φ (𝓝[≠] 0) (𝓝 0))
  (h4 : Tendsto ψ (𝓝[≠] 0) (𝓝 1))
  (h5 : ∀ n : ℕ, 0 < n → u n = Real.sqrt 2 / (n : ℝ))
  (h6 : ∀ n : ℕ, 0 < n → v n = 1 / (n : ℝ))
  (h7 : ∀ n : ℕ, 0 < n → ¬ IsRat (u n) ∧ IsRat (v n))
  (h8 : Tendsto u atTop (𝓝 0))
  (h9 : Tendsto v atTop (𝓝 0))
  (h10 : ∀ n : ℕ, 0 < n → φ (u n) = 0 ∧ ψ (φ (u n)) = 0)
  (h11 : ∀ n : ℕ, 0 < n → φ (v n) ≠ 0 ∧ ψ (φ (v n)) = 1)
  : ¬ ∃ L : ℝ, Tendsto (fun x => ψ (φ x)) (𝓝[≠] 0) (𝓝 L) := by
  sorry

-- Exercise 607, gap 9
/-
PROOF GAP @9
ASSUM:
1. (forall (x) (p) (q), x ∈ RationalSet ∧ p ∈ IntegerSet ∧ q ∈ PosIntegerSet ∧ gcd(p, q) = 1 ∧ x = frac(p, q) ⇒ φ(x) = frac(1, q)) ∧ (forall (x), x ∈ RealSet ∧ x ∉ RationalSet ⇒ φ(x) = 0)
2. ψ = (fun x [x ∈ RealSet] . cases{ 1 if x ≠ 0; 0 if x = 0 })
3. lim_{ x → 0 } (φ(x)) = 0
4. lim_{ x → 0 } (ψ(x)) = 1
5. u = (fun n [n ∈ PosIntegerSet] . frac(sqrtn(2, 2), n))
6. v = (fun n [n ∈ PosIntegerSet] . frac(1, n))
7. forall (n), n ∈ PosIntegerSet ⇒ u(n) ∈ RealSet ∧ u(n) ∉ RationalSet ∧ v(n) ∈ RationalSet
8. seqlim_{ n → +∞ } (u(n)) = 0
9. seqlim_{ n → +∞ } (v(n)) = 0
10. forall (n), n ∈ PosIntegerSet ⇒ φ(u(n)) = 0 ∧ ψ(φ(u(n))) = 0
11. forall (n), n ∈ PosIntegerSet ⇒ φ(v(n)) ≠ 0 ∧ ψ(φ(v(n))) = 1
12. ¬(exists (L), L ∈ RealSet ∧ lim_{ x → 0 } (ψ(φ(x))) = L)

GOAL:
¬(forall (φ) (ψ) (a) (A) (B), φ : RealSet → RealSet ∧ ψ : RealSet → RealSet ∧ a ∈ RealSet ∧ A ∈ RealSet ∧ B ∈ RealSet ∧ lim_{ x → a } (φ(x)) = A ∧ lim_{ x → A } (ψ(x)) = B ⇒ lim_{ x → a } (ψ(φ(x))) = B)

METHOD:

-/
theorem proof_gap_exercise_607_9
  (φ ψ : ℝ → ℝ)
  (u v : ℕ → ℝ)
  (h1 : PhiSpec φ)
  (h2 : ψ = (fun x : ℝ => if x ≠ 0 then 1 else 0))
  (h3 : Tendsto φ (𝓝[≠] 0) (𝓝 0))
  (h4 : Tendsto ψ (𝓝[≠] 0) (𝓝 1))
  (h5 : ∀ n : ℕ, 0 < n → u n = Real.sqrt 2 / (n : ℝ))
  (h6 : ∀ n : ℕ, 0 < n → v n = 1 / (n : ℝ))
  (h7 : ∀ n : ℕ, 0 < n → ¬ IsRat (u n) ∧ IsRat (v n))
  (h8 : Tendsto u atTop (𝓝 0))
  (h9 : Tendsto v atTop (𝓝 0))
  (h10 : ∀ n : ℕ, 0 < n → φ (u n) = 0 ∧ ψ (φ (u n)) = 0)
  (h11 : ∀ n : ℕ, 0 < n → φ (v n) ≠ 0 ∧ ψ (φ (v n)) = 1)
  (h12 : ¬ ∃ L : ℝ, Tendsto (fun x => ψ (φ x)) (𝓝[≠] 0) (𝓝 L))
  : ¬ (∀ (f g : ℝ → ℝ) (a A B : ℝ),
    Tendsto f (𝓝[≠] a) (𝓝 A) ∧ Tendsto g (𝓝[≠] A) (𝓝 B) →
    Tendsto (fun x => g (f x)) (𝓝[≠] a) (𝓝 B)) := by
  sorry

end Exercise607
