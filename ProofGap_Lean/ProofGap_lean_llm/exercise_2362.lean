import Mathlib

open Filter MeasureTheory
open scoped Topology

namespace Exercise2362

/- On each interval used below, 0 < x < 1: both bases x and log(1/x)
are positive, so the real integrand is positive and continuous locally.
Its nonnegative Lebesgue integral equals its extended improper integral.
Finiteness is therefore ordinary improper convergence (no principal value).
The outer x quantifiers printed by FNFL are retained; dx binds the inner
integration variable, as explicitly shown by the original text and RNFL.
Limit equality means existence of a common finite real limit.
-/
noncomputable def powerLogIntegral (p q a b : ℝ) : ENNReal :=
  ∫⁻ x in Set.Ioo a b,
    ENNReal.ofReal (Real.rpow x p * Real.rpow (Real.log (1 / x)) q)

-- Exercise 2362, gap 1
/-
PROOF GAP @1
ASSUM:
1. p ∈ RealSet
2. q ∈ RealSet
3. p > -1 ∧ q > -1

GOAL:
forall (x), x ∈ RealSet ⇒ DefInt(0, 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) = DefInt(0, frac(1, 2), x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) + DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))

METHOD:

-/
theorem proof_gap_exercise_2362_1
  (p q : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : p > -1 ∧ q > -1)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → powerLogIntegral p q 0 1 = powerLogIntegral p q 0 (1 / 2) + powerLogIntegral p q (1 / 2) 1 := by
  sorry

-- Exercise 2362, gap 2
/-
PROOF GAP @2
ASSUM:
1. p ∈ RealSet
2. q ∈ RealSet
3. forall (x), x ∈ RealSet ⇒ DefInt(0, 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) = DefInt(0, frac(1, 2), x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) + DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))
4. p > -1 ∧ q > -1

GOAL:
lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q})

METHOD:

-/
theorem proof_gap_exercise_2362_2
  (p q : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → powerLogIntegral p q 0 1 = powerLogIntegral p q 0 (1 / 2) + powerLogIntegral p q (1 / 2) 1)
  (h4 : p > -1 ∧ q > -1)
  : ∃ L : ℝ, Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L) ∧ Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L) := by
  sorry

-- Exercise 2362, gap 3
/-
PROOF GAP @3
ASSUM:
1. p ∈ RealSet
2. q ∈ RealSet
3. forall (x), x ∈ RealSet ⇒ DefInt(0, 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) = DefInt(0, frac(1, 2), x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) + DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))
4. lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q})
5. p > -1 ∧ q > -1

GOAL:
lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q}) = 1

METHOD:

-/
theorem proof_gap_exercise_2362_3
  (p q : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → powerLogIntegral p q 0 1 = powerLogIntegral p q 0 (1 / 2) + powerLogIntegral p q (1 / 2) 1)
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L) ∧ Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L))
  (h5 : p > -1 ∧ q > -1)
  : Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 1) := by
  sorry

-- Exercise 2362, gap 4
/-
PROOF GAP @4
ASSUM:
1. p ∈ RealSet
2. q ∈ RealSet
3. forall (x), x ∈ RealSet ⇒ DefInt(0, 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) = DefInt(0, frac(1, 2), x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) + DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))
4. lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q})
5. lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q}) = 1

GOAL:
lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = 1

METHOD:

-/
theorem proof_gap_exercise_2362_4
  (p q : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → powerLogIntegral p q 0 1 = powerLogIntegral p q 0 (1 / 2) + powerLogIntegral p q (1 / 2) 1)
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L) ∧ Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L))
  (h5 : Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 1))
  : Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 1) := by
  sorry

-- Exercise 2362, gap 5
/-
PROOF GAP @5
ASSUM:
1. p ∈ RealSet
2. q ∈ RealSet
3. forall (x), x ∈ RealSet ⇒ DefInt(0, 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) = DefInt(0, frac(1, 2), x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) + DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))
4. lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q})
5. lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q}) = 1
6. lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = 1
7. p > -1 ∧ q > -1

GOAL:
forall (x), x ∈ RealSet ∧ q > -1 ⇒ ConvergentSeries(DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))

METHOD:
[@method 根据 "广义积分比较判别法" @]
-/
theorem proof_gap_exercise_2362_5
  (p q : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → powerLogIntegral p q 0 1 = powerLogIntegral p q 0 (1 / 2) + powerLogIntegral p q (1 / 2) 1)
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L) ∧ Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L))
  (h5 : Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 1))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 1))
  (h7 : p > -1 ∧ q > -1)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ q > -1 → powerLogIntegral p q (1 / 2) 1 < ⊤ := by
  sorry

-- Exercise 2362, gap 6
/-
PROOF GAP @6
ASSUM:
1. p ∈ RealSet
2. q ∈ RealSet
3. forall (x), x ∈ RealSet ⇒ DefInt(0, 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) = DefInt(0, frac(1, 2), x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) + DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))
4. lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q})
5. lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q}) = 1
6. lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = 1
7. forall (x), x ∈ RealSet ∧ q > -1 ⇒ ConvergentSeries(DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))
8. p > -1 ∧ q > -1

GOAL:
forall (x), x ∈ RealSet ∧ q ≤ -1 ⇒ DivergentSeries(DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))

METHOD:
[@method 根据 "广义积分比较判别法" @]
-/
theorem proof_gap_exercise_2362_6
  (p q : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → powerLogIntegral p q 0 1 = powerLogIntegral p q 0 (1 / 2) + powerLogIntegral p q (1 / 2) 1)
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L) ∧ Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L))
  (h5 : Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 1))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 1))
  (h7 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ q > -1 → powerLogIntegral p q (1 / 2) 1 < ⊤)
  (h8 : p > -1 ∧ q > -1)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ q ≤ -1 → ¬ (powerLogIntegral p q (1 / 2) 1 < ⊤) := by
  sorry

-- Exercise 2362, gap 7
/-
PROOF GAP @7
ASSUM:
1. p ∈ RealSet
2. q ∈ RealSet
3. forall (x), x ∈ RealSet ⇒ DefInt(0, 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) = DefInt(0, frac(1, 2), x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) + DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))
4. lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q})
5. lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q}) = 1
6. lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = 1
7. forall (x), x ∈ RealSet ∧ q > -1 ⇒ ConvergentSeries(DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))
8. forall (x), x ∈ RealSet ∧ q ≤ -1 ⇒ DivergentSeries(DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))

GOAL:
forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ τ > 0

METHOD:

-/
theorem proof_gap_exercise_2362_7
  (p q : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → powerLogIntegral p q 0 1 = powerLogIntegral p q 0 (1 / 2) + powerLogIntegral p q (1 / 2) 1)
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L) ∧ Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L))
  (h5 : Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 1))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 1))
  (h7 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ q > -1 → powerLogIntegral p q (1 / 2) 1 < ⊤)
  (h8 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ q ≤ -1 → ¬ (powerLogIntegral p q (1 / 2) 1 < ⊤))
  : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → τ > 0 := by
  sorry

-- Exercise 2362, gap 8
/-
PROOF GAP @8
ASSUM:
1. p ∈ RealSet
2. q ∈ RealSet
3. forall (x), x ∈ RealSet ⇒ DefInt(0, 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) = DefInt(0, frac(1, 2), x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) + DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))
4. lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q})
5. lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q}) = 1
6. lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = 1
7. forall (x), x ∈ RealSet ∧ q > -1 ⇒ ConvergentSeries(DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))
8. forall (x), x ∈ RealSet ∧ q ≤ -1 ⇒ DivergentSeries(DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))
9. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ τ > 0

GOAL:
forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ p - τ > -1

METHOD:

-/
theorem proof_gap_exercise_2362_8
  (p q : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → powerLogIntegral p q 0 1 = powerLogIntegral p q 0 (1 / 2) + powerLogIntegral p q (1 / 2) 1)
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L) ∧ Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L))
  (h5 : Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 1))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 1))
  (h7 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ q > -1 → powerLogIntegral p q (1 / 2) 1 < ⊤)
  (h8 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ q ≤ -1 → ¬ (powerLogIntegral p q (1 / 2) 1 < ⊤))
  (h9 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → τ > 0)
  : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → p - τ > -1 := by
  sorry

-- Exercise 2362, gap 9
/-
PROOF GAP @9
ASSUM:
1. p ∈ RealSet
2. q ∈ RealSet
3. forall (x), x ∈ RealSet ⇒ DefInt(0, 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) = DefInt(0, frac(1, 2), x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) + DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))
4. lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q})
5. lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q}) = 1
6. lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = 1
7. forall (x), x ∈ RealSet ∧ q > -1 ⇒ ConvergentSeries(DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))
8. forall (x), x ∈ RealSet ∧ q ≤ -1 ⇒ DivergentSeries(DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))
9. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ τ > 0
10. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ p - τ > -1

GOAL:
forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ lim_{ x → 0^+ } (x^{-p + τ} * x^{p} * ln(frac(1, x))^{q}) = lim_{ x → 0^+ } (frac(ln(frac(1, x))^{q}, frac(1, x)^{τ}))

METHOD:

-/
theorem proof_gap_exercise_2362_9
  (p q : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → powerLogIntegral p q 0 1 = powerLogIntegral p q 0 (1 / 2) + powerLogIntegral p q (1 / 2) 1)
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L) ∧ Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L))
  (h5 : Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 1))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 1))
  (h7 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ q > -1 → powerLogIntegral p q (1 / 2) 1 < ⊤)
  (h8 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ q ≤ -1 → ¬ (powerLogIntegral p q (1 / 2) 1 < ⊤))
  (h9 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → τ > 0)
  (h10 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → p - τ > -1)
  : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → (∃ L : ℝ, Tendsto (fun x : ℝ => Real.rpow x (-p + τ) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 L) ∧ Tendsto (fun x : ℝ => Real.rpow (Real.log (1 / x)) q / Real.rpow (1 / x) τ) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 L)) := by
  sorry

-- Exercise 2362, gap 10
/-
PROOF GAP @10
ASSUM:
1. p ∈ RealSet
2. q ∈ RealSet
3. forall (x), x ∈ RealSet ⇒ DefInt(0, 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) = DefInt(0, frac(1, 2), x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) + DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))
4. lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q})
5. lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q}) = 1
6. lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = 1
7. forall (x), x ∈ RealSet ∧ q > -1 ⇒ ConvergentSeries(DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))
8. forall (x), x ∈ RealSet ∧ q ≤ -1 ⇒ DivergentSeries(DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))
9. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ τ > 0
10. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ p - τ > -1
11. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ lim_{ x → 0^+ } (x^{-p + τ} * x^{p} * ln(frac(1, x))^{q}) = lim_{ x → 0^+ } (frac(ln(frac(1, x))^{q}, frac(1, x)^{τ}))
12. p > -1 ∧ q > -1

GOAL:
forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ lim_{ x → 0^+ } (frac(ln(frac(1, x))^{q}, frac(1, x)^{τ})) = 0

METHOD:

-/
theorem proof_gap_exercise_2362_10
  (p q : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → powerLogIntegral p q 0 1 = powerLogIntegral p q 0 (1 / 2) + powerLogIntegral p q (1 / 2) 1)
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L) ∧ Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L))
  (h5 : Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 1))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 1))
  (h7 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ q > -1 → powerLogIntegral p q (1 / 2) 1 < ⊤)
  (h8 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ q ≤ -1 → ¬ (powerLogIntegral p q (1 / 2) 1 < ⊤))
  (h9 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → τ > 0)
  (h10 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → p - τ > -1)
  (h11 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → (∃ L : ℝ, Tendsto (fun x : ℝ => Real.rpow x (-p + τ) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 L) ∧ Tendsto (fun x : ℝ => Real.rpow (Real.log (1 / x)) q / Real.rpow (1 / x) τ) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 L)))
  (h12 : p > -1 ∧ q > -1)
  : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → Tendsto (fun x : ℝ => Real.rpow (Real.log (1 / x)) q / Real.rpow (1 / x) τ) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  sorry

-- Exercise 2362, gap 11
/-
PROOF GAP @11
ASSUM:
1. p ∈ RealSet
2. q ∈ RealSet
3. forall (x), x ∈ RealSet ⇒ DefInt(0, 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) = DefInt(0, frac(1, 2), x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) + DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))
4. lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q})
5. lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q}) = 1
6. lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = 1
7. forall (x), x ∈ RealSet ∧ q > -1 ⇒ ConvergentSeries(DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))
8. forall (x), x ∈ RealSet ∧ q ≤ -1 ⇒ DivergentSeries(DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))
9. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ τ > 0
10. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ p - τ > -1
11. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ lim_{ x → 0^+ } (x^{-p + τ} * x^{p} * ln(frac(1, x))^{q}) = lim_{ x → 0^+ } (frac(ln(frac(1, x))^{q}, frac(1, x)^{τ}))
12. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ lim_{ x → 0^+ } (frac(ln(frac(1, x))^{q}, frac(1, x)^{τ})) = 0

GOAL:
forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ lim_{ x → 0^+ } (x^{-p + τ} * x^{p} * ln(frac(1, x))^{q}) = 0

METHOD:

-/
theorem proof_gap_exercise_2362_11
  (p q : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → powerLogIntegral p q 0 1 = powerLogIntegral p q 0 (1 / 2) + powerLogIntegral p q (1 / 2) 1)
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L) ∧ Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L))
  (h5 : Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 1))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 1))
  (h7 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ q > -1 → powerLogIntegral p q (1 / 2) 1 < ⊤)
  (h8 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ q ≤ -1 → ¬ (powerLogIntegral p q (1 / 2) 1 < ⊤))
  (h9 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → τ > 0)
  (h10 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → p - τ > -1)
  (h11 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → (∃ L : ℝ, Tendsto (fun x : ℝ => Real.rpow x (-p + τ) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 L) ∧ Tendsto (fun x : ℝ => Real.rpow (Real.log (1 / x)) q / Real.rpow (1 / x) τ) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 L)))
  (h12 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → Tendsto (fun x : ℝ => Real.rpow (Real.log (1 / x)) q / Real.rpow (1 / x) τ) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
  : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → Tendsto (fun x : ℝ => Real.rpow x (-p + τ) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  sorry

-- Exercise 2362, gap 12
/-
PROOF GAP @12
ASSUM:
1. p ∈ RealSet
2. q ∈ RealSet
3. forall (x), x ∈ RealSet ⇒ DefInt(0, 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) = DefInt(0, frac(1, 2), x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) + DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))
4. lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q})
5. lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q}) = 1
6. lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = 1
7. forall (x), x ∈ RealSet ∧ q > -1 ⇒ ConvergentSeries(DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))
8. forall (x), x ∈ RealSet ∧ q ≤ -1 ⇒ DivergentSeries(DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))
9. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ τ > 0
10. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ p - τ > -1
11. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ lim_{ x → 0^+ } (x^{-p + τ} * x^{p} * ln(frac(1, x))^{q}) = lim_{ x → 0^+ } (frac(ln(frac(1, x))^{q}, frac(1, x)^{τ}))
12. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ lim_{ x → 0^+ } (frac(ln(frac(1, x))^{q}, frac(1, x)^{τ})) = 0
13. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ lim_{ x → 0^+ } (x^{-p + τ} * x^{p} * ln(frac(1, x))^{q}) = 0

GOAL:
forall (τ), τ ∈ RealSet ⇒ (forall (x), x ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ ConvergentSeries(DefInt(0, frac(1, 2), x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))))

METHOD:
[@method 根据 "广义积分比较判别法" @]
-/
theorem proof_gap_exercise_2362_12
  (p q : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → powerLogIntegral p q 0 1 = powerLogIntegral p q 0 (1 / 2) + powerLogIntegral p q (1 / 2) 1)
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L) ∧ Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L))
  (h5 : Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 1))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 1))
  (h7 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ q > -1 → powerLogIntegral p q (1 / 2) 1 < ⊤)
  (h8 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ q ≤ -1 → ¬ (powerLogIntegral p q (1 / 2) 1 < ⊤))
  (h9 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → τ > 0)
  (h10 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → p - τ > -1)
  (h11 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → (∃ L : ℝ, Tendsto (fun x : ℝ => Real.rpow x (-p + τ) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 L) ∧ Tendsto (fun x : ℝ => Real.rpow (Real.log (1 / x)) q / Real.rpow (1 / x) τ) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 L)))
  (h12 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → Tendsto (fun x : ℝ => Real.rpow (Real.log (1 / x)) q / Real.rpow (1 / x) τ) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
  (h13 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → Tendsto (fun x : ℝ => Real.rpow x (-p + τ) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
  : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) → ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → powerLogIntegral p q 0 (1 / 2) < ⊤ := by
  sorry

-- Exercise 2362, gap 13
/-
PROOF GAP @13
ASSUM:
1. p ∈ RealSet
2. q ∈ RealSet
3. forall (x), x ∈ RealSet ⇒ DefInt(0, 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) = DefInt(0, frac(1, 2), x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) + DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))
4. lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q})
5. lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q}) = 1
6. lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = 1
7. forall (x), x ∈ RealSet ∧ q > -1 ⇒ ConvergentSeries(DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))
8. forall (x), x ∈ RealSet ∧ q ≤ -1 ⇒ DivergentSeries(DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))
9. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ τ > 0
10. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ p - τ > -1
11. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ lim_{ x → 0^+ } (x^{-p + τ} * x^{p} * ln(frac(1, x))^{q}) = lim_{ x → 0^+ } (frac(ln(frac(1, x))^{q}, frac(1, x)^{τ}))
12. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ lim_{ x → 0^+ } (frac(ln(frac(1, x))^{q}, frac(1, x)^{τ})) = 0
13. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ lim_{ x → 0^+ } (x^{-p + τ} * x^{p} * ln(frac(1, x))^{q}) = 0
14. forall (τ), τ ∈ RealSet ⇒ (forall (x), x ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ ConvergentSeries(DefInt(0, frac(1, 2), x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))))

GOAL:
forall (x), x ∈ RealSet ∧ p > -1 ∧ q > -1 ⇒ ConvergentSeries(DefInt(0, 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))

METHOD:

-/
theorem proof_gap_exercise_2362_13
  (p q : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → powerLogIntegral p q 0 1 = powerLogIntegral p q 0 (1 / 2) + powerLogIntegral p q (1 / 2) 1)
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L) ∧ Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L))
  (h5 : Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 1))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 1))
  (h7 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ q > -1 → powerLogIntegral p q (1 / 2) 1 < ⊤)
  (h8 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ q ≤ -1 → ¬ (powerLogIntegral p q (1 / 2) 1 < ⊤))
  (h9 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → τ > 0)
  (h10 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → p - τ > -1)
  (h11 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → (∃ L : ℝ, Tendsto (fun x : ℝ => Real.rpow x (-p + τ) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 L) ∧ Tendsto (fun x : ℝ => Real.rpow (Real.log (1 / x)) q / Real.rpow (1 / x) τ) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 L)))
  (h12 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → Tendsto (fun x : ℝ => Real.rpow (Real.log (1 / x)) q / Real.rpow (1 / x) τ) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
  (h13 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → Tendsto (fun x : ℝ => Real.rpow x (-p + τ) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
  (h14 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) → ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → powerLogIntegral p q 0 (1 / 2) < ⊤)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 → powerLogIntegral p q 0 1 < ⊤ := by
  sorry

-- Exercise 2362, gap 14
/-
PROOF GAP @14
ASSUM:
1. p ∈ RealSet
2. q ∈ RealSet
3. forall (x), x ∈ RealSet ⇒ DefInt(0, 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) = DefInt(0, frac(1, 2), x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) + DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))
4. lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q})
5. lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q}) = 1
6. lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = 1
7. forall (x), x ∈ RealSet ∧ q > -1 ⇒ ConvergentSeries(DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))
8. forall (x), x ∈ RealSet ∧ q ≤ -1 ⇒ DivergentSeries(DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))
9. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ τ > 0
10. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ p - τ > -1
11. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ lim_{ x → 0^+ } (x^{-p + τ} * x^{p} * ln(frac(1, x))^{q}) = lim_{ x → 0^+ } (frac(ln(frac(1, x))^{q}, frac(1, x)^{τ}))
12. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ lim_{ x → 0^+ } (frac(ln(frac(1, x))^{q}, frac(1, x)^{τ})) = 0
13. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ lim_{ x → 0^+ } (x^{-p + τ} * x^{p} * ln(frac(1, x))^{q}) = 0
14. forall (τ), τ ∈ RealSet ⇒ (forall (x), x ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ ConvergentSeries(DefInt(0, frac(1, 2), x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))))
15. forall (x), x ∈ RealSet ∧ p > -1 ∧ q > -1 ⇒ ConvergentSeries(DefInt(0, 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))
16. p > -1 ∧ q > -1

GOAL:
forall (x), x ∈ RealSet ∧ p ≤ -1 ∧ q > -1 ⇒ DefInt(0, frac(1, 2), x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) ≥ DefInt(0, frac(1, 2), x^{-1} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))

METHOD:

-/
theorem proof_gap_exercise_2362_14
  (p q : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → powerLogIntegral p q 0 1 = powerLogIntegral p q 0 (1 / 2) + powerLogIntegral p q (1 / 2) 1)
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L) ∧ Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L))
  (h5 : Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 1))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 1))
  (h7 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ q > -1 → powerLogIntegral p q (1 / 2) 1 < ⊤)
  (h8 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ q ≤ -1 → ¬ (powerLogIntegral p q (1 / 2) 1 < ⊤))
  (h9 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → τ > 0)
  (h10 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → p - τ > -1)
  (h11 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → (∃ L : ℝ, Tendsto (fun x : ℝ => Real.rpow x (-p + τ) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 L) ∧ Tendsto (fun x : ℝ => Real.rpow (Real.log (1 / x)) q / Real.rpow (1 / x) τ) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 L)))
  (h12 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → Tendsto (fun x : ℝ => Real.rpow (Real.log (1 / x)) q / Real.rpow (1 / x) τ) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
  (h13 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → Tendsto (fun x : ℝ => Real.rpow x (-p + τ) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
  (h14 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) → ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → powerLogIntegral p q 0 (1 / 2) < ⊤)
  (h15 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 → powerLogIntegral p q 0 1 < ⊤)
  (h16 : p > -1 ∧ q > -1)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p ≤ -1 ∧ q > -1 → powerLogIntegral p q 0 (1 / 2) ≥ powerLogIntegral (-1) q 0 (1 / 2) := by
  sorry

-- Exercise 2362, gap 15
/-
PROOF GAP @15
ASSUM:
1. p ∈ RealSet
2. q ∈ RealSet
3. forall (x), x ∈ RealSet ⇒ DefInt(0, 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) = DefInt(0, frac(1, 2), x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) + DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))
4. lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q})
5. lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q}) = 1
6. lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = 1
7. forall (x), x ∈ RealSet ∧ q > -1 ⇒ ConvergentSeries(DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))
8. forall (x), x ∈ RealSet ∧ q ≤ -1 ⇒ DivergentSeries(DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))
9. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ τ > 0
10. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ p - τ > -1
11. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ lim_{ x → 0^+ } (x^{-p + τ} * x^{p} * ln(frac(1, x))^{q}) = lim_{ x → 0^+ } (frac(ln(frac(1, x))^{q}, frac(1, x)^{τ}))
12. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ lim_{ x → 0^+ } (frac(ln(frac(1, x))^{q}, frac(1, x)^{τ})) = 0
13. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ lim_{ x → 0^+ } (x^{-p + τ} * x^{p} * ln(frac(1, x))^{q}) = 0
14. forall (τ), τ ∈ RealSet ⇒ (forall (x), x ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ ConvergentSeries(DefInt(0, frac(1, 2), x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))))
15. forall (x), x ∈ RealSet ∧ p > -1 ∧ q > -1 ⇒ ConvergentSeries(DefInt(0, 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))
16. forall (x), x ∈ RealSet ∧ p ≤ -1 ∧ q > -1 ⇒ DefInt(0, frac(1, 2), x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) ≥ DefInt(0, frac(1, 2), x^{-1} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))

GOAL:
forall (x), x ∈ RealSet ∧ p ≤ -1 ∧ q > -1 ⇒ DefInt(0, frac(1, 2), x^{-1} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) = +∞

METHOD:

-/
theorem proof_gap_exercise_2362_15
  (p q : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → powerLogIntegral p q 0 1 = powerLogIntegral p q 0 (1 / 2) + powerLogIntegral p q (1 / 2) 1)
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L) ∧ Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L))
  (h5 : Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 1))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 1))
  (h7 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ q > -1 → powerLogIntegral p q (1 / 2) 1 < ⊤)
  (h8 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ q ≤ -1 → ¬ (powerLogIntegral p q (1 / 2) 1 < ⊤))
  (h9 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → τ > 0)
  (h10 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → p - τ > -1)
  (h11 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → (∃ L : ℝ, Tendsto (fun x : ℝ => Real.rpow x (-p + τ) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 L) ∧ Tendsto (fun x : ℝ => Real.rpow (Real.log (1 / x)) q / Real.rpow (1 / x) τ) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 L)))
  (h12 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → Tendsto (fun x : ℝ => Real.rpow (Real.log (1 / x)) q / Real.rpow (1 / x) τ) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
  (h13 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → Tendsto (fun x : ℝ => Real.rpow x (-p + τ) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
  (h14 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) → ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → powerLogIntegral p q 0 (1 / 2) < ⊤)
  (h15 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 → powerLogIntegral p q 0 1 < ⊤)
  (h16 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p ≤ -1 ∧ q > -1 → powerLogIntegral p q 0 (1 / 2) ≥ powerLogIntegral (-1) q 0 (1 / 2))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p ≤ -1 ∧ q > -1 → powerLogIntegral (-1) q 0 (1 / 2) = ⊤ := by
  sorry

-- Exercise 2362, gap 16
/-
PROOF GAP @16
ASSUM:
1. p ∈ RealSet
2. q ∈ RealSet
3. forall (x), x ∈ RealSet ⇒ DefInt(0, 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) = DefInt(0, frac(1, 2), x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) + DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))
4. lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q})
5. lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q}) = 1
6. lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = 1
7. forall (x), x ∈ RealSet ∧ q > -1 ⇒ ConvergentSeries(DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))
8. forall (x), x ∈ RealSet ∧ q ≤ -1 ⇒ DivergentSeries(DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))
9. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ τ > 0
10. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ p - τ > -1
11. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ lim_{ x → 0^+ } (x^{-p + τ} * x^{p} * ln(frac(1, x))^{q}) = lim_{ x → 0^+ } (frac(ln(frac(1, x))^{q}, frac(1, x)^{τ}))
12. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ lim_{ x → 0^+ } (frac(ln(frac(1, x))^{q}, frac(1, x)^{τ})) = 0
13. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ lim_{ x → 0^+ } (x^{-p + τ} * x^{p} * ln(frac(1, x))^{q}) = 0
14. forall (τ), τ ∈ RealSet ⇒ (forall (x), x ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ ConvergentSeries(DefInt(0, frac(1, 2), x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))))
15. forall (x), x ∈ RealSet ∧ p > -1 ∧ q > -1 ⇒ ConvergentSeries(DefInt(0, 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))
16. forall (x), x ∈ RealSet ∧ p ≤ -1 ∧ q > -1 ⇒ DefInt(0, frac(1, 2), x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) ≥ DefInt(0, frac(1, 2), x^{-1} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))
17. forall (x), x ∈ RealSet ∧ p ≤ -1 ∧ q > -1 ⇒ DefInt(0, frac(1, 2), x^{-1} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) = +∞

GOAL:
forall (x), x ∈ RealSet ∧ p ≤ -1 ∧ q > -1 ⇒ DivergentSeries(DefInt(0, 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))

METHOD:

-/
theorem proof_gap_exercise_2362_16
  (p q : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → powerLogIntegral p q 0 1 = powerLogIntegral p q 0 (1 / 2) + powerLogIntegral p q (1 / 2) 1)
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L) ∧ Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L))
  (h5 : Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 1))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 1))
  (h7 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ q > -1 → powerLogIntegral p q (1 / 2) 1 < ⊤)
  (h8 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ q ≤ -1 → ¬ (powerLogIntegral p q (1 / 2) 1 < ⊤))
  (h9 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → τ > 0)
  (h10 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → p - τ > -1)
  (h11 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → (∃ L : ℝ, Tendsto (fun x : ℝ => Real.rpow x (-p + τ) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 L) ∧ Tendsto (fun x : ℝ => Real.rpow (Real.log (1 / x)) q / Real.rpow (1 / x) τ) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 L)))
  (h12 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → Tendsto (fun x : ℝ => Real.rpow (Real.log (1 / x)) q / Real.rpow (1 / x) τ) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
  (h13 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → Tendsto (fun x : ℝ => Real.rpow x (-p + τ) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
  (h14 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) → ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → powerLogIntegral p q 0 (1 / 2) < ⊤)
  (h15 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 → powerLogIntegral p q 0 1 < ⊤)
  (h16 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p ≤ -1 ∧ q > -1 → powerLogIntegral p q 0 (1 / 2) ≥ powerLogIntegral (-1) q 0 (1 / 2))
  (h17 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p ≤ -1 ∧ q > -1 → powerLogIntegral (-1) q 0 (1 / 2) = ⊤)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p ≤ -1 ∧ q > -1 → ¬ (powerLogIntegral p q 0 1 < ⊤) := by
  sorry

-- Exercise 2362, gap 17
/-
PROOF GAP @17
ASSUM:
1. p ∈ RealSet
2. q ∈ RealSet
3. forall (x), x ∈ RealSet ⇒ DefInt(0, 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) = DefInt(0, frac(1, 2), x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) + DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))
4. lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q})
5. lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q}) = 1
6. lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = 1
7. forall (x), x ∈ RealSet ∧ q > -1 ⇒ ConvergentSeries(DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))
8. forall (x), x ∈ RealSet ∧ q ≤ -1 ⇒ DivergentSeries(DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))
9. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ τ > 0
10. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ p - τ > -1
11. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ lim_{ x → 0^+ } (x^{-p + τ} * x^{p} * ln(frac(1, x))^{q}) = lim_{ x → 0^+ } (frac(ln(frac(1, x))^{q}, frac(1, x)^{τ}))
12. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ lim_{ x → 0^+ } (frac(ln(frac(1, x))^{q}, frac(1, x)^{τ})) = 0
13. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ lim_{ x → 0^+ } (x^{-p + τ} * x^{p} * ln(frac(1, x))^{q}) = 0
14. forall (τ), τ ∈ RealSet ⇒ (forall (x), x ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ ConvergentSeries(DefInt(0, frac(1, 2), x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))))
15. forall (x), x ∈ RealSet ∧ p > -1 ∧ q > -1 ⇒ ConvergentSeries(DefInt(0, 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))
16. forall (x), x ∈ RealSet ∧ p ≤ -1 ∧ q > -1 ⇒ DefInt(0, frac(1, 2), x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) ≥ DefInt(0, frac(1, 2), x^{-1} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))
17. forall (x), x ∈ RealSet ∧ p ≤ -1 ∧ q > -1 ⇒ DefInt(0, frac(1, 2), x^{-1} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) = +∞
18. forall (x), x ∈ RealSet ∧ p ≤ -1 ∧ q > -1 ⇒ DivergentSeries(DefInt(0, 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))

GOAL:
forall (x), x ∈ RealSet ⇒ (ConvergentSeries(DefInt(0, 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))) ⇔ p > -1 ∧ q > -1)

METHOD:

-/
theorem proof_gap_exercise_2362_17
  (p q : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → powerLogIntegral p q 0 1 = powerLogIntegral p q 0 (1 / 2) + powerLogIntegral p q (1 / 2) 1)
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L) ∧ Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L))
  (h5 : Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 1))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 1))
  (h7 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ q > -1 → powerLogIntegral p q (1 / 2) 1 < ⊤)
  (h8 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ q ≤ -1 → ¬ (powerLogIntegral p q (1 / 2) 1 < ⊤))
  (h9 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → τ > 0)
  (h10 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → p - τ > -1)
  (h11 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → (∃ L : ℝ, Tendsto (fun x : ℝ => Real.rpow x (-p + τ) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 L) ∧ Tendsto (fun x : ℝ => Real.rpow (Real.log (1 / x)) q / Real.rpow (1 / x) τ) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 L)))
  (h12 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → Tendsto (fun x : ℝ => Real.rpow (Real.log (1 / x)) q / Real.rpow (1 / x) τ) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
  (h13 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → Tendsto (fun x : ℝ => Real.rpow x (-p + τ) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
  (h14 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) → ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → powerLogIntegral p q 0 (1 / 2) < ⊤)
  (h15 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 → powerLogIntegral p q 0 1 < ⊤)
  (h16 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p ≤ -1 ∧ q > -1 → powerLogIntegral p q 0 (1 / 2) ≥ powerLogIntegral (-1) q 0 (1 / 2))
  (h17 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p ≤ -1 ∧ q > -1 → powerLogIntegral (-1) q 0 (1 / 2) = ⊤)
  (h18 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p ≤ -1 ∧ q > -1 → ¬ (powerLogIntegral p q 0 1 < ⊤))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → (powerLogIntegral p q 0 1 < ⊤ ↔ p > -1 ∧ q > -1) := by
  sorry

-- Exercise 2362, gap 18
/-
PROOF GAP @18
ASSUM:
1. p ∈ RealSet
2. q ∈ RealSet
3. forall (x), x ∈ RealSet ⇒ DefInt(0, 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) = DefInt(0, frac(1, 2), x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) + DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))
4. lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q})
5. lim_{ x → 1^- } (x^{p} * frac(ln(frac(1, x)), 1 - x)^{q}) = 1
6. lim_{ x → 1^- } ((1 - x)^{-q} * x^{p} * ln(frac(1, x))^{q}) = 1
7. forall (x), x ∈ RealSet ∧ q > -1 ⇒ ConvergentSeries(DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))
8. forall (x), x ∈ RealSet ∧ q ≤ -1 ⇒ DivergentSeries(DefInt(frac(1, 2), 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))
9. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ τ > 0
10. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ p - τ > -1
11. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ lim_{ x → 0^+ } (x^{-p + τ} * x^{p} * ln(frac(1, x))^{q}) = lim_{ x → 0^+ } (frac(ln(frac(1, x))^{q}, frac(1, x)^{τ}))
12. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ lim_{ x → 0^+ } (frac(ln(frac(1, x))^{q}, frac(1, x)^{τ})) = 0
13. forall (τ), τ ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ lim_{ x → 0^+ } (x^{-p + τ} * x^{p} * ln(frac(1, x))^{q}) = 0
14. forall (τ), τ ∈ RealSet ⇒ (forall (x), x ∈ RealSet ∧ p > -1 ∧ q > -1 ∧ τ = frac(p + 1, 2) ⇒ ConvergentSeries(DefInt(0, frac(1, 2), x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))))
15. forall (x), x ∈ RealSet ∧ p > -1 ∧ q > -1 ⇒ ConvergentSeries(DefInt(0, 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))
16. forall (x), x ∈ RealSet ∧ p ≤ -1 ∧ q > -1 ⇒ DefInt(0, frac(1, 2), x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) ≥ DefInt(0, frac(1, 2), x^{-1} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))
17. forall (x), x ∈ RealSet ∧ p ≤ -1 ∧ q > -1 ⇒ DefInt(0, frac(1, 2), x^{-1} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)) = +∞
18. forall (x), x ∈ RealSet ∧ p ≤ -1 ∧ q > -1 ⇒ DivergentSeries(DefInt(0, 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x)))
19. forall (x), x ∈ RealSet ⇒ (ConvergentSeries(DefInt(0, 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))) ⇔ p > -1 ∧ q > -1)
20. p > -1 ∧ q > -1

GOAL:
forall (x), x ∈ RealSet ⇒ ((p, q) ∈ { (p, q) | p ∈ RealSet ∧ q ∈ RealSet ∧ p > -1 ∧ q > -1 } ⇔ ConvergentSeries(DefInt(0, 1, x^{p} * ln(frac(1, x))^{q} * diff(fun x [x ∈ RealSet] . x))))

METHOD:

-/
theorem proof_gap_exercise_2362_18
  (p q : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : q ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → powerLogIntegral p q 0 1 = powerLogIntegral p q 0 (1 / 2) + powerLogIntegral p q (1 / 2) 1)
  (h4 : ∃ L : ℝ, Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L) ∧ Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 L))
  (h5 : Tendsto (fun x : ℝ => Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 1))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1 - x) (-q) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 1 (Set.Iio 1)) (𝓝 1))
  (h7 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ q > -1 → powerLogIntegral p q (1 / 2) 1 < ⊤)
  (h8 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ q ≤ -1 → ¬ (powerLogIntegral p q (1 / 2) 1 < ⊤))
  (h9 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → τ > 0)
  (h10 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → p - τ > -1)
  (h11 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → (∃ L : ℝ, Tendsto (fun x : ℝ => Real.rpow x (-p + τ) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 L) ∧ Tendsto (fun x : ℝ => Real.rpow (Real.log (1 / x)) q / Real.rpow (1 / x) τ) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 L)))
  (h12 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → Tendsto (fun x : ℝ => Real.rpow (Real.log (1 / x)) q / Real.rpow (1 / x) τ) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
  (h13 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → Tendsto (fun x : ℝ => Real.rpow x (-p + τ) * Real.rpow x p * Real.rpow (Real.log (1 / x)) q) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
  (h14 : ∀ τ : ℝ, τ ∈ (Set.univ : Set ℝ) → ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 ∧ τ = (p + 1) / 2 → powerLogIntegral p q 0 (1 / 2) < ⊤)
  (h15 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p > -1 ∧ q > -1 → powerLogIntegral p q 0 1 < ⊤)
  (h16 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p ≤ -1 ∧ q > -1 → powerLogIntegral p q 0 (1 / 2) ≥ powerLogIntegral (-1) q 0 (1 / 2))
  (h17 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p ≤ -1 ∧ q > -1 → powerLogIntegral (-1) q 0 (1 / 2) = ⊤)
  (h18 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ p ≤ -1 ∧ q > -1 → ¬ (powerLogIntegral p q 0 1 < ⊤))
  (h19 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → (powerLogIntegral p q 0 1 < ⊤ ↔ p > -1 ∧ q > -1))
  (h20 : p > -1 ∧ q > -1)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → ((p, q) ∈ ({z : ℝ × ℝ | z.1 ∈ (Set.univ : Set ℝ) ∧ z.2 ∈ (Set.univ : Set ℝ) ∧ z.1 > -1 ∧ z.2 > -1}) ↔ powerLogIntegral p q 0 1 < ⊤) := by
  sorry

end Exercise2362
