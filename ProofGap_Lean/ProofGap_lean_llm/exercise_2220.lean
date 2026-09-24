import Mathlib

open scoped BigOperators Topology
open Filter

namespace Exercise2220

-- Positive integer indices are represented by naturals; the value at n = 0
-- is irrelevant for convergence at infinity. Every division is in ℝ.
noncomputable def originalSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, 1 / ((n : ℝ) + (i : ℝ))

noncomputable def riemannSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, (1 / (1 + (i : ℝ) / (n : ℝ))) * (1 / (n : ℝ))

-- Equality of existing real limits, including existence of both limits.
def SameLimit : Prop :=
  ∃ L : ℝ, Tendsto originalSum atTop (𝓝 L) ∧ Tendsto riemannSum atTop (𝓝 L)

-- diff(id) is dx, so the differential contributes a factor of one.
noncomputable def integralValue : ℝ := ∫ x in (0 : ℝ)..1, 1 / (1 + x)

end Exercise2220

open Exercise2220

/- Exercise 2220, gap 1
PROOF GAP @1
ASSUM:

GOAL:
lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(1, n + i))) = lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(1, 1 + frac(i, n)) * frac(1, n)))

METHOD:

-/
theorem proof_gap_exercise_2220_1 : SameLimit := by
  sorry

/- Exercise 2220, gap 2
PROOF GAP @2
ASSUM:
1. lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(1, n + i))) = lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(1, 1 + frac(i, n)) * frac(1, n)))

GOAL:
lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(1, 1 + frac(i, n)) * frac(1, n))) = DefInt(0, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x)) * diff(fun x [x ∈ RealSet] . x))

METHOD:

-/
theorem proof_gap_exercise_2220_2
    (h1 : SameLimit) : Tendsto riemannSum atTop (𝓝 integralValue) := by
  sorry

/- Exercise 2220, gap 3
PROOF GAP @3
ASSUM:
1. lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(1, n + i))) = lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(1, 1 + frac(i, n)) * frac(1, n)))
2. lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(1, 1 + frac(i, n)) * frac(1, n))) = DefInt(0, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x)) * diff(fun x [x ∈ RealSet] . x))

GOAL:
DefInt(0, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x)) * diff(fun x [x ∈ RealSet] . x)) = ln(2)

METHOD:

-/
theorem proof_gap_exercise_2220_3
    (h1 : SameLimit)
    (h2 : Tendsto riemannSum atTop (𝓝 integralValue)) :
    integralValue = Real.log 2 := by
  sorry

/- Exercise 2220, gap 4
PROOF GAP @4
ASSUM:
1. lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(1, n + i))) = lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(1, 1 + frac(i, n)) * frac(1, n)))
2. lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(1, 1 + frac(i, n)) * frac(1, n))) = DefInt(0, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x)) * diff(fun x [x ∈ RealSet] . x))
3. DefInt(0, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x)) * diff(fun x [x ∈ RealSet] . x)) = ln(2)

GOAL:
lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(1, n + i))) = ln(2)

METHOD:

-/
theorem proof_gap_exercise_2220_4
    (h1 : SameLimit)
    (h2 : Tendsto riemannSum atTop (𝓝 integralValue))
    (h3 : integralValue = Real.log 2) :
    Tendsto originalSum atTop (𝓝 (Real.log 2)) := by
  sorry

