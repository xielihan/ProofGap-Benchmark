import Mathlib

open scoped BigOperators Topology
open Filter

namespace Exercise2221

-- Positive integer indices are represented by Nat; the extra n = 0 term
-- does not affect the limit atTop. All arithmetic in summands is real.
noncomputable def originalSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, (n : ℝ) / ((n : ℝ) ^ 2 + (i : ℝ) ^ 2)

noncomputable def riemannSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, (1 / (1 + ((i : ℝ) / (n : ℝ)) ^ 2)) *
    (1 / (n : ℝ))

-- Equality of the two finite limits includes their existence.
def sameLimit : Prop :=
  ∃ L : ℝ, Tendsto originalSum atTop (𝓝 L) ∧
    Tendsto riemannSum atTop (𝓝 L)

-- diff(id) is dx, so this is the ordinary integral with respect to x.
noncomputable def integralValue : ℝ :=
  ∫ x in (0 : ℝ)..1, 1 / (1 + x ^ 2)

end Exercise2221

open Exercise2221

/- Exercise 2221, gap 1
PROOF GAP @1
ASSUM:

GOAL:
lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(n, n^{2} + i^{2}))) = lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(1, 1 + frac(i, n)^{2}) * frac(1, n)))

METHOD:

-/
theorem proof_gap_exercise_2221_1 : sameLimit := by
  sorry

/- Exercise 2221, gap 2
PROOF GAP @2
ASSUM:
1. lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(n, n^{2} + i^{2}))) = lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(1, 1 + frac(i, n)^{2}) * frac(1, n)))

GOAL:
lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(1, 1 + frac(i, n)^{2}) * frac(1, n))) = DefInt(0, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x))

METHOD:

-/
theorem proof_gap_exercise_2221_2
    (h1 : sameLimit) :
    Tendsto riemannSum atTop (𝓝 integralValue) := by
  sorry

/- Exercise 2221, gap 3
PROOF GAP @3
ASSUM:
1. lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(n, n^{2} + i^{2}))) = lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(1, 1 + frac(i, n)^{2}) * frac(1, n)))
2. lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(1, 1 + frac(i, n)^{2}) * frac(1, n))) = DefInt(0, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x))

GOAL:
DefInt(0, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = frac(π, 4)

METHOD:

-/
theorem proof_gap_exercise_2221_3
    (h1 : sameLimit)
    (h2 : Tendsto riemannSum atTop (𝓝 integralValue)) :
    integralValue = Real.pi / 4 := by
  sorry

/- Exercise 2221, gap 4
PROOF GAP @4
ASSUM:
1. lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(n, n^{2} + i^{2}))) = lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(1, 1 + frac(i, n)^{2}) * frac(1, n)))
2. lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(1, 1 + frac(i, n)^{2}) * frac(1, n))) = DefInt(0, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x))
3. DefInt(0, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = frac(π, 4)

GOAL:
lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(n, n^{2} + i^{2}))) = frac(π, 4)

METHOD:

-/
theorem proof_gap_exercise_2221_4
    (h1 : sameLimit)
    (h2 : Tendsto riemannSum atTop (𝓝 integralValue))
    (h3 : integralValue = Real.pi / 4) :
    Tendsto originalSum atTop (𝓝 (Real.pi / 4)) := by
  sorry

