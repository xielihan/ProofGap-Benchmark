import Mathlib

open scoped BigOperators Topology
open Filter

namespace Exercise2224

-- Positive integer indices are represented by naturals atTop; the value at zero
-- does not affect the limit. All divisions and square roots are real-valued.
noncomputable def outerSum (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i ∈ Finset.Icc 1 n, Real.sqrt (1 + (i : ℝ) / (n : ℝ))

noncomputable def innerSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, (1 / (n : ℝ)) * Real.sqrt (1 + (i : ℝ) / (n : ℝ))

-- Equality of the two existing finite limits.
def sameLimit : Prop :=
  ∃ L : ℝ, Tendsto outerSum atTop (𝓝 L) ∧ Tendsto innerSum atTop (𝓝 L)

-- diff(fun x => x) is dx, so its density is one.
noncomputable def integralValue : ℝ :=
  ∫ x in (0 : ℝ)..1, Real.sqrt (1 + x)

noncomputable def answer : ℝ := (2 / 3 : ℝ) * (2 * Real.sqrt 2 - 1)

end Exercise2224

open Exercise2224

/- Exercise 2224, gap 1
SHA-256: e2ab5e4548bb843ee1c1d697636db7b185904d7109a628552dd0509ac4beff11
PROOF GAP @1
ASSUM:

GOAL:
lim_{ n → +∞ } (frac(1, n) * (sum_{ i = 1 }^{ n } (sqrtn(2, 1 + frac(i, n))))) = lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(1, n) * sqrtn(2, 1 + frac(i, n))))

METHOD:

-/
theorem proof_gap_exercise_2224_1 : sameLimit := by
  sorry

/- Exercise 2224, gap 2
SHA-256: 5371463795e2fcf2ae92ddc7413acd1fab9eb785e771e08e8d17a9ff103cfe3b
PROOF GAP @2
ASSUM:
1. lim_{ n → +∞ } (frac(1, n) * (sum_{ i = 1 }^{ n } (sqrtn(2, 1 + frac(i, n))))) = lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(1, n) * sqrtn(2, 1 + frac(i, n))))

GOAL:
lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(1, n) * sqrtn(2, 1 + frac(i, n)))) = DefInt(0, 1, (fun x [x ∈ RealSet] . sqrtn(2, 1 + x)) * diff(fun x [x ∈ RealSet] . x))

METHOD:

-/
theorem proof_gap_exercise_2224_2
  (h1 : sameLimit) : Tendsto innerSum atTop (𝓝 integralValue) := by
  sorry

/- Exercise 2224, gap 3
SHA-256: 9252ea31905317921a161a7a1a78506348f72dd26b87fa45c1ebe65bc52485f7
PROOF GAP @3
ASSUM:
1. lim_{ n → +∞ } (frac(1, n) * (sum_{ i = 1 }^{ n } (sqrtn(2, 1 + frac(i, n))))) = lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(1, n) * sqrtn(2, 1 + frac(i, n))))
2. lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(1, n) * sqrtn(2, 1 + frac(i, n)))) = DefInt(0, 1, (fun x [x ∈ RealSet] . sqrtn(2, 1 + x)) * diff(fun x [x ∈ RealSet] . x))

GOAL:
DefInt(0, 1, (fun x [x ∈ RealSet] . sqrtn(2, 1 + x)) * diff(fun x [x ∈ RealSet] . x)) = frac(2, 3) * (2 * sqrtn(2, 2) - 1)

METHOD:

-/
theorem proof_gap_exercise_2224_3
  (h1 : sameLimit)
  (h2 : Tendsto innerSum atTop (𝓝 integralValue))
  : integralValue = answer := by
  sorry

/- Exercise 2224, gap 4
SHA-256: 0bfb3185e423b7ba33ea651dbc425c3926a516b031969b98e087cb7476b53c56
PROOF GAP @4
ASSUM:
1. lim_{ n → +∞ } (frac(1, n) * (sum_{ i = 1 }^{ n } (sqrtn(2, 1 + frac(i, n))))) = lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(1, n) * sqrtn(2, 1 + frac(i, n))))
2. lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(1, n) * sqrtn(2, 1 + frac(i, n)))) = DefInt(0, 1, (fun x [x ∈ RealSet] . sqrtn(2, 1 + x)) * diff(fun x [x ∈ RealSet] . x))
3. DefInt(0, 1, (fun x [x ∈ RealSet] . sqrtn(2, 1 + x)) * diff(fun x [x ∈ RealSet] . x)) = frac(2, 3) * (2 * sqrtn(2, 2) - 1)

GOAL:
lim_{ n → +∞ } (frac(1, n) * (sum_{ i = 1 }^{ n } (sqrtn(2, 1 + frac(i, n))))) = frac(2, 3) * (2 * sqrtn(2, 2) - 1)

METHOD:

-/
theorem proof_gap_exercise_2224_4
  (h1 : sameLimit)
  (h2 : Tendsto innerSum atTop (𝓝 integralValue))
  (h3 : integralValue = answer)
  : Tendsto outerSum atTop (𝓝 answer) := by
  sorry

