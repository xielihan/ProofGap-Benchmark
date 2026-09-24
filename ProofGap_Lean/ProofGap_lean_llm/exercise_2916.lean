import Mathlib

noncomputable section

/-!
Generated from proofgrader DSL gaps. This file intentionally contains theorem
statements with `by sorry` placeholders only; it was not compiled in this round.
The original DSL assumptions and goals are preserved in comments above each gap.
-/

namespace ProofGapBatch5

abbrev SeqR := ℕ → ℝ
abbrev SeqC := ℕ → ℂ

def RadiusOfConvergenceR (_a : SeqR) : ℝ := 0
def RadiusOfConvergenceC (_a : SeqC) : ℝ := 0
def seqLim (_u : ℕ → ℝ) (_L : ℝ) : Prop := True
def seqLiminf (_u : ℕ → ℝ) : ℝ := 0
def seqLimsup (_u : ℕ → ℝ) : ℝ := 0
def ConvergentSeriesR (_u : ℕ → ℝ) : Prop := True
def ConvergentSeriesC (_u : ℕ → ℂ) : Prop := True
def UniformConvergentOn (_F : ℕ → ℝ → ℝ) (_s : Set ℝ) (_f : ℝ → ℝ) : Prop := True
def DiffableFuncAtIter (_f : ℝ → ℝ) (_m : ℕ) (_c : ℝ) : Prop := True
def iterDerivValue (_f : ℝ → ℝ) (_m : ℕ) (_x : ℝ) : ℝ := 0
def partialSum (u : ℕ → ℝ) (n : ℕ) : ℝ := Finset.sum (Finset.range (n+1)) u
def tailSeriesR (_start : ℕ) (_u : ℕ → ℝ) : ℝ := 0
def tailSeriesC (_start : ℕ) (_u : ℕ → ℂ) : Prop := True
def geomSeries (_x : ℝ) : ℝ := 0
def nroot (n : ℕ) (x : ℝ) : ℝ := x ^ (1 / (n : ℝ))
def factR (n : ℕ) : ℝ := (Nat.factorial n : ℝ)

namespace exercise_2916

variable (z : ℂ) (c : SeqC)
/-
===== GAP 1 original DSL =====
PROOF GAP @1
ASSUM:
1. z ∈ ComplexSet
2. c : NonNegIntegerSet → ComplexSet
3. forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ⇒ c(n) = frac(1, n * 2^{n})

GOAL:
seqlim_{ n → +∞ } (|frac(c(n), c(n + 1))|) = 2

METHOD:
-/
theorem proof_gap_exercise_2916_1 (hc : ∀ n : ℕ, 0 < n → c n = (1 : ℂ) / (n * 2^n : ℕ)) :
    seqLim (fun n => ‖(c n) / (c (n+1))‖) 2 := by
  sorry

/-
===== GAP 2 original DSL =====
PROOF GAP @2
ASSUM:
1. z ∈ ComplexSet
2. c : NonNegIntegerSet → ComplexSet
3. forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ⇒ c(n) = frac(1, n * 2^{n})
4. seqlim_{ n → +∞ } (|frac(c(n), c(n + 1))|) = 2

GOAL:
RadiusOfConvergence(c) = 2

METHOD:
-/
theorem proof_gap_exercise_2916_2 (hc : ∀ n : ℕ, 0 < n → c n = (1 : ℂ) / (n * 2^n : ℕ)) :
    RadiusOfConvergenceC c = 2 := by
  sorry

/-
===== GAP 3 original DSL =====
PROOF GAP @3
ASSUM:
1. z ∈ ComplexSet
2. c : NonNegIntegerSet → ComplexSet
3. forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ⇒ c(n) = frac(1, n * 2^{n})
4. seqlim_{ n → +∞ } (|frac(c(n), c(n + 1))|) = 2
5. RadiusOfConvergence(c) = 2

GOAL:
ConvergentSeries(sum_{ n = 1 }^{ +∞ } (c(n) * (z - 1 - __IMAGINARY_UNIT__)^{n})) ⇔ |z - 1 - __IMAGINARY_UNIT__| < 2

METHOD:
-/
theorem proof_gap_exercise_2916_3 (hc : ∀ n : ℕ, 0 < n → c n = (1 : ℂ) / (n * 2^n : ℕ)) :
    ConvergentSeriesC (fun n => c n * (z - 1 - Complex.I)^n) ↔ ‖z - 1 - Complex.I‖ < 2 := by
  sorry

/-
===== GAP 4 original DSL =====
PROOF GAP @4
ASSUM:
1. z ∈ ComplexSet
2. c : NonNegIntegerSet → ComplexSet
3. forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ⇒ c(n) = frac(1, n * 2^{n})
4. seqlim_{ n → +∞ } (|frac(c(n), c(n + 1))|) = 2
5. RadiusOfConvergence(c) = 2
6. ConvergentSeries(sum_{ n = 1 }^{ +∞ } (c(n) * (z - 1 - __IMAGINARY_UNIT__)^{n})) ⇔ |z - 1 - __IMAGINARY_UNIT__| < 2

GOAL:
forall (x), x ∈ RealSet ⇒ (forall (y), z = x + y * __IMAGINARY_UNIT__ ∧ x ∈ RealSet ∧ y ∈ RealSet ⇒ (|z - 1 - __IMAGINARY_UNIT__| < 2 ⇔ (x - 1)^{2} + (y - 1)^{2} < 2^{2}))

METHOD:
-/
theorem proof_gap_exercise_2916_4 (hc : ∀ n : ℕ, 0 < n → c n = (1 : ℂ) / (n * 2^n : ℕ)) :
    ∀ x y : ℝ, z = x + y * Complex.I → (‖z - 1 - Complex.I‖ < 2 ↔ (x-1)^2 + (y-1)^2 < 2^2) := by
  sorry

/-
===== GAP 5 original DSL =====
PROOF GAP @5
ASSUM:
1. z ∈ ComplexSet
2. c : NonNegIntegerSet → ComplexSet
3. forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ⇒ c(n) = frac(1, n * 2^{n})
4. seqlim_{ n → +∞ } (|frac(c(n), c(n + 1))|) = 2
5. RadiusOfConvergence(c) = 2
6. ConvergentSeries(sum_{ n = 1 }^{ +∞ } (c(n) * (z - 1 - __IMAGINARY_UNIT__)^{n})) ⇔ |z - 1 - __IMAGINARY_UNIT__| < 2
7. forall (x), x ∈ RealSet ⇒ (forall (y), z = x + y * __IMAGINARY_UNIT__ ∧ x ∈ RealSet ∧ y ∈ RealSet ⇒ (|z - 1 - __IMAGINARY_UNIT__| < 2 ⇔ (x - 1)^{2} + (y - 1)^{2} < 2^{2}))

GOAL:
{ z | z ∈ ComplexSet, |z - 1 - __IMAGINARY_UNIT__| < 2 } = { x + y * __IMAGINARY_UNIT__ | x ∈ RealSet, y ∈ RealSet, (x - 1)^{2} + (y - 1)^{2} < 2^{2} } ⇔ ConvergentSeries(sum_{ n = 1 }^{ +∞ } (c(n) * (z - 1 - __IMAGINARY_UNIT__)^{n}))

METHOD:
-/
theorem proof_gap_exercise_2916_5 (hc : ∀ n : ℕ, 0 < n → c n = (1 : ℂ) / (n * 2^n : ℕ)) :
    ({z : ℂ | ‖z - 1 - Complex.I‖ < 2} = {w : ℂ | ∃ x y : ℝ, w = x + y * Complex.I ∧ (x-1)^2 + (y-1)^2 < 2^2}) ↔ ConvergentSeriesC (fun n => c n * (z - 1 - Complex.I)^n) := by
  sorry

end exercise_2916

end ProofGapBatch5
