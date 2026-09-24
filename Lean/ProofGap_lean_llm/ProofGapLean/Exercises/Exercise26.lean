import ProofGapLean.Prelude.Elementary

/-!
# Exercise 26

Semantic formalization of `proof_gap/exercise_26/{1,...,12}.txt`.
The substitution is `t = x - 2`.  Several generated gaps split the interval
`-8 ≤ t ∧ t ≤ 4` into false standalone equivalences; those gaps are repaired
to retain the complete interval.
-/

namespace ProofGap.Exercise26

def Original (x : ℝ) : Prop :=
  |x + 2| + |x - 2| ≤ 12

def Transformed (t : ℝ) : Prop :=
  |t + 4| + |t| ≤ 12

def IntervalT (t : ℝ) : Prop :=
  -8 ≤ t ∧ t ≤ 4

def IntervalX (x : ℝ) : Prop :=
  -8 ≤ x - 2 ∧ x - 2 ≤ 4

/-- Source: `proof_gap/exercise_26/1.txt`. -/
theorem gap1
    (x t : ℝ)
    (ht : t = x - 2) :
    Original x ↔ Transformed t := by
  subst t
  unfold Original Transformed
  constructor <;> intro h <;> convert h using 1 <;> ring

/-- Source: `proof_gap/exercise_26/2.txt`. -/
theorem gap2
    (x t : ℝ)
    (ht : t = x - 2)
    (h1 : Original x ↔ Transformed t) :
    Original x ↔ |t + 4| ≤ 12 - |t| := by
  rw [h1]
  unfold Transformed
  constructor <;> intro h <;> linarith

/-- Source: `proof_gap/exercise_26/3.txt`. -/
theorem gap3
    (x t : ℝ)
    (ht : t = x - 2)
    (h2 : Original x ↔ |t + 4| ≤ 12 - |t|) :
    Original x ↔
      t ^ 2 + 8 * t + 16 ≤ 144 - 24 * |t| + t ^ 2 := by
  rw [h2]
  by_cases ht0 : 0 ≤ t
  · rw [abs_of_nonneg ht0, abs_of_nonneg (by linarith : 0 ≤ t + 4)]
    constructor <;> intro h <;> nlinarith
  · have htneg : t < 0 := lt_of_not_ge ht0
    rw [abs_of_neg htneg]
    by_cases ht4 : 0 ≤ t + 4
    · rw [abs_of_nonneg ht4]
      constructor <;> intro h <;> nlinarith
    · rw [abs_of_neg (lt_of_not_ge ht4)]
      constructor <;> intro h <;> nlinarith

/-- Source: `proof_gap/exercise_26/4.txt`. -/
theorem gap4
    (x t : ℝ)
    (ht : t = x - 2)
    (h3 : Original x ↔
      t ^ 2 + 8 * t + 16 ≤ 144 - 24 * |t| + t ^ 2) :
    Original x ↔ 3 * |t| ≤ 16 - t := by
  rw [h3]
  constructor <;> intro h <;> linarith

/-- Source: `proof_gap/exercise_26/5.txt`. -/
theorem gap5
    (x t : ℝ)
    (ht : t = x - 2)
    (h4 : Original x ↔ 3 * |t| ≤ 16 - t) :
    Original x ↔ t ^ 2 + 4 * t - 32 ≤ 0 := by
  rw [h4]
  by_cases ht0 : 0 ≤ t
  · rw [abs_of_nonneg ht0]
    constructor <;> intro h <;> nlinarith
  · rw [abs_of_neg (lt_of_not_ge ht0)]
    constructor <;> intro h <;> nlinarith

/-- Source: `proof_gap/exercise_26/6.txt`; repaired to the full interval. -/
theorem gap6
    (x t : ℝ)
    (ht : t = x - 2)
    (h5 : Original x ↔ t ^ 2 + 4 * t - 32 ≤ 0) :
    Original x ↔ IntervalT t := by
  rw [h5]
  unfold IntervalT
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg (t + 2)]
  · rintro ⟨hl, hu⟩
    have hprod : (t + 8) * (t - 4) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    nlinarith

/-- Source: `proof_gap/exercise_26/7.txt`; repaired to the full interval. -/
theorem gap7
    (x t : ℝ)
    (ht : t = x - 2)
    (h6 : Original x ↔ IntervalT t) :
    Original x ↔ IntervalT t := by
  exact h6

/-- Source: `proof_gap/exercise_26/8.txt`; repaired to the full interval. -/
theorem gap8
    (x t : ℝ)
    (ht : t = x - 2)
    (h7 : Original x ↔ IntervalT t) :
    Original x ↔ IntervalT t := by
  exact h7

/-- Source: `proof_gap/exercise_26/9.txt`; repaired to the translated interval. -/
theorem gap9
    (x t : ℝ)
    (ht : t = x - 2)
    (h8 : Original x ↔ IntervalT t) :
    Original x ↔ IntervalX x := by
  simpa [IntervalT, IntervalX, ht] using h8

/-- Source: `proof_gap/exercise_26/10.txt`; repaired to the translated interval. -/
theorem gap10
    (x t : ℝ)
    (ht : t = x - 2)
    (h9 : Original x ↔ IntervalX x) :
    Original x ↔ IntervalX x := by
  exact h9

/-- Source: `proof_gap/exercise_26/11.txt`; repaired to the translated interval. -/
theorem gap11
    (x t : ℝ)
    (ht : t = x - 2)
    (h10 : Original x ↔ IntervalX x) :
    Original x ↔ IntervalX x := by
  exact h10

/-- Source: `proof_gap/exercise_26/12.txt`. -/
theorem gap12
    (x : ℝ)
    (h11 : Original x ↔ IntervalX x) :
    x ∈ Set.Icc (-6 : ℝ) 6 ↔ Original x := by
  rw [h11]
  change (-6 ≤ x ∧ x ≤ 6) ↔ (-8 ≤ x - 2 ∧ x - 2 ≤ 4)
  constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> linarith

end ProofGap.Exercise26
