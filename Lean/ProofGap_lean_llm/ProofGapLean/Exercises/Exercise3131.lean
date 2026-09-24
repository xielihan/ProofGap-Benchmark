import ProofGapLean.Prelude.Analysis
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Nat.Choose.Sum

namespace ProofGap.Exercise3131

noncomputable section

open scoped BigOperators

def generalizedBernstein (f : ℝ → ℝ) (a b : ℝ)
    (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    f (a + (b - a) * ((j : ℝ) / n)) *
      (Nat.choose n j : ℝ) *
      ((x - a) ^ j * (b - x) ^ (n - j) / (b - a) ^ n)

def expBernstein (a b k : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  generalizedBernstein (fun z => Real.exp (k * z)) a b n x

def substitutedSum (a b k : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    Real.exp (k * (a + (b - a) * ((j : ℝ) / n))) *
      (Nat.choose n j : ℝ) *
      ((x - a) ^ j * (b - x) ^ (n - j) / (b - a) ^ n)

def factoredSum (a b k : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (k * a) / (b - a) ^ n *
    ∑ j ∈ Finset.range (n + 1),
      Real.exp (k * (b - a) * ((j : ℝ) / n)) *
        (Nat.choose n j : ℝ) * (x - a) ^ j * (b - x) ^ (n - j)

def binomialBase (a b k : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (k * (b - a) / n) * (x - a) + b - x

def normalizedBase (a b k : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (Real.exp (k * (b - a) / n) - 1) * ((x - a) / (b - a)) + 1

/--
Exercise 3131, gap 1; make the interval,
nonzero denominator, and positive Bernstein degree explicit.
-/
theorem gap1 (a b k x : ℝ) (hab : a < b) (hx : x ∈ Set.Icc a b) :
    ∀ n : ℕ, 1 ≤ n →
      expBernstein a b k n x =
        generalizedBernstein (fun z => Real.exp (k * z)) a b n x := by
  intro n hn
  rfl

/-- Exercise 3131, gap 2; substitute the exponential function. -/
theorem gap2 (a b k x : ℝ) (hab : a < b) (hx : x ∈ Set.Icc a b) :
    ∀ n : ℕ, 1 ≤ n →
      expBernstein a b k n x = substitutedSum a b k n x := by
  intro n hn
  rfl

/-- Exercise 3131, gap 3; factor out `exp(ka)/(b-a)^n`. -/
theorem gap3 (a b k x : ℝ) (hab : a < b) (hx : x ∈ Set.Icc a b) :
    ∀ n : ℕ, 1 ≤ n →
      expBernstein a b k n x = factoredSum a b k n x := by
  intro n hn
  rw [gap2 a b k x hab hx n hn]
  unfold substitutedSum factoredSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show
    k * (a + (b - a) * ((j : ℝ) / n)) =
      k * a + k * (b - a) * ((j : ℝ) / n) by ring]
  rw [Real.exp_add]
  ring

/-- Exercise 3131, gap 4; apply the binomial theorem. -/
theorem gap4 (a b k x : ℝ) (hab : a < b) (hx : x ∈ Set.Icc a b) :
    ∀ n : ℕ, 1 ≤ n →
      expBernstein a b k n x =
        Real.exp (k * a) / (b - a) ^ n *
          binomialBase a b k n x ^ n := by
  intro n hn
  rw [gap3 a b k x hab hx n hn]
  unfold factoredSum binomialBase
  apply congrArg
    (fun z : ℝ => Real.exp (k * a) / (b - a) ^ n * z)
  have hexp (j : ℕ) :
      Real.exp (k * (b - a) * ((j : ℝ) / n)) =
        Real.exp (k * (b - a) / n) ^ j := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [show
    Real.exp (k * (b - a) / n) * (x - a) + b - x =
      Real.exp (k * (b - a) / n) * (x - a) + (b - x) by ring]
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hexp j, mul_pow]
  ring

/-- Exercise 3131, gap 5; move the denominator inside the power. -/
theorem gap5 (a b k x : ℝ) (hab : a < b) (hx : x ∈ Set.Icc a b) :
    ∀ n : ℕ, 1 ≤ n →
      expBernstein a b k n x =
        Real.exp (k * a) *
          (binomialBase a b k n x / (b - a)) ^ n := by
  intro n hn
  rw [gap4 a b k x hab hx n hn]
  rw [div_pow]
  ring

/-- Exercise 3131, gap 6; normalize the affine base. -/
theorem gap6 (a b k x : ℝ) (hab : a < b) (hx : x ∈ Set.Icc a b) :
    ∀ n : ℕ, 1 ≤ n →
      Real.exp (k * a) *
          (binomialBase a b k n x / (b - a)) ^ n =
        Real.exp (k * a) * normalizedBase a b k n x ^ n := by
  intro n hn
  apply congrArg
    (fun z : ℝ => Real.exp (k * a) * z ^ n)
  unfold binomialBase normalizedBase
  have hba : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  field_simp [hba] <;> ring

/-- Exercise 3131, gap 7; final closed exponential form. -/
theorem gap7 (a b k x : ℝ) (hab : a < b) (hx : x ∈ Set.Icc a b) :
    ∀ n : ℕ, 1 ≤ n →
      expBernstein a b k n x =
        Real.exp (k * a) * normalizedBase a b k n x ^ n := by
  intro n hn
  calc
    expBernstein a b k n x =
        Real.exp (k * a) *
          (binomialBase a b k n x / (b - a)) ^ n :=
      gap5 a b k x hab hx n hn
    _ = Real.exp (k * a) * normalizedBase a b k n x ^ n :=
      gap6 a b k x hab hx n hn

end

end ProofGap.Exercise3131
