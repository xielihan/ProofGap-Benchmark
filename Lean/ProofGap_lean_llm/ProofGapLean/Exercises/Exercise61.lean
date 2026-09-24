import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Discrete
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Order.Floor

open scoped Topology

/-!
# Exercise 61

Semantic formalization of `proof_gap/exercise_61/{1,...,10}.txt`.
The auxiliary integer is selected separately for each real parameter `a`.
-/

namespace ProofGap.Exercise61

noncomputable section

def LargeCutoff (a : ℝ) (k : ℕ) : Prop :=
  0 < k ∧ 2 * |a| < k

def u (a : ℝ) (n : ℕ) : ℝ :=
  a ^ n / (Nat.factorial n : ℝ)

def factorProduct (a : ℝ) (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.Icc 1 n, |a| / (j : ℝ)

def upper (a : ℝ) (k n : ℕ) : ℝ :=
  (2 * |a|) ^ k / (2 : ℝ) ^ n

private theorem factorProduct_succ (a : ℝ) (n : ℕ) :
    factorProduct a (n + 1) =
      factorProduct a n * (|a| / ((n + 1 : ℕ) : ℝ)) := by
  unfold factorProduct
  rw [Finset.prod_Icc_succ_top (by omega)]

private theorem factorProduct_eq (a : ℝ) (n : ℕ) :
    factorProduct a n = |a| ^ n / (Nat.factorial n : ℝ) := by
  induction n with
  | zero =>
      norm_num [factorProduct]
  | succ n ih =>
      rw [factorProduct_succ, ih, Nat.factorial_succ]
      norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      field_simp
      rw [pow_succ]

private theorem factorProduct_nonneg (a : ℝ) (n : ℕ) :
    0 ≤ factorProduct a n := by
  unfold factorProduct
  positivity

private theorem factorProduct_le_pow (a : ℝ) (n : ℕ) :
    factorProduct a n ≤ |a| ^ n := by
  induction n with
  | zero =>
      norm_num [factorProduct]
  | succ n ih =>
      rw [factorProduct_succ, pow_succ]
      have hratio :
          |a| / (((n + 1 : ℕ) : ℝ)) ≤ |a| :=
        div_le_self (abs_nonneg a) (by norm_num)
      exact mul_le_mul ih hratio (by positivity) (by positivity)

/-- Source: `proof_gap/exercise_61/1.txt`; the witness is chosen pointwise. -/
theorem gap1 :
    ∀ a : ℝ, ∃ k : ℕ, 0 < k := by
  intro a
  exact ⟨1, by omega⟩

/-- Source: `proof_gap/exercise_61/2.txt`; the quantifier order is repaired. -/
theorem gap2
    (h1 : ∀ a : ℝ, ∃ k : ℕ, 0 < k) :
    ∀ a : ℝ, ∃ k : ℕ, LargeCutoff a k := by
  intro a
  refine ⟨Nat.floor (2 * |a|) + 1, ?_⟩
  constructor
  · omega
  · simpa [Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one (2 * |a|)

/-- Source: `proof_gap/exercise_61/3.txt`; nonnegativity includes `a=0`. -/
theorem gap3
    (a : ℝ) (k : ℕ)
    (hk : LargeCutoff a k) :
    ∀ n : ℕ, k < n → 0 ≤ |u a n| := by
  intro n hn
  exact abs_nonneg _

/-- Source: `proof_gap/exercise_61/4.txt`; ellipses are a finite product. -/
theorem gap4
    (a : ℝ) (k : ℕ)
    (hk : LargeCutoff a k) :
    ∀ n : ℕ, k < n → |u a n| = factorProduct a n := by
  intro n hn
  rw [factorProduct_eq]
  unfold u
  rw [abs_div, abs_pow]
  simp

/-- Source: `proof_gap/exercise_61/5.txt`; `≤` includes `a=0`. -/
theorem gap5
    (a : ℝ) (k : ℕ)
    (hk : LargeCutoff a k)
    (h4 : ∀ n : ℕ, k < n → |u a n| = factorProduct a n) :
    ∀ n : ℕ, k < n →
      factorProduct a n ≤ |a| ^ k * (1 / 2 : ℝ) ^ (n - k) := by
  have hbase :
      factorProduct a k ≤ |a| ^ k * (1 / 2 : ℝ) ^ (k - k) := by
    simpa using factorProduct_le_pow a k
  have hstep :
      ∀ m : ℕ, k ≤ m →
        factorProduct a m ≤ |a| ^ k * (1 / 2 : ℝ) ^ (m - k) →
        factorProduct a (m + 1) ≤
          |a| ^ k * (1 / 2 : ℝ) ^ ((m + 1) - k) := by
    intro m hkm ihm
    have hmpos : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
    have hratio :
        |a| / (((m + 1 : ℕ) : ℝ)) ≤ (1 / 2 : ℝ) := by
      apply (div_le_iff₀ hmpos).2
      have hcut : 2 * |a| < (k : ℝ) := hk.2
      have hcast : (k : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show k ≤ m + 1 by omega)
      nlinarith
    rw [factorProduct_succ]
    calc
      factorProduct a m * (|a| / (((m + 1 : ℕ) : ℝ))) ≤
          (|a| ^ k * (1 / 2 : ℝ) ^ (m - k)) *
            (|a| / (((m + 1 : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_right ihm (by positivity)
      _ ≤ (|a| ^ k * (1 / 2 : ℝ) ^ (m - k)) * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = |a| ^ k * (1 / 2 : ℝ) ^ ((m + 1) - k) := by
        rw [show (m + 1) - k = (m - k) + 1 by omega, pow_succ]
        ring
  intro n hn
  exact Nat.le_induction hbase hstep n (Nat.le_of_lt hn)

/-- Source: `proof_gap/exercise_61/6.txt`. -/
theorem gap6
    (a : ℝ) (k : ℕ) :
    ∀ n : ℕ, k < n →
      |a| ^ k * (1 / 2 : ℝ) ^ (n - k) = upper a k n := by
  intro n hn
  unfold upper
  rw [show n = k + (n - k) by omega, pow_add]
  rw [show k + (n - k) - k = n - k by omega, div_pow]
  norm_num
  field_simp
  ring

/-- Source: `proof_gap/exercise_61/7.txt`; nonnegativity includes `a=0`. -/
theorem gap7
    (a : ℝ) (k : ℕ) :
    ∀ n : ℕ, k < n → 0 ≤ upper a k n := by
  intro n hn
  unfold upper
  positivity

/-- Source: `proof_gap/exercise_61/8.txt`. -/
theorem gap8
    (a : ℝ) (k : ℕ) :
    Tendsto (upper a k) atTop (𝓝 0) := by
  have hpow :
      Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
  unfold upper
  simpa [div_pow] using hpow.const_mul ((2 * |a|) ^ k)

/-- Source: `proof_gap/exercise_61/9.txt`. -/
theorem gap9
    (a : ℝ)
    (h2 : ∀ a : ℝ, ∃ k : ℕ, LargeCutoff a k) :
    Tendsto (u a) atTop (𝓝 0) := by
  simpa [u] using
    (FloorSemiring.tendsto_pow_div_factorial_atTop a :
      Tendsto (fun n : ℕ => a ^ n / (Nat.factorial n : ℝ))
        atTop (𝓝 0))

/-- Source: `proof_gap/exercise_61/10.txt`. -/
theorem gap10
    (a : ℝ)
    (h9 : Tendsto (u a) atTop (𝓝 0)) :
    Tendsto (u a) atTop (𝓝 0) := by
  exact h9

end

end ProofGap.Exercise61
