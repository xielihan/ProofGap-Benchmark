import ProofGapLean.Prelude.Finite

/-!
# Exercise 4

Semantic formalization of Exercise 4, gaps 1,...,6.
The source ellipsis `1 + 2 + 2² + ... + 2ⁿ⁻¹` is represented by the standard
finite sum `∑ i ∈ range n, 2^i`.
-/

namespace ProofGap.Exercise4

def geometricSum (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, 2 ^ i

def GeometricFormula (n : ℕ) : Prop :=
  geometricSum n = 2 ^ n - 1

def BaseCase : Prop :=
  ∀ n : ℕ, n = 1 → (1 : ℕ) = 2 ^ 1 - 1

def AddNextPower : Prop :=
  ∀ n k : ℕ, n = k → GeometricFormula k →
    geometricSum (k + 1) = (2 ^ k - 1) + 2 ^ k

def SimplifyPowers : Prop :=
  ∀ n k : ℕ, n = k → GeometricFormula k →
    (2 ^ k - 1) + 2 ^ k = 2 ^ (k + 1) - 1

def InductionStep : Prop :=
  ∀ n k : ℕ, n = k → GeometricFormula k → GeometricFormula (k + 1)

/-- Exercise 4, gap 1. -/
theorem gap1 : BaseCase := by
  intro n hn
  norm_num

/-- Exercise 4, gap 2. -/
theorem gap2
    (h1 : BaseCase) :
    AddNextPower := by
  intro n k hnk hGk
  change geometricSum k = 2 ^ k - 1 at hGk
  rw [geometricSum, Finset.sum_range_succ, ← geometricSum, hGk]

/-- Exercise 4, gap 3. -/
theorem gap3
    (h1 : BaseCase)
    (h2 : AddNextPower) :
    SimplifyPowers := by
  intro n k hnk hGk
  rw [pow_succ]
  have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
  omega

/-- Exercise 4, gap 4. -/
theorem gap4
    (h1 : BaseCase)
    (h2 : AddNextPower)
    (h3 : SimplifyPowers) :
    InductionStep := by
  intro n k hnk hGk
  change geometricSum (k + 1) = 2 ^ (k + 1) - 1
  calc
    geometricSum (k + 1) = (2 ^ k - 1) + 2 ^ k := h2 n k hnk hGk
    _ = 2 ^ (k + 1) - 1 := h3 n k hnk hGk

/-- Exercise 4, gap 5. -/
theorem gap5
    (h1 : BaseCase)
    (h2 : AddNextPower)
    (h3 : SimplifyPowers)
    (h4 : InductionStep) :
    ∀ n : ℕ, 0 < n → GeometricFormula n := by
  intro n hn
  have hbase : GeometricFormula 1 := by
    change geometricSum 1 = 2 ^ 1 - 1
    norm_num [geometricSum]
  exact Nat.le_induction hbase (fun k _ ih => h4 k k rfl ih) n hn

/--
Exercise 4, gap 6.

The final source goal drops the positive-integer qualifier.  Interpreting the
index as `ℕ` is mathematically sound because the identity also holds for `n=0`.
-/
theorem gap6
    (h1 : BaseCase)
    (h2 : AddNextPower)
    (h3 : SimplifyPowers)
    (h4 : InductionStep)
    (h5 : ∀ n : ℕ, 0 < n → GeometricFormula n) :
    ∀ n : ℕ, GeometricFormula n := by
  intro n
  cases n with
  | zero => norm_num [GeometricFormula, geometricSum]
  | succ k => exact h5 (k + 1) (by omega)

end ProofGap.Exercise4
