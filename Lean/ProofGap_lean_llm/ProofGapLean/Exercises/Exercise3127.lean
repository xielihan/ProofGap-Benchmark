import ProofGapLean.Prelude.Analysis
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Nat.Choose.Sum

namespace ProofGap.Exercise3127

noncomputable section

open scoped BigOperators

def bernstein (n : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    f ((k : ℝ) / n) * (Nat.choose n k : ℝ) *
      x ^ k * (1 - x) ^ (n - k)

def firstMomentSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    ((k : ℝ) / n) * (Nat.choose n k : ℝ) *
      x ^ k * (1 - x) ^ (n - k)

def reducedBinomialSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n,
    (Nat.choose (n - 1) k : ℝ) * x ^ k *
      (1 - x) ^ (n - 1 - k)

def secondMomentSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    ((k : ℝ) ^ 2 / (n : ℝ) ^ 2) * (Nat.choose n k : ℝ) *
      x ^ k * (1 - x) ^ (n - k)

def thirdMomentSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    ((k : ℝ) ^ 3 / (n : ℝ) ^ 3) * (Nat.choose n k : ℝ) *
      x ^ k * (1 - x) ^ (n - k)

def squareIntermediate (n : ℕ) (x : ℝ) : ℝ :=
  x - (((n : ℝ) - 1) / n) * x * (1 - x)

def squareClosedForm (n : ℕ) (x : ℝ) : ℝ :=
  x ^ 2 + x * (1 - x) / n

def cubeIntermediate (n : ℕ) (x : ℝ) : ℝ :=
  squareClosedForm n x -
    ((((n : ℝ) - 1) * ((n : ℝ) - 2) * x * (1 - x)) /
      (n : ℝ) ^ 2) * (x + 1 / ((n : ℝ) - 2))

def cubeClosedForm (n : ℕ) (x : ℝ) : ℝ :=
  (1 - 1 / (n : ℝ)) * (1 - 2 / (n : ℝ)) * x ^ 3 +
    (3 / (n : ℝ)) * (1 - 1 / (n : ℝ)) * x ^ 2 +
    1 / (n : ℝ) ^ 2 * x

/--
Source: `proof_gap/exercise_3127/1.txt`; specialize to the identity
function and require a positive Bernstein degree.
-/
private theorem cast_choose_step (n k : ℕ) :
    (((k + 1 : ℕ) : ℝ) * (Nat.choose (n + 1) (k + 1) : ℝ)) =
      (((n + 1 : ℕ) : ℝ) * (Nat.choose n k : ℝ)) := by
  norm_cast
  first
  | simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Nat.succ_mul_choose_eq n k)
  | simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Nat.succ_mul_choose_eq n k).symm

private theorem square_recurrence (n : ℕ) (hn : 2 ≤ n) (x : ℝ) :
    bernstein n (fun z => z ^ 2) x =
      x / (n : ℝ) *
        (((n - 1 : ℕ) : ℝ) * firstMomentSum (n - 1) x +
          reducedBinomialSum n x) := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  have hm0 : ((n - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show n - 1 ≠ 0 by omega)
  have hpred : n - 1 + 1 = n := by omega
  unfold bernstein
  rw [Finset.sum_range_succ']
  simp
  unfold firstMomentSum reducedBinomialSum
  rw [hpred]
  simp only [mul_add, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k < n := Finset.mem_range.mp hk
  have hsub : n - (k + 1) = n - 1 - k := by omega
  have hc := cast_choose_step (n - 1) k
  rw [hpred] at hc
  have hcoef :
      (((k + 1 : ℕ) : ℝ) / (n : ℝ)) *
          (Nat.choose n (k + 1) : ℝ) =
        (Nat.choose (n - 1) k : ℝ) := by
    calc
      (((k + 1 : ℕ) : ℝ) / (n : ℝ)) *
            (Nat.choose n (k + 1) : ℝ) =
          ((((k + 1 : ℕ) : ℝ) * (Nat.choose n (k + 1) : ℝ)) /
            (n : ℝ)) := by ring
      _ = (Nat.choose (n - 1) k : ℝ) := by
        apply (div_eq_iff hn0).2
        simpa [mul_comm, mul_left_comm, mul_assoc] using hc
  have hpow :
      ((((k + 1 : ℕ) : ℝ) / (n : ℝ)) ^ 2) *
          (Nat.choose n (k + 1) : ℝ) =
        (((k + 1 : ℕ) : ℝ) / (n : ℝ)) *
          (Nat.choose (n - 1) k : ℝ) := by
    calc
      ((((k + 1 : ℕ) : ℝ) / (n : ℝ)) ^ 2) *
            (Nat.choose n (k + 1) : ℝ) =
          (((k + 1 : ℕ) : ℝ) / (n : ℝ)) *
            ((((k + 1 : ℕ) : ℝ) / (n : ℝ)) *
              (Nat.choose n (k + 1) : ℝ)) := by ring
      _ = (((k + 1 : ℕ) : ℝ) / (n : ℝ)) *
          (Nat.choose (n - 1) k : ℝ) := by rw [hcoef]
  have hpow' :
      ((((k : ℝ) + 1) / (n : ℝ)) ^ 2) *
          (Nat.choose n (k + 1) : ℝ) =
        (((k : ℝ) + 1) / (n : ℝ)) *
          (Nat.choose (n - 1) k : ℝ) := by
    simpa using hpow
  rw [hpow', hsub, pow_succ]
  field_simp [hn0, hm0] <;> ring

private theorem cube_recurrence (n : ℕ) (hn : 2 ≤ n) (x : ℝ) :
    bernstein n (fun z => z ^ 3) x =
      x / (n : ℝ) ^ 2 *
        ((((n - 1 : ℕ) : ℝ) ^ 2 * secondMomentSum (n - 1) x +
          2 * ((n - 1 : ℕ) : ℝ) * firstMomentSum (n - 1) x) +
          reducedBinomialSum n x) := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  have hm0 : ((n - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show n - 1 ≠ 0 by omega)
  have hpred : n - 1 + 1 = n := by omega
  unfold bernstein
  rw [Finset.sum_range_succ']
  simp
  unfold secondMomentSum firstMomentSum reducedBinomialSum
  rw [hpred]
  simp only [mul_add, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k < n := Finset.mem_range.mp hk
  have hsub : n - (k + 1) = n - 1 - k := by omega
  have hc := cast_choose_step (n - 1) k
  rw [hpred] at hc
  have hcoef :
      (((k + 1 : ℕ) : ℝ) / (n : ℝ)) *
          (Nat.choose n (k + 1) : ℝ) =
        (Nat.choose (n - 1) k : ℝ) := by
    calc
      (((k + 1 : ℕ) : ℝ) / (n : ℝ)) *
            (Nat.choose n (k + 1) : ℝ) =
          ((((k + 1 : ℕ) : ℝ) * (Nat.choose n (k + 1) : ℝ)) /
            (n : ℝ)) := by ring
      _ = (Nat.choose (n - 1) k : ℝ) := by
        apply (div_eq_iff hn0).2
        simpa [mul_comm, mul_left_comm, mul_assoc] using hc
  have hpow :
      ((((k + 1 : ℕ) : ℝ) / (n : ℝ)) ^ 3) *
          (Nat.choose n (k + 1) : ℝ) =
        ((((k + 1 : ℕ) : ℝ) / (n : ℝ)) ^ 2) *
          (Nat.choose (n - 1) k : ℝ) := by
    calc
      ((((k + 1 : ℕ) : ℝ) / (n : ℝ)) ^ 3) *
            (Nat.choose n (k + 1) : ℝ) =
          ((((k + 1 : ℕ) : ℝ) / (n : ℝ)) ^ 2) *
            ((((k + 1 : ℕ) : ℝ) / (n : ℝ)) *
              (Nat.choose n (k + 1) : ℝ)) := by ring
      _ = ((((k + 1 : ℕ) : ℝ) / (n : ℝ)) ^ 2) *
          (Nat.choose (n - 1) k : ℝ) := by rw [hcoef]
  have hpow' :
      ((((k : ℝ) + 1) / (n : ℝ)) ^ 3) *
          (Nat.choose n (k + 1) : ℝ) =
        ((((k : ℝ) + 1) / (n : ℝ)) ^ 2) *
          (Nat.choose (n - 1) k : ℝ) := by
    simpa using hpow
  rw [hpow', hsub, pow_succ]
  field_simp [hn0, hm0] <;> ring

theorem gap1 :
    ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
      bernstein n (fun z => z) x = firstMomentSum n x := by
  intro n hn x
  rfl

/-- Source: `proof_gap/exercise_3127/2.txt`; reindex the positive first moment. -/
theorem gap2 :
    ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
      firstMomentSum n x = x * reducedBinomialSum n x := by
  intro n hn x
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  have hpred : n - 1 + 1 = n := by omega
  unfold firstMomentSum
  rw [Finset.sum_range_succ']
  simp
  unfold reducedBinomialSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k < n := Finset.mem_range.mp hk
  have hsub : n - (k + 1) = n - 1 - k := by omega
  have hc := cast_choose_step (n - 1) k
  rw [hpred] at hc
  have hcoef :
      (((k + 1 : ℕ) : ℝ) / (n : ℝ)) *
          (Nat.choose n (k + 1) : ℝ) =
        (Nat.choose (n - 1) k : ℝ) := by
    calc
      (((k + 1 : ℕ) : ℝ) / (n : ℝ)) *
            (Nat.choose n (k + 1) : ℝ) =
          ((((k + 1 : ℕ) : ℝ) * (Nat.choose n (k + 1) : ℝ)) /
            (n : ℝ)) := by ring
      _ = (Nat.choose (n - 1) k : ℝ) := by
        apply (div_eq_iff hn0).2
        simpa [mul_comm, mul_left_comm, mul_assoc] using hc
  rw [hsub, pow_succ]
  have hcoef' :
      (((k : ℝ) + 1) / (n : ℝ)) *
          (Nat.choose n (k + 1) : ℝ) =
        (Nat.choose (n - 1) k : ℝ) := by
    simpa using hcoef
  rw [hcoef']
  ring

/-- Source: `proof_gap/exercise_3127/3.txt`; apply the binomial theorem. -/
theorem gap3 :
    ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
      x * reducedBinomialSum n x =
        x * (x + (1 - x)) ^ (n - 1) := by
  intro n hn x
  apply congrArg (fun t : ℝ => x * t)
  unfold reducedBinomialSum
  have hpred : n - 1 + 1 = n := by omega
  simpa [hpred, mul_comm, mul_left_comm, mul_assoc] using
    (add_pow x (1 - x) (n - 1)).symm

/-- Source: `proof_gap/exercise_3127/4.txt`; simplify the binomial power. -/
theorem gap4 :
    ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
      x * (x + (1 - x)) ^ (n - 1) = x := by
  intro n hn x
  simp

/-- Source: `proof_gap/exercise_3127/5.txt`; Bernstein reproduces affine functions. -/
theorem gap5 :
    ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
      bernstein n (fun z => z) x = x := by
  intro n hn x
  calc
    bernstein n (fun z => z) x = firstMomentSum n x := gap1 n hn x
    _ = x * reducedBinomialSum n x := gap2 n hn x
    _ = x * (x + (1 - x)) ^ (n - 1) := gap3 n hn x
    _ = x := gap4 n hn x

/-- Source: `proof_gap/exercise_3127/6.txt`; specialize to the square function. -/
theorem gap6 :
    ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
      bernstein n (fun z => z ^ 2) x = secondMomentSum n x := by
  intro n hn x
  simpa only [bernstein, secondMomentSum, div_pow]

/-- Source: `proof_gap/exercise_3127/7.txt`; evaluate the second binomial moment. -/
theorem gap7 :
    ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
      bernstein n (fun z => z ^ 2) x = squareIntermediate n x := by
  intro n hn x
  by_cases hnone : n = 1
  · subst n
    norm_num [bernstein, squareIntermediate, Finset.sum_range_succ]
    <;> ring
  · have hn2 : 2 ≤ n := by omega
    have hm : 1 ≤ n - 1 := by omega
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (show n ≠ 0 by omega)
    have hfirst : firstMomentSum (n - 1) x = x := by
      calc
        firstMomentSum (n - 1) x =
            x * reducedBinomialSum (n - 1) x := gap2 (n - 1) hm x
        _ = x * (x + (1 - x)) ^ (n - 1 - 1) := gap3 (n - 1) hm x
        _ = x := gap4 (n - 1) hm x
    have hred : reducedBinomialSum n x = 1 := by
      unfold reducedBinomialSum
      have hpred : n - 1 + 1 = n := by omega
      calc
        (∑ k ∈ Finset.range n,
            (Nat.choose (n - 1) k : ℝ) * x ^ k *
              (1 - x) ^ (n - 1 - k)) =
            (x + (1 - x)) ^ (n - 1) := by
              simpa [hpred, mul_comm, mul_left_comm, mul_assoc] using
                (add_pow x (1 - x) (n - 1)).symm
        _ = 1 := by simp
    rw [square_recurrence n hn2 x, hfirst, hred]
    unfold squareIntermediate
    rw [Nat.cast_sub hn]
    field_simp [hn0]
    ring

/-- Source: `proof_gap/exercise_3127/8.txt`; algebraic form of the second moment. -/
theorem gap8 :
    ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
      squareIntermediate n x = squareClosedForm n x := by
  intro n hn x
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  unfold squareIntermediate squareClosedForm
  field_simp [hn0]
  ring

/-- Source: `proof_gap/exercise_3127/9.txt`. -/
theorem gap9 :
    ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
      bernstein n (fun z => z ^ 2) x = squareClosedForm n x := by
  intro n hn x
  calc
    bernstein n (fun z => z ^ 2) x = squareIntermediate n x := gap7 n hn x
    _ = squareClosedForm n x := gap8 n hn x

/-- Source: `proof_gap/exercise_3127/10.txt`; specialize to the cube function. -/
theorem gap10 :
    ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
      bernstein n (fun z => z ^ 3) x = thirdMomentSum n x := by
  intro n hn x
  simpa only [bernstein, thirdMomentSum, div_pow]

/--
Source: `proof_gap/exercise_3127/11.txt`; the source difference factor
`x/(n-2)+1` is false.  Replace it by the equivalent falling-factorial
factor `x+1/(n-2)` and require `n≥3`.
-/
theorem gap11 :
    ∀ n : ℕ, 3 ≤ n → ∀ x : ℝ,
      bernstein n (fun z => z ^ 3) x = cubeIntermediate n x := by
  intro n hn x
  have hn2 : 2 ≤ n := by omega
  have hm : 1 ≤ n - 1 := by omega
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  have hn20 : (n : ℝ) - 2 ≠ 0 := by
    exact_mod_cast (show n - 2 ≠ 0 by omega)
  have hnm10 : (n : ℝ) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast (show n ≠ 1 by omega)
  have hfirst : firstMomentSum (n - 1) x = x := by
    calc
      firstMomentSum (n - 1) x =
          x * reducedBinomialSum (n - 1) x := gap2 (n - 1) hm x
      _ = x * (x + (1 - x)) ^ (n - 1 - 1) := gap3 (n - 1) hm x
      _ = x := gap4 (n - 1) hm x
  have hsecond : secondMomentSum (n - 1) x = squareClosedForm (n - 1) x := by
    calc
      secondMomentSum (n - 1) x =
          bernstein (n - 1) (fun z => z ^ 2) x := (gap6 (n - 1) hm x).symm
      _ = squareClosedForm (n - 1) x := gap9 (n - 1) hm x
  have hred : reducedBinomialSum n x = 1 := by
    unfold reducedBinomialSum
    have hpred : n - 1 + 1 = n := by omega
    calc
      (∑ k ∈ Finset.range n,
          (Nat.choose (n - 1) k : ℝ) * x ^ k *
            (1 - x) ^ (n - 1 - k)) =
          (x + (1 - x)) ^ (n - 1) := by
            simpa [hpred, mul_comm, mul_left_comm, mul_assoc] using
              (add_pow x (1 - x) (n - 1)).symm
      _ = 1 := by simp
  rw [cube_recurrence n hn2 x, hsecond, hfirst, hred]
  unfold cubeIntermediate
  unfold squareClosedForm
  rw [Nat.cast_sub (show 1 ≤ n by omega)]
  field_simp [hn0, hn20, hnm10]
  ring

/-- Source: `proof_gap/exercise_3127/12.txt`; closed third-moment formula. -/
theorem gap12 :
    ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
      bernstein n (fun z => z ^ 3) x = cubeClosedForm n x := by
  intro n hn x
  by_cases hnone : n = 1
  · subst n
    norm_num [bernstein, cubeClosedForm, Finset.sum_range_succ]
    <;> ring
  · have hn2 : 2 ≤ n := by omega
    have hm : 1 ≤ n - 1 := by omega
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (show n ≠ 0 by omega)
    have hnm10 : (n : ℝ) - 1 ≠ 0 := by
      exact_mod_cast (show n - 1 ≠ 0 by omega)
    have hfirst : firstMomentSum (n - 1) x = x := by
      calc
        firstMomentSum (n - 1) x =
            x * reducedBinomialSum (n - 1) x := gap2 (n - 1) hm x
        _ = x * (x + (1 - x)) ^ (n - 1 - 1) := gap3 (n - 1) hm x
        _ = x := gap4 (n - 1) hm x
    have hsecond : secondMomentSum (n - 1) x = squareClosedForm (n - 1) x := by
      calc
        secondMomentSum (n - 1) x =
            bernstein (n - 1) (fun z => z ^ 2) x := (gap6 (n - 1) hm x).symm
        _ = squareClosedForm (n - 1) x := gap9 (n - 1) hm x
    have hred : reducedBinomialSum n x = 1 := by
      unfold reducedBinomialSum
      have hpred : n - 1 + 1 = n := by omega
      calc
        (∑ k ∈ Finset.range n,
            (Nat.choose (n - 1) k : ℝ) * x ^ k *
              (1 - x) ^ (n - 1 - k)) =
            (x + (1 - x)) ^ (n - 1) := by
              simpa [hpred, mul_comm, mul_left_comm, mul_assoc] using
                (add_pow x (1 - x) (n - 1)).symm
        _ = 1 := by simp
    rw [cube_recurrence n hn2 x, hsecond, hfirst, hred]
    unfold squareClosedForm cubeClosedForm
    rw [Nat.cast_sub (show 1 ≤ n by omega)]
    field_simp [hn0, hnm10]
    ring

end

end ProofGap.Exercise3127
