import ProofGapLean.Prelude.Discrete
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Factorial.BigOperators

namespace ProofGap.Exercise2651

noncomputable section

open scoped BigOperators

def factorialSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, (Nat.factorial k : ℝ)

def u (n : ℕ) : ℝ :=
  factorialSum n / (Nat.factorial (2 * n) : ℝ)

def tailProduct (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.Icc (n + 1) (2 * n), (k : ℝ)

def intermediateBound (n : ℕ) : ℝ :=
  (n : ℝ) * Nat.factorial n /
    ((Nat.factorial n : ℝ) * tailProduct n)

def reducedBound (n : ℕ) : ℝ :=
  n / tailProduct n

def comparison (n : ℕ) : ℝ :=
  1 / (((2 * n - 1 : ℕ) : ℝ) * (2 * n : ℝ))

private theorem factorial_eq_mul_tailProduct (n : ℕ) :
    (Nat.factorial (2 * n) : ℝ) =
      (Nat.factorial n : ℝ) * tailProduct n := by
  unfold tailProduct
  have hnat : Nat.factorial (2 * n) =
      Nat.factorial n * ∏ k ∈ Finset.Icc (n + 1) (2 * n), k := by
    calc
      Nat.factorial (2 * n) = Nat.factorial (n + n) := by congr 1 <;> omega
      _ = Nat.factorial n * (n + 1).ascFactorial n :=
        (Nat.factorial_mul_ascFactorial n n).symm
      _ = Nat.factorial n * ∏ k ∈ Finset.Icc (n + 1) (2 * n), k := by
        congr 1
        rw [Nat.ascFactorial_eq_prod_range]
        rw [← Finset.Ico_succ_right_eq_Icc]
        rw [Finset.prod_Ico_eq_prod_range]
        rw [show Order.succ (2 * n) = 2 * n + 1 by rfl]
        rw [show 2 * n + 1 - (n + 1) = n by omega]
  simpa only [Nat.cast_mul, Nat.cast_prod] using
    congrArg (fun m : ℕ => (m : ℝ)) hnat

private theorem tailProduct_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < tailProduct n := by
  unfold tailProduct
  apply Finset.prod_pos
  intro k hk
  have hk' := (Finset.mem_Icc.mp hk).1
  exact_mod_cast (show 0 < k by omega)

theorem gap1 :
    ∀ n : ℕ, 1 ≤ n → 0 < u n := by
  intro n hn
  unfold u
  apply div_pos
  · unfold factorialSum
    apply Finset.sum_pos'
    · intro k hk
      positivity
    · refine ⟨n, ?_, ?_⟩
      · exact Finset.mem_Icc.mpr ⟨hn, le_rfl⟩
      · positivity
  · positivity

theorem gap2 :
    ∀ n : ℕ, 1 ≤ n → u n ≤ intermediateBound n := by
  intro n hn
  have hsum : factorialSum n ≤ (n : ℝ) * (Nat.factorial n : ℝ) := by
    unfold factorialSum
    calc
      (∑ k ∈ Finset.Icc 1 n, (Nat.factorial k : ℝ)) ≤
          ∑ _k ∈ Finset.Icc 1 n, (Nat.factorial n : ℝ) := by
        gcongr with k hk
        exact (Finset.mem_Icc.mp hk).2
      _ = (n : ℝ) * (Nat.factorial n : ℝ) := by
        simp
  rw [u, intermediateBound, factorial_eq_mul_tailProduct]
  exact div_le_div_of_nonneg_right hsum
    (mul_nonneg (by positivity) (tailProduct_pos n hn).le)

theorem gap3 :
    ∀ n : ℕ, 1 ≤ n → intermediateBound n = reducedBound n := by
  intro n hn
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have htail : tailProduct n ≠ 0 := (tailProduct_pos n hn).ne'
  unfold intermediateBound reducedBound
  field_simp

theorem gap4 :
    ∀ n : ℕ, 3 ≤ n → reducedBound n < comparison n := by
  intro n hn
  let pfx : ℝ := ∏ k ∈ Finset.Icc (n + 1) (2 * n - 2), (k : ℝ)
  have hpfx : (n : ℝ) < pfx := by
    have hmem : n + 1 ∈ Finset.Icc (n + 1) (2 * n - 2) := by
      simp only [Finset.mem_Icc, le_rfl, true_and]
      omega
    have hle : ((n + 1 : ℕ) : ℝ) ≤ pfx := by
      dsimp [pfx]
      calc
        ((n + 1 : ℕ) : ℝ) = ∏ k ∈ {n + 1}, (k : ℝ) := by simp
        _ ≤ ∏ k ∈ Finset.Icc (n + 1) (2 * n - 2), (k : ℝ) := by
          apply Finset.prod_le_prod_of_subset_of_one_le
          · simpa using hmem
          · intro k hk
            positivity
          · intro k hk hnot
            have hk' := (Finset.mem_Icc.mp hk).1
            norm_cast
            omega
    have hlt : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_succ_self n
    exact hlt.trans_le hle
  have htail : tailProduct n =
      pfx * ((2 * n - 1 : ℕ) : ℝ) * (2 * n : ℝ) := by
    unfold tailProduct
    rw [← show (2 * n - 1) + 1 = 2 * n by omega]
    rw [Finset.prod_Icc_succ_top (by omega)]
    rw [← show (2 * n - 2) + 1 = 2 * n - 1 by omega]
    rw [Finset.prod_Icc_succ_top (by omega)]
    dsimp [pfx]
    rw [show 2 * n - 2 + 1 = 2 * n - 1 by omega]
    rw [show 2 * n - 1 + 1 = 2 * n by omega]
    norm_num [Nat.cast_mul]
  have hleft : 0 < ((2 * n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < 2 * n - 1 by omega)
  have hright : 0 < (2 * n : ℝ) := by positivity
  have hpfxpos : 0 < pfx := lt_trans (by positivity) hpfx
  unfold reducedBound comparison
  rw [htail]
  rw [div_lt_div_iff₀ (mul_pos (mul_pos hpfxpos hleft) hright)
    (mul_pos hleft hright)]
  nlinarith [mul_lt_mul_of_pos_right hpfx (mul_pos hleft hright)]

theorem gap5 :
    ∀ n : ℕ, 1 ≤ n → 0 < comparison n := by
  intro n hn
  unfold comparison
  apply one_div_pos.mpr
  apply mul_pos
  · exact_mod_cast (show 0 < 2 * n - 1 by omega)
  · positivity

theorem gap6 :
    Summable (fun n : ℕ => comparison (n + 1)) := by
  have hp : Summable (fun n : ℕ =>
      1 / ((((n + 1 : ℕ) : ℝ)) ^ 2)) := by
    exact (summable_nat_add_iff 1).2
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  apply Summable.of_nonneg_of_le
  · intro n
    unfold comparison
    positivity
  · intro n
    unfold comparison
    refine one_div_le_one_div_of_le
      (a := ((((n + 1 : ℕ) : ℝ)) ^ 2)) ?_ ?_
    · apply sq_pos_of_pos
      exact_mod_cast Nat.succ_pos n
    rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
    norm_num [Nat.cast_add, Nat.cast_mul, pow_two]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    nlinarith
  · exact hp

theorem gap7
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 ≤ u n)
    (hbound : ∀ n : ℕ, 3 ≤ n → u n ≤ comparison n)
    (hcomparison : Summable (fun n : ℕ => comparison (n + 1))) :
    Summable (fun n : ℕ => u (n + 1)) := by
  apply (summable_nat_add_iff 2).1
  apply Summable.of_nonneg_of_le
  · intro n
    exact hpos (n + 3) (by omega)
  · intro n
    exact hbound (n + 3) (by omega)
  · exact (summable_nat_add_iff 2).2 hcomparison

theorem gap8
    (hsum : Summable (fun n : ℕ => u (n + 1))) :
    Summable (fun n : ℕ => u (n + 1)) := by
  exact hsum

end

end ProofGap.Exercise2651
