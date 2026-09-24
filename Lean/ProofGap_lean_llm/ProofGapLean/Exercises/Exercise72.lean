import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Discrete
import ProofGapLean.Exercises.Exercise69
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

open Filter Topology

/-!
# Exercise 72

Semantic formalization of `proof_gap/exercise_72/{1,...,26}.txt`.
-/

namespace ProofGap.Exercise72

noncomputable section

def x (n : ℕ) : ℝ :=
  (1 + 1 / (n : ℝ)) ^ n

def productExpansion (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    (1 / (Nat.factorial j : ℝ)) *
      ∏ i ∈ Finset.Ico 1 j, (1 - (i : ℝ) / (n : ℝ))

def truncatedProductExpansion (n k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    (1 / (Nat.factorial j : ℝ)) *
      ∏ i ∈ Finset.Ico 1 j, (1 - (i : ℝ) / (n : ℝ))

def omega (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), 1 / (Nat.factorial j : ℝ)

def tail (n m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range m, 1 / (Nat.factorial (n + j + 1) : ℝ)

def geometricFactor (n m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range m, (1 / ((n : ℝ) + 2)) ^ j

def remainderBound (n : ℕ) : ℝ :=
  1 / (Nat.factorial (n + 1) : ℝ) * ((n : ℝ) + 2) / ((n : ℝ) + 1)

def sharperBound (n : ℕ) : ℝ :=
  1 / (Nat.factorial n : ℝ) * ((n : ℝ) + 2) / ((n : ℝ) + 1) ^ 2

private theorem omega_monotone : Monotone omega := by
  apply monotone_nat_of_le_succ
  intro n
  unfold omega
  calc
    (∑ j ∈ Finset.range (n + 1), 1 / (Nat.factorial j : ℝ)) ≤
        (∑ j ∈ Finset.range (n + 1), 1 / (Nat.factorial j : ℝ)) +
          1 / (Nat.factorial (n + 1) : ℝ) := by
            exact le_add_of_nonneg_right (by positivity)
    _ = ∑ j ∈ Finset.range (n + 1 + 1),
        1 / (Nat.factorial j : ℝ) := (Finset.sum_range_succ _ _).symm

private theorem omega_tendsto_exp :
    Tendsto omega atTop (𝓝 (Real.exp 1)) := by
  have hs := (NormedSpace.expSeries_div_hasSum_exp (1 : ℝ)).tendsto_sum_nat
  have hs' := hs.comp (tendsto_add_atTop_nat 1)
  change Tendsto
    (fun n : ℕ => ∑ j ∈ Finset.range (n + 1),
      1 / (Nat.factorial j : ℝ)) atTop (𝓝 (Real.exp 1))
  simpa only [Function.comp_apply, one_pow, one_div, Real.exp_eq_exp_ℝ] using hs'

/-- Source: `proof_gap/exercise_72/1.txt`; the ellipsis is a finite sum/product. -/
theorem gap1 :
    ∀ n : ℕ, 0 < n → x n = productExpansion n := by
  intro n hn
  simpa [x, productExpansion, ProofGap.Exercise69.x,
    ProofGap.Exercise69.factorialExpansion] using
    ProofGap.Exercise69.gap4 n hn

private theorem product_term_pos {n j : ℕ} (hj : j ≤ n) :
    0 < (1 / (Nat.factorial j : ℝ)) *
      ∏ i ∈ Finset.Ico 1 j, (1 - (i : ℝ) / (n : ℝ)) := by
  have hfactor :
      ∀ i ∈ Finset.Ico 1 j, 0 < 1 - (i : ℝ) / (n : ℝ) := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
    have hin : i < n := (Finset.mem_Ico.mp hi).2.trans_le hj
    have hnR : (0 : ℝ) < n := by
      exact_mod_cast (show 0 < n by omega)
    rw [sub_pos, div_lt_one hnR]
    exact_mod_cast hin
  exact mul_pos (by positivity) (Finset.prod_pos hfactor)

/-- Source: `proof_gap/exercise_72/2.txt`; the truncated expansion is explicit. -/
theorem gap2 :
    ∀ n k : ℕ, 0 < k → k < n →
      x n > truncatedProductExpansion n k := by
  intro n k hk hkn
  rw [gap1 n (by omega)]
  let f : ℕ → ℝ := fun j =>
    (1 / (Nat.factorial j : ℝ)) *
      ∏ i ∈ Finset.Ico 1 j, (1 - (i : ℝ) / (n : ℝ))
  have hsplit := Finset.sum_range_add_sum_Ico f
    (show k + 1 ≤ n + 1 by omega)
  have htail :
      0 < ∑ j ∈ Finset.Ico (k + 1) (n + 1), f j := by
    apply Finset.sum_pos
    · intro j hj
      exact product_term_pos (by
        have := (Finset.mem_Ico.mp hj).2
        omega)
    · exact ⟨k + 1, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩⟩
  unfold productExpansion truncatedProductExpansion
  change (∑ j ∈ Finset.range (n + 1), f j) >
    ∑ j ∈ Finset.range (k + 1), f j
  linarith

/-- Source: `proof_gap/exercise_72/3.txt`. -/
theorem gap3
    (e : ℝ)
    (hx : Tendsto x atTop (𝓝 e)) :
    ∀ k : ℕ, 0 < k → e ≥ omega k := by
  intro k _
  have hxexp : Tendsto x atTop (𝓝 (Real.exp 1)) := by
    change Tendsto (fun n : ℕ => (1 + 1 / (n : ℝ)) ^ n)
      atTop (𝓝 (Real.exp 1))
    simpa only [one_div] using Real.tendsto_one_add_div_pow_exp (1 : ℝ)
  have he : e = Real.exp 1 := tendsto_nhds_unique hx hxexp
  rw [he]
  apply le_of_tendsto_of_tendsto tendsto_const_nhds omega_tendsto_exp
  exact (Filter.eventually_ge_atTop k).mono fun n hn => omega_monotone hn

/-- Source: `proof_gap/exercise_72/4.txt`; the putative limit is named explicitly. -/
theorem gap4
    (e L : ℝ)
    (hL : Tendsto omega atTop (𝓝 L))
    (hbound : ∀ k : ℕ, 0 < k → omega k ≤ e) :
    L ≤ e := by
  apply le_of_tendsto hL
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with k hk
  exact hbound k (by omega)

/-- Source: `proof_gap/exercise_72/5.txt`. -/
theorem gap5 :
    ∀ n : ℕ, 1 < n → x n < omega n := by
  intro n hn
  rw [gap1 n (by omega)]
  unfold productExpansion omega
  apply Finset.sum_lt_sum
  · intro j hj
    have hjn : j ≤ n := by simpa using hj
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hprod :
        ∏ i ∈ Finset.Ico 1 j, (1 - (i : ℝ) / (n : ℝ)) ≤ 1 := by
      apply Finset.prod_le_one
      · intro i hi
        have hin : i < n :=
          (Finset.mem_Ico.mp hi).2.trans_le hjn
        have hiR : (i : ℝ) < (n : ℝ) := by exact_mod_cast hin
        have hdiv : (i : ℝ) / (n : ℝ) < 1 :=
          (div_lt_one hnR).2 hiR
        linarith
      · intro i hi
        have hi0 : 0 ≤ (i : ℝ) / (n : ℝ) := by positivity
        linarith
    calc
      (1 / (Nat.factorial j : ℝ)) *
          ∏ i ∈ Finset.Ico 1 j, (1 - (i : ℝ) / (n : ℝ)) ≤
          (1 / (Nat.factorial j : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = 1 / (Nat.factorial j : ℝ) := mul_one _
  · refine ⟨2, ?_, ?_⟩
    · simp
      omega
    · rw [Finset.prod_Ico_succ_top (show 1 ≤ 1 by omega)]
      simp only [Finset.Ico_self, Finset.prod_empty, one_mul]
      norm_num [Nat.factorial]
      have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hone : 0 < 1 / (n : ℝ) := one_div_pos.mpr hnR
      linarith

/-- Source: `proof_gap/exercise_72/6.txt`; both limits are named. -/
theorem gap6
    (e L : ℝ)
    (hx : Tendsto x atTop (𝓝 e))
    (hω : Tendsto omega atTop (𝓝 L))
    (hbound : ∀ n : ℕ, 0 < n → x n ≤ omega n) :
    e ≤ L := by
  apply le_of_tendsto_of_tendsto hx hω
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  exact hbound n (by omega)

/-- Source: `proof_gap/exercise_72/7.txt`. -/
theorem gap7
    (e : ℝ)
    (hupper : ∀ k : ℕ, 0 < k → omega k ≤ e)
    (hlower : ∀ n : ℕ, 0 < n → x n ≤ omega n)
    (hx : Tendsto x atTop (𝓝 e)) :
    Tendsto omega atTop (𝓝 e) := by
  have hexp_le : Real.exp 1 ≤ e :=
    gap4 e (Real.exp 1) omega_tendsto_exp hupper
  have he_le : e ≤ Real.exp 1 :=
    gap6 e (Real.exp 1) hx omega_tendsto_exp hlower
  have he : e = Real.exp 1 := le_antisymm he_le hexp_le
  simpa [he] using omega_tendsto_exp

/-- Source: `proof_gap/exercise_72/8.txt`; `m = 0` is excluded from strict positivity. -/
theorem gap8 :
    ∀ n m : ℕ, 0 < m → 0 < omega (n + m) - omega n := by
  intro n m hm
  let f : ℕ → ℝ := fun j => 1 / (Nat.factorial j : ℝ)
  have hsplit := Finset.sum_range_add_sum_Ico f
    (show n + 1 ≤ n + m + 1 by omega)
  have heq :
      omega (n + m) - omega n =
        ∑ j ∈ Finset.Ico (n + 1) (n + m + 1), f j := by
    unfold omega
    change (∑ j ∈ Finset.range (n + m + 1), f j) -
        (∑ j ∈ Finset.range (n + 1), f j) =
      ∑ j ∈ Finset.Ico (n + 1) (n + m + 1), f j
    linarith
  rw [heq]
  apply Finset.sum_pos
  · intro j _
    positivity
  · exact ⟨n + 1, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩⟩

/-- Source: `proof_gap/exercise_72/9.txt`; the omitted tail is an explicit finite sum. -/
theorem gap9 :
    ∀ n m : ℕ, omega (n + m) - omega n = tail n m := by
  intro n m
  let f : ℕ → ℝ := fun j => 1 / (Nat.factorial j : ℝ)
  have hsplit := Finset.sum_range_add_sum_Ico f
    (show n + 1 ≤ n + m + 1 by omega)
  unfold omega tail
  change (∑ j ∈ Finset.range (n + m + 1), f j) -
      (∑ j ∈ Finset.range (n + 1), f j) =
    ∑ j ∈ Finset.range m, f (n + j + 1)
  calc
    (∑ j ∈ Finset.range (n + m + 1), f j) -
        (∑ j ∈ Finset.range (n + 1), f j) =
        ∑ j ∈ Finset.Ico (n + 1) (n + m + 1), f j := by
          linarith
    _ = ∑ j ∈ Finset.range m, f (n + j + 1) := by
      rw [Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr
      · congr 1
        omega
      · intro j _
        congr 1
        omega

/-- Source: `proof_gap/exercise_72/10.txt`; strictness requires at least two terms. -/
theorem gap10 :
    ∀ n m : ℕ, 2 < m →
      tail n m <
        1 / (Nat.factorial (n + 1) : ℝ) * geometricFactor n m := by
  intro n m hm
  unfold tail geometricFactor
  rw [Finset.mul_sum]
  apply Finset.sum_lt_sum
  · intro j _
    have hfactNat :
        Nat.factorial (n + 1) * (n + 2) ^ j ≤
          Nat.factorial (n + j + 1) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Nat.factorial_mul_pow_le_factorial (m := n + 1) (n := j))
    have hfact :
        (Nat.factorial (n + 1) : ℝ) * ((n : ℝ) + 2) ^ j ≤
          (Nat.factorial (n + j + 1) : ℝ) := by
      exact_mod_cast hfactNat
    calc
      1 / (Nat.factorial (n + j + 1) : ℝ) ≤
          1 / ((Nat.factorial (n + 1) : ℝ) * ((n : ℝ) + 2) ^ j) :=
        one_div_le_one_div_of_le (by positivity) hfact
      _ = 1 / (Nat.factorial (n + 1) : ℝ) *
          (1 / ((n : ℝ) + 2)) ^ j := by
        field_simp
        rw [← mul_pow]
        have hb : ((n : ℝ) + 2) * (1 / ((n : ℝ) + 2)) = 1 := by
          field_simp
        rw [hb, one_pow]
  · refine ⟨2, by simp; omega, ?_⟩
    have hfactNat :
        Nat.factorial (n + 1) * (n + 2) ^ 2 <
          Nat.factorial (n + 2 + 1) := by
      have hbase : n + 2 < n + 3 := by omega
      have hcoeff :
          0 < Nat.factorial (n + 1) * (n + 2) := by positivity
      calc
        Nat.factorial (n + 1) * (n + 2) ^ 2 =
            (Nat.factorial (n + 1) * (n + 2)) * (n + 2) := by ring
        _ < (Nat.factorial (n + 1) * (n + 2)) * (n + 3) :=
          Nat.mul_lt_mul_of_pos_left hbase hcoeff
        _ = Nat.factorial (n + 2 + 1) := by
          simp only [Nat.factorial_succ]
          ring
    have hfact :
        (Nat.factorial (n + 1) : ℝ) * ((n : ℝ) + 2) ^ 2 <
          (Nat.factorial (n + 2 + 1) : ℝ) := by
      exact_mod_cast hfactNat
    calc
      1 / (Nat.factorial (n + 2 + 1) : ℝ) <
          1 / ((Nat.factorial (n + 1) : ℝ) * ((n : ℝ) + 2) ^ 2) :=
        one_div_lt_one_div_of_lt (by positivity) hfact
      _ = 1 / (Nat.factorial (n + 1) : ℝ) *
          (1 / ((n : ℝ) + 2)) ^ 2 := by
        field_simp

private theorem tail_le_geometric (n m : ℕ) :
    tail n m ≤
      1 / (Nat.factorial (n + 1) : ℝ) * geometricFactor n m := by
  unfold tail geometricFactor
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hfactNat :
      Nat.factorial (n + 1) * (n + 2) ^ j ≤
        Nat.factorial (n + j + 1) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Nat.factorial_mul_pow_le_factorial (m := n + 1) (n := j))
  have hfact :
      (Nat.factorial (n + 1) : ℝ) * ((n : ℝ) + 2) ^ j ≤
        (Nat.factorial (n + j + 1) : ℝ) := by
    exact_mod_cast hfactNat
  calc
    1 / (Nat.factorial (n + j + 1) : ℝ) ≤
        1 / ((Nat.factorial (n + 1) : ℝ) * ((n : ℝ) + 2) ^ j) :=
      one_div_le_one_div_of_le (by positivity) hfact
    _ = 1 / (Nat.factorial (n + 1) : ℝ) *
        (1 / ((n : ℝ) + 2)) ^ j := by
      field_simp
      rw [← mul_pow]
      have hb : ((n : ℝ) + 2) * (1 / ((n : ℝ) + 2)) = 1 := by
        field_simp
      rw [hb, one_pow]

/-- Source: `proof_gap/exercise_72/11.txt`; the finite geometric sum is explicit. -/
theorem gap11 :
    ∀ n m : ℕ, 0 < m →
      1 / (Nat.factorial (n + 1) : ℝ) * geometricFactor n m <
        remainderBound n := by
  intro n m hm
  let r : ℝ := 1 / ((n : ℝ) + 2)
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hr1 : r ≠ 1 := by
    dsimp [r]
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have : (1 : ℝ) < (n : ℝ) + 2 := by linarith
    exact ne_of_lt ((div_lt_one (by positivity)).2 this)
  have hden : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr1)
  have hinv :
      1 / (1 - r) = ((n : ℝ) + 2) / ((n : ℝ) + 1) := by
    apply (div_eq_iff hden).2
    dsimp [r]
    field_simp
    ring
  have hform :
      geometricFactor n m =
        (((n : ℝ) + 2) / ((n : ℝ) + 1)) * (1 - r ^ m) := by
    unfold geometricFactor
    change (∑ j ∈ Finset.range m, r ^ j) = _
    rw [geom_sum_eq hr1]
    calc
      (r ^ m - 1) / (r - 1) = (1 - r ^ m) / (1 - r) := by
        field_simp [hden, sub_ne_zero.mpr hr1]
        ring
      _ = (1 / (1 - r)) * (1 - r ^ m) := by ring
      _ = (((n : ℝ) + 2) / ((n : ℝ) + 1)) * (1 - r ^ m) := by
        rw [hinv]
  rw [hform]
  unfold remainderBound
  have hcoeff : 0 < 1 / (Nat.factorial (n + 1) : ℝ) := by positivity
  have hratio : 0 < ((n : ℝ) + 2) / ((n : ℝ) + 1) := by positivity
  have hrpow : 0 < r ^ m := pow_pos hr _
  have hremform :
      (1 / (Nat.factorial (n + 1) : ℝ)) * ((n : ℝ) + 2) /
          ((n : ℝ) + 1) =
        (1 / (Nat.factorial (n + 1) : ℝ)) *
          (((n : ℝ) + 2) / ((n : ℝ) + 1)) := by ring
  rw [hremform]
  nlinarith [mul_pos (mul_pos hcoeff hratio) hrpow]

/-- Source: `proof_gap/exercise_72/12.txt`. -/
theorem gap12 :
    ∀ n : ℕ, 0 < remainderBound n := by
  intro n
  unfold remainderBound
  positivity

/-- Source: `proof_gap/exercise_72/13.txt`. -/
theorem gap13
    (e : ℝ)
    (hω : Tendsto omega atTop (𝓝 e))
    (hmono : Monotone omega) :
    ∀ n : ℕ, 0 ≤ e - omega n := by
  intro n
  have hle : omega n ≤ e := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hω
    exact (Filter.eventually_ge_atTop n).mono fun m hnm => hmono hnm
  linarith

/-- Source: `proof_gap/exercise_72/14.txt`. -/
theorem gap14
    (e : ℝ)
    (hω : Tendsto omega atTop (𝓝 e)) :
    ∀ n : ℕ, e - omega n ≤ remainderBound n := by
  intro n
  have hshift :
      Tendsto (fun m : ℕ => omega (n + m) - omega n)
        atTop (𝓝 (e - omega n)) := by
    have h := (hω.comp (tendsto_add_atTop_nat n)).sub
      (tendsto_const_nhds (x := omega n))
    simpa [Nat.add_comm] using h
  apply le_of_tendsto_of_tendsto hshift tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with m hm
  rw [gap9]
  exact (tail_le_geometric n m).trans
    (gap11 n m (by omega)).le

/-- Source: `proof_gap/exercise_72/15.txt`. -/
theorem gap15 :
    ∀ n : ℕ, remainderBound n = sharperBound n := by
  intro n
  unfold remainderBound sharperBound
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- Source: `proof_gap/exercise_72/16.txt`. -/
theorem gap16 :
    ∀ n : ℕ, 0 ≤ sharperBound n := by
  intro n
  unfold sharperBound
  positivity

/-- Source: `proof_gap/exercise_72/17.txt`; the right side is undefined at zero informally. -/
theorem gap17 :
    ∀ n : ℕ, 0 < n →
      ((n : ℝ) + 2) / ((n : ℝ) + 1) ^ 2 < 1 / (n : ℝ) := by
  intro n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_lt_div_iff₀ (sq_pos_of_pos (by linarith : (0 : ℝ) < n + 1)) hnR]
  nlinarith

/-- Source: `proof_gap/exercise_72/18.txt`. -/
theorem gap18
    (e : ℝ)
    (hω : Tendsto omega atTop (𝓝 e)) :
    ∀ n : ℕ, 0 < e - omega n := by
  intro n
  have hstrict : omega n < omega (n + 1) := by
    have := gap8 n 1 (by omega)
    simpa using this
  have hle : omega (n + 1) ≤ e := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hω
    exact (Filter.eventually_ge_atTop (n + 1)).mono fun m hnm =>
      omega_monotone hnm
  linarith

/-- Source: `proof_gap/exercise_72/19.txt`; the bound is restricted to positive n. -/
theorem gap19
    (e : ℝ)
    (hω : Tendsto omega atTop (𝓝 e)) :
    ∀ n : ℕ, 0 < n →
      e - omega n < 1 / (Nat.factorial n : ℝ) * (1 / (n : ℝ)) := by
  intro n hn
  have hrem := gap14 e hω n
  rw [gap15 n] at hrem
  unfold sharperBound at hrem
  rw [mul_div_assoc] at hrem
  have hratio := gap17 n hn
  have hcoeff : 0 < 1 / (Nat.factorial n : ℝ) := by positivity
  exact hrem.trans_lt (mul_lt_mul_of_pos_left hratio hcoeff)

/-- Source: `proof_gap/exercise_72/20.txt`; the strict positivity fails at zero. -/
theorem gap20 :
    ∀ n : ℕ, 0 < n →
      0 < 1 / (Nat.factorial n : ℝ) * (1 / (n : ℝ)) := by
  intro n hn
  positivity

/-- Source: `proof_gap/exercise_72/21.txt`; one function θ works on positive indices. -/
theorem gap21
    (e : ℝ)
    (hω : Tendsto omega atTop (𝓝 e)) :
    ∃ θ : ℕ → ℝ, ∀ n : ℕ, 0 < n →
      e = omega n + θ n / ((Nat.factorial n : ℝ) * (n : ℝ)) := by
  refine ⟨fun n => (e - omega n) *
    ((Nat.factorial n : ℝ) * (n : ℝ)), ?_⟩
  intro n hn
  have hden : (Nat.factorial n : ℝ) * (n : ℝ) ≠ 0 := by
    positivity
  field_simp
  ring

/-- Source: `proof_gap/exercise_72/22.txt`; θ is tied to the remainder identity. -/
theorem gap22
    (e : ℝ) (θ : ℕ → ℝ)
    (hid : ∀ n : ℕ, 0 < n →
      e = omega n + θ n / ((Nat.factorial n : ℝ) * (n : ℝ)))
    (hpos : ∀ n : ℕ, 0 < n → 0 < e - omega n) :
    ∀ n : ℕ, 0 < n → 0 < θ n := by
  intro n hn
  have hden : 0 < (Nat.factorial n : ℝ) * (n : ℝ) := by
    positivity
  have hidn := hid n hn
  have hrem := hpos n hn
  rw [hidn] at hrem
  have : 0 < θ n / ((Nat.factorial n : ℝ) * (n : ℝ)) := by
    linarith
  rcases div_pos_iff.mp this with h | h
  · exact h.1
  · linarith

/-- Source: `proof_gap/exercise_72/23.txt`; the same θ is used. -/
theorem gap23
    (e : ℝ) (θ : ℕ → ℝ)
    (hid : ∀ n : ℕ, 0 < n →
      e = omega n + θ n / ((Nat.factorial n : ℝ) * (n : ℝ)))
    (hupper : ∀ n : ℕ, 0 < n →
      e - omega n < 1 / (Nat.factorial n : ℝ) * (1 / (n : ℝ))) :
    ∀ n : ℕ, 0 < n → θ n < 1 := by
  intro n hn
  have hden : 0 < (Nat.factorial n : ℝ) * (n : ℝ) := by
    positivity
  have hidn := hid n hn
  have hu := hupper n hn
  rw [hidn] at hu
  have hrewrite :
      1 / (Nat.factorial n : ℝ) * (1 / (n : ℝ)) =
        1 / ((Nat.factorial n : ℝ) * (n : ℝ)) := by
    field_simp
  rw [hrewrite] at hu
  have hu' :
      θ n / ((Nat.factorial n : ℝ) * (n : ℝ)) <
        1 / ((Nat.factorial n : ℝ) * (n : ℝ)) := by
    linarith
  exact (div_lt_div_iff_of_pos_right hden).mp hu'

/-- Source: `proof_gap/exercise_72/24.txt`. -/
theorem gap24 :
    1 / ((Nat.factorial 8 : ℝ) * 8) < 0.0000032 := by
  norm_num [Nat.factorial]

/-- Source: `proof_gap/exercise_72/25.txt`; `±` is an absolute-error bound. -/
theorem gap25
    (e : ℝ)
    (hθ : ∃ θ : ℕ → ℝ,
      (∀ n : ℕ, 0 < n →
        e = omega n + θ n / ((Nat.factorial n : ℝ) * (n : ℝ))) ∧
      (∀ n : ℕ, 0 < n → 0 < θ n ∧ θ n < 1)) :
    |e - 2.71828| ≤ 0.00001 := by
  rcases hθ with ⟨θ, hid, hbounds⟩
  have heq := hid 8 (by norm_num)
  have ht := hbounds 8 (by norm_num)
  norm_num [omega, Nat.factorial, Finset.sum_range_succ] at heq
  rw [abs_le]
  constructor <;> norm_num <;> nlinarith

/-- Source: `proof_gap/exercise_72/26.txt`. -/
theorem gap26
    (e : ℝ)
    (hω : Tendsto omega atTop (𝓝 e)) :
    Tendsto omega atTop (𝓝 e) := by
  exact hω

end

end ProofGap.Exercise72
