import ProofGapLean.Prelude.Full
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Nat.Choose.Cast

open scoped Topology

/-!
# Exercise 60

Semantic formalization of `proof_gap/exercise_60/{1,...,24}.txt`.
The exponent `k` is real, so real powers are represented by `Real.rpow`.
-/

namespace ProofGap.Exercise60

noncomputable section

def binomialExpansion (lam : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℝ) * lam ^ j

def seq (a k : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (n : ℝ) k / a ^ n

def negativeRewrite (a k : ℝ) (n : ℕ) : ℝ :=
  1 / (a ^ n * Real.rpow (n : ℝ) (-k))

def linearUpper (a : ℝ) (n : ℕ) : ℝ :=
  (4 * (n : ℝ)) / ((n : ℝ) ^ 2 * (a - 1) ^ 2)

def rootBase (a k : ℝ) : ℝ :=
  Real.rpow a (1 / k)

def rootSequence (a k : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) / (rootBase a k) ^ n

def SameLimit (u v : ℕ → ℝ) : Prop :=
  ∀ l : ℝ, Tendsto u atTop (𝓝 l) ↔ Tendsto v atTop (𝓝 l)

private theorem seq_eq_negativeRewrite (a k : ℝ) (n : ℕ) :
    seq a k n = negativeRewrite a k n := by
  unfold seq negativeRewrite
  rw [show Real.rpow (n : ℝ) (-k) =
    (Real.rpow (n : ℝ) k)⁻¹ from
      Real.rpow_neg (Nat.cast_nonneg n) k]
  simp [one_div, div_eq_mul_inv, mul_inv_rev]

/-- Source: `proof_gap/exercise_60/1.txt`. -/
theorem gap1
    (a lam : ℝ)
    (ha : 1 < a)
    (hal : a = 1 + lam) :
    0 < lam := by
  linarith

/-- Source: `proof_gap/exercise_60/2.txt`. -/
theorem gap2
    (a lam : ℝ)
    (hal : a = 1 + lam) :
    ∀ n : ℕ, a ^ n = (1 + lam) ^ n := by
  intro n
  rw [hal]

/-- Source: `proof_gap/exercise_60/3.txt`. -/
theorem gap3
    (lam : ℝ) :
    ∀ n : ℕ, (1 + lam) ^ n = binomialExpansion lam n := by
  intro n
  unfold binomialExpansion
  rw [add_comm]
  simpa [mul_comm] using (add_pow lam 1 n)

/-- Source: `proof_gap/exercise_60/4.txt`. -/
theorem gap4
    (lam : ℝ)
    (hlam : 0 < lam)
    (h3 : ∀ n : ℕ, (1 + lam) ^ n = binomialExpansion lam n) :
    ∀ n : ℕ,
      binomialExpansion lam n >
        ((n : ℝ) * ((n : ℝ) - 1) / 2) * lam ^ 2 := by
  intro n
  by_cases hn : n < 2
  · interval_cases n <;>
      simp [binomialExpansion, Finset.sum_range_succ] <;> positivity
  · have hzero : 0 ∈ Finset.range (n + 1) := by simp
    have htwo : 2 ∈ (Finset.range (n + 1)).erase 0 := by
      simp
      omega
    let f : ℕ → ℝ := fun j => (Nat.choose n j : ℝ) * lam ^ j
    have hle : f 2 ≤ ∑ j ∈ (Finset.range (n + 1)).erase 0, f j :=
      Finset.single_le_sum
        (f := f) (fun j hj => by
          unfold f
          positivity) htwo
    have hsum :=
      Finset.sum_erase_add (Finset.range (n + 1)) f hzero
    have hfzero : f 0 = 1 := by simp [f]
    rw [hfzero] at hsum
    have hftwo :
        f 2 = ((n : ℝ) * ((n : ℝ) - 1) / 2) * lam ^ 2 := by
      unfold f
      rw [Nat.cast_choose_two ℝ n]
    unfold binomialExpansion
    change (∑ j ∈ Finset.range (n + 1), f j) > _
    rw [← hftwo]
    linarith

/-- Source: `proof_gap/exercise_60/5.txt`. -/
theorem gap5
    (a lam : ℝ)
    (h2 : ∀ n : ℕ, a ^ n = (1 + lam) ^ n)
    (h3 : ∀ n : ℕ, (1 + lam) ^ n = binomialExpansion lam n)
    (h4 : ∀ n : ℕ,
      binomialExpansion lam n >
        ((n : ℝ) * ((n : ℝ) - 1) / 2) * lam ^ 2) :
    ∀ n : ℕ,
      a ^ n > ((n : ℝ) * ((n : ℝ) - 1) / 2) * lam ^ 2 := by
  intro n
  rw [h2 n, h3 n]
  exact h4 n

/-- Source: `proof_gap/exercise_60/6.txt`. -/
theorem gap6 :
    ∀ n : ℕ, 2 < n → (n : ℝ) - 1 > (n : ℝ) / 2 := by
  intro n hn
  have hncast : (2 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  linarith

/-- Source: `proof_gap/exercise_60/7.txt`. -/
theorem gap7
    (a lam : ℝ)
    (h5 : ∀ n : ℕ,
      a ^ n > ((n : ℝ) * ((n : ℝ) - 1) / 2) * lam ^ 2)
    (h6 : ∀ n : ℕ, 2 < n → (n : ℝ) - 1 > (n : ℝ) / 2) :
    ∀ n : ℕ, 2 < n →
      a ^ n > ((n : ℝ) ^ 2 / 4) * lam ^ 2 := by
  intro n hn
  have hnpos : 0 < (n : ℝ) := by positivity
  have hlin := h6 n hn
  have hcoef :
      (n : ℝ) ^ 2 / 4 ≤ (n : ℝ) * ((n : ℝ) - 1) / 2 := by
    nlinarith
  have hbound :
      ((n : ℝ) ^ 2 / 4) * lam ^ 2 ≤
        ((n : ℝ) * ((n : ℝ) - 1) / 2) * lam ^ 2 := by
    exact mul_le_mul_of_nonneg_right hcoef (sq_nonneg lam)
  exact hbound.trans_lt (h5 n)

/-- Source: `proof_gap/exercise_60/8.txt`. -/
theorem gap8
    (a lam : ℝ)
    (hal : a = 1 + lam) :
    ∀ n : ℕ, 2 < n →
      ((n : ℝ) ^ 2 / 4) * lam ^ 2 =
        ((n : ℝ) ^ 2 * (a - 1) ^ 2) / 4 := by
  intro n hn
  rw [hal]
  ring

/-- Source: `proof_gap/exercise_60/9.txt`. -/
theorem gap9
    (a lam : ℝ)
    (h7 : ∀ n : ℕ, 2 < n →
      a ^ n > ((n : ℝ) ^ 2 / 4) * lam ^ 2)
    (h8 : ∀ n : ℕ, 2 < n →
      ((n : ℝ) ^ 2 / 4) * lam ^ 2 =
        ((n : ℝ) ^ 2 * (a - 1) ^ 2) / 4) :
    ∀ n : ℕ, 2 < n →
      a ^ n > ((n : ℝ) ^ 2 * (a - 1) ^ 2) / 4 := by
  intro n hn
  rw [← h8 n hn]
  exact h7 n hn

/-- Source: `proof_gap/exercise_60/10.txt`. -/
theorem gap10
    (a : ℝ) :
    ∀ k : ℝ, k ≤ 0 →
      SameLimit (seq a k) (negativeRewrite a k) := by
  intro k hk l
  exact Filter.tendsto_congr (seq_eq_negativeRewrite a k)

/-- Source: `proof_gap/exercise_60/11.txt`. -/
theorem gap11
    (a : ℝ)
    (ha : 1 < a) :
    ∀ k : ℝ, k ≤ 0 →
      Tendsto (negativeRewrite a k) atTop (𝓝 0) := by
  intro k hk
  have hainvpos : 0 < a⁻¹ := inv_pos.mpr (lt_trans zero_lt_one ha)
  have hainvlt : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ ha
  have hgeom :
      Tendsto (fun n : ℕ => (a⁻¹) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one
      (by simpa [abs_of_pos hainvpos] using hainvlt)
  apply squeeze_zero' (f := negativeRewrite a k)
    (g := fun n : ℕ => (a⁻¹) ^ n)
  · exact Filter.Eventually.of_forall fun n => by
      rw [← seq_eq_negativeRewrite]
      unfold seq
      exact div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) k)
        (pow_nonneg (le_trans zero_le_one ha.le) n)
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    rw [← seq_eq_negativeRewrite]
    unfold seq
    have hbase : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hrpow : Real.rpow (n : ℝ) k ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hbase hk
    have hden : 0 < a ^ n := pow_pos (lt_trans zero_lt_one ha) n
    calc
      Real.rpow (n : ℝ) k / a ^ n ≤ 1 / a ^ n :=
        (div_le_div_iff_of_pos_right hden).2 hrpow
      _ = (a⁻¹) ^ n := by simp [one_div, inv_pow]
  · exact hgeom

/-- Source: `proof_gap/exercise_60/12.txt`. -/
theorem gap12
    (a : ℝ)
    (h10 : ∀ k : ℝ, k ≤ 0 →
      SameLimit (seq a k) (negativeRewrite a k))
    (h11 : ∀ k : ℝ, k ≤ 0 →
      Tendsto (negativeRewrite a k) atTop (𝓝 0)) :
    ∀ k : ℝ, k ≤ 0 → Tendsto (seq a k) atTop (𝓝 0) := by
  intro k hk
  exact (h10 k hk 0).mpr (h11 k hk)

/-- Source: `proof_gap/exercise_60/13.txt`; positive `n` is restored. -/
theorem gap13
    (a : ℝ)
    (ha : 1 < a) :
    ∀ (k : ℝ) (n : ℕ), k = 1 → 0 < n → 0 < seq a k n := by
  intro k n hk hn
  subst k
  unfold seq
  exact div_pos
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) 1)
    (pow_pos (lt_trans zero_lt_one ha) n)

/-- Source: `proof_gap/exercise_60/14.txt`. -/
theorem gap14
    (a : ℝ) :
    ∀ (k : ℝ) (n : ℕ), k = 1 →
      seq a k n = (n : ℝ) / a ^ n := by
  intro k n hk
  subst k
  simp [seq, Real.rpow_one]

/-- Source: `proof_gap/exercise_60/15.txt`; the source condition `n>2` is restored. -/
theorem gap15
    (a : ℝ)
    (ha : 1 < a)
    (h9 : ∀ n : ℕ, 2 < n →
      a ^ n > ((n : ℝ) ^ 2 * (a - 1) ^ 2) / 4) :
    ∀ (k : ℝ) (n : ℕ), k = 1 → 2 < n →
      (n : ℝ) / a ^ n < linearUpper a n := by
  intro k n hk hn
  unfold linearUpper
  have hnpos : 0 < (n : ℝ) := by positivity
  have hapos : 0 < a := lt_trans zero_lt_one ha
  have hsubpos : 0 < a - 1 := sub_pos.mpr ha
  have hsmall :
      0 < ((n : ℝ) ^ 2 * (a - 1) ^ 2) / 4 := by positivity
  have hpowpos : 0 < a ^ n := pow_pos hapos n
  calc
    (n : ℝ) / a ^ n <
        (n : ℝ) / (((n : ℝ) ^ 2 * (a - 1) ^ 2) / 4) :=
      (div_lt_div_iff_of_pos_left hnpos hpowpos hsmall).2 (h9 n hn)
    _ = (4 * (n : ℝ)) / ((n : ℝ) ^ 2 * (a - 1) ^ 2) := by
      field_simp

/-- Source: `proof_gap/exercise_60/16.txt`; positive `n` is restored. -/
theorem gap16
    (a : ℝ)
    (ha : 1 < a) :
    ∀ (k : ℝ) (n : ℕ), k = 1 → 0 < n →
      0 < linearUpper a n := by
  intro k n hk hn
  unfold linearUpper
  have hna : 0 < (n : ℝ) := by positivity
  have haa : 0 < a - 1 := sub_pos.mpr ha
  positivity

/-- Source: `proof_gap/exercise_60/17.txt`. -/
theorem gap17
    (a : ℝ)
    (ha : 1 < a) :
    ∀ k : ℝ, k = 1 →
      Tendsto (linearUpper a) atTop (𝓝 0) := by
  intro k hk
  have hane : a - 1 ≠ 0 := (sub_pos.mpr ha).ne'
  have hlim :
      Tendsto (fun n : ℕ => (4 / (a - 1) ^ 2 : ℝ) / (n : ℝ))
        atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (4 / (a - 1) ^ 2 : ℝ)
  apply Filter.Tendsto.congr' _ hlim
  filter_upwards [Filter.eventually_ne_atTop 0] with n hn
  unfold linearUpper
  have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp [hnreal, hane]

/-- Source: `proof_gap/exercise_60/18.txt`. -/
theorem gap18
    (a : ℝ)
    (ha : 1 < a)
    (h13 : ∀ (k : ℝ) (n : ℕ), k = 1 → 0 < n → 0 < seq a k n)
    (h14 : ∀ (k : ℝ) (n : ℕ), k = 1 →
      seq a k n = (n : ℝ) / a ^ n)
    (h15 : ∀ (k : ℝ) (n : ℕ), k = 1 → 2 < n →
      (n : ℝ) / a ^ n < linearUpper a n)
    (h17 : ∀ k : ℝ, k = 1 →
      Tendsto (linearUpper a) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n : ℝ) / a ^ n) atTop (𝓝 0) := by
  have hainvpos : 0 ≤ a⁻¹ := (inv_pos.mpr (lt_trans zero_lt_one ha)).le
  have hainvlt : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ ha
  have hlim :=
    tendsto_self_mul_const_pow_of_lt_one hainvpos hainvlt
  apply Filter.Tendsto.congr' _ hlim
  exact Filter.Eventually.of_forall fun n => by
    change (n : ℝ) * (a⁻¹) ^ n = (n : ℝ) * (a ^ n)⁻¹
    rw [inv_pow]

/-- Source: `proof_gap/exercise_60/19.txt`. -/
theorem gap19
    (a : ℝ)
    (ha : 1 < a) :
    ∀ (k : ℝ) (n : ℕ), 0 < k →
      seq a k n = Real.rpow (rootSequence a k n) k := by
  intro k n hk
  unfold seq rootSequence rootBase
  change
    (n : ℝ) ^ k / a ^ n =
      ((n : ℝ) / (a ^ (1 / k)) ^ n) ^ k
  rw [Real.div_rpow (Nat.cast_nonneg n)
    (pow_nonneg (Real.rpow_nonneg (le_trans zero_le_one ha.le) (1 / k)) n) k]
  congr 1
  rw [Real.rpow_pow_comm (le_trans zero_le_one ha.le)]
  simpa [one_div] using
    (Real.rpow_inv_rpow
      (pow_nonneg (le_trans zero_le_one ha.le) n) hk.ne').symm

/-- Source: `proof_gap/exercise_60/20.txt`. -/
theorem gap20
    (a : ℝ)
    (ha : 1 < a) :
    ∀ k : ℝ, 0 < k → 1 < rootBase a k := by
  intro k hk
  unfold rootBase
  exact Real.one_lt_rpow ha (one_div_pos.mpr hk)

/-- Source: `proof_gap/exercise_60/21.txt`. -/
theorem gap21
    (a : ℝ)
    (h18 : Tendsto (fun n : ℕ => (n : ℝ) / a ^ n) atTop (𝓝 0))
    (h20 : ∀ k : ℝ, 0 < k → 1 < rootBase a k) :
    ∀ k : ℝ, 0 < k →
      Tendsto (rootSequence a k) atTop (𝓝 0) := by
  intro k hk
  have hb : 1 < rootBase a k := h20 k hk
  have hbinvpos : 0 ≤ (rootBase a k)⁻¹ :=
    (inv_pos.mpr (lt_trans zero_lt_one hb)).le
  have hbinvlt : (rootBase a k)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ hb
  have hlim :=
    tendsto_self_mul_const_pow_of_lt_one hbinvpos hbinvlt
  apply Filter.Tendsto.congr' _ hlim
  exact Filter.Eventually.of_forall fun n => by
    unfold rootSequence
    change
      (n : ℝ) * (rootBase a k)⁻¹ ^ n =
        (n : ℝ) * ((rootBase a k) ^ n)⁻¹
    rw [inv_pow]

/-- Source: `proof_gap/exercise_60/22.txt`. -/
theorem gap22
    (a : ℝ)
    (h19 : ∀ (k : ℝ) (n : ℕ), 0 < k →
      seq a k n = Real.rpow (rootSequence a k n) k)
    (h21 : ∀ k : ℝ, 0 < k →
      Tendsto (rootSequence a k) atTop (𝓝 0)) :
    ∀ k : ℝ, 0 < k → Tendsto (seq a k) atTop (𝓝 0) := by
  intro k hk
  have hrpow :
      Tendsto (fun n : ℕ => Real.rpow (rootSequence a k n) k)
        atTop (𝓝 0) := by
    have ht := (h21 k hk).rpow_const (Or.inr hk.le)
    rw [Real.zero_rpow hk.ne'] at ht
    exact ht
  apply Filter.Tendsto.congr' _ hrpow
  exact Filter.Eventually.of_forall fun n => (h19 k n hk).symm

/-- Source: `proof_gap/exercise_60/23.txt`. -/
theorem gap23
    (a : ℝ)
    (ha : 1 < a)
    (h12 : ∀ k : ℝ, k ≤ 0 → Tendsto (seq a k) atTop (𝓝 0))
    (h22 : ∀ k : ℝ, 0 < k → Tendsto (seq a k) atTop (𝓝 0)) :
    ∀ k : ℝ, 1 < a → Tendsto (seq a k) atTop (𝓝 0) := by
  intro k ha'
  by_cases hk : k ≤ 0
  · exact h12 k hk
  · exact h22 k (lt_of_not_ge hk)

/-- Source: `proof_gap/exercise_60/24.txt`. -/
theorem gap24
    (a : ℝ)
    (ha : 1 < a)
    (h23 : ∀ k : ℝ, 1 < a → Tendsto (seq a k) atTop (𝓝 0)) :
    ∀ k : ℝ, Tendsto (seq a k) atTop (𝓝 0) := by
  intro k
  exact h23 k ha

end

end ProofGap.Exercise60
