import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Finite
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

namespace ProofGap.Exercise424

open scoped BigOperators

noncomputable section

def sumPowers (n : ℕ) (x : ℝ) : ℝ :=
  (Finset.Icc 1 n).sum (fun i => x ^ i)
def weightedSum (n : ℕ) (x : ℝ) : ℝ :=
  (Finset.range n).sum (fun j => ((n - j : ℕ) : ℝ) * x ^ j)
def quotient (n : ℕ) (x : ℝ) : ℝ :=
  (sumPowers n x - n) / (x - 1)
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_424/1.txt`; replace ellipses by a finite sum. -/
private theorem sumPowers_eq_range_sum (n : ℕ) (x : ℝ) :
    sumPowers n x =
      (Finset.range n).sum (fun j => x ^ (j + 1)) := by
  unfold sumPowers
  have hset :
      Finset.Icc 1 n =
        (Finset.range n).image (fun j => j + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨hk1, hkn⟩
      have hk0 : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk1
      refine ⟨k - 1, ?_, Nat.sub_add_cancel hk1⟩
      exact (Nat.sub_lt hk0 Nat.zero_lt_one).trans_le hkn
    · rintro ⟨j, hjn, rfl⟩
      constructor
      · simpa [Nat.succ_eq_add_one] using
          Nat.succ_le_succ (Nat.zero_le j)
      · simpa [Nat.succ_eq_add_one] using hjn
  rw [hset, Finset.sum_image]
  intro a ha b hb hab
  exact Nat.add_right_cancel hab

private theorem weightedSum_succ (n : ℕ) (x : ℝ) :
    weightedSum (n + 1) x =
      weightedSum n x +
        (Finset.range (n + 1)).sum (fun j => x ^ j) := by
  have hsum :
      (∑ j ∈ Finset.range n,
          (((n + 1 - j : ℕ) : ℝ) * x ^ j)) =
        (∑ j ∈ Finset.range n,
          (((n - j : ℕ) : ℝ) * x ^ j)) +
        ∑ j ∈ Finset.range n, x ^ j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    have hnat : n + 1 - j = (n - j) + 1 := by
      omega
    rw [hnat, Nat.cast_add, Nat.cast_one]
    ring
  simp only [weightedSum, Finset.sum_range_succ]
  rw [hsum]
  have hsub : n + 1 - n = 1 := by
    omega
  simp only [hsub, Nat.cast_one, one_mul]
  ring

private theorem geom_sum_factor (n : ℕ) (x : ℝ) :
    (x - 1) * (Finset.range n).sum (fun j => x ^ j) =
      x ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      calc
        (x - 1) *
            ((Finset.range n).sum (fun j => x ^ j) + x ^ n) =
          (x - 1) * (Finset.range n).sum (fun j => x ^ j) +
            (x - 1) * x ^ n := by ring
        _ = (x ^ n - 1) + (x - 1) * x ^ n := by rw [ih]
        _ = x ^ (n + 1) - 1 := by
              rw [pow_succ]
              ring

private theorem weightedSum_one (n : ℕ) :
    weightedSum n 1 = (n : ℝ) * (n + 1) / 2 := by
  induction n with
  | zero => simp [weightedSum]
  | succ n ih =>
      rw [weightedSum_succ n 1, ih]
      simp only [one_pow, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one, Nat.cast_succ]
      ring

theorem gap1 (n : ℕ) : ∀ x,
    sumPowers n x - n = (Finset.Icc 1 n).sum (fun i => x ^ i - 1) := by
  intro x
  have hc : (Finset.Icc 1 n).card = n := by
    simp
  simp [sumPowers, Finset.sum_sub_distrib, hc]

/-- Source: `proof_gap/exercise_424/2.txt`; replace the nested geometric ellipses by `weightedSum`. -/
theorem gap2 (n : ℕ) : ∀ x,
    sumPowers n x - n = (x - 1) * weightedSum n x := by
  intro x
  induction n with
  | zero =>
      simp [sumPowers, weightedSum]
  | succ n ih =>
      rw [sumPowers_eq_range_sum, Finset.sum_range_succ, weightedSum_succ]
      rw [sumPowers_eq_range_sum] at ih
      calc
        (∑ j ∈ Finset.range n, x ^ (j + 1)) + x ^ (n + 1) -
              (↑(n + 1) : ℝ) =
            ((∑ j ∈ Finset.range n, x ^ (j + 1)) - (n : ℝ)) +
              (x ^ (n + 1) - 1) := by
                rw [Nat.cast_add, Nat.cast_one]
                ring
        _ = (x - 1) * weightedSum n x + (x ^ (n + 1) - 1) := by
              rw [ih]
        _ = (x - 1) *
              (weightedSum n x +
                ∑ j ∈ Finset.range (n + 1), x ^ j) := by
              rw [← geom_sum_factor (n + 1) x]
              ring

/-- Source: `proof_gap/exercise_424/3.txt`. -/
theorem gap3 (n : ℕ) : ∀ x,
    sumPowers n x - n = (x - 1) * weightedSum n x := by
  exact gap2 n

/-- Source: `proof_gap/exercise_424/4.txt`. -/
theorem gap4 (n : ℕ) :
    HasLimitAt (quotient n) 1 (n * (n + 1) / 2) ↔
      HasLimitAt (weightedSum n) 1 (n * (n + 1) / 2) := by
  have heq :
      quotient n =ᶠ[nhdsWithin 1 ({1} : Set ℝ)ᶜ] weightedSum n := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx1 : x ≠ 1 := by
      simpa using hx
    rw [quotient, gap3 n x]
    apply (div_eq_iff (sub_ne_zero.mpr hx1)).2
    ring
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

/-- Source: `proof_gap/exercise_424/5.txt`. -/
theorem gap5 (n : ℕ) :
    HasLimitAt (weightedSum n) 1 (n * (n + 1) / 2) := by
  unfold HasLimitAt
  have hc : ContinuousAt (weightedSum n) 1 := by
    unfold weightedSum
    fun_prop
  have ht := hc.tendsto
  rw [weightedSum_one] at ht
  exact ht.mono_left inf_le_left

/-- Source: `proof_gap/exercise_424/6.txt`. -/
theorem gap6 (n : ℕ) :
    (Finset.Icc 1 n).sum (fun k => k) = n * (n + 1) / 2 := by
  have hsubset : Finset.Icc 1 n ⊆ Finset.range (n + 1) := by
    intro k hk
    simp at hk ⊢
    omega
  calc
    (Finset.Icc 1 n).sum (fun k => k) =
        (Finset.range (n + 1)).sum (fun k => k) := by
          apply Finset.sum_subset hsubset
          intro k hk hki
          simp at hk hki ⊢
          omega
    _ = n * (n + 1) / 2 := by
          simpa [Finset.sum_range_id, Nat.mul_comm]

/-- Source: `proof_gap/exercise_424/7.txt`. -/
theorem gap7 (n : ℕ) :
    HasLimitAt (quotient n) 1 (n * (n + 1) / 2) := by
  exact (gap4 n).2 (gap5 n)

end

end ProofGap.Exercise424
