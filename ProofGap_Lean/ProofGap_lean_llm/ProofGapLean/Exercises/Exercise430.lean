import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Finite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise430

noncomputable section

def average (n : ℕ) (x a : ℝ) : ℝ :=
  (1 / (n : ℝ)) *
    (Finset.Icc 1 (n - 1)).sum (fun i => (x + (i : ℝ) * a / n) ^ 2)
def expanded (n : ℕ) (x a : ℝ) : ℝ :=
  (1 / (n : ℝ)) *
    (((n - 1 : ℕ) : ℝ) * x ^ 2 +
      2 * a * x / n * (Finset.Icc 1 (n - 1)).sum (fun i => (i : ℝ)) +
      a ^ 2 / (n : ℝ) ^ 2 *
        (Finset.Icc 1 (n - 1)).sum (fun i => ((i : ℝ) ^ 2)))

/-- Exercise 430, gap 1; replace summation ellipses by finite sums. -/
private theorem sum_Icc_eq_sum_range_of_zero
    (f : ℕ → ℝ) (hf : f 0 = 0) (n : ℕ) :
    (Finset.Icc 1 (n - 1)).sum f = (Finset.range n).sum f := by
  cases n with
  | zero => simp
  | succ n =>
      have hs :
          Finset.Icc 1 (Nat.succ n - 1) =
            (Finset.range (Nat.succ n)).erase 0 := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]
        omega
      rw [hs]
      have hmem : 0 ∈ Finset.range (Nat.succ n) := by simp
      calc
        ((Finset.range (Nat.succ n)).erase 0).sum f =
            ((Finset.range (Nat.succ n)).erase 0).sum f + f 0 := by
              rw [hf, add_zero]
        _ = (Finset.range (Nat.succ n)).sum f :=
          Finset.sum_erase_add (s := Finset.range (Nat.succ n))
            (f := f) hmem

private theorem sum_range_cast_id (n : ℕ) :
    (Finset.range n).sum (fun i => (i : ℝ)) =
      (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, Nat.cast_succ]
      ring

private theorem sum_range_cast_sq (n : ℕ) :
    (Finset.range n).sum (fun i => ((i : ℝ) ^ 2)) =
      (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, Nat.cast_succ]
      ring

private theorem sum_Icc_cast_id (n : ℕ) :
    (Finset.Icc 1 (n - 1)).sum (fun i => (i : ℝ)) =
      (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  rw [sum_Icc_eq_sum_range_of_zero (fun i => (i : ℝ)) (by simp) n]
  exact sum_range_cast_id n

private theorem sum_Icc_cast_sq (n : ℕ) :
    (Finset.Icc 1 (n - 1)).sum (fun i => ((i : ℝ) ^ 2)) =
      (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6 := by
  rw [sum_Icc_eq_sum_range_of_zero (fun i => ((i : ℝ) ^ 2)) (by simp) n]
  exact sum_range_cast_sq n

private theorem average_eq_expanded (n : ℕ) (hn : 1 ≤ n) (x a : ℝ) :
    average n x a = expanded n x a := by
  unfold average expanded
  have hs :
      Finset.Icc 1 (n - 1) = (Finset.range n).erase 0 := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]
    omega
  have hzero : 0 ∈ Finset.range n := by
    exact Finset.mem_range.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hcard : (Finset.Icc 1 (n - 1)).card = n - 1 := by
    rw [hs, Finset.card_erase_of_mem hzero, Finset.card_range]
  congr 1
  calc
    (Finset.Icc 1 (n - 1)).sum
        (fun i => (x + (i : ℝ) * a / n) ^ 2) =
      (Finset.Icc 1 (n - 1)).sum
        (fun i =>
          x ^ 2 + (2 * a * x / n) * (i : ℝ) +
            (a ^ 2 / (n : ℝ) ^ 2) * ((i : ℝ) ^ 2)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
    _ =
      ((n - 1 : ℕ) : ℝ) * x ^ 2 +
        2 * a * x / n *
          (Finset.Icc 1 (n - 1)).sum (fun i => (i : ℝ)) +
        a ^ 2 / (n : ℝ) ^ 2 *
          (Finset.Icc 1 (n - 1)).sum (fun i => ((i : ℝ) ^ 2)) := by
        simp [Finset.sum_add_distrib, Finset.mul_sum, hcard]

private theorem expanded_eq_polynomial
    (n : ℕ) (hn : n ≠ 0) (x a : ℝ) :
    expanded n x a =
      (1 - (n : ℝ)⁻¹) * x ^ 2 +
        a * x * (1 - (n : ℝ)⁻¹) +
        a ^ 2 / 6 * (1 - (n : ℝ)⁻¹) * (2 - (n : ℝ)⁻¹) := by
  unfold expanded
  rw [sum_Icc_cast_id, sum_Icc_cast_sq]
  have hpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  rw [Nat.cast_sub hpos]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp [hnR]
  ring_nf

theorem gap1 (x a : ℝ) :
    Filter.Tendsto (fun n => average n x a) Filter.atTop
        (nhds (x ^ 2 + a * x + a ^ 2 / 3)) ↔
      Filter.Tendsto (fun n => expanded n x a) Filter.atTop
        (nhds (x ^ 2 + a * x + a ^ 2 / 3)) := by
  have heq :
      (fun n : ℕ => average n x a) =ᶠ[Filter.atTop]
        (fun n : ℕ => expanded n x a) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    exact average_eq_expanded n hn x a
  exact Filter.tendsto_congr' heq

/-- Exercise 430, gap 2. -/
theorem gap2 (x a : ℝ) :
    Filter.Tendsto (fun n => expanded n x a) Filter.atTop
      (nhds (x ^ 2 + a * x + a ^ 2 / 3)) := by
  have hinvR :
      Filter.Tendsto (fun t : ℝ => t⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hinv :
      Filter.Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) Filter.atTop (nhds 0) :=
    hinvR.comp tendsto_natCast_atTop_atTop
  have hone :
      Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  have htwo :
      Filter.Tendsto (fun _ : ℕ => (2 : ℝ)) Filter.atTop (nhds 2) :=
    tendsto_const_nhds
  have hx2 :
      Filter.Tendsto (fun _ : ℕ => x ^ 2) Filter.atTop (nhds (x ^ 2)) :=
    tendsto_const_nhds
  have hax :
      Filter.Tendsto (fun _ : ℕ => a * x) Filter.atTop (nhds (a * x)) :=
    tendsto_const_nhds
  have ha2 :
      Filter.Tendsto (fun _ : ℕ => a ^ 2 / 6) Filter.atTop
        (nhds (a ^ 2 / 6)) :=
    tendsto_const_nhds
  have hmone := hone.sub hinv
  have hmtwo := htwo.sub hinv
  have hlim :=
    ((hmone.mul hx2).add (hax.mul hmone)).add
      ((ha2.mul hmone).mul hmtwo)
  have hpoly :
      Filter.Tendsto
        (fun n : ℕ =>
          (1 - (n : ℝ)⁻¹) * x ^ 2 +
            a * x * (1 - (n : ℝ)⁻¹) +
            a ^ 2 / 6 * (1 - (n : ℝ)⁻¹) * (2 - (n : ℝ)⁻¹))
        Filter.atTop (nhds (x ^ 2 + a * x + a ^ 2 / 3)) := by
    convert hlim using 1 <;> ring
  have heq :
      (fun n : ℕ => expanded n x a) =ᶠ[Filter.atTop]
        (fun n : ℕ =>
          (1 - (n : ℝ)⁻¹) * x ^ 2 +
            a * x * (1 - (n : ℝ)⁻¹) +
            a ^ 2 / 6 * (1 - (n : ℝ)⁻¹) * (2 - (n : ℝ)⁻¹)) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : n ≠ 0 :=
      Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn)
    exact expanded_eq_polynomial n hn0 x a
  exact (Filter.tendsto_congr' heq).mpr hpoly

end

end ProofGap.Exercise430
