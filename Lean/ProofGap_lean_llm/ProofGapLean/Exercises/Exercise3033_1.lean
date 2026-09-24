import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise3033_1

noncomputable section

open Filter
open scoped BigOperators Topology

def term (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (n + 1) / ((1 - x ^ n) * (1 - x ^ (n + 1)))

def partialSum (x : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, term x k

private lemma pow_ne_one_of_abs_lt_one
    (x : ℝ) (hx : |x| < 1) (n : ℕ) (hn : 1 ≤ n) : x ^ n ≠ 1 := by
  have hp : |x ^ n| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg x) hx (Nat.ne_of_gt hn)
  intro h
  rw [h, abs_one] at hp
  exact (lt_irrefl (1 : ℝ)) hp

theorem gap1 (x : ℝ) (hx : |x| < 1) (n : ℕ) (hn : 1 ≤ n) :
    1 / (1 - x ^ n) - 1 / (1 - x ^ (n + 1)) =
      x ^ n * (1 - x) / ((1 - x ^ n) * (1 - x ^ (n + 1))) := by
  have h1 : 1 - x ^ n ≠ 0 :=
    sub_ne_zero.mpr (pow_ne_one_of_abs_lt_one x hx n hn).symm
  have h2 : 1 - x ^ (n + 1) ≠ 0 :=
    sub_ne_zero.mpr
      (pow_ne_one_of_abs_lt_one x hx (n + 1) (by omega)).symm
  field_simp [h1, h2]
  rw [pow_succ]
  ring

theorem gap2 (x : ℝ) (hx : |x| < 1) (n : ℕ) (hn : 1 ≤ n) :
    x ^ n * (1 - x) / ((1 - x ^ n) * (1 - x ^ (n + 1))) =
      (1 - x) / x * term x n := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [term, zero_pow (Nat.ne_of_gt hn)]
  · have h1 : 1 - x ^ n ≠ 0 :=
      sub_ne_zero.mpr (pow_ne_one_of_abs_lt_one x hx n hn).symm
    have h2 : 1 - x ^ (n + 1) ≠ 0 :=
      sub_ne_zero.mpr
        (pow_ne_one_of_abs_lt_one x hx (n + 1) (by omega)).symm
    unfold term
    field_simp [hx0, h1, h2] <;> rw [pow_succ] <;> ring

theorem gap3 (x : ℝ) (hx : |x| < 1) (n : ℕ) (hn : 1 ≤ n) :
    1 / (1 - x ^ n) - 1 / (1 - x ^ (n + 1)) =
      (1 - x) / x * term x n := by
  calc
    1 / (1 - x ^ n) - 1 / (1 - x ^ (n + 1)) =
        x ^ n * (1 - x) /
          ((1 - x ^ n) * (1 - x ^ (n + 1))) := gap1 x hx n hn
    _ = (1 - x) / x * term x n := gap2 x hx n hn

theorem gap4 (x : ℝ) (hx : |x| < 1) (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, (1 - x) / x * term x k) =
      (∑ k ∈ Finset.Icc 1 N, 1 / (1 - x ^ k)) -
      ∑ k ∈ Finset.Icc 1 N, 1 / (1 - x ^ (k + 1)) := by
  calc
    (∑ k ∈ Finset.Icc 1 N, (1 - x) / x * term x k) =
        ∑ k ∈ Finset.Icc 1 N,
          (1 / (1 - x ^ k) - 1 / (1 - x ^ (k + 1))) := by
            apply Finset.sum_congr rfl
            intro k hk
            exact (gap3 x hx k (Finset.mem_Icc.mp hk).1).symm
    _ = (∑ k ∈ Finset.Icc 1 N, 1 / (1 - x ^ k)) -
        ∑ k ∈ Finset.Icc 1 N, 1 / (1 - x ^ (k + 1)) := by
          rw [Finset.sum_sub_distrib]

theorem gap5 (x : ℝ) (hx : |x| < 1) (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, 1 / (1 - x ^ k)) -
        (∑ k ∈ Finset.Icc 1 N, 1 / (1 - x ^ (k + 1))) =
      1 / (1 - x) - 1 / (1 - x ^ (N + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hIcc :
          Finset.Icc 1 N.succ =
            insert N.succ (Finset.Icc 1 N) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot : N.succ ∉ Finset.Icc 1 N := by
        simp [Finset.mem_Icc]
      rw [hIcc, Finset.sum_insert hnot, Finset.sum_insert hnot]
      simp only [Nat.succ_eq_add_one]
      linear_combination ih

theorem gap6 (x : ℝ) (hx : |x| < 1) (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, (1 - x) / x * term x k) =
      1 / (1 - x) - 1 / (1 - x ^ (N + 1)) := by
  calc
    (∑ k ∈ Finset.Icc 1 N, (1 - x) / x * term x k) =
        (∑ k ∈ Finset.Icc 1 N, 1 / (1 - x ^ k)) -
          ∑ k ∈ Finset.Icc 1 N, 1 / (1 - x ^ (k + 1)) :=
      gap4 x hx N
    _ = 1 / (1 - x) - 1 / (1 - x ^ (N + 1)) := gap5 x hx N

theorem gap7 (x : ℝ) (hx : |x| < 1) (N : ℕ) :
    partialSum x N =
      x / (1 - x) ^ 2 -
        x / (1 - x) * (1 / (1 - x ^ (N + 1))) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [partialSum, term]
  · have hxlt : x < 1 := lt_of_le_of_lt (le_abs_self x) hx
    have hnum : 1 - x ≠ 0 := sub_ne_zero.mpr (ne_of_gt hxlt)
    have hpow : 1 - x ^ (N + 1) ≠ 0 :=
      sub_ne_zero.mpr
        (pow_ne_one_of_abs_lt_one x hx (N + 1) (by omega)).symm
    apply mul_left_cancel₀ (div_ne_zero hnum hx0)
    calc
      (1 - x) / x * partialSum x N =
          ∑ k ∈ Finset.Icc 1 N, (1 - x) / x * term x k := by
            rw [partialSum, Finset.mul_sum]
      _ = 1 / (1 - x) - 1 / (1 - x ^ (N + 1)) := gap6 x hx N
      _ = (1 - x) / x *
          (x / (1 - x) ^ 2 -
            x / (1 - x) * (1 / (1 - x ^ (N + 1)))) := by
              field_simp [hx0, hnum, hpow] <;> ring

theorem gap8 (x : ℝ) (hx : |x| < 1) :
    Tendsto (partialSum x) atTop
      (𝓝 (∑' n : ℕ, term x (n + 1))) := by
  have ha0 : 0 ≤ |x| := abs_nonneg x
  have ha1 : |x| ≤ 1 := le_of_lt hx
  have hd : 0 < 1 - |x| := sub_pos.mpr hx
  have hpow_le (k : ℕ) : |x| ^ (k + 1) ≤ |x| := by
    rw [pow_succ]
    have hk : |x| ^ k ≤ 1 := pow_le_one₀ ha0 ha1
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) ha0]
  have hden_lower (k : ℕ) :
      1 - |x| ≤ |1 - x ^ (k + 1)| := by
    have hp : |x ^ (k + 1)| ≤ |x| := by
      simpa [abs_pow] using hpow_le k
    have hrev := abs_sub_abs_le_abs_sub (1 : ℝ) (x ^ (k + 1))
    calc
      1 - |x| ≤ 1 - |x ^ (k + 1)| := sub_le_sub_left hp 1
      _ ≤ |1 - x ^ (k + 1)| := by
        simpa only [abs_one] using hrev
  have ha_norm : ‖(abs x : ℝ)‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg ha0] using hx
  have hgeo : Summable (fun n : ℕ => |x| ^ n) :=
    summable_geometric_of_norm_lt_one ha_norm
  have hmajor :
      Summable (fun n : ℕ => 1 / (1 - |x|) ^ 2 * |x| ^ (n + 2)) := by
    have hc := hgeo.mul_left ((1 / (1 - |x|) ^ 2) * |x| ^ 2)
    simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using hc
  have hsummable : Summable (fun n : ℕ => term x (n + 1)) := by
    refine Summable.of_norm_bounded hmajor ?_
    intro n
    have h1 := hden_lower n
    have h2 := hden_lower (n + 1)
    have hprod :
        (1 - |x|) ^ 2 ≤
          |(1 - x ^ (n + 1)) * (1 - x ^ ((n + 1) + 1))| := by
      rw [abs_mul, pow_two]
      exact mul_le_mul h1 h2 (le_of_lt hd) (abs_nonneg _)
    have hdenpos : 0 < (1 - |x|) ^ 2 := sq_pos_of_pos hd
    have hquot :
        |x| ^ (n + 2) /
            |(1 - x ^ (n + 1)) * (1 - x ^ ((n + 1) + 1))| ≤
          |x| ^ (n + 2) / (1 - |x|) ^ 2 :=
      div_le_div_of_nonneg_left (pow_nonneg ha0 _) hdenpos hprod
    have hn2 : (n + 1) + 1 = n + 2 := by omega
    simpa [term, Real.norm_eq_abs, abs_div, abs_pow, hn2,
      div_eq_mul_inv, mul_comm] using hquot
  have hsum : ∀ N : ℕ,
      Finset.sum (Finset.range N) (fun n => term x (n + 1)) =
        partialSum x N := by
    intro N
    induction N with
    | zero => simp [partialSum]
    | succ N ih =>
        have hIcc :
            Finset.Icc 1 N.succ =
              insert N.succ (Finset.Icc 1 N) := by
          ext k
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        have hnot : N.succ ∉ Finset.Icc 1 N := by
          simp [Finset.mem_Icc]
        rw [Finset.sum_range_succ, ih]
        unfold partialSum
        rw [hIcc, Finset.sum_insert hnot]
        simp only [Nat.succ_eq_add_one]
        ring
  simpa only [hsum] using hsummable.hasSum.tendsto_sum_nat

theorem gap9 (x : ℝ) (hx : |x| < 1) :
    Tendsto (fun N : ℕ => 1 / (1 - x ^ (N + 1))) atTop (𝓝 1) ∧
    Tendsto (partialSum x) atTop
      (𝓝 (x / (1 - x) ^ 2 - x / (1 - x) * 1)) := by
  have hp0 : Tendsto (fun N : ℕ => x ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hx
  have hp : Tendsto (fun N : ℕ => x ^ (N + 1)) atTop (𝓝 0) := by
    simpa [pow_succ] using
      hp0.mul
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => x) atTop (𝓝 x))
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hraw :=
    hone.div (hone.sub hp) (by norm_num : (1 : ℝ) - 0 ≠ 0)
  change
    Tendsto (fun N : ℕ => 1 / (1 - x ^ (N + 1))) atTop
      (𝓝 ((1 : ℝ) / (1 - 0))) at hraw
  have hrecip :
      Tendsto (fun N : ℕ => 1 / (1 - x ^ (N + 1))) atTop (𝓝 1) := by
    simpa using hraw
  have hA :
      Tendsto (fun _ : ℕ => x / (1 - x) ^ 2) atTop
        (𝓝 (x / (1 - x) ^ 2)) := tendsto_const_nhds
  have hB :
      Tendsto (fun _ : ℕ => x / (1 - x)) atTop
        (𝓝 (x / (1 - x))) := tendsto_const_nhds
  have hpartial :
      Tendsto (partialSum x) atTop
        (𝓝 (x / (1 - x) ^ 2 - x / (1 - x) * 1)) := by
    rw [show partialSum x =
      (fun N : ℕ =>
        x / (1 - x) ^ 2 -
          x / (1 - x) * (1 / (1 - x ^ (N + 1)))) from
      funext (fun N => gap7 x hx N)]
    exact hA.sub (hB.mul hrecip)
  exact ⟨hrecip, hpartial⟩

theorem gap10 (x : ℝ) (hx : |x| < 1) :
    x / (1 - x) ^ 2 - x / (1 - x) * 1 =
      x / (1 - x) ^ 2 - x / (1 - x) := by
  ring

theorem gap11 (x : ℝ) (hx : |x| < 1) :
    x / (1 - x) ^ 2 - x / (1 - x) =
      x ^ 2 / (1 - x) ^ 2 := by
  have hxlt : x < 1 := lt_of_le_of_lt (le_abs_self x) hx
  have hden : 1 - x ≠ 0 := sub_ne_zero.mpr (ne_of_gt hxlt)
  field_simp [hden]
  ring

theorem gap12 (x : ℝ) (hx : |x| < 1) :
    (∑' n : ℕ, term x (n + 1)) = x ^ 2 / (1 - x) ^ 2 := by
  have hlimit :
      (∑' n : ℕ, term x (n + 1)) =
        x / (1 - x) ^ 2 - x / (1 - x) * 1 :=
    tendsto_nhds_unique (gap8 x hx) (gap9 x hx).2
  calc
    (∑' n : ℕ, term x (n + 1)) =
        x / (1 - x) ^ 2 - x / (1 - x) * 1 := hlimit
    _ = x / (1 - x) ^ 2 - x / (1 - x) := gap10 x hx
    _ = x ^ 2 / (1 - x) ^ 2 := gap11 x hx

end

end ProofGap.Exercise3033_1
