import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace ProofGap.Exercise3033_2

noncomputable section

open Filter
open scoped BigOperators Topology

def term (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (n + 1) / ((1 - x ^ n) * (1 - x ^ (n + 1)))

def partialSum (x : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, term x k

private lemma one_sub_pow_ne_zero
    (x : ℝ) (hx : 1 < |x|) (n : ℕ) (hn : 1 ≤ n) :
    1 - x ^ n ≠ 0 := by
  intro hzero
  have hxn : x ^ n = 1 := by linarith
  have hpow : 1 < |x| ^ n := one_lt_pow₀ hx (by omega)
  have habs : |x| ^ n = 1 := by
    calc
      |x| ^ n = |x ^ n| := (abs_pow x n).symm
      _ = 1 := by simp [hxn]
  linarith

private lemma tendsto_one_div_one_sub_pow
    (x : ℝ) (hx : 1 < |x|) :
    Tendsto (fun N : ℕ => 1 / (1 - x ^ (N + 1))) atTop (𝓝 0) := by
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    norm_num at hx
  have hinv : ‖x⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_inv]
    exact inv_lt_one_of_one_lt₀ hx
  have hbase :
      Tendsto (fun N : ℕ => (x⁻¹) ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hinv
  have hshift :
      Tendsto (fun N : ℕ => (x⁻¹) ^ (N + 1)) atTop (𝓝 0) := by
    simpa [pow_succ] using hbase.mul_const (x⁻¹)
  have hquot :
      Tendsto
        (fun N : ℕ =>
          (x⁻¹) ^ (N + 1) / ((x⁻¹) ^ (N + 1) - 1))
        atTop (𝓝 0) := by
    have h := hshift.div (hshift.sub tendsto_const_nhds)
      (by norm_num : (0 : ℝ) - 1 ≠ 0)
    simpa using h
  refine hquot.congr' (Filter.Eventually.of_forall ?_)
  intro N
  have hxp : x ^ (N + 1) ≠ 0 := pow_ne_zero _ hx0
  rw [inv_pow]
  field_simp [hxp] <;> ring

private lemma summable_one_div_one_sub_pow
    (x : ℝ) (hx : 1 < |x|) :
    Summable (fun n : ℕ => 1 / (1 - x ^ (n + 1))) := by
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    norm_num at hx
  let q : ℝ := x⁻¹
  let r : ℝ := |q|
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact abs_nonneg q
  have hr : r < 1 := by
    dsimp [r, q]
    rw [abs_inv]
    exact inv_lt_one_of_one_lt₀ hx
  have hd : 0 < 1 - r := sub_pos.mpr hr
  have hrnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr
  have hgeom0 : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_norm_lt_one hrnorm
  have hgeom :
      Summable (fun n : ℕ => (1 / (1 - r)) * r ^ n) :=
    hgeom0.mul_left (1 / (1 - r))
  refine hgeom.of_norm_bounded ?_
  intro n
  let y : ℝ := q ^ (n + 1)
  have hxp : x ^ (n + 1) ≠ 0 := pow_ne_zero _ hx0
  have hid :
      1 / (1 - x ^ (n + 1)) = y / (y - 1) := by
    dsimp [y, q]
    rw [inv_pow]
    field_simp [hxp] <;> ring
  have hyabs : |y| = r ^ (n + 1) := by
    simpa [y, r] using (abs_pow q (n + 1))
  have hrn : r ^ n ≤ 1 := pow_le_one₀ hr0 (le_of_lt hr)
  have hyn_le : |y| ≤ r ^ n := by
    calc
      |y| = r ^ (n + 1) := hyabs
      _ = r ^ n * r := by rw [pow_succ]
      _ ≤ r ^ n * 1 :=
        mul_le_mul_of_nonneg_left (le_of_lt hr) (pow_nonneg hr0 n)
      _ = r ^ n := by ring
  have hy_le_r : |y| ≤ r := by
    calc
      |y| = r ^ (n + 1) := hyabs
      _ = r ^ n * r := by rw [pow_succ]
      _ ≤ 1 * r := mul_le_mul_of_nonneg_right hrn hr0
      _ = r := by ring
  have hreverse : 1 - |y| ≤ |1 - y| := by
    simpa using (abs_sub_abs_le_abs_sub (1 : ℝ) y)
  have hden : 1 - r ≤ |y - 1| := by
    calc
      1 - r ≤ 1 - |y| := sub_le_sub_left hy_le_r 1
      _ ≤ |1 - y| := hreverse
      _ = |y - 1| := abs_sub_comm 1 y
  have hdenpos : 0 < |y - 1| := lt_of_lt_of_le hd hden
  have hfactor : 1 ≤ (1 / (1 - r)) * |y - 1| := by
    have hquot : 1 ≤ |y - 1| / (1 - r) := by
      apply (le_div_iff₀ hd).2
      simpa using hden
    calc
      1 ≤ |y - 1| / (1 - r) := hquot
      _ = (1 / (1 - r)) * |y - 1| := by ring
  have hbound :
      |1 / (1 - x ^ (n + 1))| ≤ (1 / (1 - r)) * r ^ n := by
    rw [hid, abs_div]
    apply (div_le_iff₀ hdenpos).2
    calc
      |y| ≤ r ^ n := hyn_le
      _ = r ^ n * 1 := by ring
      _ ≤ r ^ n * ((1 / (1 - r)) * |y - 1|) :=
        mul_le_mul_of_nonneg_left hfactor (pow_nonneg hr0 n)
      _ = ((1 / (1 - r)) * r ^ n) * |y - 1| := by ring
  have hcoef0 : 0 ≤ 1 / (1 - r) :=
    le_of_lt (one_div_pos.mpr hd)
  have hmajor0 : 0 ≤ (1 / (1 - r)) * r ^ n :=
    mul_nonneg hcoef0 (pow_nonneg hr0 n)
  simpa [Real.norm_eq_abs, abs_of_nonneg hmajor0] using hbound

private lemma summable_shifted_term
    (x : ℝ) (hx : 1 < |x|) :
    Summable (fun n : ℕ => term x (n + 1)) := by
  have hx1 : 1 - x ≠ 0 := by
    simpa using one_sub_pow_ne_zero x hx 1 (by omega)
  have hA := summable_one_div_one_sub_pow x hx
  have hsucc : Function.Injective (fun n : ℕ => n + 1) := by
    intro a b hab
    exact Nat.add_right_cancel hab
  have hAshift :
      Summable (fun n : ℕ => 1 / (1 - x ^ ((n + 1) + 1))) := by
    simpa [Function.comp_def] using hA.comp_injective hsucc
  have hdiff :
      Summable (fun n : ℕ =>
        1 / (1 - x ^ (n + 1)) -
          1 / (1 - x ^ ((n + 1) + 1))) :=
    hA.sub hAshift
  have hscaled :
      Summable (fun n : ℕ =>
        x / (1 - x) *
          (1 / (1 - x ^ (n + 1)) -
            1 / (1 - x ^ ((n + 1) + 1)))) :=
    hdiff.mul_left (x / (1 - x))
  have heq :
      (fun n : ℕ => term x (n + 1)) =
        (fun n : ℕ =>
          x / (1 - x) *
            (1 / (1 - x ^ (n + 1)) -
              1 / (1 - x ^ ((n + 1) + 1)))) := by
    funext n
    have hn1 := one_sub_pow_ne_zero x hx (n + 1) (by omega)
    have hn2 := one_sub_pow_ne_zero x hx ((n + 1) + 1) (by omega)
    unfold term
    field_simp [hx1, hn1, hn2] <;> ring
  rw [heq]
  exact hscaled

theorem gap1 (x : ℝ) (hx : 1 < |x|) (n : ℕ) (hn : 1 ≤ n) :
    1 / (1 - x ^ n) - 1 / (1 - x ^ (n + 1)) =
      x ^ n * (1 - x) / ((1 - x ^ n) * (1 - x ^ (n + 1))) := by
  have hn0 := one_sub_pow_ne_zero x hx n hn
  have hn10 := one_sub_pow_ne_zero x hx (n + 1) (by omega)
  field_simp [hn0, hn10] <;> ring

theorem gap2 (x : ℝ) (hx : 1 < |x|) (n : ℕ) (hn : 1 ≤ n) :
    x ^ n * (1 - x) / ((1 - x ^ n) * (1 - x ^ (n + 1))) =
      (1 - x) / x * term x n := by
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    norm_num at hx
  have hn0 := one_sub_pow_ne_zero x hx n hn
  have hn10 := one_sub_pow_ne_zero x hx (n + 1) (by omega)
  unfold term
  field_simp [hx0, hn0, hn10] <;> ring

theorem gap3 (x : ℝ) (hx : 1 < |x|) (n : ℕ) (hn : 1 ≤ n) :
    1 / (1 - x ^ n) - 1 / (1 - x ^ (n + 1)) =
      (1 - x) / x * term x n := by
  calc
    1 / (1 - x ^ n) - 1 / (1 - x ^ (n + 1)) =
        x ^ n * (1 - x) / ((1 - x ^ n) * (1 - x ^ (n + 1))) :=
      gap1 x hx n hn
    _ = (1 - x) / x * term x n := gap2 x hx n hn

theorem gap4 (x : ℝ) (hx : 1 < |x|) (N : ℕ) :
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

theorem gap5 (x : ℝ) (hx : 1 < |x|) (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, 1 / (1 - x ^ k)) -
        (∑ k ∈ Finset.Icc 1 N, 1 / (1 - x ^ (k + 1))) =
      1 / (1 - x) - 1 / (1 - x ^ (N + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hnot : N + 1 ∉ Finset.Icc 1 N := by
        intro h
        have hle := (Finset.mem_Icc.mp h).2
        omega
      have hset :
          Finset.Icc 1 (N + 1) =
            insert (N + 1) (Finset.Icc 1 N) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hA :
          (∑ k ∈ Finset.Icc 1 (N + 1), 1 / (1 - x ^ k)) =
            (∑ k ∈ Finset.Icc 1 N, 1 / (1 - x ^ k)) +
              1 / (1 - x ^ (N + 1)) := by
        rw [hset, Finset.sum_insert hnot]
        ring
      have hB :
          (∑ k ∈ Finset.Icc 1 (N + 1), 1 / (1 - x ^ (k + 1))) =
            (∑ k ∈ Finset.Icc 1 N, 1 / (1 - x ^ (k + 1))) +
              1 / (1 - x ^ ((N + 1) + 1)) := by
        rw [hset, Finset.sum_insert hnot]
        ring
      rw [hA, hB]
      linarith [ih]

theorem gap6 (x : ℝ) (hx : 1 < |x|) (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, (1 - x) / x * term x k) =
      1 / (1 - x) - 1 / (1 - x ^ (N + 1)) := by
  calc
    (∑ k ∈ Finset.Icc 1 N, (1 - x) / x * term x k) =
        (∑ k ∈ Finset.Icc 1 N, 1 / (1 - x ^ k)) -
          ∑ k ∈ Finset.Icc 1 N, 1 / (1 - x ^ (k + 1)) :=
      gap4 x hx N
    _ = 1 / (1 - x) - 1 / (1 - x ^ (N + 1)) := gap5 x hx N

theorem gap7 (x : ℝ) (hx : 1 < |x|) (N : ℕ) :
    partialSum x N =
      x / (1 - x) ^ 2 -
        x / (1 - x) * (1 / (1 - x ^ (N + 1))) := by
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    norm_num at hx
  have hx1 : 1 - x ≠ 0 := by
    simpa using one_sub_pow_ne_zero x hx 1 (by omega)
  have hp := one_sub_pow_ne_zero x hx (N + 1) (by omega)
  have hs :
      (1 - x) / x * partialSum x N =
        1 / (1 - x) - 1 / (1 - x ^ (N + 1)) := by
    rw [partialSum, Finset.mul_sum]
    exact gap6 x hx N
  field_simp [hx0, hx1, hp] at hs ⊢ <;> nlinarith [hs]

theorem gap8 (x : ℝ) (hx : 1 < |x|) :
    Tendsto (partialSum x) atTop
      (𝓝 (∑' n : ℕ, term x (n + 1))) := by
  have ht := tendsto_one_div_one_sub_pow x hx
  have hrhs :
      Tendsto
        (fun N : ℕ =>
          x / (1 - x) ^ 2 -
            x / (1 - x) * (1 / (1 - x ^ (N + 1))))
        atTop
        (𝓝 (x / (1 - x) ^ 2 - x / (1 - x) * 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul ht)
  have hlim :
      Tendsto (partialSum x) atTop (𝓝 (x / (1 - x) ^ 2)) := by
    have h := hrhs.congr'
      (Filter.Eventually.of_forall (fun N => (gap7 x hx N).symm))
    simpa using h
  have hsum (N : ℕ) :
      (∑ n ∈ Finset.range N, term x (n + 1)) = partialSum x N := by
    induction N with
    | zero => simp [partialSum]
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        unfold partialSum
        have hnot : N + 1 ∉ Finset.Icc 1 N := by
          intro hmem
          have hle := (Finset.mem_Icc.mp hmem).2
          omega
        have hset :
            Finset.Icc 1 (N + 1) =
              insert (N + 1) (Finset.Icc 1 N) := by
          ext k
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        rw [hset, Finset.sum_insert hnot]
        ring
  have hsum_tend :
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, term x (n + 1))
        atTop (𝓝 (x / (1 - x) ^ 2)) :=
    hlim.congr'
      (Filter.Eventually.of_forall (fun N => (hsum N).symm))
  have hs : Summable (fun n : ℕ => term x (n + 1)) :=
    summable_shifted_term x hx
  have hcanonical :
      Tendsto
        (fun N : ℕ => ∑ n ∈ Finset.range N, term x (n + 1))
        atTop (𝓝 (∑' n : ℕ, term x (n + 1))) :=
    hs.hasSum.tendsto_sum_nat
  have htsum :
      (∑' n : ℕ, term x (n + 1)) = x / (1 - x) ^ 2 :=
    tendsto_nhds_unique hcanonical hsum_tend
  rw [htsum]
  exact hlim

theorem gap9 (x : ℝ) (hx : 1 < |x|) :
    Tendsto (fun N : ℕ => 1 / (x ^ (N + 1) - 1)) atTop (𝓝 0) ∧
    Tendsto (partialSum x) atTop
      (𝓝 (x / (1 - x) ^ 2 + x / (1 - x) * 0)) := by
  have ht := tendsto_one_div_one_sub_pow x hx
  have hneg :
      Tendsto (fun N : ℕ => -(1 / (1 - x ^ (N + 1)))) atTop (𝓝 0) := by
    simpa using ht.neg
  have hfirst :
      Tendsto (fun N : ℕ => 1 / (x ^ (N + 1) - 1)) atTop (𝓝 0) := by
    refine hneg.congr' (Filter.Eventually.of_forall ?_)
    intro N
    dsimp only
    have hleft := one_sub_pow_ne_zero x hx (N + 1) (by omega)
    have hright : x ^ (N + 1) - 1 ≠ 0 := by
      intro hzero
      apply hleft
      linarith
    field_simp [hleft, hright] <;> ring
  have hrhs :
      Tendsto
        (fun N : ℕ =>
          x / (1 - x) ^ 2 -
            x / (1 - x) * (1 / (1 - x ^ (N + 1))))
        atTop
        (𝓝 (x / (1 - x) ^ 2 - x / (1 - x) * 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul ht)
  have hpartial := hrhs.congr'
    (Filter.Eventually.of_forall (fun N => (gap7 x hx N).symm))
  constructor
  · exact hfirst
  · simpa using hpartial

theorem gap10 (x : ℝ) (hx : 1 < |x|) :
    x / (1 - x) ^ 2 + x / (1 - x) * 0 =
      x / (1 - x) ^ 2 := by
  ring

theorem gap11 (x : ℝ) (hx : 1 < |x|) :
    (∑' n : ℕ, term x (n + 1)) = x / (1 - x) ^ 2 := by
  have hsum := gap8 x hx
  have hclosed := (gap9 x hx).2
  have heq :
      (∑' n : ℕ, term x (n + 1)) =
        x / (1 - x) ^ 2 + x / (1 - x) * 0 :=
    tendsto_nhds_unique hsum hclosed
  calc
    (∑' n : ℕ, term x (n + 1)) =
        x / (1 - x) ^ 2 + x / (1 - x) * 0 := heq
    _ = x / (1 - x) ^ 2 := gap10 x hx

end

end ProofGap.Exercise3033_2
