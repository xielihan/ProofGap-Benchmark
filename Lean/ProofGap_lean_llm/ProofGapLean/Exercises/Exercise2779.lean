import ProofGapLean.Prelude.Analysis
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.IntervalCases

namespace ProofGap.Exercise2779

noncomputable section

open Filter
open scoped BigOperators Topology

def sign (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n * (n - 1) / 2)

def denominator (n : ℕ) (x : ℝ) : ℝ :=
  Real.rpow ((n : ℝ) ^ 2 + Real.exp x) (1 / 3 : ℝ)

def weight (n : ℕ) (x : ℝ) : ℝ :=
  1 / denominator n x

def term (n : ℕ) (x : ℝ) : ℝ :=
  sign n * weight n x

def SeriesUniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s,
    |(∑ k ∈ Finset.range (n + 1), u k x) - f x| < ε

private theorem sign_add_two (n : ℕ) : sign (n + 2) = -sign n := by
  have hchoose : (n + 2).choose 2 = n.choose 2 + (2 * n + 1) := by
    simp [Nat.choose_succ_succ, Nat.choose_one_right]
    omega
  have hodd : (-1 : ℝ) ^ (2 * n + 1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  rw [sign, sign, ← Nat.choose_two_right, ← Nat.choose_two_right, hchoose, pow_add,
    hodd]
  ring

private theorem sign_prefix_bound (n : ℕ) :
    |∑ k ∈ Finset.range n, sign (k + 1)| ≤ 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < 4
      · interval_cases n <;> norm_num [sign, Finset.sum_range_succ]
      · have h4 : 4 ≤ n := le_of_not_gt hn
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h4
        have hsum :
            (∑ k ∈ Finset.range (4 + m), sign (k + 1)) =
              ∑ k ∈ Finset.range m, sign (k + 1) := by
          rw [show 4 + m = m + 1 + 1 + 1 + 1 by omega,
            Finset.sum_range_succ, Finset.sum_range_succ,
            Finset.sum_range_succ, Finset.sum_range_succ]
          rw [show m + 1 + 1 + 1 = (m + 1) + 2 by omega,
            show m + 1 + 1 + 1 + 1 = (m + 2) + 2 by omega,
            sign_add_two (m + 1), sign_add_two (m + 2)]
          ring
        rw [hsum]
        exact ih m (by omega)

theorem gap1 (n : ℕ) :
    |∑ k ∈ Finset.Icc 1 n, sign k| ≤ 2 := by
  rw [← Finset.Ico_succ_right_eq_Icc]
  rw [Finset.sum_Ico_eq_sum_range]
  simpa [Nat.add_comm] using sign_prefix_bound n

theorem gap2 (n : ℕ) (x : ℝ) :
    weight n x > weight (n + 1) x := by
  apply one_div_lt_one_div_of_lt
  · dsimp [denominator]
    exact Real.rpow_pos_of_pos (by positivity) _
  · dsimp [denominator]
    apply Real.rpow_lt_rpow (by positivity) _ (by norm_num)
    push_cast
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [sq_nonneg (n : ℝ)]

theorem gap3 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
    weight n x <
      1 / Real.rpow ((n : ℝ) ^ 2) (1 / 3 : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (zero_lt_one.trans_le hn)
  apply one_div_lt_one_div_of_lt
  · exact Real.rpow_pos_of_pos (sq_pos_of_pos hn0) _
  · dsimp [weight, denominator]
    apply Real.rpow_lt_rpow (sq_nonneg (n : ℝ)) (by
      nlinarith [Real.exp_pos x]) (by norm_num)

theorem gap4 :
    Tendsto
      (fun n : ℕ => 1 / Real.rpow ((n : ℝ) ^ 2) (1 / 3 : ℝ))
      atTop (nhds 0) := by
  have hsq : Tendsto (fun n : ℕ => (n : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hrpow : Tendsto
      (fun n : ℕ => Real.rpow ((n : ℝ) ^ 2) (1 / 3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp hsq
  simpa [one_div] using hrpow.inv_tendsto_atTop

private theorem dirichlet_sum_bound
    (f z : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hfa : Antitone f) (hf0 : ∀ n, 0 ≤ f n)
    (hzb : ∀ n, |∑ i ∈ Finset.range n, z i| ≤ B) (n : ℕ) :
    |∑ i ∈ Finset.range n, f i * z i| ≤ B * f 0 := by
  by_cases hn : n = 0
  · subst n
    simpa using mul_nonneg hB (hf0 0)
  have hparts := Finset.sum_range_by_parts f z n
  simp only [smul_eq_mul] at hparts
  rw [hparts]
  have hleft :
      |f (n - 1) * ∑ i ∈ Finset.range n, z i| ≤ f (n - 1) * B := by
    rw [abs_mul, abs_of_nonneg (hf0 (n - 1))]
    exact mul_le_mul_of_nonneg_left (hzb n) (hf0 (n - 1))
  have hright :
      |∑ i ∈ Finset.range (n - 1),
          (f (i + 1) - f i) * ∑ j ∈ Finset.range (i + 1), z j| ≤
        ∑ i ∈ Finset.range (n - 1), (f i - f (i + 1)) * B := by
    calc
      |∑ i ∈ Finset.range (n - 1),
          (f (i + 1) - f i) * ∑ j ∈ Finset.range (i + 1), z j| ≤
          ∑ i ∈ Finset.range (n - 1),
            |(f (i + 1) - f i) * ∑ j ∈ Finset.range (i + 1), z j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (n - 1), (f i - f (i + 1)) * B := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr (hfa (Nat.le_succ i))), neg_sub]
        exact mul_le_mul_of_nonneg_left (hzb (i + 1))
          (sub_nonneg.mpr (hfa (Nat.le_succ i)))
  calc
    |f (n - 1) * ∑ i ∈ Finset.range n, z i -
        ∑ i ∈ Finset.range (n - 1),
          (f (i + 1) - f i) * ∑ j ∈ Finset.range (i + 1), z j| ≤
        |f (n - 1) * ∑ i ∈ Finset.range n, z i| +
          |∑ i ∈ Finset.range (n - 1),
            (f (i + 1) - f i) * ∑ j ∈ Finset.range (i + 1), z j| :=
      abs_sub _ _
    _ ≤ f (n - 1) * B +
        ∑ i ∈ Finset.range (n - 1), (f i - f (i + 1)) * B :=
      add_le_add hleft hright
    _ = B * f 0 := by
      rw [← Finset.sum_mul, Finset.sum_range_sub']
      ring

private theorem sign_shift_sum_bound (N r : ℕ) (hN : 1 ≤ N) :
    |∑ i ∈ Finset.range r, sign (N + i)| ≤ 4 := by
  let q := N - 1
  have hq : q + 1 = N := Nat.sub_add_cancel hN
  have heq :
      (∑ i ∈ Finset.range r, sign (N + i)) =
        (∑ i ∈ Finset.range (q + r), sign (i + 1)) -
          ∑ i ∈ Finset.range q, sign (i + 1) := by
    rw [← Finset.sum_Ico_eq_sub _ (Nat.le_add_right q r)]
    rw [Finset.sum_Ico_eq_sum_range]
    rw [Nat.add_sub_cancel_left]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    omega
  rw [heq]
  calc
    |(∑ i ∈ Finset.range (q + r), sign (i + 1)) -
        ∑ i ∈ Finset.range q, sign (i + 1)| ≤
        |∑ i ∈ Finset.range (q + r), sign (i + 1)| +
          |∑ i ∈ Finset.range q, sign (i + 1)| := abs_sub _ _
    _ ≤ 2 + 2 := add_le_add (sign_prefix_bound (q + r)) (sign_prefix_bound q)
    _ = 4 := by norm_num

private theorem weight_nonneg (n : ℕ) (x : ℝ) : 0 ≤ weight n x := by
  dsimp [weight, denominator]
  positivity

private theorem weight_antitone (x : ℝ) : Antitone (fun n => weight n x) := by
  apply antitone_nat_of_succ_le
  intro n
  exact (gap2 n x).le

private theorem weight_tendsto_zero (x : ℝ) :
    Tendsto (fun n : ℕ => weight n x) atTop (𝓝 0) := by
  have hsq : Tendsto (fun n : ℕ => (n : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hbase : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 + Real.exp x) atTop atTop :=
    tendsto_atTop_add_const_right atTop (Real.exp x) hsq
  have hrpow : Tendsto
      (fun n : ℕ => Real.rpow ((n : ℝ) ^ 2 + Real.exp x) (1 / 3 : ℝ))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp hbase
  simpa [weight, denominator, one_div] using hrpow.inv_tendsto_atTop

private theorem term_tail_bound (x : ℝ) (N r : ℕ) (hN : 1 ≤ N) :
    |∑ i ∈ Finset.range r, term (N + i) x| ≤ 4 * weight N x := by
  have hanti : Antitone (fun i => weight (N + i) x) := by
    intro i j hij
    exact weight_antitone x (Nat.add_le_add_left hij N)
  have hnonneg : ∀ i, 0 ≤ weight (N + i) x := fun i => weight_nonneg _ _
  have hbound := dirichlet_sum_bound
    (fun i => weight (N + i) x) (fun i => sign (N + i)) 4 (by norm_num)
    hanti hnonneg (fun n => sign_shift_sum_bound N n hN) r
  simpa [term, mul_comm] using hbound

private theorem hasSum_conditional_iff_tendsto_range {u : ℕ → ℝ} {l : ℝ} :
    HasSum u l (SummationFilter.conditional ℕ) ↔
      Tendsto (fun n => ∑ i ∈ Finset.range n, u i) atTop (𝓝 l) := by
  simp only [HasSum, SummationFilter.conditional_filter_eq_map_range,
    tendsto_map'_iff]
  rfl

private theorem conditional_series_data (x : ℝ) :
    HasSum (fun k => term (k + 1) x)
        (∑'[SummationFilter.conditional ℕ] k : ℕ, term (k + 1) x)
        (SummationFilter.conditional ℕ) ∧
      ∀ n : ℕ,
        |(∑ k ∈ Finset.range n, term (k + 1) x) -
            ∑'[SummationFilter.conditional ℕ] k : ℕ, term (k + 1) x| ≤
          4 * weight (n + 1) x := by
  have hanti : Antitone (fun k => weight (k + 1) x) := by
    intro i j hij
    exact weight_antitone x (Nat.add_le_add_right hij 1)
  have hzero : Tendsto (fun k => weight (k + 1) x) atTop (𝓝 0) := by
    simpa [Nat.add_comm] using
      (weight_tendsto_zero x).comp (tendsto_add_atTop_nat 1)
  have hc0 := hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded
    (z := fun k => sign (k + 1)) (b := 2) hzero
    (fun n => by
      simpa [Real.norm_eq_abs] using sign_prefix_bound n)
  have hc : CauchySeq (fun n => ∑ k ∈ Finset.range n, term (k + 1) x) := by
    simpa [term, smul_eq_mul, mul_comm] using hc0
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hc
  have hu : HasSum (fun k => term (k + 1) x) l
      (SummationFilter.conditional ℕ) :=
    hasSum_conditional_iff_tendsto_range.mpr hl
  have htsum : (∑'[SummationFilter.conditional ℕ] k : ℕ, term (k + 1) x) = l :=
    hu.tsum_eq
  constructor
  · simpa only [htsum] using hu
  · intro n
    let P : ℕ → ℝ := fun m => ∑ k ∈ Finset.range m, term (k + 1) x
    have htail_eq (r : ℕ) :
        P (n + r) - P n = ∑ i ∈ Finset.range r, term (n + 1 + i) x := by
      dsimp [P]
      rw [← Finset.sum_Ico_eq_sub _ (Nat.le_add_right n r)]
      rw [Finset.sum_Ico_eq_sum_range]
      rw [Nat.add_sub_cancel_left]
      apply Finset.sum_congr rfl
      intro i hi
      rw [show n + i + 1 = n + 1 + i by omega]
    have htail (r : ℕ) : |P (n + r) - P n| ≤ 4 * weight (n + 1) x := by
      rw [htail_eq]
      exact term_tail_bound x (n + 1) r (Nat.succ_le_succ (Nat.zero_le n))
    have hshift : Tendsto (fun r => P (n + r)) atTop (𝓝 l) := by
      simpa [P, Nat.add_comm] using hl.comp (tendsto_add_atTop_nat n)
    have hdiff : Tendsto (fun r => P (n + r) - P n) atTop (𝓝 (l - P n)) :=
      hshift.sub tendsto_const_nhds
    have hlimit : |l - P n| ≤ 4 * weight (n + 1) x :=
      le_of_tendsto hdiff.abs (Eventually.of_forall htail)
    rw [htsum]
    simpa [P, abs_sub_comm] using hlimit

theorem gap5 :
    SeriesUniformlyConvergesOn
      (fun n x => term (n + 1) x)
      (Set.Icc (-10 : ℝ) 10)
      (fun x => ∑'[SummationFilter.conditional ℕ] n : ℕ, term (n + 1) x) := by
  have hshift := gap4.comp (tendsto_add_atTop_nat 2)
  have hlim : Tendsto
      (fun n : ℕ => 4 * (1 / Real.rpow (((n + 2 : ℕ) : ℝ) ^ 2) (1 / 3 : ℝ)))
      atTop (𝓝 0) := by
    convert tendsto_const_nhds.mul hshift using 1 <;> norm_num
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hlim).2 ε hε)
  refine ⟨N, fun n hn x hx => ?_⟩
  have herr := (conditional_series_data x).2 (n + 1)
  have hw := gap3 (n + 2) x (by omega)
  exact herr.trans_lt ((mul_lt_mul_of_pos_left hw (by norm_num)).trans (hN n hn))

theorem gap6 :
    SeriesUniformlyConvergesOn
      (fun n x => term (n + 1) x)
      (Set.Icc (-10 : ℝ) 10)
      (fun x => ∑'[SummationFilter.conditional ℕ] n : ℕ, term (n + 1) x) := by
  exact gap5

end

end ProofGap.Exercise2779
