import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise3032

noncomputable section

open Filter
open scoped BigOperators Topology

def term (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 ^ n) / (1 - x ^ (2 ^ (n + 1)))

def partialSum (x : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), term x n

def remainder (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 ^ (n + 1)) / (1 - x ^ (2 ^ (n + 1)))

private theorem pow_two_pow_succ (x : ℝ) (n : ℕ) :
    (x ^ (2 ^ n)) ^ 2 = x ^ (2 ^ (n + 1)) := by
  rw [← pow_mul, pow_succ]

private theorem nonneg_pow_two_eq_one {a : ℝ} (ha : 0 ≤ a) :
    ∀ n : ℕ, a ^ (2 ^ n) = 1 → a = 1 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      intro h
      have hsquare : (a ^ (2 ^ n)) ^ 2 = 1 := by
        rw [pow_two_pow_succ]
        exact h
      have hnonneg : 0 ≤ a ^ (2 ^ n) := pow_nonneg ha _
      have hprev : a ^ (2 ^ n) = 1 := by
        nlinarith
      exact ih hprev

private theorem one_sub_pow_two_ne_zero
    (x : ℝ) (n : ℕ) (hx : |x| ≠ 1) :
    1 - x ^ (2 ^ n) ≠ 0 := by
  intro hzero
  have hp : x ^ (2 ^ n) = 1 := by
    linarith
  have habspow : |x| ^ (2 ^ n) = 1 := by
    calc
      |x| ^ (2 ^ n) = |x ^ (2 ^ n)| := (abs_pow x (2 ^ n)).symm
      _ = 1 := by rw [hp]; norm_num
  have habs : |x| = 1 :=
    nonneg_pow_two_eq_one (abs_nonneg x) n habspow
  exact hx habs

private theorem fraction_split (a : ℝ)
    (h₁ : 1 - a ≠ 0) (h₂ : 1 - a ^ 2 ≠ 0) :
    a / (1 - a) = a / (1 - a ^ 2) + a ^ 2 / (1 - a ^ 2) := by
  field_simp [h₁, h₂] <;> ring

private theorem remainder_eq_next_term_add
    (x : ℝ) (n : ℕ) (hx : |x| ≠ 1) :
    remainder x n = term x (n + 1) + remainder x (n + 1) := by
  have h₁ := one_sub_pow_two_ne_zero x (n + 1) hx
  have h₂ : 1 - (x ^ (2 ^ (n + 1))) ^ 2 ≠ 0 := by
    rw [pow_two_pow_succ x (n + 1)]
    exact one_sub_pow_two_ne_zero x ((n + 1) + 1) hx
  have hs := fraction_split (x ^ (2 ^ (n + 1))) h₁ h₂
  simpa [term, remainder, pow_two_pow_succ] using hs

private theorem partialSum_succ (x : ℝ) (n : ℕ) :
    partialSum x (n + 1) = partialSum x n + term x (n + 1) := by
  unfold partialSum
  rw [Finset.sum_range_succ]

private theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hp : 0 < (2 : ℕ) ^ n := pow_pos (by norm_num) n
      rw [pow_succ]
      omega

private theorem nat_le_two_pow_succ (n : ℕ) : n ≤ 2 ^ (n + 1) := by
  have hn := nat_le_two_pow n
  have hp : 0 < (2 : ℕ) ^ n := pow_pos (by norm_num) n
  rw [pow_succ]
  omega

private theorem tendsto_two_pow_succ :
    Tendsto (fun n : ℕ => 2 ^ (n + 1)) atTop atTop := by
  refine tendsto_atTop.2 (fun b => ?_)
  exact (eventually_ge_atTop b).mono
    (fun n hn => hn.trans (nat_le_two_pow_succ n))

private theorem partialSum_eq_head_add_tail (x : ℝ) :
    ∀ N : ℕ,
      partialSum x N =
        term x 0 + ∑ n ∈ Finset.range N, term x (n + 1) := by
  intro N
  induction N with
  | zero => simp [partialSum]
  | succ N ih =>
      calc
        partialSum x (Nat.succ N) =
            partialSum x N + term x (N + 1) := by
              simpa [Nat.succ_eq_add_one] using partialSum_succ x N
        _ = (term x 0 + ∑ n ∈ Finset.range N, term x (n + 1)) +
              term x (N + 1) := by rw [ih]
        _ = term x 0 +
              ∑ n ∈ Finset.range (Nat.succ N), term x (n + 1) := by
              rw [Finset.sum_range_succ]
              ring

private theorem shifted_partialSum_tendsto
    (x L : ℝ)
    (h : Tendsto (partialSum x) atTop (𝓝 L)) :
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, term x (n + 1))
      atTop (𝓝 (L - term x 0)) := by
  have hsub := h.sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => term x 0) atTop (𝓝 (term x 0)))
  refine hsub.congr' (Filter.Eventually.of_forall ?_)
  intro N
  rw [partialSum_eq_head_add_tail]
  ring

private theorem summable_term_of_tail_nonneg
    (x L : ℝ)
    (h : Tendsto (partialSum x) atTop (𝓝 L))
    (htail : ∀ n : ℕ, 0 ≤ term x (n + 1)) :
    Summable (term x) := by
  have htail_sum : HasSum (fun n : ℕ => term x (n + 1))
      (L - term x 0) :=
    (hasSum_iff_tendsto_nat_of_nonneg htail (L - term x 0)).2
      (shifted_partialSum_tendsto x L h)
  rw [← summable_nat_add_iff 1]
  exact htail_sum.summable

private theorem summable_term_of_tail_nonpos
    (x L : ℝ)
    (h : Tendsto (partialSum x) atTop (𝓝 L))
    (htail : ∀ n : ℕ, term x (n + 1) ≤ 0) :
    Summable (term x) := by
  have hshift := shifted_partialSum_tendsto x L h
  have hneg_tendsto :
      Tendsto
        (fun N : ℕ => ∑ n ∈ Finset.range N, -term x (n + 1))
        atTop (𝓝 (-(L - term x 0))) := by
    simpa only [Finset.sum_neg_distrib] using hshift.neg
  have hneg_sum : HasSum (fun n : ℕ => -term x (n + 1))
      (-(L - term x 0)) :=
    (hasSum_iff_tendsto_nat_of_nonneg
      (fun n => neg_nonneg.mpr (htail n)) (-(L - term x 0))).2 hneg_tendsto
  have htail_sum : Summable (fun n : ℕ => term x (n + 1)) := by
    simpa only [neg_neg] using hneg_sum.summable.neg
  rw [← summable_nat_add_iff 1]
  exact htail_sum

private theorem partialSum_tendsto_tsum_of_tendsto
    (x L : ℝ)
    (hs : Summable (term x))
    (h : Tendsto (partialSum x) atTop (𝓝 L)) :
    Tendsto (partialSum x) atTop
      (𝓝 (∑' n : ℕ, term x n)) := by
  have hstandard :
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, term x n)
        atTop (𝓝 L) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    simpa [partialSum] using h
  have htsum :
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, term x n)
        atTop (𝓝 (∑' n : ℕ, term x n)) :=
    hs.hasSum.tendsto_sum_nat
  have hvalue : L = ∑' n : ℕ, term x n :=
    tendsto_nhds_unique hstandard htsum
  simpa [hvalue] using h

private theorem even_power_eq_abs_power (x : ℝ) (n : ℕ) :
    x ^ (2 ^ (n + 1)) = |x| ^ (2 ^ (n + 1)) := by
  have hnonneg : 0 ≤ x ^ (2 ^ (n + 1)) := by
    rw [← pow_two_pow_succ x n]
    exact sq_nonneg _
  calc
    x ^ (2 ^ (n + 1)) = |x ^ (2 ^ (n + 1))| :=
      (abs_of_nonneg hnonneg).symm
    _ = |x| ^ (2 ^ (n + 1)) := abs_pow x _

private theorem abs_fraction_eq_inv_fraction
    (x : ℝ) (hx : 1 < |x|) (n : ℕ) :
    |x| ^ (2 ^ (n + 1)) / (1 - |x| ^ (2 ^ (n + 1))) =
      1 / ((1 / |x|) ^ (2 ^ (n + 1)) - 1) := by
  let A : ℝ := |x| ^ (2 ^ (n + 1))
  have hx0 : |x| ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hA0 : A ≠ 0 := by
    dsimp [A]
    exact pow_ne_zero _ hx0
  have habsne : |(|x| : ℝ)| ≠ 1 := by
    simpa using (ne_of_gt hx)
  have hA1 : 1 - A ≠ 0 := by
    dsimp [A]
    exact one_sub_pow_two_ne_zero |x| (n + 1) habsne
  have hpowinv : (1 / |x|) ^ (2 ^ (n + 1)) = A⁻¹ := by
    dsimp [A]
    simp [one_div]
  have hinvden : A⁻¹ - 1 ≠ 0 := by
    intro h
    have hi : A⁻¹ = 1 := sub_eq_zero.mp h
    have hAeq : A = 1 := by
      calc
        A = (A⁻¹)⁻¹ := by simp
        _ = 1 := by rw [hi]; simp
    apply hA1
    simp [hAeq]
  rw [hpowinv]
  change A / (1 - A) = 1 / (A⁻¹ - 1)
  field_simp [hA0, hA1, hinvden] <;> ring

theorem gap1 (x : ℝ) (n : ℕ) (hx : |x| ≠ 1) :
    x / (1 - x) = partialSum x n + remainder x n := by
  induction n with
  | zero =>
      have hs := fraction_split x
        (by simpa using one_sub_pow_two_ne_zero x 0 hx)
        (by simpa using one_sub_pow_two_ne_zero x 1 hx)
      simpa [partialSum, term, remainder] using hs
  | succ n ih =>
      calc
        x / (1 - x) = partialSum x n + remainder x n := ih
        _ = partialSum x n +
              (term x (n + 1) + remainder x (n + 1)) := by
              rw [remainder_eq_next_term_add x n hx]
        _ = partialSum x (n + 1) + remainder x (n + 1) := by
              rw [partialSum_succ]
              ring

theorem gap2 (x : ℝ) (n : ℕ) (hx : |x| ≠ 1) :
    ∃ R : ℕ → ℝ,
      x / (1 - x) = partialSum x n + R n := by
  refine ⟨remainder x, ?_⟩
  exact gap1 x n hx

theorem gap3 (x : ℝ) :
    ∀ n : ℕ, remainder x n =
      x ^ (2 ^ (n + 1)) / (1 - x ^ (2 ^ (n + 1))) := by
  intro n
  rfl

theorem gap4 (x : ℝ) (hx : |x| < 1) :
    Tendsto (remainder x) atTop (𝓝 0) := by
  have hp : Tendsto (fun k : ℕ => x ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hx
  have hy :
      Tendsto (fun n : ℕ => x ^ (2 ^ (n + 1))) atTop (𝓝 0) :=
    hp.comp tendsto_two_pow_succ
  have hden :
      Tendsto (fun n : ℕ => 1 - x ^ (2 ^ (n + 1)))
        atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub hy
  have hquot := hy.div hden (by norm_num : (1 : ℝ) - 0 ≠ 0)
  simpa [remainder] using hquot

theorem gap5 (x : ℝ) (hx : |x| < 1) :
    Tendsto (partialSum x) atTop (𝓝 (∑' n : ℕ, term x n)) := by
  have hsub :
      Tendsto (fun N : ℕ => x / (1 - x) - remainder x N)
        atTop (𝓝 (x / (1 - x) - 0)) :=
    tendsto_const_nhds.sub (gap4 x hx)
  have hpartial :
      Tendsto (partialSum x) atTop (𝓝 (x / (1 - x) - 0)) := by
    refine hsub.congr' (Filter.Eventually.of_forall ?_)
    intro N
    linarith [gap1 x N (ne_of_lt hx)]
  have htail_nonneg : ∀ n : ℕ, 0 ≤ term x (n + 1) := by
    intro n
    have hpow : |x| ^ (2 ^ ((n + 1) + 1)) < 1 :=
      pow_lt_one₀ (abs_nonneg x) hx (pow_ne_zero _ (by norm_num))
    rw [term, even_power_eq_abs_power x n,
      even_power_eq_abs_power x (n + 1)]
    exact div_nonneg (pow_nonneg (abs_nonneg x) _)
      (sub_nonneg.mpr (le_of_lt hpow))
  have hsummable : Summable (term x) :=
    summable_term_of_tail_nonneg x (x / (1 - x) - 0)
      hpartial htail_nonneg
  exact partialSum_tendsto_tsum_of_tendsto x
    (x / (1 - x) - 0) hsummable hpartial

theorem gap6 (x : ℝ) (hx : |x| < 1) :
    Tendsto (partialSum x) atTop
      (𝓝 (x / (1 - x) - 0)) := by
  have hsub :
      Tendsto (fun N : ℕ => x / (1 - x) - remainder x N)
        atTop (𝓝 (x / (1 - x) - 0)) :=
    tendsto_const_nhds.sub (gap4 x hx)
  refine hsub.congr' (Filter.Eventually.of_forall ?_)
  intro N
  linarith [gap1 x N (ne_of_lt hx)]

theorem gap7 (x : ℝ) (hx : |x| < 1) :
    Tendsto (fun N : ℕ => x / (1 - x) - remainder x N)
      atTop (𝓝 (x / (1 - x))) := by
  simpa using (tendsto_const_nhds.sub (gap4 x hx))

theorem gap8 (x : ℝ) (hx : |x| < 1) :
    (∑' n : ℕ, term x n) = x / (1 - x) := by
  have h := tendsto_nhds_unique (gap5 x hx) (gap6 x hx)
  simpa using h

theorem gap9 (x : ℝ) (hx : 1 < |x|) :
    Tendsto (fun n : ℕ => (1 / |x|) ^ (2 ^ (n + 1)))
      atTop (𝓝 0) := by
  have hpos : 0 < |x| := lt_trans zero_lt_one hx
  have hnonneg : 0 ≤ 1 / |x| := le_of_lt (one_div_pos.mpr hpos)
  have hbase : abs (1 / |x|) < 1 := by
    rw [abs_of_nonneg hnonneg]
    exact (div_lt_one hpos).2 hx
  have hp : Tendsto (fun k : ℕ => (1 / |x|) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hbase
  exact hp.comp tendsto_two_pow_succ

theorem gap10 (x : ℝ) (hx : 1 < |x|) :
    Tendsto (remainder x) atTop (𝓝 (-1)) ∧
      Tendsto
        (fun n : ℕ =>
          |x| ^ (2 ^ (n + 1)) / (1 - |x| ^ (2 ^ (n + 1))))
        atTop (𝓝 (-1)) := by
  have hpow := gap9 x hx
  have hden :
      Tendsto
        (fun n : ℕ => (1 / |x|) ^ (2 ^ (n + 1)) - 1)
        atTop (𝓝 ((0 : ℝ) - 1)) :=
    hpow.sub tendsto_const_nhds
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hinv :
      Tendsto
        (fun n : ℕ => 1 / ((1 / |x|) ^ (2 ^ (n + 1)) - 1))
        atTop (𝓝 (-1)) := by
    convert hone.div hden (by norm_num : (0 : ℝ) - 1 ≠ 0) using 1 <;>
      norm_num
  have habs :
      Tendsto
        (fun n : ℕ =>
          |x| ^ (2 ^ (n + 1)) / (1 - |x| ^ (2 ^ (n + 1))))
        atTop (𝓝 (-1)) := by
    refine hinv.congr' (Filter.Eventually.of_forall ?_)
    intro n
    exact (abs_fraction_eq_inv_fraction x hx n).symm
  have hrem : Tendsto (remainder x) atTop (𝓝 (-1)) := by
    refine habs.congr' (Filter.Eventually.of_forall ?_)
    intro n
    rw [remainder, even_power_eq_abs_power x n]
  exact ⟨hrem, habs⟩

theorem gap11 (x : ℝ) (hx : 1 < |x|) :
    Tendsto
        (fun n : ℕ =>
          |x| ^ (2 ^ (n + 1)) / (1 - |x| ^ (2 ^ (n + 1))))
        atTop (𝓝 (-1)) ∧
      Tendsto
        (fun n : ℕ =>
          1 / ((1 / |x|) ^ (2 ^ (n + 1)) - 1))
        atTop (𝓝 (-1)) := by
  have habs := (gap10 x hx).2
  have hinv :
      Tendsto
        (fun n : ℕ => 1 / ((1 / |x|) ^ (2 ^ (n + 1)) - 1))
        atTop (𝓝 (-1)) := by
    refine habs.congr' (Filter.Eventually.of_forall ?_)
    intro n
    exact abs_fraction_eq_inv_fraction x hx n
  exact ⟨habs, hinv⟩

theorem gap12 (x : ℝ) (hx : 1 < |x|) :
    Tendsto
      (fun n : ℕ => 1 / ((1 / |x|) ^ (2 ^ (n + 1)) - 1))
      atTop (𝓝 (-1)) := by
  have habs := (gap10 x hx).2
  refine habs.congr' (Filter.Eventually.of_forall ?_)
  intro n
  exact abs_fraction_eq_inv_fraction x hx n

theorem gap13 (x : ℝ) (hx : 1 < |x|) :
    Tendsto (remainder x) atTop (𝓝 (-1)) := by
  exact (gap10 x hx).1

theorem gap14 (x : ℝ) (hx : 1 < |x|) :
    Tendsto (partialSum x) atTop (𝓝 (∑' n : ℕ, term x n)) := by
  have hsub :
      Tendsto (fun N : ℕ => x / (1 - x) - remainder x N)
        atTop (𝓝 (x / (1 - x) - (-1))) :=
    tendsto_const_nhds.sub (gap13 x hx)
  have hpartial :
      Tendsto (partialSum x) atTop (𝓝 (x / (1 - x) - (-1))) := by
    refine hsub.congr' (Filter.Eventually.of_forall ?_)
    intro N
    linarith [gap1 x N (ne_of_gt hx)]
  have htail_nonpos : ∀ n : ℕ, term x (n + 1) ≤ 0 := by
    intro n
    have hpow : 1 < |x| ^ (2 ^ ((n + 1) + 1)) :=
      one_lt_pow₀ hx (pow_ne_zero _ (by norm_num))
    rw [term, even_power_eq_abs_power x n,
      even_power_eq_abs_power x (n + 1)]
    exact div_nonpos_of_nonneg_of_nonpos
      (pow_nonneg (abs_nonneg x) _)
      (sub_nonpos.mpr (le_of_lt hpow))
  have hsummable : Summable (term x) :=
    summable_term_of_tail_nonpos x (x / (1 - x) - (-1))
      hpartial htail_nonpos
  exact partialSum_tendsto_tsum_of_tendsto x
    (x / (1 - x) - (-1)) hsummable hpartial

theorem gap15 (x : ℝ) (hx : 1 < |x|) :
    Tendsto (partialSum x) atTop
      (𝓝 (x / (1 - x) - (-1))) := by
  have hsub :
      Tendsto (fun N : ℕ => x / (1 - x) - remainder x N)
        atTop (𝓝 (x / (1 - x) - (-1))) :=
    tendsto_const_nhds.sub (gap13 x hx)
  refine hsub.congr' (Filter.Eventually.of_forall ?_)
  intro N
  linarith [gap1 x N (ne_of_gt hx)]

theorem gap16 (x : ℝ) (hx : 1 < |x|) :
    Tendsto (fun N : ℕ => x / (1 - x) - remainder x N)
      atTop (𝓝 (x / (1 - x) + 1)) := by
  simpa [sub_neg_eq_add] using
    (tendsto_const_nhds.sub (gap13 x hx))

theorem gap17 (x : ℝ) (hx : 1 < |x|) :
    x / (1 - x) + 1 = 1 / (1 - x) := by
  have hden : 1 - x ≠ 0 := by
    intro h
    have hx1 : x = 1 := by linarith
    subst x
    norm_num at hx
  field_simp [hden] <;> ring

theorem gap18 (x : ℝ) (hx : 1 < |x|) :
    (∑' n : ℕ, term x n) = 1 / (1 - x) := by
  have hlim := tendsto_nhds_unique (gap14 x hx) (gap15 x hx)
  calc
    (∑' n : ℕ, term x n) = x / (1 - x) - (-1) := hlim
    _ = x / (1 - x) + 1 := by ring
    _ = 1 / (1 - x) := gap17 x hx

end

end ProofGap.Exercise3032
