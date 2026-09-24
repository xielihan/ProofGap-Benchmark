import ProofGapLean.Prelude.Analysis
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace ProofGap.Exercise2778

noncomputable section

open Filter
open scoped BigOperators Topology

def term (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ n / ((n : ℝ) + Real.sin x)

def SeriesUniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s,
    |(∑ k ∈ Finset.range (n + 1), u k x) - f x| < ε

theorem gap1 (x : ℝ) (n : ℕ)
    (hx : x ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) (hn : 2 ≤ n) :
    1 / ((n : ℝ) + Real.sin x) >
      1 / (((n + 1 : ℕ) : ℝ) + Real.sin x) := by
  apply one_div_lt_one_div_of_lt
  · have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith [Real.neg_one_le_sin x]
  · push_cast
    linarith

theorem gap2 (x : ℝ) (n : ℕ)
    (hx : x ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) (hn : 2 ≤ n) :
    0 < 1 / ((n : ℝ) + Real.sin x) := by
  apply one_div_pos.mpr
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  linarith [Real.neg_one_le_sin x]

theorem gap3 (x : ℝ) (n : ℕ)
    (hx : x ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) (hn : 2 ≤ n) :
    1 / ((n : ℝ) + Real.sin x) ≤
      1 / (((n - 1 : ℕ) : ℝ)) := by
  have hn1 : 1 ≤ n := (by norm_num : 1 ≤ 2).trans hn
  have hnm1 : (0 : ℝ) < (n - 1 : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hn
  apply one_div_le_one_div_of_le hnm1
  rw [Nat.cast_sub hn1]
  norm_num
  linarith [Real.neg_one_le_sin x]

theorem gap4 (n : ℕ) (hn : 2 ≤ n) :
    0 < 1 / (((n - 1 : ℕ) : ℝ)) := by
  apply one_div_pos.mpr
  exact_mod_cast Nat.sub_pos_of_lt hn

theorem gap5 (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + Real.sin x))
      atTop (nhds 0) := by
  simpa [one_div] using
    (tendsto_atTop_add_const_right atTop (Real.sin x)
      tendsto_natCast_atTop_atTop).inv_tendsto_atTop

theorem gap6 (n : ℕ) :
    |∑ k ∈ Finset.Icc 1 n, (-1 : ℝ) ^ k| ≤ 1 := by
  rw [← Finset.Ico_succ_right_eq_Icc]
  change |∑ k ∈ Finset.Ico 1 (n + 1), (-1 : ℝ) ^ k| ≤ 1
  rw [Finset.sum_Ico_eq_sub _ (Nat.succ_pos n)]
  rw [neg_one_geom_sum]
  split_ifs <;> norm_num

private theorem alternating_error_bound_of_tendsto
    (f : ℕ → ℝ) (hfa : Antitone f) (hf0 : ∀ n, 0 ≤ f n) {l : ℝ}
    (hfl : Tendsto (fun n => ∑ i ∈ Finset.range n, (-1) ^ i * f i) atTop (𝓝 l))
    (n : ℕ) :
    |l - ∑ i ∈ Finset.range n, (-1) ^ i * f i| ≤ f n := by
  have upper := hfa.alternating_series_le_tendsto hfl
  have lower := hfa.tendsto_le_alternating_series hfl
  obtain h | h := Nat.even_or_odd n
  · obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp h
    specialize upper k
    specialize lower k
    simp only [Finset.sum_range_succ, even_two, Even.mul_right, Even.neg_pow,
      one_pow, one_mul] at lower
    rw [abs_sub_le_iff]
    constructor
    · rwa [sub_le_iff_le_add, add_comm]
    · rw [sub_le_iff_le_add, add_comm]
      exact upper.trans (le_add_of_nonneg_right (hf0 (2 * k)))
  · obtain ⟨k, rfl⟩ := odd_iff_exists_bit1.mp h
    specialize upper (k + 1)
    specialize lower k
    rw [Nat.mul_add, Finset.sum_range_succ] at upper
    rw [abs_sub_le_iff]
    constructor
    · rw [sub_le_iff_le_add, add_comm]
      exact lower.trans (le_add_of_nonneg_right (hf0 (2 * k + 1)))
    · simpa [Finset.sum_range_succ, add_comm, pow_add] using upper

private theorem hasSum_conditional_iff_tendsto_range {u : ℕ → ℝ} {l : ℝ} :
    HasSum u l (SummationFilter.conditional ℕ) ↔
      Tendsto (fun n => ∑ i ∈ Finset.range n, u i) atTop (𝓝 l) := by
  simp only [HasSum, SummationFilter.conditional_filter_eq_map_range,
    tendsto_map'_iff]
  rfl

private theorem conditional_series_data (x : ℝ) :
    HasSum (fun k => term (k + 2) x)
        (∑'[SummationFilter.conditional ℕ] k : ℕ, term (k + 2) x)
        (SummationFilter.conditional ℕ) ∧
      ∀ n : ℕ,
        |(∑ k ∈ Finset.range n, term (k + 2) x) -
            ∑'[SummationFilter.conditional ℕ] k : ℕ, term (k + 2) x| ≤
          1 / ((n : ℝ) + 2 + Real.sin x) := by
  let a : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 2 + Real.sin x)
  have ha : Antitone a := by
    intro m n hmn
    dsimp [a]
    apply one_div_le_one_div_of_le (by
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith [Real.neg_one_le_sin x])
    have hmn' : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
    linarith
  have ha0 : ∀ k, 0 ≤ a k := by
    intro k
    dsimp [a]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    apply one_div_nonneg.mpr
    linarith [Real.neg_one_le_sin x]
  have halim : Tendsto a atTop (𝓝 0) := by
    dsimp [a]
    simpa [add_assoc, one_div] using
      (tendsto_atTop_add_const_right atTop (2 + Real.sin x)
        tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  obtain ⟨l, hl⟩ := ha.tendsto_alternating_series_of_tendsto_zero halim
  have hsum (m : ℕ) :
      (∑ k ∈ Finset.range m, term (k + 2) x) =
        ∑ k ∈ Finset.range m, (-1) ^ k * a k := by
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [term, a]
    norm_num [Nat.cast_add, Nat.cast_one, pow_add]
    ring
  have hulim : Tendsto (fun m => ∑ k ∈ Finset.range m, term (k + 2) x)
      atTop (𝓝 l) :=
    hl.congr' (Eventually.of_forall fun m => (hsum m).symm)
  have hu : HasSum (fun k => term (k + 2) x) l
      (SummationFilter.conditional ℕ) :=
    hasSum_conditional_iff_tendsto_range.mpr hulim
  have htsum : (∑'[SummationFilter.conditional ℕ] k : ℕ, term (k + 2) x) = l :=
    hu.tsum_eq
  constructor
  · simpa only [htsum] using hu
  · intro n
    rw [htsum, hsum n, abs_sub_comm]
    simpa [a] using alternating_error_bound_of_tendsto a ha ha0 hl n

theorem gap7 :
    SeriesUniformlyConvergesOn
      (fun n x => term (n + 2) x)
      (Set.Icc (0 : ℝ) (2 * Real.pi))
      (fun x => ∑'[SummationFilter.conditional ℕ] n : ℕ, term (n + 2) x) := by
  have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [one_div] using
      (tendsto_atTop_add_const_right atTop (1 : ℝ)
        tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hlim).2 ε hε)
  refine ⟨N, fun n hn x hx => ?_⟩
  have herr := (conditional_series_data x).2 (n + 1)
  have hcoef :
      1 / (((n + 1 : ℕ) : ℝ) + 2 + Real.sin x) ≤ 1 / ((n : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    norm_num [Nat.cast_add, Nat.cast_one]
    linarith [Real.neg_one_le_sin x]
  exact herr.trans_lt (hcoef.trans_lt (hN n hn))

theorem gap8 :
    SeriesUniformlyConvergesOn
      (fun n x => term (n + 2) x)
      (Set.Icc (0 : ℝ) (2 * Real.pi))
      (fun x => ∑'[SummationFilter.conditional ℕ] n : ℕ, term (n + 2) x) := by
  exact gap7

end

end ProofGap.Exercise2778
