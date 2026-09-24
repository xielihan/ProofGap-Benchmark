import ProofGapLean.Prelude.Analysis
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Normed

namespace ProofGap.Exercise2777

noncomputable section

open Filter
open scoped BigOperators Topology

def term (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ n / ((n : ℝ) + x)

def SeriesUniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s,
    |(∑ k ∈ Finset.range (n + 1), u k x) - f x| < ε

theorem gap1 (n : ℕ) :
    |∑ k ∈ Finset.Icc 1 n, (-1 : ℝ) ^ k| ≤ 1 := by
  rw [← Finset.Ico_succ_right_eq_Icc]
  change |∑ k ∈ Finset.Ico 1 (n + 1), (-1 : ℝ) ^ k| ≤ 1
  rw [Finset.sum_Ico_eq_sub _ (Nat.succ_pos n)]
  rw [neg_one_geom_sum]
  split_ifs <;> norm_num

theorem gap2 (x : ℝ) (n : ℕ) (hx : 0 < x) (hn : 1 ≤ n) :
    1 / ((n : ℝ) + x) < 1 / (n : ℝ) := by
  exact one_div_lt_one_div_of_lt (by exact_mod_cast (zero_lt_one.trans_le hn)) (by linarith)

theorem gap3 (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + x))
      atTop (nhds 0) := by
  simpa [one_div] using
    (tendsto_atTop_add_const_right atTop x tendsto_natCast_atTop_atTop).inv_tendsto_atTop

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
    tendsto_map'_iff, Function.comp_apply]
  rfl

private theorem conditional_error_bound (x : ℝ) (hx : 0 < x) (n : ℕ) :
    |(∑ k ∈ Finset.range n, term (k + 1) x) -
        ∑'[SummationFilter.conditional ℕ] k : ℕ, term (k + 1) x| ≤
      1 / ((n : ℝ) + 1 + x) := by
  let a : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1 + x)
  have ha : Antitone a := by
    intro m n hmn
    dsimp [a]
    apply one_div_le_one_div_of_le (by positivity)
    have hmn' : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
    linarith
  have ha0 : ∀ k, 0 ≤ a k := by
    intro k
    dsimp [a]
    positivity
  have halim : Tendsto a atTop (𝓝 0) := by
    dsimp [a]
    simpa [add_assoc, one_div] using
      (tendsto_atTop_add_const_right atTop (1 + x)
        tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  obtain ⟨l, hl⟩ := ha.tendsto_alternating_series_of_tendsto_zero halim
  have hsum (m : ℕ) :
      (∑ k ∈ Finset.range m, term (k + 1) x) =
        -(∑ k ∈ Finset.range m, (-1) ^ k * a k) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [term, a]
    rw [pow_succ]
    norm_num [Nat.cast_add, Nat.cast_one]
    ring
  have hulim :
      Tendsto (fun m => ∑ k ∈ Finset.range m, term (k + 1) x)
        atTop (𝓝 (-l)) :=
    hl.neg.congr' (Eventually.of_forall fun m => (hsum m).symm)
  have hu : HasSum (fun k => term (k + 1) x) (-l)
      (SummationFilter.conditional ℕ) :=
    hasSum_conditional_iff_tendsto_range.mpr hulim
  rw [hu.tsum_eq, hsum n]
  rw [sub_neg_eq_add]
  change |- (∑ k ∈ Finset.range n, (-1) ^ k * a k) + l| ≤ a n
  convert alternating_error_bound_of_tendsto a ha ha0 hl n using 1 <;> ring

theorem gap4 :
    SeriesUniformlyConvergesOn
      (fun n x => term (n + 1) x)
      (Set.Ioi (0 : ℝ))
      (fun x => ∑'[SummationFilter.conditional ℕ] n : ℕ, term (n + 1) x) := by
  have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [one_div] using
      (tendsto_atTop_add_const_right atTop (1 : ℝ)
        tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hlim).2 ε hε)
  refine ⟨N, fun n hn x hx => ?_⟩
  have hxpos : 0 < x := hx
  have herr := conditional_error_bound x hx (n + 1)
  have hcoef : 1 / (((n + 1 : ℕ) : ℝ) + 1 + x) ≤ 1 / ((n : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    norm_num [Nat.cast_add, Nat.cast_one]
    linarith
  exact herr.trans_lt (hcoef.trans_lt (hN n hn))

theorem gap5 :
    SeriesUniformlyConvergesOn
      (fun n x => term (n + 1) x)
      (Set.Ioi (0 : ℝ))
      (fun x => ∑'[SummationFilter.conditional ℕ] n : ℕ, term (n + 1) x) := by
  exact gap4

end

end ProofGap.Exercise2777
