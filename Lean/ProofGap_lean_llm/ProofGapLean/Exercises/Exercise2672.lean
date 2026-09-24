import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2672

noncomputable section

open Filter
open scoped BigOperators
open scoped Topology

def term (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ Nat.sqrt n / n

def blockWeight (k : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc (k ^ 2) ((k + 1) ^ 2 - 1), 1 / (n : ℝ)

def blockTerm (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * blockWeight k

def ConditionallySummable (f : ℕ → ℝ) : Prop :=
  ProofGap.SeriesConverges f ∧ ¬ Summable (fun n : ℕ => |f n|)

private theorem seriesConverges_of_tendsto_sum_range {f : ℕ → ℝ}
    (h : ∃ l, Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop (𝓝 l)) :
    ProofGap.SeriesConverges f := by
  rcases h with ⟨l, hl⟩
  refine ⟨l, ?_⟩
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range]
  exact hl

private theorem blockWeight_nonneg (k : ℕ) : 0 ≤ blockWeight k := by
  apply Finset.sum_nonneg
  intro n hn
  positivity

private theorem blockWeight_lower (k : ℕ) (hk : 1 ≤ k) :
    2 / (k + 1 : ℝ) < blockWeight k := by
  let a := k ^ 2
  let m := k ^ 2 + k
  let b := (k + 1) ^ 2 - 1
  let s₁ := Finset.Icc a m
  let s₂ := Finset.Ioc m b
  have hb : b = k ^ 2 + 2 * k := by
    dsimp [b]
    rw [show (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 by ring]
    omega
  have ham : a ≤ m := by simp [a, m]
  have hmb : m ≤ b := by
    rw [hb]
    simp only [m]
    omega
  have hmb' : m < b := by
    rw [hb]
    simp only [m]
    omega
  have hdisj : Disjoint s₁ s₂ := by
    rw [Finset.disjoint_left]
    intro n hn₁ hn₂
    simp only [s₁, Finset.mem_Icc] at hn₁
    simp only [s₂, Finset.mem_Ioc] at hn₂
    omega
  have hunion : s₁ ∪ s₂ = Finset.Icc a b := by
    ext n
    simp only [Finset.mem_union, s₁, s₂, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have ha_pos : 0 < a := by simp [a]; positivity
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast lt_of_lt_of_le ha_pos ham
  have hk1_pos : (0 : ℝ) < (k + 1 : ℕ) ^ 2 := by positivity
  have h₁ : s₁.card • (1 / (m : ℝ)) ≤ ∑ n ∈ s₁, 1 / (n : ℝ) := by
    apply Finset.card_nsmul_le_sum
    intro n hn
    apply one_div_le_one_div_of_le
    · exact_mod_cast ha_pos.trans_le (Finset.mem_Icc.mp hn).1
    · exact_mod_cast (Finset.mem_Icc.mp hn).2
  have h₂ : s₂.card • (1 / ((k + 1 : ℕ) ^ 2 : ℝ)) ≤
      ∑ n ∈ s₂, 1 / (n : ℝ) := by
    apply Finset.card_nsmul_le_sum
    intro n hn
    apply one_div_le_one_div_of_le
    · exact_mod_cast ha_pos.trans_le (ham.trans (Finset.mem_Ioc.mp hn).1.le)
    · exact_mod_cast (Finset.mem_Ioc.mp hn).2.trans (Nat.sub_le _ _)
  have hcard₁ : s₁.card = k + 1 := by
    simp [s₁, a, m, Nat.card_Icc]
    omega
  have hcard₂ : s₂.card = k := by
    simp [s₂, m, hb, Nat.card_Ioc]
    omega
  have hnumeric :
      2 / (k + 1 : ℝ) <
        (k + 1 : ℕ) • (1 / (m : ℝ)) + k • (1 / ((k + 1 : ℕ) ^ 2 : ℝ)) := by
    simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, m]
    push_cast
    field_simp
    nlinarith
  calc
    2 / (k + 1 : ℝ) <
        s₁.card • (1 / (m : ℝ)) + s₂.card • (1 / ((k + 1 : ℕ) ^ 2 : ℝ)) := by
      rwa [hcard₁, hcard₂]
    _ ≤ (∑ n ∈ s₁, 1 / (n : ℝ)) + ∑ n ∈ s₂, 1 / (n : ℝ) := add_le_add h₁ h₂
    _ = blockWeight k := by
      rw [← Finset.sum_union hdisj, hunion]
      simp [blockWeight, a, b]

private theorem blockWeight_upper (k : ℕ) (hk : 1 ≤ k) :
    blockWeight k < 2 / (k : ℝ) := by
  let a := k ^ 2
  let m := k ^ 2 + k
  let b := (k + 1) ^ 2 - 1
  let s₁ := Finset.Ico a m
  let s₂ := Finset.Icc m b
  have hb : b = k ^ 2 + 2 * k := by
    dsimp [b]
    rw [show (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 by ring]
    omega
  have ham : a ≤ m := by simp [a, m]
  have hmb : m ≤ b := by
    rw [hb]
    simp only [m]
    omega
  have hmb' : m < b := by
    rw [hb]
    simp only [m]
    omega
  have hdisj : Disjoint s₁ s₂ := by
    rw [Finset.disjoint_left]
    intro n hn₁ hn₂
    simp only [s₁, Finset.mem_Ico] at hn₁
    simp only [s₂, Finset.mem_Icc] at hn₂
    omega
  have hunion : s₁ ∪ s₂ = Finset.Icc a b := by
    ext n
    simp only [Finset.mem_union, s₁, s₂, Finset.mem_Ico, Finset.mem_Icc]
    omega
  have ha_pos : (0 : ℝ) < a := by simp [a]; positivity
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast lt_of_lt_of_le (by exact_mod_cast ha_pos) ham
  have h₁ : (∑ n ∈ s₁, 1 / (n : ℝ)) ≤ s₁.card • (1 / (a : ℝ)) := by
    apply Finset.sum_le_card_nsmul
    intro n hn
    apply one_div_le_one_div_of_le ha_pos
    exact_mod_cast (Finset.mem_Ico.mp hn).1
  have h₂ : (∑ n ∈ s₂, 1 / (n : ℝ)) < s₂.card • (1 / (m : ℝ)) := by
    calc
      (∑ n ∈ s₂, 1 / (n : ℝ)) < ∑ _n ∈ s₂, 1 / (m : ℝ) := by
        apply Finset.sum_lt_sum
        · intro n hn
          apply one_div_le_one_div_of_le hm_pos
          exact_mod_cast (Finset.mem_Icc.mp hn).1
        · refine ⟨b, ?_, ?_⟩
          · exact Finset.mem_Icc.mpr ⟨hmb, le_rfl⟩
          · apply one_div_lt_one_div_of_lt hm_pos
            exact_mod_cast hmb'
      _ = s₂.card • (1 / (m : ℝ)) := by simp
  have hcard₁ : s₁.card = k := by
    simp [s₁, a, m, Nat.card_Ico]
  have hcard₂ : s₂.card = k + 1 := by
    simp [s₂, m, hb, Nat.card_Icc]
    omega
  calc
    blockWeight k = (∑ n ∈ s₁, 1 / (n : ℝ)) + ∑ n ∈ s₂, 1 / (n : ℝ) := by
      rw [← Finset.sum_union hdisj, hunion]
      simp [blockWeight, a, b]
    _ < s₁.card • (1 / (a : ℝ)) + s₂.card • (1 / (m : ℝ)) := add_lt_add_of_le_of_lt h₁ h₂
    _ = 2 / (k : ℝ) := by
      rw [hcard₁, hcard₂]
      simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, a, m]
      push_cast
      field_simp
      ring

private theorem not_summable_term_shift :
    ¬ Summable (fun n : ℕ => term (n + 1)) := by
  intro h
  have habs := h.abs
  have hh : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) := by
    refine habs.congr fun n => ?_
    simp [term, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ n + 1 by positivity)]
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ)) :=
    (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 1).mp
      (by simpa using hh)
  exact Real.not_summable_one_div_natCast hbase

private theorem not_summable_block_shift :
    ¬ Summable (fun k : ℕ => blockTerm (k + 1)) := by
  intro h
  have habs := h.abs
  have hw : Summable (fun k : ℕ => blockWeight (k + 1)) := by
    refine habs.congr fun k => ?_
    simp [blockTerm, abs_mul, blockWeight_nonneg]
  have hh : Summable (fun k : ℕ => 1 / ((k + 2 : ℕ) : ℝ)) :=
    hw.of_nonneg_of_le (fun k => by positivity) fun k => by
      have hlower := blockWeight_lower (k + 1) (by omega)
      have hlower' : 2 / ((k + 2 : ℕ) : ℝ) < blockWeight (k + 1) := by
        convert hlower using 1 <;> push_cast <;> ring
      have hhalf : 1 / ((k + 2 : ℕ) : ℝ) ≤ 2 / ((k + 2 : ℕ) : ℝ) := by
        gcongr <;> norm_num
      exact hhalf.trans hlower'.le
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ)) :=
    (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 2).mp
      (by simpa using hh)
  exact Real.not_summable_one_div_natCast hbase

private theorem sqrt_eq_of_mem_block {k n : ℕ} (hlo : k ^ 2 ≤ n)
    (hhi : n < (k + 1) ^ 2) : Nat.sqrt n = k := by
  have hle : k ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by simpa [pow_two] using hlo)
  have hlt : Nat.sqrt n < k + 1 := Nat.sqrt_lt.mpr (by simpa [pow_two] using hhi)
  omega

private theorem sum_term_block (k : ℕ) :
    (∑ n ∈ Finset.Ico ((k + 1) ^ 2 - 1) ((k + 2) ^ 2 - 1), term (n + 1)) =
      blockTerm (k + 1) := by
  rw [blockTerm, blockWeight, Finset.mul_sum]
  have hk2 : k + 1 + 1 = k + 2 := by omega
  simp only [hk2]
  apply Finset.sum_bij (fun n _ => n + 1)
  · intro n hn
    simp only [Finset.mem_Ico] at hn
    apply Finset.mem_Icc.mpr
    constructor <;> omega
  · intro n₁ hn₁ n₂ hn₂ h
    omega
  · intro m hm
    refine ⟨m - 1, ?_, ?_⟩
    · simp only [Finset.mem_Ico]
      have hm' := Finset.mem_Icc.mp hm
      have hsqpos : 0 < (k + 1) ^ 2 := by positivity
      constructor <;> omega
    · have hm' := Finset.mem_Icc.mp hm
      have hmpos : 0 < m := lt_of_lt_of_le (by positivity) hm'.1
      omega
  · intro n hn
    have hn' := Finset.mem_Ico.mp hn
    have hsqrt : Nat.sqrt (n + 1) = k + 1 := by
      apply sqrt_eq_of_mem_block
      · omega
      · have hhi : n + 1 < (k + 2) ^ 2 := by omega
        simpa only [hk2] using hhi
    simp [term, hsqrt, div_eq_mul_inv]

private theorem partial_sum_at_block_end (K : ℕ) :
    (∑ n ∈ Finset.range ((K + 1) ^ 2 - 1), term (n + 1)) =
      ∑ k ∈ Finset.range K, blockTerm (k + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
      have hends : (K + 1) ^ 2 - 1 ≤ (K + 2) ^ 2 - 1 := by
        have hsq : (K + 2) ^ 2 = (K + 1) ^ 2 + 2 * (K + 1) + 1 := by ring
        omega
      calc
        (∑ n ∈ Finset.range ((K + 2) ^ 2 - 1), term (n + 1)) =
            (∑ n ∈ Finset.range ((K + 1) ^ 2 - 1), term (n + 1)) +
              ∑ n ∈ Finset.Ico ((K + 1) ^ 2 - 1) ((K + 2) ^ 2 - 1),
                term (n + 1) := (Finset.sum_range_add_sum_Ico _ hends).symm
        _ = (∑ k ∈ Finset.range K, blockTerm (k + 1)) + blockTerm (K + 1) := by
          rw [ih, sum_term_block]
        _ = ∑ k ∈ Finset.range (K + 1), blockTerm (k + 1) := by
          rw [Finset.sum_range_succ]

private theorem tendsto_nat_sqrt_atTop : Tendsto Nat.sqrt atTop atTop := by
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [eventually_ge_atTop (k ^ 2)] with n hn
  exact Nat.le_sqrt.mpr (by simpa [pow_two] using hn)

private theorem norm_partial_sum_sub_block_sum_le (N : ℕ) :
    ‖(∑ n ∈ Finset.range N, term (n + 1)) -
        ∑ k ∈ Finset.range (Nat.sqrt N), blockTerm (k + 1)‖ ≤
      blockWeight (Nat.sqrt N) := by
  let K := Nat.sqrt N
  let E := (K + 1) ^ 2 - 1
  have hKsq : K ^ 2 ≤ N := by
    simpa [K, pow_two] using Nat.sqrt_le N
  have hNlt : N < (K + 1) ^ 2 := by
    simpa [K, pow_two] using Nat.lt_succ_sqrt N
  have hNE : N ≤ E := by simp only [E]; omega
  have htail :
      (∑ n ∈ Finset.range N, term (n + 1)) -
          ∑ k ∈ Finset.range K, blockTerm (k + 1) =
        -(∑ n ∈ Finset.Ico N E, term (n + 1)) := by
    rw [← partial_sum_at_block_end K, Finset.sum_Ico_eq_sub _ hNE]
    ring
  have hreindex :
      (∑ n ∈ Finset.Ico N E, ‖term (n + 1)‖) =
        ∑ m ∈ Finset.Ioc N E, 1 / (m : ℝ) := by
    apply Finset.sum_bij (fun n _ => n + 1)
    · intro n hn
      have hn' := Finset.mem_Ico.mp hn
      exact Finset.mem_Ioc.mpr (by omega)
    · intro n₁ hn₁ n₂ hn₂ h
      omega
    · intro m hm
      refine ⟨m - 1, ?_, ?_⟩
      · simp only [Finset.mem_Ico]
        have hm' := Finset.mem_Ioc.mp hm
        constructor <;> omega
      · have hm' := Finset.mem_Ioc.mp hm
        omega
    · intro n hn
      simp [term, Real.norm_eq_abs, abs_div,
        abs_of_pos (show (0 : ℝ) < n + 1 by positivity)]
  have hsubset : Finset.Ioc N E ⊆ Finset.Icc (K ^ 2) E := by
    intro m hm
    have hm' := Finset.mem_Ioc.mp hm
    exact Finset.mem_Icc.mpr ⟨hKsq.trans hm'.1.le, hm'.2⟩
  rw [show Nat.sqrt N = K by rfl, htail, norm_neg]
  calc
    ‖∑ n ∈ Finset.Ico N E, term (n + 1)‖ ≤
        ∑ n ∈ Finset.Ico N E, ‖term (n + 1)‖ := norm_sum_le _ _
    _ = ∑ m ∈ Finset.Ioc N E, 1 / (m : ℝ) := hreindex
    _ ≤ ∑ m ∈ Finset.Icc (K ^ 2) E, 1 / (m : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => by positivity)
    _ = blockWeight K := by simp [blockWeight, E]

theorem gap1 :
    ∀ s : ℝ,
      HasSum (fun n : ℕ => term (n + 1)) s ↔
        HasSum (fun k : ℕ => blockTerm (k + 1)) s := by
  intro s
  constructor
  · intro h
    exact (not_summable_term_shift h.summable).elim
  · intro h
    exact (not_summable_block_shift h.summable).elim

theorem gap2 :
    ∀ k : ℕ, 1 ≤ k → 2 / (k + 1 : ℝ) < blockWeight k := by
  exact blockWeight_lower

theorem gap3 :
    ∀ k : ℕ, 1 ≤ k → blockWeight k < 2 / (k : ℝ) := by
  exact blockWeight_upper

theorem gap4 :
    ∀ k : ℕ, 1 ≤ k → 2 / (k + 1 : ℝ) < 2 / (k : ℝ) := by
  intro k hk
  gcongr
  exact_mod_cast Nat.lt_succ_self k

theorem gap5 :
    Tendsto (fun k : ℕ => blockWeight (k + 1)) atTop (nhds 0) := by
  have hupper : Tendsto (fun k : ℕ => 2 / (k + 1 : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).mul
        (tendsto_inv_atTop_zero.comp
          (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (.of_forall fun k => blockWeight_nonneg (k + 1)) (.of_forall fun k => ?_)
  have hu := (blockWeight_upper (k + 1) (by omega)).le
  norm_num [Nat.cast_add, Nat.cast_one] at hu ⊢
  exact hu

theorem gap6 :
    Antitone (fun k : ℕ => blockWeight (k + 1)) := by
  apply antitone_nat_of_succ_le
  intro k
  have hu := (blockWeight_upper (k + 2) (by omega)).le
  have hl := (blockWeight_lower (k + 1) (by omega)).le
  have hu' : blockWeight (k + 2) ≤ 2 / ((k + 2 : ℕ) : ℝ) := by
    convert hu using 1 <;> push_cast <;> ring
  have hl' : 2 / ((k + 2 : ℕ) : ℝ) ≤ blockWeight (k + 1) := by
    convert hl using 1 <;> push_cast <;> ring
  exact hu'.trans hl'

theorem gap7 :
    ProofGap.SeriesConverges (fun k : ℕ => blockTerm (k + 1)) := by
  have hAlt : ProofGap.SeriesConverges
      (fun k : ℕ => (-1 : ℝ) ^ k * blockWeight (k + 1)) :=
    seriesConverges_of_tendsto_sum_range
      (gap6.tendsto_alternating_series_of_tendsto_zero gap5)
  refine hAlt.neg.congr fun k => ?_
  simp [blockTerm, pow_succ]

theorem gap8 :
    ProofGap.SeriesConverges (fun n : ℕ => term (n + 1)) := by
  have hsqrtCast : Tendsto (fun N : ℕ => (Nat.sqrt N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_nat_sqrt_atTop
  have hupper : Tendsto (fun N : ℕ => 2 / (Nat.sqrt N : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).mul
        (tendsto_inv_atTop_zero.comp hsqrtCast)
  have hweight : Tendsto (fun N : ℕ => blockWeight (Nat.sqrt N)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (.of_forall fun N => blockWeight_nonneg (Nat.sqrt N)) ?_
    filter_upwards [tendsto_nat_sqrt_atTop.eventually (eventually_ge_atTop 1)] with N hN
    exact (gap3 (Nat.sqrt N) hN).le
  rcases gap7 with ⟨l, hl⟩
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff] at hl
  simp only [Function.comp_def] at hl
  have hblocks : Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range (Nat.sqrt N), blockTerm (k + 1))
      atTop (𝓝 l) := hl.comp tendsto_nat_sqrt_atTop
  have herror : Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.range N, term (n + 1)) -
        ∑ k ∈ Finset.range (Nat.sqrt N), blockTerm (k + 1))
      atTop (𝓝 0) :=
    squeeze_zero_norm norm_partial_sum_sub_block_sum_le hweight
  apply seriesConverges_of_tendsto_sum_range
  refine ⟨l, ?_⟩
  simpa only [sub_add_cancel, zero_add] using herror.add hblocks

theorem gap9 :
    ¬ Summable (fun n : ℕ => |term (n + 1)|) := by
  intro h
  exact not_summable_term_shift h.of_abs

theorem gap10 :
    ConditionallySummable (fun n : ℕ => term (n + 1)) := by
  exact ⟨gap8, gap9⟩

end

end ProofGap.Exercise2672
