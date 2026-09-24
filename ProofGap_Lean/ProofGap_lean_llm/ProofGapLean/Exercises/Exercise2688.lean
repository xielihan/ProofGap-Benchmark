import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Positivity
import Mathlib.Order.Filter.AtTopBot.Defs

namespace ProofGap.Exercise2688

noncomputable section

open Filter
open scoped BigOperators

def term (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ Int.floor (Real.log n) / (n : ℝ)

def logBlock (k : ℕ) : Finset ℕ :=
  (Finset.range (⌊Real.exp (k + 1)⌋₊ + 1)).filter
    (fun n => 1 ≤ n ∧ Int.floor (Real.log n) = k)

def blockSize (k : ℕ) : ℕ :=
  (logBlock k).card

def blockTerm (k : ℕ) : ℝ :=
  ∑ n ∈ logBlock k, term n

def amplitude (k : ℕ) : ℝ :=
  ∑ n ∈ logBlock k, 1 / (n : ℝ)

def epsilon : ℝ :=
  (Real.exp 1 - 1) / (4 * Real.exp 1)

private theorem tail_sum_small {f : ℕ → ℝ} (hf : Summable f) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ N : ℕ, ∀ s : Finset ℕ, (∀ n ∈ s, N ≤ n) →
      |∑ n ∈ s, f n| < ε := by
  have hev : ∀ᶠ s : Finset ℕ in atTop,
      dist (∑ n ∈ s, f n) (∑' n, f n) < ε / 2 :=
    (Metric.tendsto_nhds.1 hf.hasSum) (ε / 2) (by linarith)
  obtain ⟨u, hu⟩ := eventually_atTop.1 hev
  have hsmall : ∀ s : Finset ℕ, Disjoint u s →
      |∑ n ∈ s, f n| < ε := by
    intro s hdisj
    have hbig := hu (u ∪ s) (by
      intro n hn
      simp [hn])
    have hbase := hu u le_rfl
    rw [Finset.sum_union hdisj] at hbig
    rw [Real.dist_eq] at hbig hbase
    have halg :
        (∑ n ∈ s, f n) =
          (((∑ n ∈ u, f n) + (∑ n ∈ s, f n)) -
              (∑' n, f n)) -
            ((∑ n ∈ u, f n) - (∑' n, f n)) := by
      ring
    rw [halg]
    calc
      |(((∑ n ∈ u, f n) + (∑ n ∈ s, f n)) -
          (∑' n, f n)) -
        ((∑ n ∈ u, f n) - (∑' n, f n))| ≤
          |((∑ n ∈ u, f n) + (∑ n ∈ s, f n)) -
            (∑' n, f n)| +
          |(∑ n ∈ u, f n) - (∑' n, f n)| := abs_sub _ _
      _ < ε / 2 + ε / 2 := add_lt_add hbig hbase
      _ = ε := by ring
  by_cases hempty : u = ∅
  · refine ⟨0, ?_⟩
    intro s hs
    apply hsmall s
    simp [hempty]
  · have hne : u.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    refine ⟨u.max' hne + 1, ?_⟩
    intro s hs
    apply hsmall s
    rw [Finset.disjoint_left]
    intro n hnu hns
    have hnle : n ≤ u.max' hne := Finset.le_max' u n hnu
    have hnlarge : u.max' hne + 1 ≤ n := hs n hns
    omega

theorem gap1 :
    ∀ k n : ℕ, n ∈ logBlock k →
      Real.exp k ≤ n ∧ (n : ℝ) < Real.exp 1 * Real.exp k := by
  intro k n hn
  rcases Finset.mem_filter.mp hn with ⟨hrange, hnpos, hfloor⟩
  have hnpos' : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hlowerLog : (k : ℝ) ≤ Real.log (n : ℝ) := by
    have h := Int.floor_le (Real.log (n : ℝ))
    rw [hfloor] at h
    simpa using h
  have hupperLog : Real.log (n : ℝ) < (k : ℝ) + 1 := by
    have h := Int.lt_floor_add_one (Real.log (n : ℝ))
    rw [hfloor] at h
    simpa using h
  constructor
  · have h := Real.exp_le_exp.mpr hlowerLog
    simpa [Real.exp_log hnpos'] using h
  · have h := Real.exp_lt_exp.mpr hupperLog
    rw [Real.exp_log hnpos'] at h
    simpa [Real.exp_add, mul_comm] using h

theorem gap2 :
    ∃ p : ℕ → ℕ, ∀ k : ℕ, (logBlock k).card = p k := by
  exact ⟨fun k => (logBlock k).card, fun k => rfl⟩

theorem gap3 :
    Tendsto
      (fun k : ℕ => (blockSize k : ℝ) / Real.exp k)
      atTop (nhds (Real.exp 1 - 1)) := by
  have hblock : ∀ k : ℕ,
      logBlock k = Finset.Ico ⌈Real.exp (k : ℝ)⌉₊ ⌈Real.exp ((k + 1 : ℕ) : ℝ)⌉₊ := by
    intro k
    ext n
    constructor
    · intro hn
      have hb := gap1 k n hn
      have hlower : ⌈Real.exp (k : ℝ)⌉₊ ≤ n :=
        Nat.ceil_le.mpr hb.1
      have hupper : n < ⌈Real.exp ((k + 1 : ℕ) : ℝ)⌉₊ := by
        apply Nat.lt_ceil.mpr
        simpa [Nat.cast_add, Real.exp_add, mul_comm] using hb.2
      exact Finset.mem_Ico.mpr ⟨hlower, hupper⟩
    · intro hn
      rcases Finset.mem_Ico.mp hn with ⟨hlowerNat, hupperNat⟩
      have hlower : Real.exp (k : ℝ) ≤ (n : ℝ) :=
        Nat.ceil_le.mp hlowerNat
      have hupper : (n : ℝ) < Real.exp ((k + 1 : ℕ) : ℝ) :=
        Nat.lt_ceil.mp hupperNat
      have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hlower
      have hlogLower : (k : ℝ) ≤ Real.log (n : ℝ) := by
        apply Real.exp_le_exp.mp
        simpa [Real.exp_log hnpos] using hlower
      have hlogUpper : Real.log (n : ℝ) < (k : ℝ) + 1 := by
        apply Real.exp_lt_exp.mp
        rw [Real.exp_log hnpos]
        simpa [Nat.cast_add] using hupper
      have hfloor : Int.floor (Real.log (n : ℝ)) = (k : ℤ) := by
        rw [Int.floor_eq_iff]
        constructor <;> simpa using ‹_›
      have hupper' : (n : ℝ) < Real.exp ((k : ℝ) + 1) := by
        simpa [Nat.cast_add] using hupper
      have hnfloor : n ≤ ⌊Real.exp ((k : ℝ) + 1)⌋₊ :=
        Nat.le_floor hupper'.le
      apply Finset.mem_filter.mpr
      constructor
      · simp only [Finset.mem_range]
        exact Nat.lt_succ_of_le hnfloor
      constructor
      · exact_mod_cast hnpos
      · simpa using hfloor
  have hexp : Tendsto (fun k : ℕ => Real.exp (k : ℝ)) atTop atTop :=
    Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun k : ℕ => (Real.exp (k : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hexp
  have hceil : Tendsto
      (fun k : ℕ => (⌈Real.exp (k : ℝ)⌉₊ : ℝ) / Real.exp (k : ℝ))
      atTop (nhds 1) := by
    have hu : Tendsto (fun k : ℕ => 1 + (Real.exp (k : ℝ))⁻¹)
        atTop (nhds 1) := by
      simpa using (tendsto_const_nhds.add hinv)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds hu
    · filter_upwards [] with k
      apply (le_div_iff₀ (Real.exp_pos _)).2
      simpa using (Nat.le_ceil (Real.exp (k : ℝ)))
    · filter_upwards [] with k
      apply (div_le_iff₀ (Real.exp_pos _)).2
      have hc' : (⌈Real.exp (k : ℝ)⌉₊ : ℝ) ≤ Real.exp (k : ℝ) + 1 :=
        (Nat.ceil_lt_add_one (Real.exp_pos (k : ℝ)).le).le
      calc
        (⌈Real.exp (k : ℝ)⌉₊ : ℝ) ≤ Real.exp (k : ℝ) + 1 := hc'
        _ = (1 + (Real.exp (k : ℝ))⁻¹) * Real.exp (k : ℝ) := by
          simp [add_mul, Real.exp_ne_zero]
  have hshift : Tendsto (fun k : ℕ => k + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with a ha
    omega
  have hlim : Tendsto
      (fun k : ℕ =>
        ((⌈Real.exp ((k + 1 : ℕ) : ℝ)⌉₊ : ℝ) /
            Real.exp ((k + 1 : ℕ) : ℝ)) * Real.exp 1 -
          (⌈Real.exp (k : ℝ)⌉₊ : ℝ) / Real.exp (k : ℝ))
      atTop (nhds (Real.exp 1 - 1)) := by
    simpa using ((hceil.comp hshift).mul tendsto_const_nhds).sub hceil
  have hfun :
      (fun k : ℕ => (blockSize k : ℝ) / Real.exp (k : ℝ)) =
      (fun k : ℕ =>
        ((⌈Real.exp ((k + 1 : ℕ) : ℝ)⌉₊ : ℝ) /
            Real.exp ((k + 1 : ℕ) : ℝ)) * Real.exp 1 -
          (⌈Real.exp (k : ℝ)⌉₊ : ℝ) / Real.exp (k : ℝ)) := by
    funext k
    have hceilmono : ⌈Real.exp (k : ℝ)⌉₊ ≤
        ⌈Real.exp ((k + 1 : ℕ) : ℝ)⌉₊ := by
      apply Nat.ceil_mono
      apply Real.exp_le_exp.mpr
      norm_num
    rw [blockSize, hblock, Nat.card_Ico, Nat.cast_sub hceilmono]
    have headd : Real.exp ((k + 1 : ℕ) : ℝ) =
        Real.exp (k : ℝ) * Real.exp 1 := by
      simp [Nat.cast_add, Real.exp_add]
    rw [headd]
    field_simp [Real.exp_ne_zero]
  rw [hfun]
  exact hlim

theorem gap4 :
    ∀ k : ℕ, blockTerm k = (-1 : ℝ) ^ k * amplitude k := by
  intro k
  rw [blockTerm, amplitude, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hfloor := (Finset.mem_filter.mp hn).2.2
  rw [term, hfloor, zpow_natCast]
  ring

theorem gap5 :
    ∀ k : ℕ,
      amplitude k ≥ (blockSize k : ℝ) / (Real.exp 1 * Real.exp k) := by
  intro k
  rw [amplitude]
  calc
    (∑ n ∈ logBlock k, 1 / (n : ℝ)) ≥
        ∑ n ∈ logBlock k, 1 / (Real.exp 1 * Real.exp k) := by
      apply Finset.sum_le_sum
      intro n hn
      have hb := (gap1 k n hn).2.le
      have hnpos : 0 < (n : ℝ) := by
        have h := (Finset.mem_filter.mp hn).2.1
        exact_mod_cast h
      exact one_div_le_one_div_of_le hnpos hb
    _ = (blockSize k : ℝ) / (Real.exp 1 * Real.exp k) := by
      simp [blockSize, div_eq_mul_inv]

theorem gap6 :
    ∀ k : ℕ,
      (blockSize k : ℝ) / (Real.exp 1 * Real.exp k) =
        ((blockSize k : ℝ) / Real.exp k) / Real.exp 1 := by
  intro k
  field_simp [Real.exp_ne_zero]

theorem gap7 :
    ∃ K : ℕ, ∀ k ≥ K,
      (blockSize k : ℝ) / (Real.exp 1 * Real.exp k) ≥
        (Real.exp 1 - 1) / (2 * Real.exp 1) := by
  have he : 1 < Real.exp 1 := by
    simpa using Real.exp_lt_exp.mpr (show (0 : ℝ) < 1 by norm_num)
  have hlt : (Real.exp 1 - 1) / 2 < Real.exp 1 - 1 := by linarith
  have hev : ∀ᶠ k : ℕ in atTop,
      (Real.exp 1 - 1) / 2 < (blockSize k : ℝ) / Real.exp k :=
    (tendsto_order.1 gap3).1 _ hlt
  rcases eventually_atTop.1 hev with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk
  rw [gap6]
  calc
    (blockSize k : ℝ) / Real.exp k / Real.exp 1 ≥
        ((Real.exp 1 - 1) / 2) / Real.exp 1 :=
      (div_le_div_iff_of_pos_right (Real.exp_pos 1)).2 (hK k hk).le
    _ = (Real.exp 1 - 1) / (2 * Real.exp 1) := by ring

theorem gap8 :
    ∃ K : ℕ, ∀ k ≥ K,
      amplitude k ≥ (Real.exp 1 - 1) / (2 * Real.exp 1) := by
  obtain ⟨K, hK⟩ := gap7
  exact ⟨K, fun k hk => le_trans (hK k hk) (gap5 k)⟩

theorem gap9 (hconv : Summable (fun n : ℕ => term (n + 1))) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ m n : ℕ, N₀ ≤ m → m ≤ n →
        |∑ j ∈ Finset.Icc m n, term j| < ε := by
  intro ε hε
  have hterm : Summable term :=
    (summable_nat_add_iff 1).1 (by simpa using hconv)
  obtain ⟨N₀, hN₀⟩ := tail_sum_small hterm hε
  refine ⟨N₀, ?_⟩
  intro m n hm hmn
  apply hN₀ (Finset.Icc m n)
  intro j hj
  exact le_trans hm (Finset.mem_Icc.mp hj).1

theorem gap10 (hconv : Summable (fun n : ℕ => term (n + 1))) :
    ∀ N₀ : ℕ, ∃ K : ℕ, ∀ k ≥ K, ∀ n ∈ logBlock k, N₀ ≤ n := by
  intro N₀
  refine ⟨N₀, ?_⟩
  intro k hk n hn
  have hkn : (k : ℝ) ≤ (n : ℝ) := by
    have hkexp : (k : ℝ) ≤ Real.exp (k : ℝ) := by
      have h := Real.add_one_le_exp (k : ℝ)
      linarith
    exact le_trans hkexp (gap1 k n hn).1
  have hNn : (N₀ : ℝ) ≤ (n : ℝ) :=
    le_trans (by exact_mod_cast hk) hkn
  exact_mod_cast hNn

theorem gap11 (hconv : Summable (fun n : ℕ => term (n + 1))) :
    ∃ N₀ K : ℕ, ∀ k ≥ K, ∀ n ∈ logBlock k, N₀ ≤ n := by
  exact ⟨0, 0, by intro k hk n hn; omega⟩

theorem gap12 (hconv : Summable (fun n : ℕ => term (n + 1))) :
    ∃ K : ℕ, ∀ k ≥ K, |blockTerm k| < epsilon := by
  have he : 1 < Real.exp 1 := by
    simpa using Real.exp_lt_exp.mpr (show (0 : ℝ) < 1 by norm_num)
  have heps : 0 < epsilon := by
    rw [epsilon]
    exact div_pos (sub_pos.mpr he) (mul_pos (by norm_num) (Real.exp_pos 1))
  have hterm : Summable term :=
    (summable_nat_add_iff 1).1 (by simpa using hconv)
  obtain ⟨N₀, htail⟩ := tail_sum_small hterm heps
  obtain ⟨K, hK⟩ := gap10 hconv N₀
  refine ⟨K, ?_⟩
  intro k hk
  rw [blockTerm]
  apply htail (logBlock k)
  exact hK k hk

theorem gap13 :
    ∀ k : ℕ, |blockTerm k| = amplitude k := by
  intro k
  have ha : 0 ≤ amplitude k := by
    unfold amplitude
    apply Finset.sum_nonneg
    intro n hn
    positivity
  rw [gap4, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg ha]

theorem gap14 (hconv : Summable (fun n : ℕ => term (n + 1))) :
    ∃ K : ℕ, ∀ k ≥ K,
      |blockTerm k| ≥ (Real.exp 1 - 1) / (2 * Real.exp 1) := by
  obtain ⟨K, hK⟩ := gap8
  refine ⟨K, ?_⟩
  intro k hk
  rw [gap13]
  exact hK k hk

theorem gap15 (hconv : Summable (fun n : ℕ => term (n + 1))) :
    ∃ K : ℕ, ∀ k ≥ K, |blockTerm k| ≥ 2 * epsilon := by
  obtain ⟨K, hK⟩ := gap14 hconv
  have hid : (Real.exp 1 - 1) / (2 * Real.exp 1) = 2 * epsilon := by
    rw [epsilon]
    ring
  refine ⟨K, ?_⟩
  intro k hk
  rw [← hid]
  exact hK k hk

theorem gap16 :
    (Real.exp 1 - 1) / (2 * Real.exp 1) = 2 * epsilon := by
  rw [epsilon]
  ring

theorem gap17 :
    2 * epsilon > epsilon := by
  have he : 1 < Real.exp 1 := by
    simpa using Real.exp_lt_exp.mpr (show (0 : ℝ) < 1 by norm_num)
  have heps : 0 < epsilon := by
    rw [epsilon]
    exact div_pos (sub_pos.mpr he) (mul_pos (by norm_num) (Real.exp_pos 1))
  linarith

theorem gap18 (hconv : Summable (fun n : ℕ => term (n + 1))) :
    ∃ K : ℕ, ∀ k ≥ K, |blockTerm k| > epsilon := by
  obtain ⟨K, hK⟩ := gap15 hconv
  refine ⟨K, ?_⟩
  intro k hk
  exact lt_of_lt_of_le gap17 (hK k hk)

theorem gap19 :
    Summable (fun n : ℕ => term (n + 1)) → False := by
  intro hconv
  obtain ⟨K₁, hsmall⟩ := gap12 hconv
  obtain ⟨K₂, hlarge⟩ := gap18 hconv
  let k := max K₁ K₂
  have hs := hsmall k (le_max_left _ _)
  have hl := hlarge k (le_max_right _ _)
  linarith

theorem gap20 :
    ¬ Summable (fun n : ℕ => term (n + 1)) := by
  exact gap19

end

end ProofGap.Exercise2688
