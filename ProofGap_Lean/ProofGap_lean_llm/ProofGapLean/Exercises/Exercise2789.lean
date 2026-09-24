import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise2789

noncomputable section

open Filter
open scoped BigOperators

def AdmissibleSet (a : ℕ → ℝ) (E : Set ℝ) : Prop :=
  (∃ M > 0, ∀ x ∈ E, |x| ≤ M) ∧
  ∀ n : ℕ, 1 ≤ n → a n ∉ E

def term (a : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  1 / (x - a n)

def SeriesUniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (s : Set ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s,
    |(∑ k ∈ Finset.range (n + 1), u k x) - g x| < ε

theorem gap1 (a : ℕ → ℝ) (E : Set ℝ)
    (ha : Tendsto a atTop atTop) (hE : AdmissibleSet a E) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ E, |x / a n| ≠ 1 := by
  rcases hE.1 with ⟨M, hMpos, hM⟩
  rcases eventually_atTop.1 ((tendsto_atTop.1 ha) (M + 1)) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn x hx
  have han_lower : M + 1 ≤ a n := hN n hn
  have han_pos : 0 < a n := by linarith
  have han : a n ≠ 0 := ne_of_gt han_pos
  have hxlt : |x| < |a n| := by
    rw [abs_of_pos han_pos]
    nlinarith [hM x hx]
  have hratio : |x / a n| < 1 := by
    rw [abs_div]
    exact (div_lt_one (abs_pos.mpr han)).2 hxlt
  exact ne_of_lt hratio

theorem gap2 (a : ℕ → ℝ) (ha : Tendsto a atTop atTop) :
    Tendsto (fun n : ℕ => 1 / |a n|) atTop (nhds 0) := by
  have hinv : Tendsto (fun n : ℕ => 1 / a n) atTop (nhds 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero.comp ha)
  apply hinv.congr'
  filter_upwards [((tendsto_atTop.1 ha) 0)] with n hn
  rw [abs_of_nonneg hn]

theorem gap3 (a : ℕ → ℝ) (E : Set ℝ)
    (ha : Tendsto a atTop atTop) (hE : AdmissibleSet a E) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ E, |x / a n| < 1 / 2 := by
  rcases hE.1 with ⟨M, hMpos, hM⟩
  rcases eventually_atTop.1 ((tendsto_atTop.1 ha) (2 * M + 1)) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn x hx
  have han_lower : 2 * M + 1 ≤ a n := hN n hn
  have han_pos : 0 < a n := by linarith
  have han : a n ≠ 0 := ne_of_gt han_pos
  rw [abs_div, abs_of_pos han_pos]
  apply (div_lt_iff₀ han_pos).2
  nlinarith [hM x hx]

theorem gap4 (a : ℕ → ℝ) (n : ℕ) (x : ℝ) (han : a n ≠ 0) :
    |term a n x| =
      (1 / |a n|) * (1 / |1 - x / a n|) := by
  have hfactor : x - a n = -(a n) * (1 - x / a n) := by
    field_simp [han]
    <;> ring
  unfold term
  rw [abs_div, abs_one, hfactor, abs_mul, abs_neg]
  by_cases hrest : |1 - x / a n| = 0
  · simp [hrest]
  · field_simp [abs_ne_zero.mpr han, hrest]

theorem gap5 (a : ℕ → ℝ) (n : ℕ) (x : ℝ)
    (han : a n ≠ 0) (hratio : |x / a n| < 1) :
    (1 / |a n|) * (1 / |1 - x / a n|) ≤
      (1 / |a n|) * (1 / (1 - |x / a n|)) := by
  have han_abs : 0 < |a n| := abs_pos.mpr han
  have hleft : 0 < 1 - |x / a n| := sub_pos.mpr hratio
  have hden : 1 - |x / a n| ≤ |1 - x / a n| := by
    simpa using (abs_sub_abs_le_abs_sub (1 : ℝ) (x / a n))
  have hinv : 1 / |1 - x / a n| ≤ 1 / (1 - |x / a n|) :=
    one_div_le_one_div_of_le hleft hden
  exact mul_le_mul_of_nonneg_left hinv (le_of_lt (one_div_pos.mpr han_abs))

theorem gap6 (a : ℕ → ℝ) (n : ℕ) (x : ℝ)
    (han : a n ≠ 0) (hratio : |x / a n| < 1 / 2) :
    (1 / |a n|) * (1 / (1 - |x / a n|)) ≤
      2 / |a n| := by
  have han_abs : 0 < |a n| := abs_pos.mpr han
  have hden : 0 < 1 - |x / a n| := by linarith
  have hinv : 1 / (1 - |x / a n|) ≤ 2 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  calc
    (1 / |a n|) * (1 / (1 - |x / a n|))
        ≤ (1 / |a n|) * 2 :=
      mul_le_mul_of_nonneg_left hinv (le_of_lt (one_div_pos.mpr han_abs))
    _ = 2 / |a n| := by ring

theorem gap7 (a : ℕ → ℝ) (n : ℕ) (x : ℝ)
    (han : a n ≠ 0) (hratio : |x / a n| < 1 / 2) :
    |term a n x| ≤ 2 / |a n| := by
  have hratio_one : |x / a n| < 1 := by linarith
  calc
    |term a n x| =
        (1 / |a n|) * (1 / |1 - x / a n|) := gap4 a n x han
    _ ≤ (1 / |a n|) * (1 / (1 - |x / a n|)) :=
      gap5 a n x han hratio_one
    _ ≤ 2 / |a n| := gap6 a n x han hratio

theorem gap8 (a : ℕ → ℝ)
    (hsum : Summable (fun n : ℕ => |1 / a (n + 1)|)) :
    Summable (fun n : ℕ => 2 / |a (n + 1)|) := by
  simpa [abs_div, div_eq_mul_inv] using hsum.mul_left (2 : ℝ)

theorem gap9 (a : ℕ → ℝ) (E : Set ℝ) (x : ℝ)
    (ha : Tendsto a atTop atTop)
    (hsum : Summable (fun n : ℕ => |1 / a (n + 1)|))
    (hE : AdmissibleSet a E) (hx : x ∈ E) :
    Summable (fun n : ℕ => |term a (n + 1) x|) := by
  rcases gap3 a E ha hE with ⟨Nr, hNr⟩
  rcases eventually_atTop.1 ((tendsto_atTop.1 ha) (1 : ℝ)) with ⟨Na, hNa⟩
  have hmajor : Summable (fun n : ℕ => 2 / |a (n + 1)|) := gap8 a hsum
  refine hmajor.of_norm_bounded_eventually ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop (max Nr Na)] with n hn
  have hnr : Nr ≤ n + 1 := by omega
  have hna : Na ≤ n + 1 := by omega
  have hapos : 0 < a (n + 1) := lt_of_lt_of_le zero_lt_one (hNa (n + 1) hna)
  have han : a (n + 1) ≠ 0 := ne_of_gt hapos
  have hratio : |x / a (n + 1)| < 1 / 2 := hNr (n + 1) hnr x hx
  simpa [Real.norm_eq_abs] using gap7 a (n + 1) x han hratio

theorem gap10 (a : ℕ → ℝ) (E : Set ℝ)
    (ha : Tendsto a atTop atTop)
    (hsum : Summable (fun n : ℕ => |1 / a (n + 1)|))
    (hE : AdmissibleSet a E) :
    SeriesUniformlyConvergesOn
      (fun n x => term a (n + 1) x)
      E
      (fun x => ∑' n : ℕ, term a (n + 1) x) := by
  intro ε hε
  rcases gap3 a E ha hE with ⟨Nr, hNr⟩
  rcases eventually_atTop.1 ((tendsto_atTop.1 ha) (1 : ℝ)) with ⟨Na, hNa⟩
  let b : ℕ → ℝ := fun k => 2 / |a (k + 1)|
  have hb : Summable b := by
    simpa [b] using gap8 a hsum
  have hbconv :
      Tendsto (fun m : ℕ => ∑ k ∈ Finset.range m, b k) atTop
        (nhds (∑' k : ℕ, b k)) :=
    hb.hasSum.tendsto_sum_nat
  have hevent : ∀ᶠ m : ℕ in atTop,
      dist (∑ k ∈ Finset.range m, b k) (∑' k : ℕ, b k) < ε :=
    (Metric.tendsto_nhds.1 hbconv) ε hε
  rcases eventually_atTop.1 hevent with ⟨Nt, hNt⟩
  refine ⟨max (max Nr Na) Nt, ?_⟩
  intro n hn x hx
  let f : ℕ → ℝ := fun k => term a (k + 1) x
  have hfabs : Summable (fun k : ℕ => |f k|) := by
    simpa [f] using gap9 a E x ha hsum hE hx
  have hf : Summable f := by
    apply Summable.of_norm
    simpa [Real.norm_eq_abs] using hfabs
  have hnr : Nr ≤ n + 1 := by omega
  have hna : Na ≤ n + 1 := by omega
  have hnt : Nt ≤ n + 1 := by omega
  have hbound : ∀ k : ℕ, ‖f (k + (n + 1))‖ ≤ b (k + (n + 1)) := by
    intro k
    have hindex_r : Nr ≤ (k + (n + 1)) + 1 := by omega
    have hindex_a : Na ≤ (k + (n + 1)) + 1 := by omega
    have hapos : 0 < a ((k + (n + 1)) + 1) :=
      lt_of_lt_of_le zero_lt_one (hNa ((k + (n + 1)) + 1) hindex_a)
    have han : a ((k + (n + 1)) + 1) ≠ 0 := ne_of_gt hapos
    have hratio : |x / a ((k + (n + 1)) + 1)| < 1 / 2 :=
      hNr ((k + (n + 1)) + 1) hindex_r x hx
    simpa [f, b, Real.norm_eq_abs] using
      gap7 a ((k + (n + 1)) + 1) x han hratio
  have hshift_inj : Function.Injective (fun k : ℕ => k + (n + 1)) := by
    intro i j hij
    exact Nat.add_right_cancel hij
  have hftnorm : Summable (fun k : ℕ => ‖f (k + (n + 1))‖) := by
    simpa [Real.norm_eq_abs] using hfabs.comp_injective hshift_inj
  have hbt : Summable (fun k : ℕ => b (k + (n + 1))) :=
    hb.comp_injective hshift_inj
  have htail_bound :
      ‖∑' k : ℕ, f (k + (n + 1))‖ ≤
        ∑' k : ℕ, b (k + (n + 1)) := by
    calc
      ‖∑' k : ℕ, f (k + (n + 1))‖
          ≤ ∑' k : ℕ, ‖f (k + (n + 1))‖ :=
        norm_tsum_le_tsum_norm hftnorm
      _ ≤ ∑' k : ℕ, b (k + (n + 1)) :=
        Summable.tsum_le_tsum hbound hftnorm hbt
  have hidf :
      (∑ k ∈ Finset.range (n + 1), f k) +
          (∑' k : ℕ, f (k + (n + 1))) = ∑' k : ℕ, f k := by
    simpa using hf.sum_add_tsum_nat_add (n + 1)
  have hidb :
      (∑ k ∈ Finset.range (n + 1), b k) +
          (∑' k : ℕ, b (k + (n + 1))) = ∑' k : ℕ, b k := by
    simpa using hb.sum_add_tsum_nat_add (n + 1)
  have hbt_nonneg : 0 ≤ ∑' k : ℕ, b (k + (n + 1)) := by
    apply tsum_nonneg
    intro k
    exact div_nonneg (by norm_num) (abs_nonneg _)
  have hclose :
      |(∑ k ∈ Finset.range (n + 1), b k) - ∑' k : ℕ, b k| < ε := by
    simpa [Real.dist_eq] using hNt (n + 1) hnt
  have herror :
      |(∑ k ∈ Finset.range (n + 1), f k) - ∑' k : ℕ, f k| < ε := by
    calc
      |(∑ k ∈ Finset.range (n + 1), f k) - ∑' k : ℕ, f k|
          = ‖∑' k : ℕ, f (k + (n + 1))‖ := by
              rw [← hidf]
              simp [Real.norm_eq_abs]
      _ ≤ ∑' k : ℕ, b (k + (n + 1)) := htail_bound
      _ = |(∑ k ∈ Finset.range (n + 1), b k) - ∑' k : ℕ, b k| := by
              rw [← hidb]
              simp [abs_of_nonneg hbt_nonneg]
      _ < ε := hclose
  simpa [f] using herror

theorem gap11 (a : ℕ → ℝ) (E : Set ℝ)
    (ha : Tendsto a atTop atTop)
    (hsum : Summable (fun n : ℕ => |1 / a (n + 1)|))
    (hE : AdmissibleSet a E) :
    (∀ x ∈ E, Summable (fun n : ℕ => |term a (n + 1) x|)) ∧
    SeriesUniformlyConvergesOn
      (fun n x => term a (n + 1) x)
      E
      (fun x => ∑' n : ℕ, term a (n + 1) x) := by
  constructor
  · intro x hx
    exact gap9 a E x ha hsum hE hx
  · exact gap10 a E ha hsum hE

end

end ProofGap.Exercise2789
