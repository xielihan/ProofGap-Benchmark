import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Leibniz

namespace ProofGap.Exercise2717

noncomputable section

open Filter

def coefficient (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / (2 * (n : ℝ) - 1)

def ratio (x : ℝ) : ℝ :=
  (1 - x) / (1 + x)

def term (x : ℝ) (n : ℕ) : ℝ :=
  coefficient n * ratio x ^ n

def ConditionallySummable (x : ℝ) : Prop :=
  ProofGap.SeriesConverges (fun n : ℕ => term x (n + 1)) ∧
    ¬ ProofGap.SeriesConverges (fun n : ℕ => |term x (n + 1)|)

private theorem seriesConverges_iff_tendsto_partialSums {f : ℕ → ℝ} :
    ProofGap.SeriesConverges f ↔
      ∃ s : ℝ, Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop (nhds s) := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
      tendsto_map'_iff, Function.comp_def] at hs
    exact hs
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
      tendsto_map'_iff, Function.comp_def]
    exact hs

private theorem seriesConverges_of_summable {f : ℕ → ℝ} (hf : Summable f) :
    ProofGap.SeriesConverges f := by
  exact hf.mono_filter SummationFilter.le_atTop

private theorem summable_of_seriesConverges_of_nonneg {f : ℕ → ℝ}
    (hf0 : ∀ n, 0 ≤ f n) (hf : ProofGap.SeriesConverges f) : Summable f := by
  obtain ⟨s, hs⟩ := seriesConverges_iff_tendsto_partialSums.mp hf
  obtain ⟨c, hc⟩ := hs.bddAbove_range
  exact summable_of_sum_range_le hf0 fun n => hc ⟨n, rfl⟩

private theorem tendsto_zero_of_seriesConverges {f : ℕ → ℝ}
    (hf : ProofGap.SeriesConverges f) : Tendsto f atTop (nhds 0) := by
  obtain ⟨s, hs⟩ := seriesConverges_iff_tendsto_partialSums.mp hf
  have hs' := hs.comp (tendsto_add_atTop_nat 1)
  simpa [Finset.sum_range_succ] using hs'.sub hs

private lemma abs_coefficient_succ (n : ℕ) :
    |coefficient (n + 1)| = 1 / (2 * (n : ℝ) + 1) := by
  have hden : 0 < 1 + (n : ℝ) * 2 := by positivity
  simp [coefficient, abs_div, abs_pow]
  convert abs_of_pos hden using 1 <;> ring

private lemma abs_term_succ (x : ℝ) (n : ℕ) :
    |term x (n + 1)| = |ratio x| ^ (n + 1) / (2 * (n : ℝ) + 1) := by
  rw [term, abs_mul, abs_pow, abs_coefficient_succ]
  ring

private theorem not_summable_abs_term_zero :
    ¬ Summable (fun n : ℕ => |term 0 (n + 1)|) := by
  intro h
  have hodd : Summable (fun n : ℕ => 1 / (2 * (n : ℝ) + 1)) := by
    simpa [abs_term_succ, ratio] using h
  have hhalf : Summable (fun n : ℕ => 1 / (2 * ((n : ℝ) + 1))) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hodd
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hshift : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    convert hhalf.mul_left (2 : ℝ) using 1
    funext n
    field_simp
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff 1).mp
  simpa [Nat.cast_add] using hshift

private theorem seriesConverges_term_zero :
    ProofGap.SeriesConverges (fun n : ℕ => term 0 (n + 1)) := by
  rw [seriesConverges_iff_tendsto_partialSums]
  refine ⟨-(Real.pi / 4), ?_⟩
  convert Real.tendsto_sum_pi_div_four.neg using 1
  · funext k
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    simp [term, coefficient, ratio, pow_succ]
    ring

private theorem not_seriesConverges_abs_term_zero :
    ¬ ProofGap.SeriesConverges (fun n : ℕ => |term 0 (n + 1)|) := by
  intro h
  apply not_summable_abs_term_zero
  exact summable_of_seriesConverges_of_nonneg (fun n => abs_nonneg _) h

private theorem one_lt_abs_ratio (x : ℝ) (hx0 : x ≠ -1) (hx : x < 0) :
    1 < |ratio x| := by
  have hden : 0 < |1 + x| := abs_pos.mpr (by
    intro h
    apply hx0
    linarith)
  rw [ratio, abs_div, one_lt_div hden]
  exact sq_lt_sq.mp (by nlinarith)

private theorem tendsto_abs_term_atTop (x : ℝ) (hx0 : x ≠ -1) (hx : x < 0) :
    Tendsto (fun n : ℕ => |term x (n + 1)|) atTop atTop := by
  let r := |ratio x|
  have hr : 1 < r := one_lt_abs_ratio x hx0 hx
  have hn : Tendsto (fun n : ℕ => (n : ℝ) / r ^ n) atTop (nhds 0) := by
    simpa using tendsto_pow_const_div_const_pow_of_one_lt 1 hr
  have h_one : Tendsto (fun n : ℕ => 1 / r ^ n) atTop (nhds 0) := by
    simpa using tendsto_pow_const_div_const_pow_of_one_lt 0 hr
  have hsmall :
      Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1) / r ^ (n + 1)) atTop (nhds 0) := by
    have h₁ : Tendsto (fun n : ℕ => (2 / r) * ((n : ℝ) / r ^ n)) atTop (nhds 0) := by
      convert (tendsto_const_nhds.mul hn) using 1 <;> norm_num
    have h₂ : Tendsto (fun n : ℕ => (1 / r) * (1 / r ^ n)) atTop (nhds 0) := by
      convert (tendsto_const_nhds.mul h_one) using 1 <;> norm_num
    have h := h₁.add h₂
    convert h using 1
    · funext n
      dsimp
      rw [pow_succ]
      field_simp [ne_of_gt hr]
    · norm_num
  have hsmall' :
      Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1) / r ^ (n + 1)) atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hsmall, Filter.Eventually.of_forall fun n => by
      simp only [Set.mem_Ioi]
      positivity⟩
  have hinv := hsmall'.inv_tendsto_nhdsGT_zero
  convert hinv using 1
  · funext n
    rw [abs_term_succ]
    dsimp [r]
    field_simp

theorem gap1 :
    Tendsto
      (fun n : ℕ =>
        |coefficient (n + 1)| / |coefficient (n + 2)|)
      atTop (nhds 1) := by
  convert tendsto_add_mul_div_add_mul_atTop_nhds (𝕜 := ℝ) 3 1 2 (d := 2) (by norm_num) using 1
  · funext n
    rw [abs_coefficient_succ, abs_coefficient_succ]
    norm_num [Nat.cast_add]
    field_simp
    ring
  · norm_num

theorem gap2 (x : ℝ) (hx : x ≠ -1) :
    |ratio x| < 1 ↔ (1 - x) ^ 2 < (1 + x) ^ 2 ∧ 0 < x := by
  have hden : 0 < |1 + x| := abs_pos.mpr (by
    intro h
    apply hx
    linarith)
  constructor
  · intro h
    have habs : |1 - x| < |1 + x| := by
      rwa [ratio, abs_div, div_lt_one hden] at h
    exact ⟨sq_lt_sq.mpr habs, by nlinarith [sq_lt_sq.mpr habs]⟩
  · rintro ⟨hsq, hxpos⟩
    rw [ratio, abs_div, div_lt_one hden]
    exact sq_lt_sq.mp hsq

theorem gap3 (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => |term x (n + 1)|) := by
  have hr : |ratio x| < 1 := (gap2 x (by linarith)).mpr ⟨by nlinarith, hx⟩
  have hgeom : Summable (fun n : ℕ => |ratio x| ^ (n + 1)) := by
    apply (summable_nat_add_iff 1).mpr
    exact summable_geometric_of_lt_one (abs_nonneg _) hr
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_) hgeom
  rw [abs_term_succ]
  have hden : 1 ≤ 2 * (n : ℝ) + 1 := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hcoeff : 1 / (2 * (n : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr hden
  calc
    |ratio x| ^ (n + 1) / (2 * (n : ℝ) + 1) =
        (1 / (2 * (n : ℝ) + 1)) * |ratio x| ^ (n + 1) := by ring
    _ ≤ 1 * |ratio x| ^ (n + 1) :=
      mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (abs_nonneg _) _)
    _ = |ratio x| ^ (n + 1) := one_mul _

theorem gap4 :
    ∀ n : ℕ, 1 ≤ n → term 0 n = coefficient n := by
  intro n hn
  simp [term, ratio]

theorem gap5 :
    ConditionallySummable 0 := by
  exact ⟨seriesConverges_term_zero, not_seriesConverges_abs_term_zero⟩

theorem gap6 (x : ℝ) (hx0 : x ≠ -1) (hx : x < 0) :
    ¬ Tendsto (fun n : ℕ => term x (n + 1)) atTop (nhds 0) := by
  intro hzero
  have habsZero : Tendsto (fun n : ℕ => |term x (n + 1)|) atTop (nhds 0) := by
    simpa [Real.norm_eq_abs] using hzero.norm
  have hlarge : ∀ᶠ n : ℕ in atTop, 1 ≤ |term x (n + 1)| :=
    (tendsto_abs_term_atTop x hx0 hx).eventually (eventually_ge_atTop (1 : ℝ))
  have hsmall : ∀ᶠ n : ℕ in atTop, |term x (n + 1)| < 1 :=
    habsZero.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hfalse : ∀ᶠ n : ℕ in atTop, False :=
    (hlarge.and hsmall).mono fun _ h => (not_lt_of_ge h.1 h.2)
  exact (hfalse.exists.elim fun _ h => h)

theorem gap7 (x : ℝ) (hx0 : x ≠ -1) (hx : x < 0) :
    ¬ Summable (fun n : ℕ => term x (n + 1)) := by
  intro h
  exact gap6 x hx0 hx h.tendsto_atTop_zero

theorem gap8 (x : ℝ) (hx0 : x ≠ -1) :
    (0 < x → Summable (fun n : ℕ => |term x (n + 1)|)) ∧
    (x = 0 → ConditionallySummable x) ∧
    (x < 0 → ¬ Summable (fun n : ℕ => term x (n + 1))) := by
  exact ⟨gap3 x, fun hx => hx ▸ gap5, gap7 x hx0⟩

end

end ProofGap.Exercise2717
