import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.RingTheory.Binomial

namespace ProofGap.Exercise2700

noncomputable section

open Filter
open Polynomial
open Asymptotics
open scoped BigOperators

def generalizedBinomial (m : ℝ) (n : ℕ) : ℝ :=
  (∏ k ∈ Finset.range n, (m - k)) / (Nat.factorial n : ℝ)

def ratioAbs (m : ℝ) (n : ℕ) : ℝ :=
  |generalizedBinomial m n / generalizedBinomial m (n + 1)|

def ratioModel (m : ℝ) (n : ℕ) : ℝ :=
  (1 + 1 / (n : ℝ)) * (1 + m / (n : ℝ))

def ratioRemainder (m : ℝ) (n : ℕ) : ℝ :=
  ratioAbs m n - (1 + (m + 1) / (n : ℝ))

def logAbs (m : ℝ) (n : ℕ) : ℝ :=
  Real.log |generalizedBinomial m n|

def ConditionallySummable (f : ℕ → ℝ) : Prop :=
  ProofGap.SeriesConverges f ∧ ¬ Summable (fun n => |f n|)

private theorem descPochhammer_smeval_eq_prod_range (m : ℝ) :
    ∀ n : ℕ, (descPochhammer ℤ n).smeval m =
      ∏ k ∈ Finset.range n, (m - k) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [descPochhammer_succ_right, smeval_mul, smeval_sub, smeval_X,
        smeval_natCast, ih, Finset.prod_range_succ]
      simp

private theorem generalizedBinomial_eq_choose (m : ℝ) (n : ℕ) :
    generalizedBinomial m n = Ring.choose m n := by
  rw [Ring.choose_eq_smul, descPochhammer_smeval_eq_prod_range]
  simp [generalizedBinomial, div_eq_mul_inv, mul_comm, smul_eq_mul]

private theorem generalizedBinomial_succ (m : ℝ) (n : ℕ) :
    generalizedBinomial m (n + 1) =
      generalizedBinomial m n * (m - n) / (n + 1) := by
  unfold generalizedBinomial
  rw [Finset.prod_range_succ, Nat.factorial_succ, Nat.cast_mul]
  push_cast
  field_simp [Nat.factorial_ne_zero]

private theorem generalizedBinomial_zero_of_pos (n : ℕ) (hn : 0 < n) :
    generalizedBinomial 0 n = 0 := by
  unfold generalizedBinomial
  apply div_eq_zero_iff.mpr
  left
  apply Finset.prod_eq_zero (i := 0)
  · exact Finset.mem_range.mpr hn
  · norm_num

private theorem generalizedBinomial_one_of_two_le (n : ℕ) (hn : 2 ≤ n) :
    generalizedBinomial 1 n = 0 := by
  unfold generalizedBinomial
  apply div_eq_zero_iff.mpr
  left
  apply Finset.prod_eq_zero (i := 1)
  · exact Finset.mem_range.mpr (by omega)
  · norm_num

private theorem generalizedBinomial_ne_zero_of_neg (m : ℝ) (hm : m < 0) :
    ∀ n : ℕ, generalizedBinomial m n ≠ 0 := by
  intro n
  unfold generalizedBinomial
  apply div_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    have hk0 : (0 : ℝ) ≤ k := by positivity
    linarith
  · exact_mod_cast Nat.factorial_ne_zero n

private theorem generalizedBinomial_ne_zero_of_not_nat (m : ℝ)
    (hm : ∀ k : ℕ, m ≠ k) :
    ∀ n : ℕ, generalizedBinomial m n ≠ 0 := by
  intro n
  unfold generalizedBinomial
  apply div_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    exact sub_ne_zero.mpr (hm k)
  · exact_mod_cast Nat.factorial_ne_zero n

private theorem negOnePow_mul_generalizedBinomial_pos (m : ℝ) (hm : m < 0) :
    ∀ n : ℕ, 0 < (-1 : ℝ) ^ n * generalizedBinomial m n := by
  intro n
  induction n with
  | zero => simp [generalizedBinomial]
  | succ n ih =>
      rw [generalizedBinomial_succ, pow_succ]
      have hnum : m - (n : ℝ) < 0 := by
        have hn : (0 : ℝ) ≤ n := by positivity
        linarith
      have hden : (0 : ℝ) < n + 1 := by positivity
      have hq : (m - (n : ℝ)) / (n + 1 : ℝ) < 0 := div_neg_of_neg_of_pos hnum hden
      calc
        (-1 : ℝ) ^ n * -1 *
            (generalizedBinomial m n * (m - (n : ℝ)) / (n + 1 : ℝ)) =
            ((-1 : ℝ) ^ n * generalizedBinomial m n) *
              (-((m - (n : ℝ)) / (n + 1 : ℝ))) := by ring
        _ > 0 := mul_pos ih (neg_pos.mpr hq)

private theorem abs_generalizedBinomial_eq_negOnePow_mul (m : ℝ) (hm : m < 0)
    (n : ℕ) :
    |generalizedBinomial m n| = (-1 : ℝ) ^ n * generalizedBinomial m n := by
  have hpos := negOnePow_mul_generalizedBinomial_pos m hm n
  have habs := abs_of_pos hpos
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at habs
  exact habs

private theorem generalizedBinomial_eq_negOnePow_mul_abs (m : ℝ) (hm : m < 0)
    (n : ℕ) :
    generalizedBinomial m n = (-1 : ℝ) ^ n * |generalizedBinomial m n| := by
  rw [abs_generalizedBinomial_eq_negOnePow_mul m hm]
  rw [← mul_assoc]
  nth_rw 1 [← one_mul (generalizedBinomial m n)]
  congr 1
  rw [← pow_add]
  norm_num

private theorem abs_generalizedBinomial_succ (m : ℝ) (hm : m < 0) (n : ℕ) :
    |generalizedBinomial m (n + 1)| =
      |generalizedBinomial m n| * ((n : ℝ) - m) / (n + 1) := by
  rw [generalizedBinomial_succ, abs_div, abs_mul]
  have hnum : m - (n : ℝ) < 0 := by
    have hn : (0 : ℝ) ≤ n := by positivity
    linarith
  have hden : (0 : ℝ) ≤ n + 1 := by positivity
  rw [abs_of_neg hnum, abs_of_nonneg hden]
  ring

private theorem factor_pos (m : ℝ) (hm₀ : -1 < m) (hm₁ : m < 0)
    (k : ℕ) (hk : 1 ≤ k) :
    0 < 1 - (m + 1) / (k : ℝ) := by
  apply sub_pos.mpr
  apply (div_lt_one (by exact_mod_cast Nat.zero_lt_one.trans_le hk)).2
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

private theorem abs_generalizedBinomial_eq_prod_Icc (m : ℝ) (hm : m < 0) :
    ∀ n : ℕ,
      |generalizedBinomial m n| =
        ∏ k ∈ Finset.Icc 1 n, (1 - (m + 1) / (k : ℝ)) := by
  intro n
  induction n with
  | zero => simp [generalizedBinomial]
  | succ n ih =>
      rw [abs_generalizedBinomial_succ m hm n,
        Finset.prod_Icc_succ_top (by omega), ih]
      have hn : (0 : ℝ) < n + 1 := by positivity
      norm_num [Nat.cast_add, Nat.cast_one]
      field_simp [ne_of_gt hn]
      ring

private theorem abs_generalizedBinomial_antitone (m : ℝ)
    (hm₀ : -1 < m) (hm₁ : m < 0) :
    Antitone (fun n : ℕ => |generalizedBinomial m (n + 1)|) := by
  intro n k hnk
  induction k, hnk using Nat.le_induction with
  | base => rfl
  | succ k hnk ih =>
      refine le_trans ?_ ih
      change |generalizedBinomial m (k + 2)| ≤
        |generalizedBinomial m (k + 1)|
      rw [abs_generalizedBinomial_succ m hm₁ (k + 1)]
      norm_num [Nat.cast_add, Nat.cast_one]
      have hq1 : (↑k + 1 - m) / (↑k + 1 + 1) ≤ 1 := by
        apply (div_le_one (by positivity)).2
        linarith
      calc
        |generalizedBinomial m (k + 1)| * (↑k + 1 - m) / (↑k + 1 + 1) =
            |generalizedBinomial m (k + 1)| *
              ((↑k + 1 - m) / (↑k + 1 + 1)) := by ring
        _ ≤ |generalizedBinomial m (k + 1)| :=
          mul_le_of_le_one_right (abs_nonneg _) hq1

private theorem sum_Icc_one_eq_sum_range (f : ℕ → ℝ) :
    ∀ n : ℕ,
      ∑ k ∈ Finset.Icc 1 n, f k =
        ∑ i ∈ Finset.range n, f (i + 1) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

private theorem logAbs_eq_sum_Icc (m : ℝ) (hm₀ : -1 < m) (hm₁ : m < 0)
    (n : ℕ) :
    logAbs m n =
      ∑ k ∈ Finset.Icc 1 n,
        Real.log (1 - (m + 1) / (k : ℝ)) := by
  unfold logAbs
  rw [abs_generalizedBinomial_eq_prod_Icc m hm₁,
    Real.log_prod]
  intro k hk
  exact ne_of_gt (factor_pos m hm₀ hm₁ k (Finset.mem_Icc.mp hk).1)

private theorem log_sum_le_neg_mul_harmonic (m : ℝ)
    (hm₀ : -1 < m) (hm₁ : m < 0) (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n,
        Real.log (1 - (m + 1) / (k : ℝ))) ≤
      -(m + 1) *
        ∑ i ∈ Finset.range n, (1 / (i + 1) : ℝ) := by
  calc
    (∑ k ∈ Finset.Icc 1 n,
        Real.log (1 - (m + 1) / (k : ℝ))) ≤
        ∑ k ∈ Finset.Icc 1 n, (-(m + 1) * (1 / (k : ℝ))) := by
      apply Finset.sum_le_sum
      intro k hk
      calc
        Real.log (1 - (m + 1) / (k : ℝ)) ≤
            (1 - (m + 1) / (k : ℝ)) - 1 :=
          Real.log_le_sub_one_of_pos
            (factor_pos m hm₀ hm₁ k (Finset.mem_Icc.mp hk).1)
        _ = -(m + 1) * (1 / (k : ℝ)) := by ring
    _ = -(m + 1) *
        ∑ i ∈ Finset.range n, (1 / (i + 1) : ℝ) := by
      rw [sum_Icc_one_eq_sum_range, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      norm_num

private theorem log_sum_tendsto_atBot (m : ℝ)
    (hm₀ : -1 < m) (hm₁ : m < 0) :
    Tendsto
      (fun n : ℕ =>
        ∑ k ∈ Finset.Icc 1 n,
          Real.log (1 - (m + 1) / (k : ℝ)))
      atTop atBot := by
  apply tendsto_atBot_mono (log_sum_le_neg_mul_harmonic m hm₀ hm₁)
  exact Real.tendsto_sum_range_one_div_nat_succ_atTop.const_mul_atTop_of_neg (by linarith)

private theorem abs_generalizedBinomial_tendsto_zero (m : ℝ)
    (hm₀ : -1 < m) (hm₁ : m < 0) :
    Tendsto (fun n : ℕ => |generalizedBinomial m (n + 1)|)
      atTop (nhds 0) := by
  have hlog : Tendsto (fun n : ℕ => logAbs m (n + 1)) atTop atBot := by
    apply ((log_sum_tendsto_atBot m hm₀ hm₁).comp
      (tendsto_add_atTop_nat 1)).congr'
    filter_upwards with n
    exact (logAbs_eq_sum_Icc m hm₀ hm₁ (n + 1)).symm
  have hexp := Real.tendsto_exp_atBot.comp hlog
  apply hexp.congr'
  filter_upwards with n
  simp only [Function.comp_apply]
  unfold logAbs
  rw [Real.exp_log (abs_pos.mpr
    (generalizedBinomial_ne_zero_of_neg m hm₁ (n + 1)))]

private theorem neg_div_nat_succ_le_abs (m : ℝ) (hm : m < 0) :
    ∀ n : ℕ,
      (-m) / (n + 1 : ℝ) ≤ |generalizedBinomial m (n + 1)| := by
  intro n
  induction n with
  | zero =>
      simp [generalizedBinomial_succ, generalizedBinomial, abs_of_neg hm]
  | succ n ih =>
      rw [abs_generalizedBinomial_succ m hm (n + 1)]
      norm_num [Nat.cast_add, Nat.cast_one] at ih ⊢
      have hn1 : (0 : ℝ) < n + 1 := by positivity
      have hn2 : (0 : ℝ) < n + 1 + 1 := by positivity
      have hq : (n + 1 : ℝ) / (n + 1 + 1 : ℝ) ≤
          (n + 1 - m) / (n + 1 + 1 : ℝ) := by
        apply (div_le_div_iff_of_pos_right hn2).2
        linarith
      calc
        (-m) / (n + 1 + 1 : ℝ) =
            ((-m) / (n + 1 : ℝ)) * ((n + 1 : ℝ) / (n + 1 + 1 : ℝ)) := by
              field_simp [ne_of_gt hn1, ne_of_gt hn2]
        _ ≤ |generalizedBinomial m (n + 1)| *
            ((n + 1 - m) / (n + 1 + 1 : ℝ)) := by
              exact mul_le_mul ih hq (by positivity) (by positivity)
        _ = |generalizedBinomial m (n + 1)| * (n + 1 - m) / (n + 1 + 1 : ℝ) := by ring

private theorem one_le_abs_generalizedBinomial_of_le_neg_one (m : ℝ)
    (hm : m ≤ -1) :
    ∀ n : ℕ, 1 ≤ |generalizedBinomial m (n + 1)| := by
  intro n
  have hmneg : m < 0 := lt_of_le_of_lt hm (by norm_num)
  induction n with
  | zero =>
      simpa [generalizedBinomial_succ, generalizedBinomial, abs_of_neg hmneg] using
        (show (1 : ℝ) ≤ -m by linarith)
  | succ n ih =>
      rw [abs_generalizedBinomial_succ m hmneg (n + 1)]
      norm_num [Nat.cast_add, Nat.cast_one] at ih ⊢
      have hq : 1 ≤ ((n + 1 - m) / (n + 1 + 1 : ℝ)) := by
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < n + 1 + 1)).2
        linarith
      have hmul := mul_le_mul ih hq (by norm_num : (0 : ℝ) ≤ 1) (abs_nonneg _)
      calc
        1 ≤ |generalizedBinomial m (n + 1)| * ((n + 1 - m) / (n + 1 + 1 : ℝ)) := by
          simpa using hmul
        _ = |generalizedBinomial m (n + 1)| * (n + 1 - m) / (n + 1 + 1 : ℝ) := by ring

private theorem generalizedBinomial_add_one (m : ℝ) (n : ℕ) :
    generalizedBinomial (m + 1) (n + 1) =
      generalizedBinomial m n + generalizedBinomial m (n + 1) := by
  simpa only [generalizedBinomial_eq_choose] using (Ring.choose_succ_succ m n)

private theorem summable_abs_of_pos_le_one (m : ℝ) (hm : 0 < m) (hm1 : m ≤ 1) :
    Summable (fun n : ℕ => |generalizedBinomial m (n + 1)|) := by
  let r := m - 1
  have hr0 : -1 < r := by dsimp [r]; linarith
  have hr1 : r ≤ 0 := by dsimp [r]; linarith
  have hdiff : ∀ n : ℕ,
      |generalizedBinomial m (n + 1)| =
        |generalizedBinomial r n| - |generalizedBinomial r (n + 1)| := by
    intro n
    by_cases hre : r = 0
    · have hmEq : m = 1 := by dsimp [r] at hre; linarith
      subst m
      subst r
      cases n with
      | zero => norm_num [generalizedBinomial]
      | succ n =>
          simp only [sub_self]
          rw [generalizedBinomial_one_of_two_le (n + 2) (by omega),
            generalizedBinomial_zero_of_pos (n + 1) (by omega),
            generalizedBinomial_zero_of_pos (n + 2) (by omega)]
          norm_num
    · have hrneg : r < 0 := lt_of_le_of_ne hr1 hre
      have hq : ((n : ℝ) - r) / (n + 1 : ℝ) ≤ 1 := by
        apply (div_le_one (by positivity)).2
        linarith
      have hle : |generalizedBinomial r (n + 1)| ≤ |generalizedBinomial r n| := by
        rw [abs_generalizedBinomial_succ r hrneg n]
        calc
          |generalizedBinomial r n| * ((n : ℝ) - r) / (n + 1 : ℝ) =
              |generalizedBinomial r n| * (((n : ℝ) - r) / (n + 1 : ℝ)) := by ring
          _ ≤ |generalizedBinomial r n| :=
            mul_le_of_le_one_right (abs_nonneg _) hq
      have hnonneg : 0 ≤
          |generalizedBinomial r n| - |generalizedBinomial r (n + 1)| := sub_nonneg.mpr hle
      calc
        abs (generalizedBinomial m (n + 1)) =
            abs (generalizedBinomial r n + generalizedBinomial r (n + 1)) := by
              congr 1
              rw [show m = r + 1 by dsimp [r]; ring]
              exact generalizedBinomial_add_one r n
        _ = abs ((-1 : ℝ) ^ n * |generalizedBinomial r n| +
            (-1 : ℝ) ^ (n + 1) * |generalizedBinomial r (n + 1)|) := by
              congr 1
              exact congrArg₂ (· + ·)
                (generalizedBinomial_eq_negOnePow_mul_abs r hrneg n)
                (generalizedBinomial_eq_negOnePow_mul_abs r hrneg (n + 1))
        _ = abs ((-1 : ℝ) ^ n *
            (|generalizedBinomial r n| - |generalizedBinomial r (n + 1)|)) := by
              congr 1
              rw [pow_succ]
              ring
        _ = |generalizedBinomial r n| - |generalizedBinomial r (n + 1)| := by
              rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
                abs_of_nonneg hnonneg]
  have hrzero : Tendsto (fun n : ℕ => |generalizedBinomial r n|) atTop (nhds 0) := by
    by_cases hre : r = 0
    · have heq : ∀ᶠ n : ℕ in atTop, |generalizedBinomial r n| = 0 := by
        filter_upwards [Ici_mem_atTop 1] with n hn
        rw [hre, generalizedBinomial_zero_of_pos n hn, abs_zero]
      apply tendsto_const_nhds.congr'
      filter_upwards [heq] with n hn
      exact hn.symm
    · have hrneg : r < 0 := lt_of_le_of_ne hr1 hre
      apply (tendsto_add_atTop_iff_nat 1).mp
      exact abs_generalizedBinomial_tendsto_zero r hr0 hrneg
  refine ⟨|generalizedBinomial r 0|, ?_⟩
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun n => abs_nonneg (generalizedBinomial m (n + 1))) _).mpr
  convert tendsto_const_nhds.sub hrzero using 1
  · ext n
    calc
      (∑ i ∈ Finset.range n, |generalizedBinomial m (i + 1)|) =
          ∑ i ∈ Finset.range n,
            (|generalizedBinomial r i| - |generalizedBinomial r (i + 1)|) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hdiff i
      _ = |generalizedBinomial r 0| - |generalizedBinomial r n| :=
        Finset.sum_range_sub' (fun i => |generalizedBinomial r i|) n
  · ring

private theorem summable_abs_of_pos_of_le_nat :
    ∀ N : ℕ, ∀ m : ℝ, 0 < m → m ≤ N →
      Summable (fun n : ℕ => |generalizedBinomial m (n + 1)|) := by
  intro N
  induction N with
  | zero =>
      intro m hm hmN
      norm_num at hmN
      linarith
  | succ N ih =>
      intro m hm hmN
      by_cases hm1 : m ≤ 1
      · exact summable_abs_of_pos_le_one m hm hm1
      · have hrpos : 0 < m - 1 := by linarith
        have hrN : m - 1 ≤ (N : ℝ) := by
          norm_num at hmN ⊢
          linarith
        have htail := ih (m - 1) hrpos hrN
        have hfull : Summable (fun n : ℕ => |generalizedBinomial (m - 1) n|) := by
          apply (summable_nat_add_iff 1).mp
          exact htail
        apply (hfull.add htail).of_nonneg_of_le
        · intro n
          exact abs_nonneg _
        · intro n
          calc
            |generalizedBinomial m (n + 1)| =
                |generalizedBinomial (m - 1) n +
                  generalizedBinomial (m - 1) (n + 1)| := by
                    congr 1
                    rw [show m = (m - 1) + 1 by ring]
                    convert generalizedBinomial_add_one (m - 1) n using 1 <;> ring
            _ ≤ |generalizedBinomial (m - 1) n| +
                |generalizedBinomial (m - 1) (n + 1)| :=
              abs_add_le _ _

private theorem seriesConverges_iff_tendsto_partialSums {f : ℕ → ℝ} :
    ProofGap.SeriesConverges f ↔
      ∃ l : ℝ, Tendsto (fun n => ∑ i ∈ Finset.range n, f i) atTop (nhds l) := by
  unfold ProofGap.SeriesConverges Summable HasSum
  simp only [SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
  rfl

private theorem seriesConverges_tendsto_zero {f : ℕ → ℝ}
    (hf : ProofGap.SeriesConverges f) : Tendsto f atTop (nhds 0) := by
  rcases seriesConverges_iff_tendsto_partialSums.mp hf with ⟨l, hl⟩
  have hshift := hl.comp (tendsto_add_atTop_nat 1)
  have hdiff := hshift.sub hl
  convert hdiff using 1
  · ext n
    simp only [Function.comp_apply]
    rw [Finset.sum_range_succ]
    ring
  · ring

private theorem seriesConverges_of_summable {f : ℕ → ℝ} (hf : Summable f) :
    ProofGap.SeriesConverges f := by
  apply seriesConverges_iff_tendsto_partialSums.mpr
  exact ⟨∑' n, f n, hf.tendsto_sum_tsum_nat⟩

theorem gap1 (m : ℝ) :
    ∀ n : ℕ, 1 ≤ n → generalizedBinomial m (n + 1) ≠ 0 →
      ratioAbs m n = |((n : ℝ) + 1) / (m - n)| := by
  intro n hn hnext
  have hdiv : generalizedBinomial m n * (m - (n : ℝ)) / (n + 1 : ℝ) ≠ 0 := by
    simpa [generalizedBinomial_succ] using hnext
  have hg : generalizedBinomial m n ≠ 0 := by
    intro h
    apply hdiv
    simp [h]
  have hmn : m - (n : ℝ) ≠ 0 := by
    intro h
    apply hdiv
    simp [h]
  unfold ratioAbs
  rw [generalizedBinomial_succ]
  congr 1
  field_simp [hg, hmn]

private theorem tendsto_ratio_linear (m : ℝ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) / ((n : ℝ) - m)) atTop (nhds 1) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹ : ℝ)) atTop (nhds 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hnum : Tendsto (fun n : ℕ => 1 + (n : ℝ)⁻¹) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hinv
  have hden : Tendsto (fun n : ℕ => 1 - m * (n : ℝ)⁻¹) atTop (nhds 1) := by
    convert tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv) using 1 <;> ring
  have h := hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
  have h' : Tendsto
      ((fun n : ℕ => 1 + (n : ℝ)⁻¹) / fun n : ℕ => 1 - m * (n : ℝ)⁻¹)
      atTop (nhds 1) := by simpa using h
  apply h'.congr'
  have hnlarge : ∀ᶠ n : ℕ in atTop, m < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop m)
  filter_upwards [Ici_mem_atTop 1, hnlarge] with n hn hmn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
  have hsub : (n : ℝ) - m ≠ 0 := ne_of_gt (sub_pos.mpr hmn)
  simp only [Pi.div_apply]
  field_simp [hn0, hsub]

theorem gap2 (m : ℝ) :
    Asymptotics.IsBigO atTop
      (fun n : ℕ =>
        |((n : ℝ) + 1) / (m - n)| - ratioModel m n)
      (fun n : ℕ => 1 / ((n : ℝ) ^ 2)) := by
  have hzero : ∀ᶠ n : ℕ in atTop,
      (1 / ((n : ℝ) ^ 2) = 0 →
        |((n : ℝ) + 1) / (m - n)| - ratioModel m n = 0) := by
    filter_upwards [Ici_mem_atTop 1] with n hn
    intro hzero
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
    exfalso
    exact (one_div_ne_zero (pow_ne_zero 2 hn0)) hzero
  have hdiv : Tendsto
      ((fun n : ℕ => |((n : ℝ) + 1) / (m - n)| - ratioModel m n) /
        fun n : ℕ => 1 / ((n : ℝ) ^ 2))
      atTop (nhds (m ^ 2)) := by
    have hlimit : Tendsto
        (fun n : ℕ => m ^ 2 * (((n : ℝ) + 1) / ((n : ℝ) - m)))
        atTop (nhds (m ^ 2)) := by
      simpa using (tendsto_const_nhds.mul (tendsto_ratio_linear m))
    apply hlimit.congr'
    have hnlarge : ∀ᶠ n : ℕ in atTop, m < (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop m)
    filter_upwards [hnlarge, Ici_mem_atTop 1] with n hmn hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
    have hsub : (n : ℝ) - m ≠ 0 := ne_of_gt (sub_pos.mpr hmn)
    have hsub' : m - (n : ℝ) ≠ 0 := ne_of_lt (sub_neg.mpr hmn)
    have hneg : ((n : ℝ) + 1) / (m - (n : ℝ)) < 0 :=
      div_neg_of_pos_of_neg (by positivity) (sub_neg.mpr hmn)
    simp only [Pi.div_apply, ratioModel]
    rw [abs_of_neg hneg]
    field_simp [hn0, hsub, hsub']
    ring
  exact isBigO_of_div_tendsto_nhds hzero (m ^ 2) hdiv

theorem gap3 (m : ℝ) :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => ratioModel m n -
        (1 + (m + 1) / (n : ℝ)))
      (fun n : ℕ => 1 / ((n : ℝ) ^ 2)) := by
  apply (isBigO_const_mul_self m (fun n : ℕ => 1 / ((n : ℝ) ^ 2)) atTop).congr'
  · filter_upwards [Ici_mem_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
    unfold ratioModel
    field_simp [hn0]
    ring
  · exact EventuallyEq.rfl

theorem gap4 (m : ℝ) (hm : ∀ k : ℕ, m ≠ k) :
    Asymptotics.IsBigO atTop (ratioRemainder m)
      (fun n : ℕ => 1 / ((n : ℝ) ^ 2)) := by
  have hratio : ratioAbs m =ᶠ[atTop]
      (fun n : ℕ => |((n : ℝ) + 1) / (m - n)|) := by
    filter_upwards [Ici_mem_atTop 1] with n hn
    exact gap1 m n hn (generalizedBinomial_ne_zero_of_not_nat m hm (n + 1))
  apply ((gap2 m).add (gap3 m)).congr'
  · filter_upwards [hratio] with n hn
    unfold ratioRemainder
    rw [hn]
    ring
  · exact EventuallyEq.rfl

theorem gap5 (m : ℝ) (hm : 0 < m) :
    Summable (fun n : ℕ => |generalizedBinomial m (n + 1)|) := by
  obtain ⟨N, hN⟩ := exists_nat_ge m
  exact summable_abs_of_pos_of_le_nat N m hm hN

theorem gap6 (m : ℝ) (hm : m < 0) :
    ¬ Summable (fun n : ℕ => |generalizedBinomial m (n + 1)|) := by
  intro hsum
  have hscaled : Summable (fun n : ℕ => (-m) * (1 / (n + 1 : ℝ))) := by
    apply hsum.of_nonneg_of_le
    · intro n
      exact mul_nonneg (neg_nonneg.mpr hm.le) (one_div_nonneg.mpr (by positivity))
    · intro n
      convert neg_div_nat_succ_le_abs m hm n using 1 <;> ring
  have hharmonic : Summable (fun n : ℕ => (1 / (n + 1 : ℝ))) := by
    apply (summable_mul_left_iff (show -m ≠ 0 by linarith)).mp
    simpa using hscaled
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff 1).mp
  simpa using hharmonic

theorem gap7 (m : ℝ) (hm : m = 0) :
    ∀ n : ℕ, 1 ≤ n → generalizedBinomial m n = 0 := by
  subst m
  intro n hn
  exact generalizedBinomial_zero_of_pos n (Nat.zero_lt_one.trans_le hn)

theorem gap8 (m : ℝ) (hm : m = 0) :
    Summable (fun n : ℕ => |generalizedBinomial m (n + 1)|) := by
  apply summable_zero.congr
  intro n
  rw [gap7 m hm (n + 1) (by omega), abs_zero]

theorem gap9 (m : ℝ) (hm₀ : -1 < m) (hm₁ : m < 0) :
    ∀ n : ℕ,
      generalizedBinomial m (n + 1) *
        generalizedBinomial m (n + 2) ≤ 0 := by
  intro n
  rw [generalizedBinomial_succ m (n + 1)]
  norm_num [Nat.cast_add, Nat.cast_one]
  have hq : (m - (↑n + 1)) / (↑n + 1 + 1) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · have hn : (0 : ℝ) ≤ n + 1 := by positivity
      linarith
    · positivity
  calc
    generalizedBinomial m (n + 1) *
        (generalizedBinomial m (n + 1) *
          (m - (↑n + 1)) / (↑n + 1 + 1)) =
        generalizedBinomial m (n + 1) ^ 2 *
          ((m - (↑n + 1)) / (↑n + 1 + 1)) := by ring
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hq

theorem gap10 (m : ℝ) (hm₀ : -1 < m) (hm₁ : m < 0) :
    ∀ n : ℕ,
      |(m - (n + 1)) / ((n : ℝ) + 2)| < 1 ↔
        |generalizedBinomial m (n + 2)| <
          |generalizedBinomial m (n + 1)| := by
  intro n
  have heq : |generalizedBinomial m (n + 2)| =
      |generalizedBinomial m (n + 1)| *
        |(m - ((n : ℝ) + 1)) / ((n : ℝ) + 2)| := by
    rw [generalizedBinomial_succ m (n + 1)]
    norm_num [Nat.cast_add, Nat.cast_one]
    rw [show generalizedBinomial m (n + 1) * (m - (↑n + 1)) / (↑n + 1 + 1) =
        generalizedBinomial m (n + 1) * ((m - (↑n + 1)) / (↑n + 2)) by ring,
      abs_mul]
  rw [heq]
  have hg : 0 < |generalizedBinomial m (n + 1)| :=
    abs_pos.mpr (generalizedBinomial_ne_zero_of_neg m hm₁ (n + 1))
  constructor
  · intro h
    calc
      |generalizedBinomial m (n + 1)| *
          |(m - ((n : ℝ) + 1)) / ((n : ℝ) + 2)| <
          |generalizedBinomial m (n + 1)| * 1 :=
        mul_lt_mul_of_pos_left h hg
      _ = |generalizedBinomial m (n + 1)| := by ring
  · intro h
    have h' : |generalizedBinomial m (n + 1)| *
        |(m - ((n : ℝ) + 1)) / ((n : ℝ) + 2)| <
        |generalizedBinomial m (n + 1)| * 1 := by simpa using h
    exact lt_of_mul_lt_mul_left h' (le_of_lt hg)

theorem gap11 (m : ℝ) (hm₀ : -1 < m) (hm₁ : m < 0) :
    Antitone (fun n : ℕ => |generalizedBinomial m (n + 1)|) := by
  exact abs_generalizedBinomial_antitone m hm₀ hm₁

theorem gap12 (m : ℝ) (hm₀ : -1 < m) (hm₁ : m < 0) :
    ∀ n : ℕ, 1 ≤ n →
      logAbs m n =
        Real.log
          |(∏ k ∈ Finset.range n, (m - k)) /
            (Nat.factorial n : ℝ)| := by
  intro n hn
  rfl

theorem gap13 (m : ℝ) (hm₀ : -1 < m) (hm₁ : m < 0) :
    ∀ n : ℕ, 1 ≤ n →
      logAbs m n =
        ∑ k ∈ Finset.Icc 1 n,
          Real.log (1 - (m + 1) / (k : ℝ)) := by
  intro n hn
  exact logAbs_eq_sum_Icc m hm₀ hm₁ n

theorem gap14 (m : ℝ) (hm₀ : -1 < m) (hm₁ : m < 0) :
    ∀ n : ℕ, 1 ≤ n →
      logAbs m n =
        ∑ k ∈ Finset.Icc 1 n,
          Real.log (1 - (m + 1) / (k : ℝ)) := by
  exact gap13 m hm₀ hm₁

theorem gap15 (m : ℝ) (hm₀ : -1 < m) (hm₁ : m < 0) :
    Tendsto
      (fun n : ℕ =>
        ∑ k ∈ Finset.Icc 1 n,
          Real.log (1 - (m + 1) / (k : ℝ)))
      atTop atBot := by
  exact log_sum_tendsto_atBot m hm₀ hm₁

theorem gap16 (m : ℝ) (hm₀ : -1 < m) (hm₁ : m < 0) :
    Tendsto (fun n : ℕ => |generalizedBinomial m (n + 1)|)
      atTop (nhds 0) := by
  exact abs_generalizedBinomial_tendsto_zero m hm₀ hm₁

theorem gap17 (m : ℝ) (hm₀ : -1 < m) (hm₁ : m < 0) :
    ProofGap.SeriesConverges
      (fun n : ℕ => generalizedBinomial m (n + 1)) := by
  rcases (gap11 m hm₀ hm₁).tendsto_alternating_series_of_tendsto_zero
      (gap16 m hm₀ hm₁) with ⟨l, hl⟩
  apply seriesConverges_iff_tendsto_partialSums.mpr
  refine ⟨-l, ?_⟩
  apply hl.neg.congr'
  filter_upwards with n
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simpa [pow_succ] using
    (generalizedBinomial_eq_negOnePow_mul_abs m hm₁ (i + 1)).symm

theorem gap18 (m : ℝ) (hm₀ : -1 < m) (hm₁ : m < 0) :
    ConditionallySummable
      (fun n : ℕ => generalizedBinomial m (n + 1)) := by
  exact ⟨gap17 m hm₀ hm₁, gap6 m hm₁⟩

theorem gap19 (m : ℝ) (hm : m ≤ -1) :
    ¬ Tendsto (fun n : ℕ => generalizedBinomial m (n + 1))
      atTop (nhds 0) := by
  intro h
  have hsmall := h.norm.eventually
    (Iio_mem_nhds (show ‖(0 : ℝ)‖ < (1 / 2 : ℝ) by norm_num))
  rcases hsmall.exists with ⟨n, hn⟩
  rw [Real.norm_eq_abs] at hn
  linarith [one_le_abs_generalizedBinomial_of_le_neg_one m hm n]

theorem gap20 (m : ℝ) (hm : m ≤ -1) :
    ¬ ProofGap.SeriesConverges
      (fun n : ℕ => generalizedBinomial m (n + 1)) := by
  intro h
  exact gap19 m hm (seriesConverges_tendsto_zero h)

set_option maxHeartbeats 800000 in
theorem gap21 (m : ℝ) :
    (Summable (fun n : ℕ => |generalizedBinomial m (n + 1)|) ↔ 0 ≤ m) ∧
    (ConditionallySummable
      (fun n : ℕ => generalizedBinomial m (n + 1)) ↔ -1 < m ∧ m < 0) ∧
    (¬ ProofGap.SeriesConverges
        (fun n : ℕ => generalizedBinomial m (n + 1)) ↔
      m ≤ -1) := by
  have habs :
      Summable (fun n : ℕ => |generalizedBinomial m (n + 1)|) ↔ 0 ≤ m := by
    constructor
    · intro h
      exact le_of_not_gt fun hm => gap6 m hm h
    · intro hm
      rcases hm.eq_or_lt with rfl | hm
      · exact gap8 0 rfl
      · exact gap5 m hm
  have hconv_nonneg (hm : 0 ≤ m) :
      ProofGap.SeriesConverges (fun n : ℕ => generalizedBinomial m (n + 1)) := by
    have hsigned : Summable (fun n : ℕ => generalizedBinomial m (n + 1)) := by
      simpa [Real.norm_eq_abs] using (habs.mpr hm).of_norm
    exact seriesConverges_of_summable hsigned
  refine ⟨habs, ?_, ?_⟩
  · constructor
    · intro hcond
      have hm1 : m < 0 := by
        by_contra h
        exact hcond.2 (habs.mpr (le_of_not_gt h))
      have hm0 : -1 < m := by
        by_contra h
        exact gap20 m (le_of_not_gt h) hcond.1
      exact ⟨hm0, hm1⟩
    · rintro ⟨hm0, hm1⟩
      exact gap18 m hm0 hm1
  · constructor
    · intro hnot
      by_contra h
      have hm0 : -1 < m := lt_of_not_ge h
      by_cases hm1 : m < 0
      · exact hnot (gap17 m hm0 hm1)
      · exact hnot (hconv_nonneg (le_of_not_gt hm1))
    · exact gap20 m

end

end ProofGap.Exercise2700
