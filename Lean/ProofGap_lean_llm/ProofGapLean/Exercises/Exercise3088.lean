import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise3088

noncomputable section

open Filter
open scoped BigOperators Topology

def term (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) / (n : ℝ)

def logTerm (n : ℕ) : ℝ :=
  Real.log (1 + term n)

def SummableFromOne (f : ℕ → ℝ) : Prop :=
  Summable (fun k : ℕ => f (k + 1))

def ConditionallySummableFromOne (f : ℕ → ℝ) : Prop :=
  ProofGap.SeriesConverges (fun k : ℕ => f (k + 1)) ∧
    ¬SummableFromOne (fun n => |f n|)

def partialProduct (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, (1 + term i)

def NonzeroConvergentProduct : Prop :=
  ∃ P : ℝ, P ≠ 0 ∧ Tendsto partialProduct atTop (𝓝 P)

private theorem seriesConverges_iff_tendsto_sum_range (u : ℕ → ℝ) :
    ProofGap.SeriesConverges u ↔
      ∃ l : ℝ,
        Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, u n) atTop (𝓝 l) := by
  unfold ProofGap.SeriesConverges Summable HasSum
  rw [SummationFilter.conditional_filter_eq_map_range]
  simp only [tendsto_map'_iff]
  constructor <;> rintro ⟨l, hl⟩
  · exact ⟨l, by simpa [Function.comp_def] using hl⟩
  · exact ⟨l, by simpa [Function.comp_def] using hl⟩

private theorem one_div_succ_antitone :
    Antitone (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ)) := by
  intro a b hab
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.add_le_add_right hab 1

private theorem one_div_succ_tendsto_zero :
    Tendsto (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hbase : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  simpa [Function.comp_def] using
    hbase.comp (tendsto_add_atTop_nat 1)

private theorem term_shift_eq (k : ℕ) :
    term (k + 1) = (-1 : ℝ) ^ k * (1 / ((k + 1 : ℕ) : ℝ)) := by
  unfold term
  rw [show k + 1 + 1 = k + 2 by omega,
    show k + 2 = 2 + k by omega, pow_add]
  norm_num
  ring

private theorem term_seriesConverges :
    ProofGap.SeriesConverges (fun k : ℕ => term (k + 1)) := by
  obtain ⟨l, hl⟩ :=
    one_div_succ_antitone.tendsto_alternating_series_of_tendsto_zero
      one_div_succ_tendsto_zero
  apply (seriesConverges_iff_tendsto_sum_range _).2
  refine ⟨l, ?_⟩
  convert hl using 1
  funext N
  apply Finset.sum_congr rfl
  intro k hk
  exact term_shift_eq k

private theorem abs_term_shift_not_summable :
    ¬ Summable (fun k : ℕ => |term (k + 1)|) := by
  intro hs
  have hshift : Summable (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ)) := by
    convert hs using 1
    funext k
    rw [term_shift_eq, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (by positivity :
        0 ≤ 1 / ((k + 1 : ℕ) : ℝ))]
  have hharm : Summable (fun n : ℕ => 1 / (n : ℝ)) := by
    apply (summable_nat_add_iff 1).mp
    simpa [Nat.cast_add] using hshift
  exact Real.not_summable_one_div_natCast hharm

private theorem partialProduct_succ (n : ℕ) :
    partialProduct (n + 1) =
      partialProduct n * (1 + term (n + 1)) := by
  unfold partialProduct
  have hIcc :
      Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext i
    simp
    omega
  rw [hIcc, Finset.prod_insert (by simp)]
  ring

private theorem pairedFactors (k : ℕ) :
    (1 + term (2 * k + 1)) * (1 + term (2 * k + 2)) = 1 := by
  have hodd : (-1 : ℝ) ^ (2 * k + 2) = 1 := by
    rw [show 2 * k + 2 = 2 * (k + 1) by omega, pow_mul]
    norm_num
  have heven : (-1 : ℝ) ^ (2 * k + 3) = -1 := by
    rw [show 2 * k + 3 = 2 * (k + 1) + 1 by omega, pow_add, pow_mul]
    norm_num
  unfold term
  rw [show 2 * k + 1 + 1 = 2 * k + 2 by omega,
    show 2 * k + 2 + 1 = 2 * k + 3 by omega, hodd, heven]
  push_cast
  have hk1 : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  have hk2 : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
  field_simp [hk1, hk2]
  ring

private theorem logTerm_pair (k : ℕ) :
    logTerm (2 * k + 1) + logTerm (2 * k + 2) = 0 := by
  let a : ℝ := 1 + term (2 * k + 1)
  let b : ℝ := 1 + term (2 * k + 2)
  have hab : a * b = 1 := by
    dsimp [a, b]
    exact pairedFactors k
  have ha : a ≠ 0 := by
    intro h
    rw [h] at hab
    norm_num at hab
  have hb : b ≠ 0 := by
    intro h
    rw [h] at hab
    norm_num at hab
  have hlog := Real.log_mul ha hb
  rw [hab] at hlog
  simpa [a, b, logTerm] using hlog.symm

private theorem log_partial_sum_even (k : ℕ) :
    (∑ i ∈ Finset.range (2 * k), logTerm (i + 1)) = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ, ih]
      have hp := logTerm_pair k
      rw [show 2 * k + 1 + 1 = 2 * k + 2 by omega]
      linarith

private theorem log_partial_sum_odd (k : ℕ) :
    (∑ i ∈ Finset.range (2 * k + 1), logTerm (i + 1)) =
      logTerm (2 * k + 1) := by
  rw [Finset.sum_range_succ, log_partial_sum_even]
  simp

private theorem term_tendsto_zero : Tendsto term atTop (𝓝 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  apply squeeze_zero' (g := fun n : ℕ => 1 / (n : ℝ))
  · exact Eventually.of_forall (fun n => norm_nonneg _)
  · filter_upwards with n
    simp [term, norm_div, norm_pow, abs_of_nonneg]
  · simpa only [one_div] using hbound

private theorem logTerm_tendsto_zero : Tendsto logTerm atTop (𝓝 0) := by
  have harg : Tendsto (fun n : ℕ => 1 + term n) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add term_tendsto_zero
  have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp harg
  simpa [logTerm] using hlog

private theorem log_partial_sum_abs_le (n : ℕ) :
    |∑ i ∈ Finset.range n, logTerm (i + 1)| ≤ |logTerm n| := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [log_partial_sum_even]
    simpa using abs_nonneg (logTerm (2 * k))
  · rw [log_partial_sum_odd]

private theorem logTerm_seriesConverges :
    ProofGap.SeriesConverges (fun k : ℕ => logTerm (k + 1)) := by
  apply (seriesConverges_iff_tendsto_sum_range _).2
  refine ⟨0, ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hevent : ∀ᶠ n : ℕ in atTop, |logTerm n| < ε := by
    have := (Metric.tendsto_nhds.1 logTerm_tendsto_zero) ε hε
    simpa [Real.dist_eq] using this
  filter_upwards [hevent] with n hn
  rw [Real.dist_eq, sub_zero]
  exact (log_partial_sum_abs_le n).trans_lt hn

private theorem abs_logTerm_even_lower (k : ℕ) :
    1 / ((2 * k + 2 : ℕ) : ℝ) ≤ |logTerm (2 * k + 2)| := by
  have hpow : (-1 : ℝ) ^ (2 * k + 3) = -1 := by
    rw [show 2 * k + 3 = 2 * (k + 1) + 1 by omega, pow_add, pow_mul]
    norm_num
  have hden : (0 : ℝ) < ((2 * k + 2 : ℕ) : ℝ) := by positivity
  have hden1 : (1 : ℝ) < ((2 * k + 2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 < 2 * k + 2)
  have hx : 0 < 1 - 1 / ((2 * k + 2 : ℕ) : ℝ) := by
    exact sub_pos.mpr ((div_lt_one hden).2 hden1)
  have hlog := Real.log_le_sub_one_of_pos hx
  have hinv : 0 < 1 / ((2 * k + 2 : ℕ) : ℝ) := one_div_pos.mpr hden
  have hlog0 : Real.log (1 - 1 / ((2 * k + 2 : ℕ) : ℝ)) ≤ 0 := by
    linarith
  have hterm : logTerm (2 * k + 2) =
      Real.log (1 - 1 / ((2 * k + 2 : ℕ) : ℝ)) := by
    unfold logTerm term
    rw [show 2 * k + 2 + 1 = 2 * k + 3 by omega, hpow]
    ring
  rw [hterm, abs_of_nonpos hlog0]
  linarith

private theorem abs_logTerm_shift_not_summable :
    ¬ Summable (fun k : ℕ => |logTerm (k + 1)|) := by
  intro hs
  have heven : Summable (fun k : ℕ => |logTerm (2 * k + 2)|) := by
    have hi : Function.Injective (fun k : ℕ => 2 * k + 1) := by
      intro a b h
      exact Nat.mul_left_cancel (by norm_num) (Nat.add_right_cancel h)
    have hc := hs.comp_injective hi
    simpa [Nat.add_assoc] using hc
  have hlower : Summable (fun k : ℕ => 1 / ((2 * k + 2 : ℕ) : ℝ)) :=
    Summable.of_nonneg_of_le (fun k => by positivity)
      abs_logTerm_even_lower heven
  have hshift : Summable (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ)) := by
    refine (hlower.mul_left 2).congr (fun k => ?_)
    push_cast
    field_simp
  have hharm : Summable (fun n : ℕ => 1 / (n : ℝ)) := by
    apply (summable_nat_add_iff 1).mp
    simpa [Nat.cast_add] using hshift
  exact Real.not_summable_one_div_natCast hharm

private theorem partialProduct_even (k : ℕ) :
    partialProduct (2 * k) = 1 := by
  induction k with
  | zero =>
      simp [partialProduct]
  | succ k ih =>
      calc
        partialProduct (2 * (k + 1)) =
            partialProduct ((2 * k + 1) + 1) := by congr 1 <;> omega
        _ = partialProduct (2 * k + 1) *
              (1 + term (2 * k + 2)) := partialProduct_succ (2 * k + 1)
        _ = (partialProduct (2 * k) * (1 + term (2 * k + 1))) *
              (1 + term (2 * k + 2)) := by
                rw [partialProduct_succ (2 * k)]
        _ = 1 := by
              rw [ih]
              simpa [mul_assoc] using pairedFactors k

private theorem partialProduct_odd (k : ℕ) :
    partialProduct (2 * k + 1) =
      1 + 1 / ((2 * k + 1 : ℕ) : ℝ) := by
  rw [partialProduct_succ (2 * k), partialProduct_even]
  have hpow : (-1 : ℝ) ^ (2 * k + 2) = 1 := by
    rw [show 2 * k + 2 = 2 * (k + 1) by omega, pow_mul]
    norm_num
  unfold term
  rw [show 2 * k + 1 = 2 * k + 1 by rfl,
    show 2 * k + 1 + 1 = 2 * k + 2 by omega, hpow]
  ring

private theorem partialProduct_error_bound (n : ℕ) :
    |partialProduct n - 1| ≤ 1 / (n : ℝ) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [partialProduct_even]
    simp
  · rw [partialProduct_odd]
    have hpos : (0 : ℝ) ≤ 1 / ((2 * k + 1 : ℕ) : ℝ) := by positivity
    rw [show 1 + 1 / ((2 * k + 1 : ℕ) : ℝ) - 1 =
      1 / ((2 * k + 1 : ℕ) : ℝ) by ring, abs_of_nonneg hpos]

private theorem partialProduct_tendsto_one :
    Tendsto partialProduct atTop (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound :
      Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n => norm_nonneg _
  · filter_upwards with n
    simpa [Real.norm_eq_abs] using partialProduct_error_bound n
  · simpa only [one_div] using hbound

/-- Source: `proof_gap/exercise_3088/1.txt`. -/
theorem gap1 : ConditionallySummableFromOne term := by
  exact ⟨term_seriesConverges, by
    unfold SummableFromOne
    exact abs_term_shift_not_summable⟩

/-- Source: `proof_gap/exercise_3088/2.txt`. -/
theorem gap2 : SummableFromOne (fun n => (term n) ^ 2) := by
  unfold SummableFromOne
  have hp : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ 2)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num : (1 : ℕ) < 2)
  have hs := (summable_nat_add_iff 1).2 hp
  convert hs using 1
  funext k
  unfold term
  push_cast
  rw [div_pow]
  have hsign : (((-1 : ℝ) ^ (k + 2)) ^ 2) = 1 := by
    rw [← pow_mul]
    norm_num
  rw [hsign]

/-- Source: `proof_gap/exercise_3088/3.txt`. -/
theorem gap3 : ConditionallySummableFromOne logTerm := by
  exact ⟨logTerm_seriesConverges, by
    unfold SummableFromOne
    exact abs_logTerm_shift_not_summable⟩

/--
Source: `proof_gap/exercise_3088/4.txt`; convergence applies to the cutoff
sequence of partial products.
-/
theorem gap4 : NonzeroConvergentProduct := by
  refine ⟨1, one_ne_zero, partialProduct_tendsto_one⟩

end

end ProofGap.Exercise3088
