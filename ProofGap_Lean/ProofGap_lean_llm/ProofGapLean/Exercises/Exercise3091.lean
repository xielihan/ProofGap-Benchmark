import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise3091

noncomputable section

open Filter
open scoped BigOperators Topology

def alternatingLogTerm (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / Real.log n

def logSquareTerm (n : ℕ) : ℝ :=
  1 / (Real.log n) ^ 2

def harmonicTerm (n : ℕ) : ℝ :=
  1 / (n : ℝ)

def SummableFromTwo (f : ℕ → ℝ) : Prop :=
  ProofGap.SeriesConverges (fun k : ℕ => f (k + 2))

def ConditionallySummableFromTwo (f : ℕ → ℝ) : Prop :=
  SummableFromTwo f ∧ ¬SummableFromTwo (fun n => |f n|)

def partialProduct (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 2 n, (1 + alternatingLogTerm i)

def NonzeroConvergentProduct : Prop :=
  ∃ P : ℝ, P ≠ 0 ∧ Tendsto partialProduct atTop (𝓝 P)

def DivergentProduct : Prop :=
  ¬NonzeroConvergentProduct

private theorem seriesConverges_of_tendsto {f : ℕ → ℝ} {s : ℝ}
    (h : Tendsto (fun n => ∑ i ∈ Finset.range n, f i) atTop (𝓝 s)) :
    ProofGap.SeriesConverges f := by
  unfold ProofGap.SeriesConverges Summable
  refine ⟨s, ?_⟩
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range]
  simpa [Function.comp_def] using h

private theorem summable_of_seriesConverges_of_nonneg {f : ℕ → ℝ}
    (h : ProofGap.SeriesConverges f) (hf : ∀ n, 0 ≤ f n) :
    Summable f := by
  unfold ProofGap.SeriesConverges Summable at h
  rcases h with ⟨s, hs⟩
  have ht : Tendsto (fun n => ∑ i ∈ Finset.range n, f i) atTop (𝓝 s) := by
    rw [HasSum, SummationFilter.conditional_filter_eq_map_range] at hs
    simpa [Function.comp_def] using hs
  exact ((hasSum_iff_tendsto_nat_of_nonneg hf s).2 ht).summable

private theorem log_two_lt_one : Real.log 2 < 1 := by
  have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≠ 1)
  norm_num at h ⊢
  exact h

private theorem log_sq_lt_nat (n : ℕ) (hn : 2 ≤ n) :
    (Real.log n) ^ 2 < (n : ℝ) := by
  by_cases hn4 : 4 ≤ n
  · let y : ℝ := Real.sqrt n
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hy0 : 0 ≤ y := Real.sqrt_nonneg _
    have hy2 : (2 : ℝ) ≤ y := by
      have hsquare : y ^ 2 = (n : ℝ) := Real.sq_sqrt hn0
      have hn4R : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
      nlinarith
    have hypos : 0 < y := lt_of_lt_of_le (by norm_num) hy2
    have hhalfpos : 0 < y / 2 := by positivity
    have hloghalf : Real.log (y / 2) ≤ y / 2 - 1 :=
      Real.log_le_sub_one_of_pos hhalfpos
    have hlogmul : Real.log y = Real.log (y / 2) + Real.log 2 := by
      rw [← Real.log_mul (ne_of_gt hhalfpos) (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
      field_simp
    have hlogy : 2 * Real.log y < y := by
      rw [hlogmul]
      nlinarith [log_two_lt_one]
    have hlogsqrt := Real.log_sqrt hn0
    have hlogn : Real.log n = 2 * Real.log y := by
      dsimp [y] at hlogsqrt ⊢
      linarith
    have hlogpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hsquare : y ^ 2 = (n : ℝ) := Real.sq_sqrt hn0
    have hloglt : Real.log n < y := by rw [hlogn]; exact hlogy
    nlinarith [mul_pos hlogpos (sub_pos.mpr hloglt)]
  · have hcases : n = 2 ∨ n = 3 := by omega
    rcases hcases with rfl | rfl
    · have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hprod := mul_pos hp (sub_pos.mpr log_two_lt_one)
      norm_num at hprod ⊢
      nlinarith
    · have hloghalf : Real.log (3 / 2 : ℝ) < 1 / 2 := by
        have h := Real.log_lt_sub_one_of_pos
          (by norm_num : (0 : ℝ) < 3 / 2)
          (by norm_num : (3 / 2 : ℝ) ≠ 1)
        norm_num at h ⊢
        exact h
      have hlogthree : Real.log 3 = Real.log (3 / 2) + Real.log 2 := by
        rw [← Real.log_mul (by norm_num : (3 / 2 : ℝ) ≠ 0)
          (by norm_num : (2 : ℝ) ≠ 0)]
        norm_num
      have hp : 0 < Real.log 3 := Real.log_pos (by norm_num)
      have hupper : Real.log 3 < 3 / 2 := by
        rw [hlogthree]
        nlinarith [log_two_lt_one]
      have hprod := mul_pos hp (sub_pos.mpr hupper)
      norm_num at hprod ⊢
      nlinarith

private theorem harmonic_lt_logSquare (n : ℕ) (hn : 2 ≤ n) :
    harmonicTerm n < logSquareTerm n := by
  have hlogpos : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  unfold harmonicTerm logSquareTerm
  exact one_div_lt_one_div_of_lt (sq_pos_of_pos hlogpos) (log_sq_lt_nat n hn)

private theorem not_summable_harmonic_shifted :
    ¬Summable (fun k : ℕ => harmonicTerm (k + 2)) := by
  intro hs
  unfold harmonicTerm at hs
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff 2).mp
  simpa [Nat.cast_add] using hs

private theorem not_summable_logSquare_shifted :
    ¬Summable (fun k : ℕ => logSquareTerm (k + 2)) := by
  intro hs
  apply not_summable_harmonic_shifted
  exact Summable.of_nonneg_of_le
    (fun k => by unfold harmonicTerm; positivity)
    (fun k => (harmonic_lt_logSquare (k + 2) (by omega)).le)
    hs

private theorem not_summable_harmonic_from_two :
    ¬SummableFromTwo harmonicTerm := by
  intro hs
  unfold SummableFromTwo at hs
  exact not_summable_harmonic_shifted
    (summable_of_seriesConverges_of_nonneg hs fun k => by
      unfold harmonicTerm
      positivity)

private theorem not_summable_logSquare_from_two :
    ¬SummableFromTwo logSquareTerm := by
  intro hs
  unfold SummableFromTwo at hs
  exact not_summable_logSquare_shifted
    (summable_of_seriesConverges_of_nonneg hs fun k => by
      unfold logSquareTerm
      positivity)

private def productFactor (n : ℕ) : ℝ := 1 + alternatingLogTerm n

private def pairTerm (k : ℕ) : ℝ :=
  productFactor (2 * k + 3) * productFactor (2 * k + 4)

private def pairLoss (k : ℕ) : ℝ := logSquareTerm (2 * k + 4)

private def pairedProduct (N : ℕ) : ℝ :=
  ∏ k ∈ Finset.range N, pairTerm k

private theorem log_gt_one_of_three_le (n : ℕ) (hn : 3 ≤ n) :
    1 < Real.log n := by
  have hlog3 : 1 < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 Real.exp_one_lt_three
  have hmono : Real.log 3 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  exact hlog3.trans_le hmono

private theorem productFactor_odd (k : ℕ) :
    productFactor (2 * k + 3) =
      1 - 1 / Real.log (((2 * k + 3 : ℕ) : ℝ)) := by
  unfold productFactor alternatingLogTerm
  have hp : ((-1 : ℝ) ^ (2 * k + 3)) = -1 := by
    rw [show 2 * k + 3 = 2 * (k + 1) + 1 by omega, pow_add, pow_mul]
    norm_num
  rw [hp]
  push_cast
  ring

private theorem productFactor_even (k : ℕ) :
    productFactor (2 * k + 4) =
      1 + 1 / Real.log (((2 * k + 4 : ℕ) : ℝ)) := by
  unfold productFactor alternatingLogTerm
  have hp : ((-1 : ℝ) ^ (2 * k + 4)) = 1 := by
    rw [show 2 * k + 4 = 2 * (k + 2) by omega, pow_mul]
    norm_num
  rw [hp]

private theorem pairTerm_pos (k : ℕ) : 0 < pairTerm k := by
  rw [pairTerm, productFactor_odd, productFactor_even]
  have hA : 1 < Real.log (((2 * k + 3 : ℕ) : ℝ)) :=
    log_gt_one_of_three_le (2 * k + 3) (by omega)
  have hB : 0 < Real.log (((2 * k + 4 : ℕ) : ℝ)) :=
    Real.log_pos (by exact_mod_cast (show 1 < 2 * k + 4 by omega))
  have hodd : 0 < 1 - 1 / Real.log (((2 * k + 3 : ℕ) : ℝ)) := by
    have := (div_lt_one (lt_trans zero_lt_one hA)).2 hA
    linarith
  have heven : 0 < 1 + 1 / Real.log (((2 * k + 4 : ℕ) : ℝ)) := by positivity
  exact mul_pos hodd heven

private theorem pairTerm_le_one_sub_loss (k : ℕ) :
    pairTerm k ≤ 1 - pairLoss k := by
  rw [pairTerm, productFactor_odd, productFactor_even]
  unfold pairLoss logSquareTerm
  let A : ℝ := Real.log (((2 * k + 3 : ℕ) : ℝ))
  let B : ℝ := Real.log (((2 * k + 4 : ℕ) : ℝ))
  have hA : 0 < A := lt_trans zero_lt_one
    (log_gt_one_of_three_le (2 * k + 3) (by omega))
  have hAB : A < B := by
    dsimp [A, B]
    apply Real.log_lt_log
    · positivity
    · exact_mod_cast (show 2 * k + 3 < 2 * k + 4 by omega)
  have hB : 0 < B := hA.trans hAB
  change (1 - 1 / A) * (1 + 1 / B) ≤ 1 - 1 / B ^ 2
  field_simp [ne_of_gt hA, ne_of_gt hB]
  nlinarith [mul_pos hA (sub_pos.mpr hAB)]

private theorem pairTerm_le_exp_neg_loss (k : ℕ) :
    pairTerm k ≤ Real.exp (-pairLoss k) := by
  calc
    pairTerm k ≤ 1 - pairLoss k := pairTerm_le_one_sub_loss k
    _ ≤ Real.exp (-pairLoss k) := by
      simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-pairLoss k)

private theorem pairLoss_pos (k : ℕ) : 0 < pairLoss k := by
  unfold pairLoss logSquareTerm
  have hlog : 0 < Real.log (((2 * k + 4 : ℕ) : ℝ)) :=
    Real.log_pos (by exact_mod_cast (show 1 < 2 * k + 4 by omega))
  exact one_div_pos.mpr (sq_pos_of_pos hlog)

private theorem not_summable_pairLoss : ¬Summable pairLoss := by
  intro hs
  have hbase : Summable (fun k : ℕ => 1 / (2 * ((k + 2 : ℕ) : ℝ))) :=
    Summable.of_nonneg_of_le
      (fun k => by positivity)
      (fun k => by
        have h := harmonic_lt_logSquare (2 * k + 4) (by omega)
        calc
          1 / (2 * ((k + 2 : ℕ) : ℝ)) = harmonicTerm (2 * k + 4) := by
            unfold harmonicTerm
            push_cast
            ring
          _ ≤ pairLoss k := by
            unfold pairLoss
            exact h.le)
      hs
  have hscaled := hbase.mul_left 2
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff 2).mp
  convert hscaled using 1
  funext k
  have hk : (2 : ℝ) * ((k : ℝ) + 2) ≠ 0 := by positivity
  field_simp [hk]

private theorem pairLoss_partialSum_tendsto_atTop :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, pairLoss k)
      atTop atTop := by
  exact (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun k => (pairLoss_pos k).le)).1 not_summable_pairLoss

private theorem pairedProduct_nonneg (N : ℕ) : 0 ≤ pairedProduct N := by
  unfold pairedProduct
  apply Finset.prod_nonneg
  intro k hk
  exact (pairTerm_pos k).le

private theorem pairedProduct_le_exp (N : ℕ) :
    pairedProduct N ≤
      Real.exp (-(∑ k ∈ Finset.range N, pairLoss k)) := by
  unfold pairedProduct
  calc
    (∏ k ∈ Finset.range N, pairTerm k) ≤
        ∏ k ∈ Finset.range N, Real.exp (-pairLoss k) := by
      apply Finset.prod_le_prod
      · intro k hk
        exact (pairTerm_pos k).le
      · intro k hk
        exact pairTerm_le_exp_neg_loss k
    _ = Real.exp (∑ k ∈ Finset.range N, -pairLoss k) := by
      rw [Real.exp_sum]
    _ = _ := by rw [Finset.sum_neg_distrib]

private theorem pairedProduct_tendsto_zero :
    Tendsto pairedProduct atTop (𝓝 0) := by
  have hupper : Tendsto
      (fun N : ℕ => Real.exp (-(∑ k ∈ Finset.range N, pairLoss k)))
      atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_neg_atBot_iff.mpr pairLoss_partialSum_tendsto_atTop)
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall pairedProduct_nonneg
  · exact Filter.Eventually.of_forall pairedProduct_le_exp
  · exact hupper

private theorem partialProduct_succ (n : ℕ) (hn : 1 ≤ n) :
    partialProduct (n + 1) = partialProduct n * productFactor (n + 1) := by
  have hs : Finset.Icc 2 (n + 1) =
      insert (n + 1) (Finset.Icc 2 n) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  unfold partialProduct productFactor
  rw [hs, Finset.prod_insert]
  · ring
  · simp

private theorem partialProduct_two :
    partialProduct 2 = productFactor 2 := by
  simp [partialProduct, productFactor]

private theorem partialProduct_even_form (N : ℕ) :
    partialProduct (2 * N + 2) = productFactor 2 * pairedProduct N := by
  induction N with
  | zero => simp [partialProduct_two, pairedProduct]
  | succ N ih =>
      rw [show 2 * (N + 1) + 2 = (2 * N + 3) + 1 by omega,
        partialProduct_succ (2 * N + 3) (by omega),
        show 2 * N + 3 = (2 * N + 2) + 1 by omega,
        partialProduct_succ (2 * N + 2) (by omega), ih]
      unfold pairedProduct
      rw [Finset.prod_range_succ]
      unfold pairTerm
      ring

private theorem partialProduct_odd_form (N : ℕ) :
    partialProduct (2 * N + 3) =
      partialProduct (2 * N + 2) * productFactor (2 * N + 3) := by
  rw [show 2 * N + 3 = (2 * N + 2) + 1 by omega,
    partialProduct_succ (2 * N + 2) (by omega)]

private theorem productFactor_two_pos : 0 < productFactor 2 := by
  unfold productFactor alternatingLogTerm
  norm_num
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

private theorem partialProduct_even_tendsto_zero :
    Tendsto (fun N : ℕ => partialProduct (2 * N + 2)) atTop (𝓝 0) := by
  have hmul := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => productFactor 2) atTop (𝓝 (productFactor 2))).mul
    pairedProduct_tendsto_zero
  have hmul' : Tendsto (fun N : ℕ => productFactor 2 * pairedProduct N)
      atTop (𝓝 0) := by simpa using hmul
  apply hmul'.congr'
  exact Filter.Eventually.of_forall fun N => (partialProduct_even_form N).symm

private theorem productFactor_odd_tendsto_one :
    Tendsto (fun N : ℕ => productFactor (2 * N + 3)) atTop (𝓝 1) := by
  have hcast : Tendsto (fun N : ℕ => (((2 * N + 3 : ℕ) : ℝ)))
      atTop atTop := by
    have hindex : Tendsto (fun N : ℕ => 2 * N + 3) atTop atTop := by
      apply tendsto_atTop_mono' atTop
        (Filter.Eventually.of_forall fun N => show N ≤ 2 * N + 3 by omega)
      exact tendsto_id
    exact tendsto_natCast_atTop_atTop.comp hindex
  have hlog : Tendsto (fun N : ℕ => Real.log (((2 * N + 3 : ℕ) : ℝ)))
      atTop atTop := Real.tendsto_log_atTop.comp hcast
  have hinv : Tendsto
      (fun N : ℕ => 1 / Real.log (((2 * N + 3 : ℕ) : ℝ)))
      atTop (𝓝 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero.comp hlog
  have hsub := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
      atTop (𝓝 1)).sub hinv
  have hsub' : Tendsto
      (fun N : ℕ => 1 - 1 / Real.log (((2 * N + 3 : ℕ) : ℝ)))
      atTop (𝓝 1) := by simpa using hsub
  apply hsub'.congr'
  exact Filter.Eventually.of_forall fun N => (productFactor_odd N).symm

private theorem partialProduct_odd_tendsto_zero :
    Tendsto (fun N : ℕ => partialProduct (2 * N + 3)) atTop (𝓝 0) := by
  have hmul := partialProduct_even_tendsto_zero.mul productFactor_odd_tendsto_one
  have hmul' : Tendsto
      (fun N : ℕ => partialProduct (2 * N + 2) * productFactor (2 * N + 3))
      atTop (𝓝 0) := by simpa using hmul
  apply hmul'.congr'
  exact Filter.Eventually.of_forall fun N => (partialProduct_odd_form N).symm

private theorem partialProduct_tendsto_zero :
    Tendsto partialProduct atTop (𝓝 0) := by
  have hparity : ∀ n : ℕ, ∃ k : ℕ, n = 2 * k ∨ n = 2 * k + 1 := by
    intro n
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · exact ⟨k, Or.inl rfl⟩
    · exact ⟨k, Or.inr rfl⟩
  have heven := partialProduct_even_tendsto_zero
  have hodd := partialProduct_odd_tendsto_zero
  rw [Metric.tendsto_atTop] at heven hodd ⊢
  intro ε hε
  obtain ⟨Ne, hNe⟩ := heven ε hε
  obtain ⟨No, hNo⟩ := hodd ε hε
  refine ⟨2 * max (Ne + 1) (No + 1) + 2, ?_⟩
  intro n hn
  obtain ⟨k, hk | hk⟩ := hparity n
  · subst n
    by_cases hk0 : k = 0
    · subst k
      omega
    · have hkNe : Ne ≤ k - 1 := by omega
      have he := hNe (k - 1) hkNe
      have hidx : 2 * (k - 1) + 2 = 2 * k := by omega
      rw [hidx] at he
      exact he
  · subst n
    by_cases hk0 : k = 0
    · subst k
      omega
    · have hkNo : No ≤ k - 1 := by omega
      have ho := hNo (k - 1) hkNo
      have hidx : 2 * (k - 1) + 3 = 2 * k + 1 := by omega
      rw [hidx] at ho
      exact ho

private theorem divergentProduct : DivergentProduct := by
  intro hconv
  rcases hconv with ⟨P, hP, hlim⟩
  have hzero : P = 0 := tendsto_nhds_unique hlim partialProduct_tendsto_zero
  exact hP hzero

private theorem conditionally_summable_alternatingLog :
    ConditionallySummableFromTwo alternatingLogTerm := by
  let b : ℕ → ℝ := fun k => 1 / Real.log ((k + 2 : ℕ) : ℝ)
  have hAnti : Antitone b := by
    intro m n hmn
    dsimp [b]
    apply one_div_le_one_div_of_le
    · exact Real.log_pos (by exact_mod_cast (show 1 < m + 2 by omega))
    · apply Real.log_le_log
      · positivity
      · exact_mod_cast Nat.add_le_add_right hmn 2
  have hcast : Tendsto (fun k : ℕ => (((k + 2 : ℕ) : ℝ)))
      atTop atTop := by
    have hindex : Tendsto (fun k : ℕ => k + 2) atTop atTop := by
      apply tendsto_atTop_mono' atTop
        (Filter.Eventually.of_forall fun k => show k ≤ k + 2 by omega)
      exact tendsto_id
    exact tendsto_natCast_atTop_atTop.comp hindex
  have hlog : Tendsto (fun k : ℕ => Real.log (((k + 2 : ℕ) : ℝ)))
      atTop atTop := Real.tendsto_log_atTop.comp hcast
  have hZero : Tendsto b atTop (𝓝 0) := by
    dsimp [b]
    simpa [one_div] using tendsto_inv_atTop_zero.comp hlog
  obtain ⟨s, hs⟩ := hAnti.tendsto_alternating_series_of_tendsto_zero hZero
  have hterm (k : ℕ) :
      (-1 : ℝ) ^ k * b k = alternatingLogTerm (k + 2) := by
    unfold alternatingLogTerm
    dsimp [b]
    rw [pow_add]
    norm_num
    simp [div_eq_mul_inv]
  have hseries : ProofGap.SeriesConverges
      (fun k : ℕ => alternatingLogTerm (k + 2)) := by
    apply seriesConverges_of_tendsto
    apply hs.congr'
    exact Filter.Eventually.of_forall fun n =>
      Finset.sum_congr rfl fun k _ => hterm k
  refine ⟨hseries, ?_⟩
  intro habs
  have habsOrd : Summable
      (fun k : ℕ => |alternatingLogTerm (k + 2)|) :=
    summable_of_seriesConverges_of_nonneg habs fun _ => abs_nonneg _
  have habsTail : Summable
      (fun k : ℕ => |alternatingLogTerm (k + 3)|) := by
    have h := (summable_nat_add_iff 1).mpr habsOrd
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hSquareTail : Summable
      (fun k : ℕ => logSquareTerm (k + 3)) :=
    Summable.of_nonneg_of_le
      (fun k => by unfold logSquareTerm; positivity)
      (fun k => by
        have hgt : 1 < Real.log (((k + 3 : ℕ) : ℝ)) :=
          log_gt_one_of_three_le (k + 3) (by omega)
        have hpos : 0 < Real.log (((k + 3 : ℕ) : ℝ)) :=
          lt_trans zero_lt_one hgt
        unfold logSquareTerm alternatingLogTerm
        rw [abs_div, abs_pow, abs_neg, abs_one, one_pow,
          abs_of_pos hpos]
        apply one_div_le_one_div_of_le hpos
        nlinarith)
      habsTail
  apply not_summable_logSquare_shifted
  apply (summable_nat_add_iff 1).mp
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hSquareTail

/-- Exercise 3091, gap 1. -/
theorem gap1 : ConditionallySummableFromTwo alternatingLogTerm := by
  exact conditionally_summable_alternatingLog

/-- Exercise 3091, gap 2. -/
theorem gap2 : ¬SummableFromTwo logSquareTerm := by
  exact not_summable_logSquare_from_two

/-- Exercise 3091, gap 3; retain the series lower bound. -/
theorem gap3 :
    ∀ n : ℕ, 2 ≤ n → (Real.log n) ^ 2 < (n : ℝ) := by
  intro n hn
  exact log_sq_lt_nat n hn

/-- Exercise 3091, gap 4; positivity starts at `n = 2`. -/
theorem gap4 :
    ∀ n : ℕ, 2 ≤ n → harmonicTerm n < logSquareTerm n := by
  intro n hn
  exact harmonic_lt_logSquare n hn

/-- Exercise 3091, gap 5. -/
theorem gap5 : ¬SummableFromTwo harmonicTerm := by
  exact not_summable_harmonic_from_two

/--
Exercise 3091, gap 6; the partial products collapse to
zero and hence diverge in the nonzero-product sense.
-/
theorem gap6 : DivergentProduct := by
  exact divergentProduct

end

end ProofGap.Exercise3091
