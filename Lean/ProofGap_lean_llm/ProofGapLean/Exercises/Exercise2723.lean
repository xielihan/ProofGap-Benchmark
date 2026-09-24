import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed

namespace ProofGap.Exercise2723

noncomputable section

open Filter

def term (p q x : ℝ) (n : ℕ) : ℝ :=
  Real.rpow n p * Real.sin (n * x) / (1 + Real.rpow n q)

def amplitude (p q : ℝ) (n : ℕ) : ℝ :=
  Real.rpow n p / (1 + Real.rpow n q)

def comparison (p q : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow n (q - p)

def partialSineSum (x : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, Real.sin ((k + 1) * x)

def nontrivialSine (x : ℝ) : Prop :=
  ¬ ∃ k : ℤ, x = (k : ℝ) * Real.pi

def ConditionallySummable (p q x : ℝ) : Prop :=
  ProofGap.SeriesConverges (fun n : ℕ => term p q x (n + 1)) ∧
    ¬ ProofGap.SeriesConverges (fun n : ℕ => |term p q x (n + 1)|)

private lemma sin_ne_zero_of_nontrivial {x : ℝ} (hx : nontrivialSine x) :
    Real.sin x ≠ 0 := by
  intro hsin
  apply hx
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hsin
  exact ⟨k, hk.symm⟩

private lemma sine_sq_le_pair (x t : ℝ) :
    Real.sin x ^ 2 ≤
      2 * (Real.sin t ^ 2 + Real.sin (t + x) ^ 2) := by
  have htcos : Real.cos t ^ 2 ≤ 1 := Real.cos_sq_le_one t
  have htxcos : Real.cos (t + x) ^ 2 ≤ 1 := Real.cos_sq_le_one (t + x)
  have hsquares : 0 ≤ Real.sin (t + x) ^ 2 + Real.sin t ^ 2 := by positivity
  have hcos : 0 ≤ 2 - (Real.cos t ^ 2 + Real.cos (t + x) ^ 2) := by
    linarith
  have hprod := mul_nonneg hsquares hcos
  have hlagrange :
      0 ≤ (Real.sin (t + x) * Real.cos (t + x) +
        Real.sin t * Real.cos t) ^ 2 := sq_nonneg _
  have hsin :
      Real.sin x = Real.sin (t + x) * Real.cos t -
        Real.cos (t + x) * Real.sin t := by
    calc
      Real.sin x = Real.sin ((t + x) - t) := by congr 1 <;> ring
      _ = _ := by rw [Real.sin_sub]
  rw [hsin]
  nlinarith

private lemma sine_sq_harmonic_le (x : ℝ) (n : ℕ) :
    Real.sin x ^ 2 / (2 * (n + 1 : ℝ)) ≤
      Real.sin ((n + 1) * x) ^ 2 / (n + 1 : ℝ) +
        2 * (Real.sin ((n + 2) * x) ^ 2 / (n + 2 : ℝ)) := by
  have hn1 : 0 < (n + 1 : ℝ) := by positivity
  have hn2 : 0 < (n + 2 : ℝ) := by positivity
  have hpair := sine_sq_le_pair x ((n + 1 : ℝ) * x)
  have hrewrite : (n + 1 : ℝ) * x + x = (n + 2 : ℝ) * x := by
    push_cast
    ring
  rw [hrewrite] at hpair
  have hfirst :
      Real.sin x ^ 2 / (2 * (n + 1 : ℝ)) ≤
        (Real.sin ((n + 1) * x) ^ 2 + Real.sin ((n + 2) * x) ^ 2) /
          (n + 1 : ℝ) := by
    calc
      Real.sin x ^ 2 / (2 * (n + 1 : ℝ)) =
          (Real.sin x ^ 2 / 2) / (n + 1 : ℝ) := by
        field_simp [hn1.ne']
      _ ≤ (Real.sin ((n + 1) * x) ^ 2 + Real.sin ((n + 2) * x) ^ 2) /
          (n + 1 : ℝ) :=
        (div_le_div_iff_of_pos_right hn1).2 (by nlinarith)
  have hnle : (n + 2 : ℝ) ≤ 2 * (n + 1 : ℝ) := by
    push_cast
    linarith
  have hsecond :
      Real.sin ((n + 2) * x) ^ 2 / (n + 1 : ℝ) ≤
        2 * (Real.sin ((n + 2) * x) ^ 2 / (n + 2 : ℝ)) := by
    rw [show 2 * (Real.sin ((n + 2) * x) ^ 2 / (n + 2 : ℝ)) =
      (2 * Real.sin ((n + 2) * x) ^ 2) / (n + 2 : ℝ) by ring]
    rw [div_le_div_iff₀ hn1 hn2]
    have hs := sq_nonneg (Real.sin ((n + 2) * x))
    nlinarith [mul_nonneg hs (sub_nonneg.mpr hnle)]
  calc
    Real.sin x ^ 2 / (2 * (n + 1 : ℝ)) ≤
        (Real.sin ((n + 1) * x) ^ 2 + Real.sin ((n + 2) * x) ^ 2) /
          (n + 1 : ℝ) := hfirst
    _ = Real.sin ((n + 1) * x) ^ 2 / (n + 1 : ℝ) +
        Real.sin ((n + 2) * x) ^ 2 / (n + 1 : ℝ) := by ring
    _ ≤ Real.sin ((n + 1) * x) ^ 2 / (n + 1 : ℝ) +
        2 * (Real.sin ((n + 2) * x) ^ 2 / (n + 2 : ℝ)) := by gcongr

private lemma not_summable_sine_sq_div (x : ℝ) (hx : nontrivialSine x) :
    ¬ Summable (fun n : ℕ =>
      Real.sin ((n + 1) * x) ^ 2 / (n + 1 : ℝ)) := by
  intro hsum
  let a : ℕ → ℝ := fun n => Real.sin ((n + 1) * x) ^ 2 / (n + 1 : ℝ)
  have hshift : Summable (fun n => a (n + 1)) :=
    (summable_nat_add_iff 1).mpr hsum
  have hmajor : Summable (fun n => a n + 2 * a (n + 1)) :=
    hsum.add (hshift.mul_left 2)
  have hsmall : Summable (fun n : ℕ =>
      Real.sin x ^ 2 / (2 * (n + 1 : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) ?_ hmajor
    intro n
    dsimp [a]
    convert sine_sq_harmonic_le x n using 1 <;> push_cast <;> ring
  have hsin : Real.sin x ≠ 0 := sin_ne_zero_of_nontrivial hx
  have hharmonic : Summable (fun n : ℕ => 1 / (n + 1 : ℝ)) := by
    convert hsmall.mul_left (2 / Real.sin x ^ 2) using 1 with n
    field_simp [hsin]
    <;> ring
  have hshifted : Summable (fun n : ℕ => 1 / |(n : ℝ) + 1| ^ (1 : ℝ)) := by
    refine hharmonic.congr (fun n => ?_)
    rw [Real.rpow_one, abs_of_pos (by positivity : 0 < (n : ℝ) + 1)]
  have := (Real.summable_one_div_nat_add_rpow 1 1).mp hshifted
  norm_num at this

private lemma seriesConverges_iff_tendsto_partialSums {f : ℕ → ℝ} :
    ProofGap.SeriesConverges f ↔
      ∃ l : ℝ, Tendsto (fun n => ∑ i ∈ Finset.range n, f i) atTop (nhds l) := by
  unfold ProofGap.SeriesConverges Summable HasSum
  simp only [SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
  rfl

private lemma seriesConverges_of_summable {f : ℕ → ℝ} (hf : Summable f) :
    ProofGap.SeriesConverges f := by
  rw [seriesConverges_iff_tendsto_partialSums]
  exact ⟨∑' n, f n, hf.hasSum.tendsto_sum_nat⟩

private lemma seriesConverges_nonneg_iff_summable {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) : ProofGap.SeriesConverges f ↔ Summable f := by
  constructor
  · rw [seriesConverges_iff_tendsto_partialSums]
    rintro ⟨l, hl⟩
    exact ⟨l, (hasSum_iff_tendsto_nat_of_nonneg hf l).2 hl⟩
  · exact seriesConverges_of_summable

private lemma seriesConverges_tendsto_zero {f : ℕ → ℝ}
    (hf : ProofGap.SeriesConverges f) : Tendsto f atTop (nhds 0) := by
  rw [seriesConverges_iff_tendsto_partialSums] at hf
  obtain ⟨l, hl⟩ := hf
  have hshift := hl.comp (tendsto_add_atTop_nat 1)
  have hsub := hshift.sub hl
  convert hsub using 1
  · funext n
    simp only [Function.comp_apply, Finset.sum_range_succ, add_sub_cancel_left]
  · ring

private lemma seriesConverges_nat_add_iff (f : ℕ → ℝ) (k : ℕ) :
    ProofGap.SeriesConverges (fun n => f (n + k)) ↔
      ProofGap.SeriesConverges f := by
  rw [seriesConverges_iff_tendsto_partialSums,
    seriesConverges_iff_tendsto_partialSums]
  let c := ∑ i ∈ Finset.range k, f i
  constructor
  · rintro ⟨l, hl⟩
    refine ⟨c + l, (tendsto_add_atTop_iff_nat k).mp ?_⟩
    apply (tendsto_const_nhds.add hl).congr'
    filter_upwards with n
    dsimp [c]
    rw [show n + k = k + n by omega, Finset.sum_range_add]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    omega
  · rintro ⟨l, hl⟩
    refine ⟨l - c, ?_⟩
    apply ((hl.comp (tendsto_add_atTop_nat k)).sub tendsto_const_nhds).congr'
    filter_upwards with n
    dsimp [c]
    rw [show n + k = k + n by omega, Finset.sum_range_add,
      add_sub_cancel_left]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    omega

private lemma sine_telescoping (x : ℝ) (n : ℕ) :
    2 * Real.sin (x / 2) * Real.sin ((n + 1) * x) =
      Real.cos (((n : ℝ) + 1 / 2) * x) -
        Real.cos (((n : ℝ) + 3 / 2) * x) := by
  rw [show ((n : ℝ) + 1 / 2) * x = (n + 1) * x - x / 2 by ring,
    show ((n : ℝ) + 3 / 2) * x = (n + 1) * x + x / 2 by ring,
    Real.cos_sub, Real.cos_add]
  ring

private lemma partialSineSum_identity (x : ℝ) (n : ℕ) :
    2 * Real.sin (x / 2) * partialSineSum x n =
      Real.cos (x / 2) - Real.cos (((n : ℝ) + 1 / 2) * x) := by
  induction n with
  | zero => simp [partialSineSum, div_eq_mul_inv, mul_comm]
  | succ n ih =>
      simp only [partialSineSum, Finset.sum_range_succ] at ih ⊢
      rw [mul_add, ih, sine_telescoping]
      push_cast
      ring

private lemma partialSineSum_bounded (x : ℝ) (hx : nontrivialSine x) :
    Bornology.IsBounded (Set.range (partialSineSum x)) := by
  have hsin : Real.sin (x / 2) ≠ 0 := by
    intro hzero
    apply hx
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hzero
    refine ⟨2 * k, ?_⟩
    calc
      x = 2 * (x / 2) := by ring
      _ = 2 * ((k : ℝ) * Real.pi) := by rw [← hk]
      _ = ((2 * k : ℤ) : ℝ) * Real.pi := by push_cast; ring
  have hden : 2 * Real.sin (x / 2) ≠ 0 := mul_ne_zero (by norm_num) hsin
  have hbound : ∀ n : ℕ, ‖partialSineSum x n‖ ≤
      2 / |2 * Real.sin (x / 2)| := by
    intro n
    have hid := partialSineSum_identity x n
    have heq : partialSineSum x n =
        (Real.cos (x / 2) - Real.cos (((n : ℝ) + 1 / 2) * x)) /
          (2 * Real.sin (x / 2)) := by
      apply (eq_div_iff hden).2
      simpa [mul_comm] using hid
    rw [Real.norm_eq_abs, heq, abs_div]
    have hnum : |Real.cos (x / 2) - Real.cos (((n : ℝ) + 1 / 2) * x)| ≤ 2 := by
      calc
        |Real.cos (x / 2) - Real.cos (((n : ℝ) + 1 / 2) * x)| ≤
            |Real.cos (x / 2)| + |Real.cos (((n : ℝ) + 1 / 2) * x)| := abs_sub _ _
        _ ≤ 2 := by
          nlinarith [Real.abs_cos_le_one (x / 2),
            Real.abs_cos_le_one (((n : ℝ) + 1 / 2) * x)]
    exact (div_le_div_iff_of_pos_right (abs_pos.mpr hden)).2 hnum
  rw [Metric.isBounded_range_iff]
  refine ⟨2 * (2 / |2 * Real.sin (x / 2)|), fun m n => ?_⟩
  rw [dist_eq_norm]
  calc
    ‖partialSineSum x m - partialSineSum x n‖ ≤
        ‖partialSineSum x m‖ + ‖partialSineSum x n‖ := norm_sub_le _ _
    _ ≤ 2 / |2 * Real.sin (x / 2)| + 2 / |2 * Real.sin (x / 2)| :=
      add_le_add (hbound m) (hbound n)
    _ = 2 * (2 / |2 * Real.sin (x / 2)|) := by ring

theorem gap1 (p q x : ℝ) (hq : 0 < q) :
    ∀ n : ℕ, 1 ≤ n →
      |Real.sin (n * x)| / (2 * Real.rpow n (q - p)) ≤ |term p q x n| := by
  intro n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hnone : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp_pos : 0 < Real.rpow n p := Real.rpow_pos_of_pos hnpos p
  have hq_pos : 0 < Real.rpow n q := Real.rpow_pos_of_pos hnpos q
  have hq_one : 1 ≤ Real.rpow n q := Real.one_le_rpow hnone hq.le
  have hden : 1 + Real.rpow n q ≤ 2 * Real.rpow n q := by linarith
  have habs :
      |term p q x n| = Real.rpow n p * |Real.sin (n * x)| /
        (1 + Real.rpow n q) := by
    have habsp : |Real.rpow n p| = Real.rpow n p := abs_of_pos hp_pos
    have habsden : |1 + Real.rpow n q| = 1 + Real.rpow n q :=
      abs_of_pos (by positivity)
    simp only [term, abs_div, abs_mul, habsp, habsden]
  rw [habs]
  have hrpow_sub : Real.rpow n (q - p) = Real.rpow n q / Real.rpow n p :=
    Real.rpow_sub hnpos q p
  rw [hrpow_sub]
  have heq :
      |Real.sin (n * x)| / (2 * (Real.rpow n q / Real.rpow n p)) =
        (Real.rpow n p * |Real.sin (n * x)|) / (2 * Real.rpow n q) := by
    field_simp [hp_pos.ne', hq_pos.ne']
    <;> ring
  rw [heq]
  exact div_le_div_of_nonneg_left (mul_nonneg hp_pos.le (abs_nonneg _))
    (by positivity) hden

theorem gap2 (p q x : ℝ) :
    ∀ n : ℕ, 1 ≤ n → |term p q x n| ≤ comparison p q n := by
  intro n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hp_pos : 0 < Real.rpow n p := Real.rpow_pos_of_pos hnpos p
  have hq_pos : 0 < Real.rpow n q := Real.rpow_pos_of_pos hnpos q
  have hsin : |Real.sin (n * x)| ≤ 1 := Real.abs_sin_le_one _
  have habs :
      |term p q x n| = Real.rpow n p * |Real.sin (n * x)| /
        (1 + Real.rpow n q) := by
    have habsp : |Real.rpow n p| = Real.rpow n p := abs_of_pos hp_pos
    have habsden : |1 + Real.rpow n q| = 1 + Real.rpow n q :=
      abs_of_pos (by positivity)
    simp only [term, abs_div, abs_mul, habsp, habsden]
  rw [habs, comparison]
  have hrpow_sub : Real.rpow n (q - p) = Real.rpow n q / Real.rpow n p :=
    Real.rpow_sub hnpos q p
  rw [hrpow_sub]
  have hnum : Real.rpow n p * |Real.sin (n * x)| ≤ Real.rpow n p := by
    nlinarith [mul_nonneg hp_pos.le (sub_nonneg.mpr hsin)]
  have hdiv :
      Real.rpow n p * |Real.sin (n * x)| / (1 + Real.rpow n q) ≤
        Real.rpow n p / Real.rpow n q :=
    div_le_div₀ hp_pos.le hnum hq_pos (by linarith)
  simpa [one_div_div] using hdiv

theorem gap3 (p q x : ℝ) :
    ∀ n : ℕ, 1 ≤ n →
      |Real.sin (n * x)| / (2 * Real.rpow n (q - p)) ≤ comparison p q n := by
  intro n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hrpos : 0 < Real.rpow n (q - p) := Real.rpow_pos_of_pos hnpos _
  rw [comparison]
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * Real.rpow n (q - p)) hrpos).2
  nlinarith [Real.abs_sin_le_one (n * x)]

theorem gap4 (p q : ℝ) :
    q - p > 1 → q > p + 1 := by
  intro h
  linarith

theorem gap5 (p q x : ℝ) (hq : 0 < q) (hpq : q > p + 1) :
    Summable (fun n : ℕ => |term p q x (n + 1)|) := by
  have hs : Summable (fun n : ℕ => comparison p q n) := by
    simpa [comparison, one_div] using
      (Real.summable_nat_rpow_inv.mpr (show 1 < q - p by linarith))
  have hshift : Summable (fun n : ℕ => comparison p q (n + 1)) :=
    (summable_nat_add_iff 1).mpr hs
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_) hshift
  exact gap2 p q x (n + 1) (by omega)

set_option maxHeartbeats 800000 in
theorem gap6 (p q x : ℝ) (hq : 0 < q) (hx : nontrivialSine x)
    (hpq : q ≤ p + 1) :
    ¬ Summable (fun n : ℕ => |term p q x (n + 1)|) := by
  intro hterm
  have hlower : Summable (fun n : ℕ =>
      |Real.sin ((n + 1) * x)| /
        (2 * Real.rpow (n + 1) (q - p))) := by
    have hnonneg : ∀ n : ℕ, 0 ≤
        |Real.sin ((n + 1) * x)| /
          (2 * Real.rpow (n + 1) (q - p)) := by
      intro n
      exact div_nonneg (abs_nonneg _)
        (mul_nonneg (by norm_num)
          (Real.rpow_nonneg (by positivity : 0 ≤ (n : ℝ) + 1) _))
    have hle : ∀ n : ℕ,
        |Real.sin ((n + 1) * x)| /
            (2 * Real.rpow (n + 1) (q - p)) ≤
          |term p q x (n + 1)| := by
      intro n
      simpa only [Nat.cast_add, Nat.cast_one] using gap1 p q x hq (n + 1) (by omega)
    exact Summable.of_nonneg_of_le hnonneg hle hterm
  have hsquares : Summable (fun n : ℕ =>
      Real.sin ((n + 1) * x) ^ 2 / (2 * (n + 1 : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun n => div_nonneg (sq_nonneg _)
      (mul_nonneg (by norm_num) (by norm_cast; omega))) (fun n => ?_) hlower
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have hnpos : 0 < (n : ℝ) + 1 := by linarith
    have hrpow_pos : 0 < Real.rpow (n + 1) (q - p) :=
      Real.rpow_pos_of_pos hnpos _
    have hrpow_le : Real.rpow (n + 1) (q - p) ≤ (n + 1 : ℝ) := by
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_le hn (show q - p ≤ 1 by linarith))
    have hsin_sq : Real.sin ((n + 1) * x) ^ 2 ≤ |Real.sin ((n + 1) * x)| := by
      have habs := Real.abs_sin_le_one ((n + 1) * x)
      rw [sq, ← abs_mul_abs_self]
      nlinarith [mul_nonneg (abs_nonneg (Real.sin ((n + 1) * x)))
        (sub_nonneg.mpr habs)]
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * (n + 1 : ℝ))
      (by positivity : 0 < 2 * Real.rpow (n + 1) (q - p))).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hsin_sq) hrpow_pos.le,
      mul_nonneg (abs_nonneg (Real.sin ((n + 1) * x)))
        (sub_nonneg.mpr hrpow_le)]
  have hsine : Summable (fun n : ℕ =>
      Real.sin ((n + 1) * x) ^ 2 / (n + 1 : ℝ)) := by
    refine (hsquares.mul_left 2).congr (fun n => ?_)
    field_simp
  exact not_summable_sine_sq_div x hx hsine

theorem gap7 (p q x : ℝ) (hx : nontrivialSine x)
    (hpq : p < q) (hqp : q ≤ p + 1) :
    Bornology.IsBounded (Set.range (partialSineSum x)) := by
  exact partialSineSum_bounded x hx

private lemma amplitude_nonneg (p q : ℝ) (n : ℕ) :
    0 ≤ amplitude p q n := by
  have hp_nonneg : 0 ≤ Real.rpow n p := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hq_nonneg : 0 ≤ Real.rpow n q := Real.rpow_nonneg (Nat.cast_nonneg n) _
  exact div_nonneg hp_nonneg (add_nonneg zero_le_one hq_nonneg)

private lemma amplitude_le_comparison (p q : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    amplitude p q n ≤ comparison p q n := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hp_pos : 0 < Real.rpow n p := Real.rpow_pos_of_pos hnpos _
  have hq_pos : 0 < Real.rpow n q := Real.rpow_pos_of_pos hnpos _
  have hrpow_sub : Real.rpow n (q - p) = Real.rpow n q / Real.rpow n p :=
    Real.rpow_sub hnpos q p
  rw [amplitude, comparison, hrpow_sub]
  have hdiv : Real.rpow n p / (1 + Real.rpow n q) ≤
      Real.rpow n p / Real.rpow n q :=
    div_le_div_of_nonneg_left hp_pos.le hq_pos (by linarith)
  simpa [one_div_div] using hdiv

theorem gap8 (p q : ℝ) (hq : 0 < q) (hpq : p < q) :
    Tendsto
      (fun n : ℕ => amplitude p q (n + 1) / comparison p q (n + 1))
      atTop (nhds 1) := by
  have hnlim : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hpow : Tendsto (fun n : ℕ => Real.rpow ((n : ℝ) + 1) q) atTop atTop :=
    (tendsto_rpow_atTop hq).comp hnlim
  have hinv : Tendsto (fun n : ℕ =>
      1 / (1 + Real.rpow ((n : ℝ) + 1) q)) atTop (nhds 0) := by
    simpa only [one_div] using (tendsto_const_nhds.add_atTop hpow).inv_tendsto_atTop
  have hfrac : Tendsto (fun n : ℕ =>
      1 - 1 / (1 + Real.rpow ((n : ℝ) + 1) q)) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hinv
  refine hfrac.congr' (Eventually.of_forall fun n => ?_)
  have hnpos : 0 < (n : ℝ) + 1 := by positivity
  have hp_pos : 0 < Real.rpow ((n : ℝ) + 1) p := Real.rpow_pos_of_pos hnpos _
  have hq_pos : 0 < Real.rpow ((n : ℝ) + 1) q := Real.rpow_pos_of_pos hnpos _
  have hr_pos : 0 < Real.rpow ((n : ℝ) + 1) (q - p) :=
    Real.rpow_pos_of_pos hnpos _
  have hmul :
      Real.rpow ((n : ℝ) + 1) p * Real.rpow ((n : ℝ) + 1) (q - p) =
        Real.rpow ((n : ℝ) + 1) q := by
    calc
      Real.rpow ((n : ℝ) + 1) p * Real.rpow ((n : ℝ) + 1) (q - p) =
          Real.rpow ((n : ℝ) + 1) (p + (q - p)) :=
        (Real.rpow_add hnpos p (q - p)).symm
      _ = Real.rpow ((n : ℝ) + 1) q := by congr 1 <;> ring
  simp only [amplitude, comparison, Nat.cast_add, Nat.cast_one]
  field_simp [hp_pos.ne', hq_pos.ne', hr_pos.ne']
  nlinarith

theorem gap9 (p q : ℝ) (hq : 0 < q) (hpq : p < q) :
    Tendsto (fun n : ℕ => amplitude p q (n + 1)) atTop (nhds 0) := by
  have hnlim : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hcomp0 : Tendsto (fun n : ℕ => comparison p q (n + 1)) atTop (nhds 0) := by
    have hpow := (tendsto_rpow_neg_atTop (show 0 < q - p by linarith)).comp hnlim
    refine hpow.congr' (Eventually.of_forall fun n => ?_)
    simp only [Function.comp_apply, comparison, Nat.cast_add, Nat.cast_one, one_div]
    exact Real.rpow_neg (by positivity : 0 ≤ (n : ℝ) + 1) (q - p)
  exact squeeze_zero (fun n => amplitude_nonneg p q (n + 1))
    (fun n => amplitude_le_comparison p q (n + 1) (by omega)) hcomp0

private lemma amplitude_eventually_antitone (p q : ℝ) (hq : 0 < q)
    (hpq : p < q) :
    ∃ N : ℕ, Antitone (fun n : ℕ => amplitude p q (n + N + 1)) := by
  let F : ℝ → ℝ := fun t => Real.rpow t p / (1 + Real.rpow t q)
  have hscaled : Tendsto (fun t : ℝ => (q - p) * Real.rpow t q)
      atTop atTop :=
    (tendsto_rpow_atTop hq).const_mul_atTop' (sub_pos.mpr hpq)
  have hevent : ∀ᶠ t : ℝ in atTop, p ≤ (q - p) * Real.rpow t q :=
    hscaled.eventually_ge_atTop p
  rcases eventually_atTop.1 hevent with ⟨A, hA⟩
  let B : ℝ := max A 1
  obtain ⟨N, hN⟩ := exists_nat_gt B
  have hderiv (t : ℝ) (ht : 0 < t) :
      HasDerivAt F
        (((p * Real.rpow t (p - 1)) * (1 + Real.rpow t q) -
          Real.rpow t p * (q * Real.rpow t (q - 1))) /
            (1 + Real.rpow t q) ^ 2) t := by
    have hpder := Real.hasDerivAt_rpow_const (p := p) (Or.inl ht.ne')
    have hqder := Real.hasDerivAt_rpow_const (p := q) (Or.inl ht.ne')
    simpa [F] using hpder.div ((hasDerivAt_const t (1 : ℝ)).add hqder)
      (by
        have hrq : 0 ≤ Real.rpow t q := Real.rpow_nonneg ht.le _
        nlinarith : 1 + Real.rpow t q ≠ 0)
  have hanti : AntitoneOn F (Set.Ici B) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici B)
    · intro t htB
      have hBt : B ≤ t := htB
      have ht : 0 < t := by
        have hB1 : 1 ≤ B := le_max_right A 1
        linarith
      exact (hderiv t ht).continuousAt.continuousWithinAt
    · intro t htB
      have ht : 0 < t := by
        have hB1 : 1 ≤ B := le_max_right A 1
        have : B < t := by simpa [B] using htB
        linarith
      exact (hderiv t ht).differentiableAt.differentiableWithinAt
    · intro t htB
      have hBt : B < t := by simpa [B] using htB
      have ht : 0 < t := by
        have hB1 : 1 ≤ B := le_max_right A 1
        linarith
      have hAt : A ≤ t := (le_max_left A 1).trans hBt.le
      have hcoef : p + (p - q) * Real.rpow t q ≤ 0 := by
        nlinarith [hA t hAt]
      have hpdecomp : Real.rpow t p =
          Real.rpow t (p - 1) * t := by
        calc
          Real.rpow t p = Real.rpow t ((p - 1) + 1) := by congr 1 <;> ring
          _ = Real.rpow t (p - 1) * Real.rpow t 1 :=
            Real.rpow_add ht (p - 1) 1
          _ = Real.rpow t (p - 1) * t := by
            simp only [Real.rpow_eq_pow, Real.rpow_one]
      have hqdecomp : Real.rpow t q =
          Real.rpow t (q - 1) * t := by
        calc
          Real.rpow t q = Real.rpow t ((q - 1) + 1) := by congr 1 <;> ring
          _ = Real.rpow t (q - 1) * Real.rpow t 1 :=
            Real.rpow_add ht (q - 1) 1
          _ = Real.rpow t (q - 1) * t := by
            simp only [Real.rpow_eq_pow, Real.rpow_one]
      rw [(hderiv t ht).deriv, hpdecomp]
      apply div_nonpos_of_nonpos_of_nonneg
      · calc
          (p * Real.rpow t (p - 1)) * (1 + Real.rpow t q) -
              (Real.rpow t (p - 1) * t) *
                (q * Real.rpow t (q - 1)) =
              Real.rpow t (p - 1) *
                (p + (p - q) * Real.rpow t q) := by
                  rw [show Real.rpow t (p - 1) * t *
                      (q * Real.rpow t (q - 1)) =
                      Real.rpow t (p - 1) * q *
                        (Real.rpow t (q - 1) * t) by ring,
                    ← hqdecomp]
                  ring
          _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
            (Real.rpow_nonneg ht.le _ ) hcoef
      · positivity
  refine ⟨N, ?_⟩
  intro m n hmn
  have hmB : B ≤ (((m + N + 1 : ℕ) : ℕ) : ℝ) := by
    exact hN.le.trans (by exact_mod_cast (show N ≤ m + N + 1 by omega))
  have hnB : B ≤ (((n + N + 1 : ℕ) : ℕ) : ℝ) := by
    exact hN.le.trans (by exact_mod_cast (show N ≤ n + N + 1 by omega))
  have hcast : (((m + N + 1 : ℕ) : ℕ) : ℝ) ≤
      (((n + N + 1 : ℕ) : ℕ) : ℝ) := by exact_mod_cast (by omega : m + N + 1 ≤ n + N + 1)
  simpa [F, amplitude] using hanti hmB hnB hcast

theorem gap10 (p q x : ℝ) (hq : 0 < q) (hx : nontrivialSine x)
    (hpq : p < q) (hqp : q ≤ p + 1) :
    ProofGap.SeriesConverges (fun n : ℕ => term p q x (n + 1)) := by
  rcases amplitude_eventually_antitone p q hq hpq with ⟨N, hanti⟩
  let a : ℕ → ℝ := fun k => amplitude p q (k + N + 1)
  let z : ℕ → ℝ := fun k => Real.sin ((k + N + 1) * x)
  have haZero : Tendsto a atTop (nhds 0) := by
    have h := (gap9 p q hq hpq).comp (tendsto_add_atTop_nat N)
    simpa [a, Function.comp_def, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using h
  rcases Metric.isBounded_range_iff.mp (partialSineSum_bounded x hx) with ⟨C, hC⟩
  have hzBound : ∀ n : ℕ, ‖∑ k ∈ Finset.range n, z k‖ ≤ C := by
    intro n
    have heq : (∑ k ∈ Finset.range n, z k) =
        partialSineSum x (N + n) - partialSineSum x N := by
      unfold z partialSineSum
      rw [Finset.sum_range_add]
      ring_nf
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      push_cast
      ring
    rw [heq, ← dist_eq_norm]
    exact hC (N + n) N
  have hcauchy := hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded
    haZero hzBound
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hcauchy
  have htail : ProofGap.SeriesConverges
      (fun k : ℕ => term p q x (k + N + 1)) := by
    rw [seriesConverges_iff_tendsto_partialSums]
    refine ⟨l, ?_⟩
    apply hl.congr'
    filter_upwards with n
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [a, z]
    simp only [smul_eq_mul, term, amplitude]
    push_cast
    ring
  apply (seriesConverges_nat_add_iff
    (fun n : ℕ => term p q x (n + 1)) N).mp
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

theorem gap11 (p q x : ℝ) (hq : 0 < q) (hx : nontrivialSine x)
    (hpq : p < q) (hqp : q ≤ p + 1) :
    ConditionallySummable p q x := by
  refine ⟨gap10 p q x hq hx hpq hqp, ?_⟩
  rw [seriesConverges_nonneg_iff_summable (fun n => abs_nonneg _)]
  exact gap6 p q x hq hx hqp

private lemma not_seriesConverges_of_q_le_p (p q x : ℝ) (hq : 0 < q)
    (hx : nontrivialSine x) (hqp : q ≤ p) :
    ¬ ProofGap.SeriesConverges (fun n : ℕ => term p q x (n + 1)) := by
  intro hconv
  have hterm0 := seriesConverges_tendsto_zero hconv
  have habs0 : Tendsto (fun n : ℕ => |term p q x (n + 1)|)
      atTop (nhds 0) := by simpa only [abs_zero] using hterm0.abs
  have hsineHalf : Tendsto
      (fun n : ℕ => |Real.sin ((n + 1) * x)| / 2) atTop (nhds 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) _ habs0
    filter_upwards with n
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have hbase : 0 < (n : ℝ) + 1 := by positivity
    have hrpos : 0 < Real.rpow ((n : ℝ) + 1) (q - p) :=
      Real.rpow_pos_of_pos hbase _
    have hrle : Real.rpow ((n : ℝ) + 1) (q - p) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hn (by linarith)
    calc
      |Real.sin ((n + 1) * x)| / 2 ≤
          |Real.sin ((n + 1) * x)| /
            (2 * Real.rpow ((n : ℝ) + 1) (q - p)) := by
              exact div_le_div_of_nonneg_left (abs_nonneg _)
                (mul_pos (by norm_num) hrpos) (by nlinarith)
      _ ≤ |term p q x (n + 1)| := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (gap1 p q x hq (n + 1) (by omega))
  have hsineAbs : Tendsto (fun n : ℕ => |Real.sin ((n + 1) * x)|)
      atTop (nhds 0) := by
    have h := (tendsto_const_nhds (x := (2 : ℝ))).mul hsineHalf
    convert h using 1
    · funext n
      ring
    · norm_num
  have hsine : Tendsto (fun n : ℕ => Real.sin ((n + 1) * x))
      atTop (nhds 0) := (tendsto_zero_iff_abs_tendsto_zero _).2 hsineAbs
  have hsineNext : Tendsto (fun n : ℕ => Real.sin ((n + 2) * x))
      atTop (nhds 0) := by
    convert hsine.comp (tendsto_add_atTop_nat 1) using 1
    funext n
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    congr 2
    ring
  have hrhs : Tendsto (fun n : ℕ =>
      2 * (Real.sin ((n + 1) * x) ^ 2 +
        Real.sin ((n + 2) * x) ^ 2)) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => Real.sin ((n + 1) * x) ^ 2)
        atTop (nhds 0) := by simpa using hsine.pow 2
    have h2 : Tendsto (fun n : ℕ => Real.sin ((n + 2) * x) ^ 2)
        atTop (nhds 0) := by simpa using hsineNext.pow 2
    simpa using (tendsto_const_nhds.mul (h1.add h2) : Tendsto
      (fun n : ℕ => 2 * (Real.sin ((n + 1) * x) ^ 2 +
        Real.sin ((n + 2) * x) ^ 2)) atTop (nhds (2 * (0 + 0))))
  have hsinpos : 0 < Real.sin x ^ 2 := sq_pos_of_ne_zero (sin_ne_zero_of_nontrivial hx)
  have hsmall : ∀ᶠ n : ℕ in atTop,
      2 * (Real.sin ((n + 1) * x) ^ 2 +
        Real.sin ((n + 2) * x) ^ 2) < Real.sin x ^ 2 :=
    (tendsto_order.1 hrhs).2 (Real.sin x ^ 2) hsinpos
  obtain ⟨n, hn⟩ := hsmall.exists
  have hpair := sine_sq_le_pair x ((n + 1 : ℝ) * x)
  have hre : (n + 1 : ℝ) * x + x = (n + 2 : ℝ) * x := by
    push_cast
    ring
  rw [hre] at hpair
  linarith

theorem gap12 (p q x : ℝ) (hq : 0 < q) (hx : nontrivialSine x)
    (hqp : q ≤ p) :
    ¬ Summable (fun n : ℕ => term p q x (n + 1)) := by
  intro hs
  exact not_seriesConverges_of_q_le_p p q x hq hx hqp
    (seriesConverges_of_summable hs)

theorem gap13 (q x : ℝ) (hq : 0 < q) (hx : nontrivialSine x) :
    {p : ℝ | Summable (fun n : ℕ => |term p q x (n + 1)|)} =
      {p : ℝ | q > p + 1} := by
  ext p
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hs
    by_contra h
    exact gap6 p q x hq hx (le_of_not_gt h) hs
  · intro hp
    exact gap5 p q x hq hp

theorem gap14 (q x : ℝ) (hq : 0 < q) (hx : nontrivialSine x) :
    {p : ℝ | ConditionallySummable p q x} =
      {p : ℝ | p < q ∧ q ≤ p + 1} := by
  ext p
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hconv, hnotabs⟩
    have hpq : p < q := by
      by_contra h
      exact not_seriesConverges_of_q_le_p p q x hq hx (le_of_not_gt h) hconv
    have hqp : q ≤ p + 1 := by
      by_contra h
      apply hnotabs
      rw [seriesConverges_nonneg_iff_summable (fun n => abs_nonneg _)]
      exact gap5 p q x hq (lt_of_not_ge h)
    exact ⟨hpq, hqp⟩
  · rintro ⟨hpq, hqp⟩
    exact gap11 p q x hq hx hpq hqp

end

end ProofGap.Exercise2723
