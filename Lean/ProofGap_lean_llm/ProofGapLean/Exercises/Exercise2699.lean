import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter

namespace ProofGap.Exercise2699

noncomputable section

open Filter
open scoped BigOperators
open scoped Topology

def risingProduct (p : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, ((k : ℝ) + 1 + p)

def magnitude (p q : ℝ) (n : ℕ) : ℝ :=
  risingProduct p n / (Nat.factorial n : ℝ) / Real.rpow n q

def signedTerm (p q : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * magnitude p q (n + 1)

def ratioError (p q : ℝ) (n : ℕ) : ℝ :=
  magnitude p q n / magnitude p q (n + 1) -
    1 - (q - p) / (n : ℝ)

def secondOrderCoefficient (p q : ℝ) : ℝ :=
  (1 / 2 : ℝ) * q * (q - 1) - p * q + p * (p + 1)

def logError (p q C : ℝ) (n : ℕ) : ℝ :=
  Real.log (magnitude p q n) - ((p - q) * Real.log n + C)

def ConditionallySummable (f : ℕ → ℝ) : Prop :=
  ProofGap.SeriesConverges f ∧ ¬ Summable (fun n => |f n|)

private theorem risingProduct_pos (p : ℝ) (hp : -1 < p) (n : ℕ) :
    0 < risingProduct p n := by
  rw [risingProduct]
  apply Finset.prod_pos
  intro k hk
  have hk0 : (0 : ℝ) ≤ k := by positivity
  linarith

private theorem magnitude_pos (p q : ℝ) (hp : -1 < p) (n : ℕ) (hn : 1 ≤ n) :
    0 < magnitude p q n := by
  rw [magnitude]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact div_pos (div_pos (risingProduct_pos p hp n) (by positivity))
    (Real.rpow_pos_of_pos hnR q)

private theorem risingProduct_succ (p : ℝ) (n : ℕ) :
    risingProduct p (n + 1) = risingProduct p n * (n + 1 + p) := by
  simp [risingProduct, Finset.prod_range_succ]

private theorem logGamma_recurrence {x : ℝ} (hx : 0 < x) :
    (Real.log ∘ Real.Gamma) (x + 1) =
      (Real.log ∘ Real.Gamma) x + Real.log x := by
  rw [Function.comp_apply, Real.Gamma_add_one hx.ne',
    Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne', add_comm,
    Function.comp_apply]

private theorem log_succ_sub_log_bigO :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => Real.log (n + 1) - Real.log n)
      (fun n : ℕ => 1 / (n : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnsR : (0 : ℝ) < n + 1 := by positivity
  have hnonneg : 0 ≤ Real.log ((n : ℝ) + 1) - Real.log n :=
    sub_nonneg.mpr (Real.log_le_log hnR (by linarith))
  have hle := Real.log_le_sub_one_of_pos (div_pos hnsR hnR)
  rw [Real.log_div hnsR.ne' hnR.ne'] at hle
  simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg,
    abs_of_pos (one_div_pos.mpr hnR)] using
    (calc
      Real.log ((n : ℝ) + 1) - Real.log n ≤ ((n : ℝ) + 1) / n - 1 := hle
      _ = 1 / (n : ℝ) := by field_simp; ring
      _ = 1 * (1 / (n : ℝ)) := by ring)

private theorem inv_succ_isBigO_inv :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => 1 / ((n : ℝ) + 1))
      (fun n : ℕ => 1 / (n : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnsR : (0 : ℝ) < n + 1 := by positivity
  simpa [Real.norm_eq_abs, abs_of_pos hnsR, abs_of_pos hnR,
    abs_of_pos (one_div_pos.mpr hnsR), abs_of_pos (one_div_pos.mpr hnR)] using
    (one_div_le_one_div_of_le hnR (by linarith : (n : ℝ) ≤ n + 1))

private theorem logGammaSeq_error_bigO (x : ℝ) (hx : 0 < x) :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => Real.BohrMollerup.logGammaSeq x n - Real.log (Real.Gamma x))
      (fun n : ℕ => 1 / (n : ℝ)) := by
  suffices hmain : ∀ m : ℕ, (m : ℝ) < x → x ≤ m + 1 →
      Asymptotics.IsBigO atTop
        (fun n : ℕ => Real.BohrMollerup.logGammaSeq x n - Real.log (Real.Gamma x))
        (fun n : ℕ => 1 / (n : ℝ)) by
    refine hmain ⌈x - 1⌉₊ ?_ ?_
    · rcases lt_or_ge x 1 with h | h
      · rwa [Nat.ceil_eq_zero.mpr (by linarith : x - 1 ≤ 0), Nat.cast_zero]
      · convert Nat.ceil_lt_add_one (by linarith : 0 ≤ x - 1)
        ring
    · rw [← sub_le_iff_le_add]
      exact Nat.le_ceil _
  intro m
  induction m generalizing x with
  | zero =>
      intro hx0 hx1
      refine Asymptotics.IsBigO.of_bound x ?_
      filter_upwards [eventually_ne_atTop 0, eventually_ge_atTop 1] with n hn0 hn
      have hlo := Real.BohrMollerup.ge_logGammaSeq (x := x)
        Real.convexOn_log_Gamma (fun {y} hy => logGamma_recurrence hy)
        (by simpa using hx0) hn0
      have hhi := Real.BohrMollerup.le_logGammaSeq (x := x)
        Real.convexOn_log_Gamma (fun {y} hy => logGamma_recurrence hy)
        (by simpa using hx0) (by simpa using hx1) n
      simp only [Function.comp_apply, Real.Gamma_one, Real.log_one, zero_add] at hlo hhi
      have hstep_nonneg : 0 ≤ Real.log ((n : ℝ) + 1) - Real.log n := by
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn
        exact sub_nonneg.mpr (Real.log_le_log hnR (by linarith))
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hstepn : ‖Real.log ((n : ℝ) + 1) - Real.log n‖ ≤
          1 * ‖1 / (n : ℝ)‖ := by
        have hle := Real.log_le_sub_one_of_pos
          (div_pos (show (0 : ℝ) < n + 1 by positivity) hnR)
        rw [Real.log_div (show (n : ℝ) + 1 ≠ 0 by positivity) hnR.ne'] at hle
        simpa [Real.norm_eq_abs, abs_of_nonneg hstep_nonneg,
          abs_of_pos hnR, abs_of_pos (one_div_pos.mpr hnR)] using
          (calc
            Real.log ((n : ℝ) + 1) - Real.log n ≤ ((n : ℝ) + 1) / n - 1 := hle
            _ = 1 / (n : ℝ) := by field_simp; ring
            _ = 1 * (1 / (n : ℝ)) := by ring)
      rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hlo)]
      rw [neg_sub]
      have herr : Real.log (Real.Gamma x) - Real.BohrMollerup.logGammaSeq x n ≤
          x * (Real.log ((n : ℝ) + 1) - Real.log n) := by linarith
      calc
        Real.log (Real.Gamma x) - Real.BohrMollerup.logGammaSeq x n ≤
            x * (Real.log ((n : ℝ) + 1) - Real.log n) := herr
        _ ≤ x * ‖(1 / (n : ℝ))‖ := by
          rw [show ‖Real.log ((n : ℝ) + 1) - Real.log n‖ =
              Real.log ((n : ℝ) + 1) - Real.log n by
            rw [Real.norm_eq_abs, abs_of_nonneg hstep_nonneg]] at hstepn
          exact mul_le_mul_of_nonneg_left (by simpa only [one_mul] using hstepn) hx.le
  | succ m ih =>
      intro hmx hxupper
      let y := x - 1
      have hy : 0 < y := by
        dsimp [y]
        have hm1 : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
        linarith
      have him : (m : ℝ) < y := by
        dsimp [y]
        norm_num at hmx
        linarith
      have hiu : y ≤ m + 1 := by
        dsimp [y]
        norm_num at hxupper ⊢
        linarith
      have hY := ih (x := y) hy him hiu
      have hYshift := hY.comp_tendsto (tendsto_add_atTop_nat 1)
      have hYshift' : Asymptotics.IsBigO atTop
          (fun n : ℕ => Real.BohrMollerup.logGammaSeq y (n + 1) -
            Real.log (Real.Gamma y))
          (fun n : ℕ => 1 / (n : ℝ)) := by
        have hinv : Asymptotics.IsBigO atTop
            ((fun n : ℕ => 1 / (n : ℝ)) ∘ fun n => n + 1)
            (fun n : ℕ => 1 / (n : ℝ)) := by
          change Asymptotics.IsBigO atTop
            (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ)))
            (fun n : ℕ => 1 / (n : ℝ))
          simpa only [Nat.cast_add, Nat.cast_one] using inv_succ_isBigO_inv
        exact hYshift.trans hinv
      have hcombined := hYshift'.sub (log_succ_sub_log_bigO.const_mul_left x)
      apply hcombined.congr'
      · filter_upwards with n
        have hseq := Real.BohrMollerup.logGammaSeq_add_one y n
        have hgamma := logGamma_recurrence hy
        dsimp [y] at hseq hgamma ⊢
        rw [sub_add_cancel] at hseq hgamma
        rw [hseq, hgamma]
        ring
      · exact Eventually.of_forall fun n => by simp

private theorem log_sub_log_add_bigO (x : ℝ) (hx : 0 < x) :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => Real.log n - Real.log ((n : ℝ) + x))
      (fun n : ℕ => 1 / (n : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound x ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnx : (0 : ℝ) < (n : ℝ) + x := by linarith
  have hnonneg : 0 ≤ Real.log ((n : ℝ) + x) - Real.log n :=
    sub_nonneg.mpr (Real.log_le_log hnR (by linarith))
  have hle := Real.log_le_sub_one_of_pos (div_pos hnx hnR)
  rw [Real.log_div hnx.ne' hnR.ne'] at hle
  rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr
    (Real.log_le_log hnR (by linarith)))]
  rw [neg_sub]
  have hbound : Real.log ((n : ℝ) + x) - Real.log n ≤ x * (1 / (n : ℝ)) := by
    calc
      Real.log ((n : ℝ) + x) - Real.log n ≤ ((n : ℝ) + x) / n - 1 := hle
      _ = x * (1 / (n : ℝ)) := by field_simp; ring
  simpa [Real.norm_eq_abs, abs_of_pos hnR, abs_of_pos (one_div_pos.mpr hnR)]
    using hbound

private theorem log_magnitude_eq (p q : ℝ) (hp : -1 < p) :
    ∀ n : ℕ, 1 ≤ n →
      Real.log (magnitude p q n) =
        (∑ k ∈ Finset.range n, Real.log ((k : ℝ) + 1 + p)) -
          Real.log (Nat.factorial n) - q * Real.log n := by
  intro n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hprod : risingProduct p n ≠ 0 := (risingProduct_pos p hp n).ne'
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hrpow : Real.rpow (n : ℝ) q ≠ 0 := (Real.rpow_pos_of_pos hnR q).ne'
  rw [magnitude, Real.log_div (div_ne_zero hprod hfac) hrpow,
    Real.log_div hprod hfac]
  rw [show Real.log (Real.rpow (n : ℝ) q) = q * Real.log n from
    Real.log_rpow hnR q]
  rw [risingProduct, Real.log_prod]
  intro k hk
  have hk0 : (0 : ℝ) ≤ k := by positivity
  linarith

private theorem logError_bigO (p q : ℝ) (hp : -1 < p) :
    ∃ C : ℝ,
      Asymptotics.IsBigO atTop (logError p q C)
        (fun n : ℕ => 1 / (n : ℝ)) := by
  let x := p + 1
  have hx : 0 < x := by dsimp [x]; linarith
  refine ⟨-Real.log (Real.Gamma x), ?_⟩
  have hlog := log_sub_log_add_bigO x hx
  have hgamma := (logGammaSeq_error_bigO x hx).const_mul_left (-1)
  have hsum := hlog.add hgamma
  apply hsum.congr'
  · filter_upwards [eventually_ge_atTop 1] with n hn
    rw [logError, log_magnitude_eq p q hp n hn]
    simp only [Real.BohrMollerup.logGammaSeq, Finset.sum_range_succ]
    dsimp [x]
    ring_nf
  · exact Eventually.of_forall fun n => by simp

private theorem magnitude_normalized_limit (p q : ℝ) (hp : -1 < p) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (fun n : ℕ =>
        magnitude p q (n + 1) / Real.rpow (n + 1) (p - q))
        atTop (𝓝 L) := by
  obtain ⟨C, hC⟩ := logError_bigO p q hp
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div] using
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  have herr : Tendsto (logError p q C) atTop (𝓝 0) := hC.trans_tendsto hinv
  have herrShift := herr.comp (tendsto_add_atTop_nat 1)
  have hexp : Tendsto (fun n : ℕ => Real.exp (logError p q C (n + 1)))
      atTop (𝓝 1) := by
    simpa only [Real.exp_zero, Function.comp_apply] using
      ((Real.continuous_exp.tendsto 0).comp herrShift)
  refine ⟨Real.exp C, Real.exp_pos C, ?_⟩
  have hmul := hexp.mul_const (Real.exp C)
  have hmul' : Tendsto
      (fun n => Real.exp ((logError p q C ∘ fun a => a + 1) n) * Real.exp C)
      atTop (𝓝 (Real.exp C)) := by simpa using hmul
  apply hmul'.congr'
  filter_upwards with n
  have hnR : (0 : ℝ) < n + 1 := by positivity
  have hm : 0 < magnitude p q (n + 1) := magnitude_pos p q hp (n + 1) (by omega)
  simp only [Function.comp_apply]
  rw [logError, Real.exp_sub, Real.exp_add, Real.exp_log hm]
  rw [show (p - q) * Real.log ((n + 1 : ℕ) : ℝ) =
      Real.log ((n + 1 : ℕ) : ℝ) * (p - q) by ring]
  norm_num [Nat.cast_add, Nat.cast_one]
  rw [← Real.rpow_def_of_pos hnR]
  field_simp [Real.exp_ne_zero, (Real.rpow_pos_of_pos hnR (p - q)).ne']

private theorem magnitude_isTheta_rpow (p q : ℝ) (hp : -1 < p) :
    Asymptotics.IsTheta atTop
      (fun n : ℕ => magnitude p q (n + 1))
      (fun n : ℕ => 1 / Real.rpow (n + 1) (q - p)) := by
  obtain ⟨L, hL, hlim⟩ := magnitude_normalized_limit p q hp
  have hlim' : Tendsto (fun n : ℕ =>
      magnitude p q (n + 1) / (1 / Real.rpow (n + 1) (q - p)))
      atTop (𝓝 L) := by
    apply hlim.congr'
    filter_upwards with n
    have hn : (0 : ℝ) ≤ n + 1 := by positivity
    rw [show p - q = -(q - p) by ring]
    apply congrArg (fun z => magnitude p q (n + 1) / z)
    simpa only [one_div] using (Real.rpow_neg hn (q - p))
  exact (Asymptotics.isTheta_of_div_tendsto_nhds_ne_zero hlim' hL.ne').symm

private theorem shifted_rpow_summable (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => 1 / Real.rpow (n + 1) s) := by
  have h := (Real.summable_one_div_nat_add_rpow (1 : ℝ) s).mpr hs
  refine h.congr fun n => ?_
  rw [abs_of_pos (show (0 : ℝ) < n + 1 by positivity)]
  rfl

private theorem shifted_rpow_not_summable (s : ℝ) (hs : s ≤ 1) :
    ¬ Summable (fun n : ℕ => 1 / Real.rpow (n + 1) s) := by
  intro h
  have h' : Summable (fun n : ℕ => 1 / |(n : ℝ) + 1| ^ s) := by
    refine h.congr fun n => ?_
    rw [abs_of_pos (show (0 : ℝ) < n + 1 by positivity)]
    rfl
  exact (not_lt_of_ge hs) ((Real.summable_one_div_nat_add_rpow (1 : ℝ) s).mp h')

private theorem seriesConverges_iff_tendsto_partialSums {f : ℕ → ℝ} :
    ProofGap.SeriesConverges f ↔
      ∃ l : ℝ, Tendsto (fun n => ∑ i ∈ Finset.range n, f i) atTop (nhds l) := by
  unfold ProofGap.SeriesConverges Summable HasSum
  simp only [SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff,
    Function.comp_apply]
  rfl

private theorem seriesConverges_nat_add_iff (f : ℕ → ℝ) (k : ℕ) :
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

private def ratioModel (p q x : ℝ) : ℝ :=
  (1 + x) / (1 + (p + 1) * x) * Real.rpow (1 + x) q

private def ratioModelDeriv (p q x : ℝ) : ℝ :=
  (-p / (1 + (p + 1) * x) ^ 2) * Real.rpow (1 + x) q +
    ((1 + x) / (1 + (p + 1) * x)) *
      (q * Real.rpow (1 + x) (q - 1))

private theorem ratioModel_hasDerivAt (p q x : ℝ) (hx : 0 < 1 + x)
    (hden : 1 + (p + 1) * x ≠ 0) :
    HasDerivAt (ratioModel p q) (ratioModelDeriv p q x) x := by
  have hnum : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    convert (hasDerivAt_const x 1).add (hasDerivAt_id x) using 1 <;> ring
  have hden' : HasDerivAt (fun y : ℝ => 1 + (p + 1) * y) (p + 1) x := by
    convert (hasDerivAt_const x 1).add ((hasDerivAt_id x).const_mul (p + 1)) using 1 <;>
      ring
  have hquot := hnum.div hden' hden
  have hquot' : HasDerivAt
      (fun y : ℝ => (1 + y) / (1 + (p + 1) * y))
      (-p / (1 + (p + 1) * x) ^ 2) x := by
    convert hquot using 1 <;> field_simp <;> ring
  have hrpow := hnum.rpow_const (p := q) (Or.inl hx.ne')
  change HasDerivAt (fun y : ℝ => Real.rpow (1 + y) q)
    (1 * q * Real.rpow (1 + x) (q - 1)) x at hrpow
  have hrpow' : HasDerivAt (fun y : ℝ => Real.rpow (1 + y) q)
      (q * Real.rpow (1 + x) (q - 1)) x := by
    simpa only [one_mul] using hrpow
  simpa only [ratioModel, ratioModelDeriv] using hquot'.mul hrpow'

private theorem ratioModelDeriv_hasDerivAt_zero (p q : ℝ) :
    HasDerivAt (ratioModelDeriv p q)
      (2 * secondOrderCoefficient p q) 0 := by
  have hlin : HasDerivAt (fun y : ℝ => 1 + (p + 1) * y) (p + 1) 0 := by
    convert (hasDerivAt_const 0 1).add ((hasDerivAt_id 0).const_mul (p + 1)) using 1 <;>
      ring
  have hlin2 := hlin.pow 2
  have hu := (hasDerivAt_const 0 (-p)).div hlin2 (by norm_num)
  have hu' : HasDerivAt (fun y : ℝ => -p / (1 + (p + 1) * y) ^ 2)
      (2 * p * (p + 1)) 0 := by
    convert hu using 1 <;> norm_num <;> ring
  have hnum : HasDerivAt (fun y : ℝ => 1 + y) 1 0 := by
    simpa only [zero_add] using (hasDerivAt_const 0 (1 : ℝ)).add (hasDerivAt_id 0)
  have hb := hnum.rpow_const (p := q) (Or.inl (by norm_num))
  change HasDerivAt (fun y : ℝ => Real.rpow (1 + y) q)
    (1 * q * Real.rpow (1 + 0) (q - 1)) 0 at hb
  have hb' : HasDerivAt (fun y : ℝ => Real.rpow (1 + y) q) q 0 := by
    simpa using hb
  have ha := hnum.div hlin (by norm_num)
  have ha' : HasDerivAt (fun y : ℝ => (1 + y) / (1 + (p + 1) * y)) (-p) 0 := by
    convert ha using 1 <;> norm_num <;> ring
  have houterDiff : DifferentiableAt ℝ (fun z : ℝ => z ^ (q - 1)) 1 :=
    Real.differentiableAt_rpow_const_of_ne (q - 1) (one_ne_zero : (1 : ℝ) ≠ 0)
  have houterDeriv : deriv (fun z : ℝ => z ^ (q - 1)) 1 = q - 1 := by
    rw [Real.deriv_rpow_const]
    simp
  have houter : HasDerivAt (fun z : ℝ => z ^ (q - 1)) (q - 1) 1 :=
    houterDiff.hasDerivAt.congr_deriv houterDeriv
  have houter' : HasDerivAt (fun z : ℝ => z ^ (q - 1)) (q - 1) (1 + 0) := by
    simpa using houter
  have hv0 := houter'.comp 0 hnum
  have hv := hv0.const_mul q
  have hv' : HasDerivAt (fun y : ℝ => q * (1 + y) ^ (q - 1))
      (q * (q - 1)) 0 := by
    simpa using hv
  have hsum := (hu'.mul hb').add (ha'.mul hv')
  have hEq :
      (2 * p * (p + 1)) * Real.rpow (1 + 0) q +
          (-p / (1 + (p + 1) * 0) ^ 2) * q +
        ((-p) * (q * Real.rpow (1 + 0) (q - 1)) +
          ((1 + 0) / (1 + (p + 1) * 0)) * (q * (q - 1))) =
        2 * secondOrderCoefficient p q := by
    norm_num [secondOrderCoefficient]
    ring
  have hsum' := hsum.congr_deriv hEq
  simpa only [ratioModelDeriv, Real.rpow_eq_pow] using hsum'

private theorem ratioModel_taylor_bound (p q : ℝ) (hp : -1 < p) :
    ∃ C : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |ratioModel p q x -
        (1 + (q - p) * x + secondOrderCoefficient p q * x ^ 2)| ≤ C * x ^ 3 := by
  let f : ℝ → ℝ := ratioModel p q
  let s : Set ℝ := Set.Icc (0 : ℝ) 1
  have hnum : ContDiff ℝ 3 (fun x : ℝ => 1 + x) := contDiff_const.add contDiff_id
  have hden : ContDiff ℝ 3 (fun x : ℝ => 1 + (p + 1) * x) :=
    contDiff_const.add (contDiff_const.mul contDiff_id)
  have hden0 : ∀ x ∈ s, 1 + (p + 1) * x ≠ 0 := by
    intro x hx
    have hp1 : 0 < p + 1 := by linarith
    have hx0 : 0 ≤ x := hx.1
    positivity
  have hrpow : ContDiffOn ℝ 3 (fun x : ℝ => Real.rpow (1 + x) q) s :=
    hnum.contDiffOn.rpow_const_of_ne (fun x hx => by linarith [hx.1])
  have hf : ContDiffOn ℝ 3 f s := by
    exact (hnum.contDiffOn.div hden.contDiffOn hden0).mul hrpow
  obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound (n := 2)
    (a := (0 : ℝ)) (b := 1) (by norm_num) hf
  refine ⟨C, fun x hx => ?_⟩
  have hud : UniqueDiffOn ℝ s := uniqueDiffOn_Icc (by norm_num)
  have hu0 : UniqueDiffWithinAt ℝ s 0 := hud 0 (by norm_num [s])
  have hd1 : iteratedDerivWithin 1 f s 0 = q - p := by
    rw [iteratedDerivWithin_one]
    calc
      derivWithin f s 0 = ratioModelDeriv p q 0 := by
        simpa [f] using
          (ratioModel_hasDerivAt p q 0 (by norm_num) (by norm_num)).hasDerivWithinAt.derivWithin hu0
      _ = q - p := by
        norm_num [ratioModelDeriv]
        ring
  have heq : ∀ y ∈ s, derivWithin f s y = ratioModelDeriv p q y := by
    intro y hy
    have hybase : 0 < 1 + y := by linarith [hy.1]
    have hyden : 1 + (p + 1) * y ≠ 0 := hden0 y hy
    simpa [f] using
      (ratioModel_hasDerivAt p q y hybase hyden).hasDerivWithinAt.derivWithin (hud y hy)
  have hd2 : iteratedDerivWithin 2 f s 0 = 2 * secondOrderCoefficient p q := by
    rw [show 2 = 1 + 1 by norm_num, iteratedDerivWithin_succ, iteratedDerivWithin_one]
    have hw := (ratioModelDeriv_hasDerivAt_zero p q).hasDerivWithinAt.congr heq
      (heq 0 (by norm_num [s]))
    exact hw.derivWithin hu0
  have htaylor : taylorWithinEval f 2 s 0 x =
      1 + (q - p) * x + secondOrderCoefficient p q * x ^ 2 := by
    rw [show 2 = 1 + 1 by norm_num, taylorWithinEval_succ,
      taylorWithinEval_succ, taylor_within_zero_eval, hd1, hd2]
    norm_num [f, ratioModel, smul_eq_mul]
    ring
  rw [← htaylor]
  simpa [s, f, Real.norm_eq_abs] using hC x hx

theorem gap1 (p q : ℝ) (hp : -1 < p) :
    ∀ n : ℕ, 1 ≤ n →
      |(-1 : ℝ) ^ (n - 1) * magnitude p q n| = magnitude p q n := by
  intro n hn
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos (magnitude_pos p q hp n hn)]
  simp

theorem gap2 (p q : ℝ) (hp : -1 < p) :
    ∀ n : ℕ, 1 ≤ n →
      magnitude p q n / magnitude p q (n + 1) =
        |signedTerm p q (n - 1)| / |signedTerm p q n| := by
  intro n hn
  rw [signedTerm, signedTerm]
  simpa [Nat.sub_add_cancel hn] using congrArg₂ (· / ·)
    (gap1 p q hp n hn).symm (gap1 p q hp (n + 1) (by omega)).symm

theorem gap3 (p q : ℝ) (hp : -1 < p) :
    ∀ n : ℕ, 1 ≤ n →
      magnitude p q n / magnitude p q (n + 1) =
        ((n : ℝ) + 1) / ((n : ℝ) + 1 + p) *
          Real.rpow (((n : ℝ) + 1) / n) q := by
  intro n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnp : 0 < (n : ℝ) + 1 + p := by
    have hn0 : (0 : ℝ) ≤ n := by positivity
    linarith
  have hrn : Real.rpow (n : ℝ) q ≠ 0 := (Real.rpow_pos_of_pos hnR q).ne'
  have hrns : Real.rpow ((n : ℝ) + 1) q ≠ 0 :=
    (Real.rpow_pos_of_pos (by positivity) q).ne'
  have hprod : risingProduct p n ≠ 0 := (risingProduct_pos p hp n).ne'
  rw [magnitude, magnitude, risingProduct_succ, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  rw [show Real.rpow (((n : ℝ) + 1) / n) q =
      Real.rpow ((n : ℝ) + 1) q / Real.rpow n q by
    exact Real.div_rpow (by positivity) hnR.le q]
  field_simp

theorem gap4 (p q : ℝ) :
    -1 < p →
    ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) / ((n : ℝ) + 1 + p) *
          Real.rpow (((n : ℝ) + 1) / n) q =
        1 + (q - p) / (n : ℝ) + ratioError p q n := by
  intro hp n hn
  rw [ratioError, gap3 p q hp n hn]
  ring

theorem gap5 (p q : ℝ) (hp : -1 < p) :
    ∀ n : ℕ, 1 ≤ n →
      magnitude p q n / magnitude p q (n + 1) =
        1 + (q - p) / (n : ℝ) + ratioError p q n := by
  intro n hn
  rw [gap3 p q hp n hn, gap4 p q hp n hn]

theorem gap6 (p q : ℝ) (hp : -1 < p) :
    Asymptotics.IsBigO atTop
      (fun n : ℕ =>
        ratioError p q n -
          secondOrderCoefficient p q / ((n : ℝ) ^ 2))
      (fun n : ℕ => 1 / ((n : ℝ) ^ 3)) := by
  obtain ⟨C, hC⟩ := ratioModel_taylor_bound p q hp
  refine Asymptotics.IsBigO.of_bound |C| ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let x : ℝ := 1 / (n : ℝ)
  have hx : x ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [x]; positivity
    · dsimp [x]
      exact (div_le_one hnR).mpr (by exact_mod_cast hn)
  have ht := hC x hx
  have hbase : ((n : ℝ) + 1) / n = 1 + x := by
    dsimp [x]
    field_simp <;> ring
  have hfrac : ((n : ℝ) + 1) / ((n : ℝ) + 1 + p) =
      (1 + x) / (1 + (p + 1) * x) := by
    have hnp : (n : ℝ) + 1 + p ≠ 0 := by
      have : 0 < (n : ℝ) + 1 + p := by linarith
      exact this.ne'
    have hdenid : 1 + (p + 1) * x = ((n : ℝ) + 1 + p) / n := by
      dsimp [x]
      field_simp
      ring
    rw [← hbase, hdenid]
    field_simp [hnR.ne', hnp] <;> ring
  have hmodel : magnitude p q n / magnitude p q (n + 1) = ratioModel p q x := by
    rw [gap3 p q hp n hn, ratioModel, hbase, hfrac]
  have herr : ratioError p q n - secondOrderCoefficient p q / (n : ℝ) ^ 2 =
      ratioModel p q x -
        (1 + (q - p) * x + secondOrderCoefficient p q * x ^ 2) := by
    rw [ratioError, hmodel]
    dsimp [x]
    field_simp <;> ring
  have hx3 : x ^ 3 = 1 / (n : ℝ) ^ 3 := by
    dsimp [x]
    field_simp <;> ring
  rw [Real.norm_eq_abs, herr]
  calc
    |ratioModel p q x -
        (1 + (q - p) * x + secondOrderCoefficient p q * x ^ 2)| ≤ C * x ^ 3 := ht
    _ ≤ |C| * x ^ 3 :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ = |C| * ‖1 / (n : ℝ) ^ 3‖ := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (n : ℝ) ^ 3), hx3]

theorem gap7 (p q : ℝ) (hp : -1 < p) (h : p + 1 < q) :
    Summable (fun n : ℕ => magnitude p q (n + 1)) := by
  have hbase := shifted_rpow_summable (q - p) (by linarith)
  exact summable_of_isBigO_nat hbase (magnitude_isTheta_rpow p q hp).1

theorem gap8 (p q : ℝ) (hp : -1 < p) (h : p + 1 < q) :
    Summable (fun n : ℕ => |signedTerm p q n|) := by
  refine (gap7 p q hp h).congr fun n => ?_
  simpa [signedTerm] using (gap1 p q hp (n + 1) (by omega)).symm

theorem gap9 (p q : ℝ) (hp : -1 < p) (h : q ≤ p + 1) :
    ¬ Summable (fun n : ℕ => magnitude p q (n + 1)) := by
  intro hmag
  have hbase : Summable (fun n : ℕ => 1 / Real.rpow (n + 1) (q - p)) :=
    summable_of_isBigO_nat hmag (magnitude_isTheta_rpow p q hp).2
  exact shifted_rpow_not_summable (q - p) (by linarith) hbase

theorem gap10 (p q : ℝ) (hp : -1 < p) (hpq : p < q)
    (hcrit : q ≤ p + 1) :
    ∃ N : ℕ, ∀ n ≥ N,
      magnitude p q (n + 1) < magnitude p q n := by
  have hd : HasDerivAt (ratioModel p q) (q - p) 0 := by
    convert (ratioModel_hasDerivAt p q 0 (by norm_num) (by norm_num)) using 1 <;>
      simp [ratioModelDeriv] <;> ring
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div] using
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hinvpos : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hinv, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact one_div_pos.mpr hnR
  have hslope := hd.tendsto_slope_zero_right.comp hinvpos
  have hslopepos : ∀ᶠ n : ℕ in atTop,
      0 < (1 / (n : ℝ))⁻¹ •
        (ratioModel p q (0 + 1 / (n : ℝ)) - ratioModel p q 0) :=
    (tendsto_order.1 hslope).1 0 (by linarith)
  rw [eventually_atTop] at hslopepos
  obtain ⟨N, hN⟩ := hslopepos
  refine ⟨max 1 N, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hnN : N ≤ n := le_trans (le_max_right _ _) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  let x : ℝ := 1 / (n : ℝ)
  have hx : 0 < x := by dsimp [x]; positivity
  have hs := hN n hnN
  have hmodelgt : 1 < ratioModel p q x := by
    have hs' : 0 < x⁻¹ * (ratioModel p q x - 1) := by
      simpa [x, ratioModel, smul_eq_mul] using hs
    rcases (mul_pos_iff.mp hs') with h | h
    · linarith
    · linarith [inv_pos.mpr hx]
  have hbase : ((n : ℝ) + 1) / n = 1 + x := by
    dsimp [x]
    field_simp <;> ring
  have hfrac : ((n : ℝ) + 1) / ((n : ℝ) + 1 + p) =
      (1 + x) / (1 + (p + 1) * x) := by
    have hnp : (n : ℝ) + 1 + p ≠ 0 := by
      have : 0 < (n : ℝ) + 1 + p := by linarith
      exact this.ne'
    have hdenid : 1 + (p + 1) * x = ((n : ℝ) + 1 + p) / n := by
      dsimp [x]
      field_simp
      ring
    rw [← hbase, hdenid]
    field_simp [hnR.ne', hnp] <;> ring
  have hmodel : magnitude p q n / magnitude p q (n + 1) = ratioModel p q x := by
    rw [gap3 p q hp n hn1, ratioModel, hbase, hfrac]
  have hratio : 1 < magnitude p q n / magnitude p q (n + 1) := by
    rw [hmodel]
    exact hmodelgt
  simpa only [one_mul] using
    (lt_div_iff₀ (magnitude_pos p q hp (n + 1) (by omega))).mp hratio

theorem gap11 (p q : ℝ) (hpq : p < q) :
    0 < q - p := by linarith

theorem gap12 (p q : ℝ) (hp : -1 < p) :
    ∀ n : ℕ, 1 ≤ n →
      Real.log (magnitude p q n) =
        (∑ k ∈ Finset.range n, Real.log ((k : ℝ) + 1 + p)) -
          Real.log (Nat.factorial n) - q * Real.log n := by
  exact log_magnitude_eq p q hp

theorem gap13 (p q : ℝ) (hp : -1 < p) :
    ∃ C : ℝ,
      Asymptotics.IsBigO atTop (logError p q C)
        (fun n : ℕ => 1 / (n : ℝ)) := by
  exact logError_bigO p q hp

theorem gap14 (p q : ℝ) (hp : -1 < p) :
    ∃ C : ℝ,
      Asymptotics.IsBigO atTop
        (fun n : ℕ =>
          Real.log (magnitude p q n) -
            ((p - q) * Real.log n + C))
        (fun n : ℕ => 1 / (n : ℝ)) := by
  simpa only [logError] using gap13 p q hp

theorem gap15 (p q : ℝ) (hp : -1 < p) (hpq : p < q) :
    Tendsto (fun n : ℕ => magnitude p q (n + 1))
      atTop (nhds 0) := by
  obtain ⟨L, hL, hnorm⟩ := magnitude_normalized_limit p q hp
  have hpow : Tendsto (fun n : ℕ => Real.rpow (n + 1) (p - q)) atTop (𝓝 0) := by
    have hbase : Tendsto (fun x : ℝ => Real.rpow x (-(q - p))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by linarith)
    have hcast : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
      simpa only [Function.comp_apply] using
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    have hc := hbase.comp hcast
    rw [show p - q = -(q - p) by ring]
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one, add_comm] using hc
  have hmul := hnorm.mul hpow
  have hmul' : Tendsto
      (fun n => magnitude p q (n + 1) / Real.rpow (n + 1) (p - q) *
        Real.rpow (n + 1) (p - q)) atTop (𝓝 0) := by simpa using hmul
  apply hmul'.congr'
  filter_upwards with n
  have hr : Real.rpow ((n + 1 : ℕ) : ℝ) (p - q) ≠ 0 :=
    (Real.rpow_pos_of_pos (by positivity) (p - q)).ne'
  norm_num [Nat.cast_add, Nat.cast_one] at hr ⊢
  exact div_mul_cancel₀ _ hr

theorem gap16 (p q : ℝ) (hp : -1 < p) (hpq : p < q)
    (hcrit : q ≤ p + 1) :
    ProofGap.SeriesConverges (signedTerm p q) := by
  obtain ⟨N, hdec⟩ := gap10 p q hp hpq hcrit
  let k : ℕ := 2 * N
  have hanti : Antitone (fun n : ℕ => magnitude p q (n + k + 1)) := by
    refine antitone_nat_of_succ_le fun n => ?_
    have hstep := (hdec (n + k + 1) (by dsimp [k]; omega)).le
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep
  have hzero : Tendsto (fun n : ℕ => magnitude p q (n + k + 1))
      atTop (𝓝 0) := by
    have hshift := (gap15 p q hp hpq).comp (tendsto_add_atTop_nat k)
    simpa [Nat.add_assoc] using hshift
  obtain ⟨l, hl⟩ := hanti.tendsto_alternating_series_of_tendsto_zero hzero
  have htail : ProofGap.SeriesConverges (fun n => signedTerm p q (n + k)) := by
    apply seriesConverges_iff_tendsto_partialSums.mpr
    refine ⟨l, ?_⟩
    apply hl.congr'
    filter_upwards with n
    apply Finset.sum_congr rfl
    intro i hi
    simp [signedTerm, k, pow_add, pow_mul, Nat.add_assoc]
  exact (seriesConverges_nat_add_iff (signedTerm p q) k).mp htail

theorem gap17 (p q : ℝ) (hp : -1 < p) (hpq : p < q)
    (hcrit : q ≤ p + 1) :
    ConditionallySummable (signedTerm p q) := by
  refine ⟨gap16 p q hp hpq hcrit, ?_⟩
  intro habs
  apply gap9 p q hp hcrit
  refine habs.congr fun n => ?_
  simpa [signedTerm] using gap1 p q hp (n + 1) (by omega)

theorem gap18 (p : ℝ) (hp : -1 < p) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (fun n : ℕ => magnitude p p (n + 1)) atTop (nhds L) := by
  obtain ⟨L, hL, hnorm⟩ := magnitude_normalized_limit p p hp
  refine ⟨L, hL, ?_⟩
  simpa using hnorm

theorem gap19 (p : ℝ) (hp : -1 < p) :
    ¬ Tendsto (fun n : ℕ => magnitude p p (n + 1))
      atTop (nhds 0) := by
  rintro h0
  obtain ⟨L, hL, hLlim⟩ := gap18 p hp
  have : L = 0 := tendsto_nhds_unique hLlim h0
  linarith

theorem gap20 (p : ℝ) (hp : -1 < p) :
    ¬ Summable (signedTerm p p) := by
  intro hsum
  apply gap19 p hp
  have hzero := hsum.tendsto_atTop_zero
  have habs : Tendsto (fun n : ℕ => |signedTerm p p n|) atTop (𝓝 0) := by
    simpa [Real.norm_eq_abs] using hzero.norm
  apply habs.congr'
  filter_upwards with n
  simpa [signedTerm] using gap1 p p hp (n + 1) (by omega)

theorem gap21 (p q : ℝ) (hp : -1 < p) (hqp : q < p) :
    ∃ N : ℕ, ∀ n ≥ N,
      magnitude p q n < magnitude p q (n + 1) := by
  have hd : HasDerivAt (ratioModel p q) (q - p) 0 := by
    convert (ratioModel_hasDerivAt p q 0 (by norm_num) (by norm_num)) using 1 <;>
      simp [ratioModelDeriv] <;> ring
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div] using
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hinvpos : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hinv, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact one_div_pos.mpr hnR
  have hslope := hd.tendsto_slope_zero_right.comp hinvpos
  have hslopeneg : ∀ᶠ n : ℕ in atTop,
      (1 / (n : ℝ))⁻¹ •
        (ratioModel p q (0 + 1 / (n : ℝ)) - ratioModel p q 0) < 0 :=
    (tendsto_order.1 hslope).2 0 (by linarith)
  rw [eventually_atTop] at hslopeneg
  obtain ⟨N, hN⟩ := hslopeneg
  refine ⟨max 1 N, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hnN : N ≤ n := le_trans (le_max_right _ _) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  let x : ℝ := 1 / (n : ℝ)
  have hx : 0 < x := by dsimp [x]; positivity
  have hs := hN n hnN
  have hmodellt : ratioModel p q x < 1 := by
    have hs' : x⁻¹ * (ratioModel p q x - 1) < 0 := by
      simpa [x, ratioModel, smul_eq_mul] using hs
    rcases (mul_neg_iff.mp hs') with h | h
    · linarith
    · linarith [inv_pos.mpr hx]
  have hbase : ((n : ℝ) + 1) / n = 1 + x := by
    dsimp [x]
    field_simp <;> ring
  have hfrac : ((n : ℝ) + 1) / ((n : ℝ) + 1 + p) =
      (1 + x) / (1 + (p + 1) * x) := by
    have hnp : (n : ℝ) + 1 + p ≠ 0 := by
      have : 0 < (n : ℝ) + 1 + p := by linarith
      exact this.ne'
    have hdenid : 1 + (p + 1) * x = ((n : ℝ) + 1 + p) / n := by
      dsimp [x]
      field_simp
      ring
    rw [← hbase, hdenid]
    field_simp [hnR.ne', hnp] <;> ring
  have hmodel : magnitude p q n / magnitude p q (n + 1) = ratioModel p q x := by
    rw [gap3 p q hp n hn1, ratioModel, hbase, hfrac]
  have hratio : magnitude p q n / magnitude p q (n + 1) < 1 := by
    rw [hmodel]
    exact hmodellt
  exact (div_lt_one (magnitude_pos p q hp (n + 1) (by omega))).mp hratio

theorem gap22 (p q : ℝ) (hp : -1 < p) (hqp : q < p) :
    ¬ Tendsto (fun n : ℕ => magnitude p q (n + 1))
      atTop (nhds 0) := by
  intro h0
  obtain ⟨L, hL, hnorm⟩ := magnitude_normalized_limit p q hp
  have hpow : Tendsto (fun n : ℕ => Real.rpow (n + 1) (p - q)) atTop atTop := by
    have hcast : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
      simpa only [Function.comp_apply] using
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    have hc := (tendsto_rpow_atTop (by linarith : 0 < p - q)).comp hcast
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using hc
  have htop : Tendsto (fun n : ℕ => magnitude p q (n + 1)) atTop atTop := by
    have hmul := hnorm.pos_mul_atTop hL hpow
    apply hmul.congr'
    filter_upwards with n
    have hr : Real.rpow ((n + 1 : ℕ) : ℝ) (p - q) ≠ 0 :=
      (Real.rpow_pos_of_pos (by positivity) (p - q)).ne'
    norm_num [Nat.cast_add, Nat.cast_one] at hr ⊢
    exact div_mul_cancel₀ _ hr
  have hsmall : ∀ᶠ n in atTop, magnitude p q (n + 1) < 1 :=
    (tendsto_order.1 h0).2 1 zero_lt_one
  have hlarge : ∀ᶠ n in atTop, 2 < magnitude p q (n + 1) :=
    htop.eventually (eventually_gt_atTop 2)
  rcases (hsmall.and hlarge).exists with ⟨n, hs, hl⟩
  linarith

theorem gap23 (p q : ℝ) (hp : -1 < p) (hqp : q < p) :
    ¬ Summable (signedTerm p q) := by
  intro hsum
  apply gap22 p q hp hqp
  have hzero := hsum.tendsto_atTop_zero
  have habs : Tendsto (fun n : ℕ => |signedTerm p q n|) atTop (𝓝 0) := by
    simpa [Real.norm_eq_abs] using hzero.norm
  apply habs.congr'
  filter_upwards with n
  simpa [signedTerm] using gap1 p q hp (n + 1) (by omega)

theorem gap24 (p q : ℝ) (hp : -1 < p) :
    (p + 1 < q → Summable (fun n : ℕ => |signedTerm p q n|)) ∧
    (p < q ∧ q ≤ p + 1 → ConditionallySummable (signedTerm p q)) ∧
    (q ≤ p → ¬ Summable (signedTerm p q)) := by
  refine ⟨gap8 p q hp, ?_, ?_⟩
  · rintro ⟨hpq, hcrit⟩
    exact gap17 p q hp hpq hcrit
  · intro hqp
    rcases hqp.lt_or_eq with hlt | heq
    · exact gap23 p q hp hlt
    · subst q
      exact gap20 p hp

end

end ProofGap.Exercise2699
