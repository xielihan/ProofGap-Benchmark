import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Data.Nat.Choose.Central
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise2932_11

noncomputable section

open scoped BigOperators Interval

def arcsinOverX (x : ℝ) : ℝ :=
  Real.arcsin x / x

def centralCoefficient (n : ℕ) : ℝ :=
  (Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n

def quotientTerm (n : ℕ) (x : ℝ) : ℝ :=
  centralCoefficient n * x ^ (2 * n) / (2 * n + 1 : ℕ)

def integratedTerm (n : ℕ) : ℝ :=
  centralCoefficient n * (1 / 2 : ℝ) ^ (2 * n + 1) /
    (((2 * n + 1 : ℕ) : ℝ) ^ 2)

def targetIntegral : ℝ :=
  ∫ x in (0 : ℝ)..(1 / 2 : ℝ), arcsinOverX x

def partialIntegral : ℝ :=
  ∑ n ∈ Finset.range 3, integratedTerm n

def remainder : ℝ :=
  targetIntegral - partialIntegral

def remainderBound : ℝ :=
  centralCoefficient 3 * (1 / 2 : ℝ) ^ 7 / 7 ^ 2 *
    ∑' n : ℕ, (1 / 2 ^ 2 : ℝ) ^ n

def looseBound : ℝ :=
  (1 / (7 ^ 2 * 2 ^ 7) : ℝ) *
    (1 / (1 - (1 / 2 ^ 2 : ℝ)))

def Approx (u v ε : ℝ) : Prop :=
  |u - v| < ε

private def positiveHalfChoose (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * Ring.choose (-(1 / 2 : ℝ)) n

private theorem ringChoose_succ (r : ℝ) (n : ℕ) :
    Ring.choose r (n + 1) =
      Ring.choose r n * (r - n) / (n + 1) := by
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul]
  simp only [smul_eq_mul, descPochhammer_succ_right,
    Polynomial.smeval_mul, Polynomial.smeval_sub,
    Polynomial.smeval_X, Polynomial.smeval_natCast,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hf, hn]
  ring

private theorem positiveHalfChoose_succ (n : ℕ) :
    positiveHalfChoose (n + 1) =
      positiveHalfChoose n * (2 * (n : ℝ) + 1) /
        (2 * ((n : ℝ) + 1)) := by
  rw [positiveHalfChoose, positiveHalfChoose, ringChoose_succ, pow_succ]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hn]
  ring

private theorem centralCoefficient_succ (n : ℕ) :
    centralCoefficient (n + 1) =
      centralCoefficient n * (2 * (n : ℝ) + 1) /
        (2 * ((n : ℝ) + 1)) := by
  have hnat := Nat.succ_mul_centralBinom_succ n
  simp only [Nat.centralBinom] at hnat
  have hreal := congrArg (fun m : ℕ => (m : ℝ)) hnat
  push_cast at hreal
  rw [centralCoefficient, centralCoefficient, pow_succ]
  have hp : (4 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hp, hn]
  nlinarith

private theorem positiveHalfChoose_eq_centralCoefficient (n : ℕ) :
    positiveHalfChoose n = centralCoefficient n := by
  induction n with
  | zero =>
      norm_num [positiveHalfChoose, centralCoefficient,
        Ring.choose_zero_right, Nat.choose]
  | succ n ih =>
      rw [positiveHalfChoose_succ, centralCoefficient_succ, ih]

private theorem centralCoefficient_nonneg (n : ℕ) :
    0 ≤ centralCoefficient n := by
  exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)

private theorem centralCoefficient_pos (n : ℕ) :
    0 < centralCoefficient n := by
  have hchoose : 0 < Nat.choose (2 * n) n := by
    simpa [Nat.centralBinom] using Nat.centralBinom_pos n
  exact div_pos (by exact_mod_cast hchoose) (by positivity)

private theorem centralCoefficient_le_one (n : ℕ) :
    centralCoefficient n ≤ 1 := by
  rw [centralCoefficient]
  apply (div_le_one (by positivity)).2
  have h := Nat.centralBinom_le_four_pow n
  simp only [Nat.centralBinom] at h
  exact_mod_cast h

private theorem centralSeries_hasSum (t : ℝ) (ht : |t| < 1) :
    HasSum (fun n => centralCoefficient n * t ^ (2 * n))
      (1 / Real.sqrt (1 - t ^ 2)) := by
  have hzabs : |-(t ^ 2)| < 1 := by
    rw [abs_neg, abs_pow]
    nlinarith [abs_nonneg t]
  have hz : -(t ^ 2) ∈ Metric.eball (0 : ℝ) 1 := by
    simp only [Metric.mem_eball, edist_dist, dist_zero_right,
      ENNReal.ofReal_lt_one]
    simpa [Real.norm_eq_abs] using hzabs
  have h :=
    (Real.one_add_rpow_hasFPowerSeriesOnBall_zero
      (a := -(1 / 2 : ℝ))).hasSum hz
  have hfun :
      (fun n : ℕ =>
        (binomialSeries ℝ (-(1 / 2 : ℝ)) n)
          (fun _ => -(t ^ 2))) =
        fun n => centralCoefficient n * t ^ (2 * n) := by
    funext n
    rw [binomialSeries_apply]
    simp only [smul_eq_mul]
    rw [show (List.ofFn (fun _ : Fin n => -(t ^ 2))).prod =
        (-(t ^ 2)) ^ n by simp]
    rw [show -(t ^ 2) = (-1 : ℝ) * t ^ 2 by ring, mul_pow,
      pow_mul]
    rw [← positiveHalfChoose_eq_centralCoefficient]
    simp only [positiveHalfChoose]
    ring
  rw [hfun] at h
  have hpos : 0 < 1 - t ^ 2 := by
    have hsq : t ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one t).2 ht
    linarith
  have hvalue :
      (1 - t ^ 2) ^ (-(1 / 2 : ℝ)) =
        1 / Real.sqrt (1 - t ^ 2) := by
    rw [Real.sqrt_eq_rpow]
    rw [Real.rpow_neg hpos.le]
    simp [one_div]
  convert h using 1
  simpa [sub_eq_add_neg] using hvalue.symm

private def arcsinSeriesTerm (n : ℕ) (t : ℝ) : ℝ :=
  centralCoefficient n * t ^ (2 * n + 1) /
    ((2 * n + 1 : ℕ) : ℝ)

private theorem integral_centralTerm (t : ℝ) (n : ℕ) :
    (∫ u in (0 : ℝ)..t,
      centralCoefficient n * u ^ (2 * n)) =
        arcsinSeriesTerm n t := by
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp [arcsinSeriesTerm]
  ring

private theorem norm_centralTerm_le
    (t u : ℝ) (n : ℕ) (ht0 : 0 ≤ t) (htle : t ≤ 1 / 2)
    (hu : u ∈ Set.uIcc 0 t) :
    ‖centralCoefficient n * u ^ (2 * n)‖ ≤
      (1 / 4 : ℝ) ^ n := by
  rw [Set.uIcc_of_le ht0] at hu
  have huabs : |u| ≤ (1 / 2 : ℝ) := by
    rw [abs_of_nonneg hu.1]
    exact hu.2.trans htle
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (centralCoefficient_nonneg n), abs_pow]
  calc
    centralCoefficient n * |u| ^ (2 * n) ≤
        1 * |u| ^ (2 * n) := by
      gcongr
      exact centralCoefficient_le_one n
    _ ≤ 1 * (1 / 2 : ℝ) ^ (2 * n) := by
      gcongr
    _ = (1 / 4 : ℝ) ^ n := by
      rw [one_mul, pow_mul]
      norm_num

private theorem integral_inv_sqrt_eq_arcsin
    (t : ℝ) (ht0 : 0 ≤ t) (htle : t ≤ 1 / 2) :
    (∫ u in (0 : ℝ)..t, 1 / Real.sqrt (1 - u ^ 2)) =
      Real.arcsin t := by
  have hinside (u : ℝ) (hu : u ∈ Set.uIcc 0 t) :
      |u| < 1 := by
    rw [Set.uIcc_of_le ht0] at hu
    rw [abs_of_nonneg hu.1]
    linarith [hu.2]
  have hderiv :
      ∀ u ∈ Set.uIcc (0 : ℝ) t,
        HasDerivAt Real.arcsin
          (1 / Real.sqrt (1 - u ^ 2)) u := by
    intro u hu
    have hu1 := hinside u hu
    rw [abs_lt] at hu1
    exact Real.hasDerivAt_arcsin (by linarith) (by linarith)
  have hcont :
      ContinuousOn (fun u : ℝ => 1 / Real.sqrt (1 - u ^ 2))
        (Set.uIcc 0 t) := by
    intro u hu
    have hu1 := hinside u hu
    have hpos : 0 < 1 - u ^ 2 := by
      have hsquare : u ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one u).2 hu1
      linarith
    have hsqrt :
        Continuous (fun v : ℝ => Real.sqrt (1 - v ^ 2)) :=
      Real.continuous_sqrt.comp
        (continuous_const.sub (continuous_id.pow 2))
    apply ContinuousAt.continuousWithinAt
    exact continuousAt_const.div hsqrt.continuousAt
      (Real.sqrt_ne_zero'.2 hpos)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderiv hcont.intervalIntegrable]
  simp

private theorem arcsinSeriesTerm_hasSum
    (t : ℝ) (ht0 : 0 < t) (htle : t ≤ 1 / 2) :
    HasSum (fun n => arcsinSeriesTerm n t) (Real.arcsin t) := by
  have h :
      HasSum
        (fun n : ℕ =>
          ∫ u in (0 : ℝ)..t,
            centralCoefficient n * u ^ (2 * n))
        (∫ u in (0 : ℝ)..t, 1 / Real.sqrt (1 - u ^ 2)) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n (_ : ℝ) => (1 / 4 : ℝ) ^ n)
    · intro n
      apply Continuous.aestronglyMeasurable
      fun_prop
    · intro n
      filter_upwards with u hu
      exact norm_centralTerm_le t u n ht0.le htle
        (Set.uIoc_subset_uIcc hu)
    · filter_upwards with u hu
      exact summable_geometric_of_norm_lt_one
        (by norm_num [Real.norm_eq_abs] :
          ‖(1 / 4 : ℝ)‖ < 1)
    · exact intervalIntegrable_const
    · filter_upwards with u hu
      have hu' := Set.uIoc_subset_uIcc hu
      rw [Set.uIcc_of_le ht0.le] at hu'
      have huabs : |u| < 1 := by
        rw [abs_of_nonneg hu'.1]
        linarith [hu'.2]
      exact centralSeries_hasSum u huabs
  have h' :
      HasSum (fun n => arcsinSeriesTerm n t)
        (∫ u in (0 : ℝ)..t, 1 / Real.sqrt (1 - u ^ 2)) := by
    apply h.congr_fun
    intro n
    exact (integral_centralTerm t n).symm
  rw [integral_inv_sqrt_eq_arcsin t ht0.le htle] at h'
  exact h'

private theorem quotientTerm_hasSum
    (t : ℝ) (ht0 : 0 < t) (htle : t ≤ 1 / 2) :
    HasSum (fun n => quotientTerm n t) (arcsinOverX t) := by
  have h := (arcsinSeriesTerm_hasSum t ht0 htle).div_const t
  convert h using 1
  funext n
  unfold arcsinSeriesTerm quotientTerm
  rw [show 2 * n + 1 = 2 * n + 1 by rfl, pow_succ]
  field_simp [ht0.ne']

private theorem interval_facts
    {t : ℝ} (ht : t ∈ Set.uIoc (0 : ℝ) (1 / 2 : ℝ)) :
    0 < t ∧ t ≤ 1 / 2 := by
  rw [Set.uIoc_of_le (by norm_num)] at ht
  exact ht

private theorem integral_quotientTerm (n : ℕ) :
    (∫ t in (0 : ℝ)..(1 / 2 : ℝ), quotientTerm n t) =
      integratedTerm n := by
  have hfun :
      (fun t : ℝ => quotientTerm n t) =
        fun t : ℝ =>
          (centralCoefficient n / (((2 * n + 1 : ℕ) : ℝ))) *
            t ^ (2 * n) := by
    funext t
    unfold quotientTerm
    ring
  rw [hfun, intervalIntegral.integral_const_mul, integral_pow]
  simp [integratedTerm]
  field_simp

private theorem norm_quotientTerm_le
    (t : ℝ) (n : ℕ) (ht : t ∈ Set.uIcc 0 (1 / 2 : ℝ)) :
    ‖quotientTerm n t‖ ≤ (1 / 4 : ℝ) ^ n := by
  have habs : |t| ≤ (1 / 2 : ℝ) := by
    have hdist := Real.dist_left_le_of_mem_uIcc ht
    simpa [Real.dist_eq] using hdist
  have hden :
      (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ 2 * n + 1 by omega)
  calc
    ‖quotientTerm n t‖ =
        centralCoefficient n * |t| ^ (2 * n) /
          ((2 * n + 1 : ℕ) : ℝ) := by
      rw [Real.norm_eq_abs]
      unfold quotientTerm
      rw [abs_div, abs_mul,
        abs_of_nonneg (centralCoefficient_nonneg n), abs_pow,
        abs_of_pos (by positivity :
          (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ))]
    _ ≤ centralCoefficient n * |t| ^ (2 * n) :=
      div_le_self (mul_nonneg (centralCoefficient_nonneg n) (by positivity))
        hden
    _ ≤ 1 * (1 / 2 : ℝ) ^ (2 * n) := by
      gcongr
      exact centralCoefficient_le_one n
    _ = (1 / 4 : ℝ) ^ n := by
      rw [one_mul, pow_mul]
      norm_num

private theorem quotientIntegral_hasSum :
    HasSum
      (fun n : ℕ =>
        ∫ t in (0 : ℝ)..(1 / 2 : ℝ), quotientTerm n t)
      targetIntegral := by
  unfold targetIntegral
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n (_ : ℝ) => (1 / 4 : ℝ) ^ n)
  · intro n
    apply Continuous.aestronglyMeasurable
    unfold quotientTerm
    fun_prop
  · intro n
    filter_upwards with t ht
    exact norm_quotientTerm_le t n (Set.uIoc_subset_uIcc ht)
  · filter_upwards with t ht
    exact summable_geometric_of_norm_lt_one
      (by norm_num [Real.norm_eq_abs] :
        ‖(1 / 4 : ℝ)‖ < 1)
  · exact intervalIntegrable_const
  · filter_upwards with t ht
    obtain ⟨ht0, htle⟩ := interval_facts ht
    exact quotientTerm_hasSum t ht0 htle

private theorem integratedTerm_hasSum :
    HasSum integratedTerm targetIntegral := by
  apply quotientIntegral_hasSum.congr_fun
  intro n
  exact (integral_quotientTerm n).symm

private theorem summable_integratedTerm :
    Summable integratedTerm :=
  integratedTerm_hasSum.summable

theorem gap1 :
    targetIntegral =
      ∫ x in (0 : ℝ)..(1 / 2 : ℝ),
        ∑' n : ℕ, quotientTerm n x := by
  unfold targetIntegral
  apply intervalIntegral.integral_congr_ae
  filter_upwards with t ht
  obtain ⟨ht0, htle⟩ := interval_facts ht
  exact (quotientTerm_hasSum t ht0 htle).tsum_eq.symm

theorem gap2 :
    targetIntegral = ∑' n : ℕ, integratedTerm n := by
  exact integratedTerm_hasSum.tsum_eq.symm

private theorem centralCoefficient_antitone :
    Antitone centralCoefficient := by
  apply antitone_nat_of_succ_le
  intro n
  rw [centralCoefficient_succ]
  have hratio_nonneg :
      0 ≤ (2 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1)) := by
    positivity
  have hratio_le :
      (2 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1)) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    linarith
  calc
    centralCoefficient n * (2 * (n : ℝ) + 1) /
          (2 * ((n : ℝ) + 1)) =
        centralCoefficient n *
          ((2 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1))) := by
            ring
    _ ≤ centralCoefficient n * 1 :=
      mul_le_mul_of_nonneg_left hratio_le
        (centralCoefficient_nonneg n)
    _ = centralCoefficient n := by ring

private theorem integratedTerm_pos (n : ℕ) :
    0 < integratedTerm n := by
  unfold integratedTerm
  exact div_pos
    (mul_pos (centralCoefficient_pos n) (by positivity))
    (by positivity)

private theorem remainder_eq_tail :
    remainder = ∑' n : ℕ, integratedTerm (n + 3) := by
  rw [remainder, partialIntegral, ← integratedTerm_hasSum.tsum_eq]
  have hsplit := summable_integratedTerm.sum_add_tsum_nat_add 3
  linarith

private theorem tail_summable :
    Summable (fun n : ℕ => integratedTerm (n + 3)) :=
  (summable_nat_add_iff 3).2 summable_integratedTerm

private theorem tail_term_le_majorant (n : ℕ) :
    integratedTerm (n + 3) ≤
      integratedTerm 3 * (1 / 4 : ℝ) ^ n := by
  have hc :
      centralCoefficient (n + 3) ≤ centralCoefficient 3 :=
    centralCoefficient_antitone (by omega)
  have hp :
      0 ≤ (1 / 2 : ℝ) ^ (2 * (n + 3) + 1) := by positivity
  have hden :
      (49 : ℝ) ≤
        (((2 * (n + 3) + 1 : ℕ) : ℝ) ^ 2) := by
    have hbase :
        (7 : ℝ) ≤ ((2 * (n + 3) + 1 : ℕ) : ℝ) := by
      exact_mod_cast
        (show 7 ≤ 2 * (n + 3) + 1 by omega)
    calc
      (49 : ℝ) = (7 : ℝ) ^ 2 := by norm_num
      _ ≤ (((2 * (n + 3) + 1 : ℕ) : ℝ) ^ 2) :=
        (sq_le_sq₀ (by norm_num) (by positivity)).2 hbase
  calc
    integratedTerm (n + 3) =
        centralCoefficient (n + 3) *
          (1 / 2 : ℝ) ^ (2 * (n + 3) + 1) /
            (((2 * (n + 3) + 1 : ℕ) : ℝ) ^ 2) := rfl
    _ ≤
        centralCoefficient 3 *
          (1 / 2 : ℝ) ^ (2 * (n + 3) + 1) /
            (((2 * (n + 3) + 1 : ℕ) : ℝ) ^ 2) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc hp) (by positivity)
    _ ≤
        centralCoefficient 3 *
          (1 / 2 : ℝ) ^ (2 * (n + 3) + 1) / 49 := by
      exact div_le_div₀
        (mul_nonneg (centralCoefficient_nonneg 3) hp)
        (le_refl _) (by norm_num) hden
    _ =
        (centralCoefficient 3 * (1 / 2 : ℝ) ^ 7 / 49) *
          (1 / 4 : ℝ) ^ n := by
      rw [show 2 * (n + 3) + 1 = 7 + 2 * n by omega,
        pow_add, pow_mul]
      norm_num
      ring
    _ = integratedTerm 3 * (1 / 4 : ℝ) ^ n := by
      norm_num [integratedTerm]

private theorem majorant_summable :
    Summable (fun n : ℕ =>
      integratedTerm 3 * (1 / 4 : ℝ) ^ n) :=
  (summable_geometric_of_norm_lt_one
    (by norm_num [Real.norm_eq_abs] :
      ‖(1 / 4 : ℝ)‖ < 1)).mul_left _

theorem gap3 :
    0 < remainder := by
  rw [remainder_eq_tail]
  have hsplit := tail_summable.sum_add_tsum_nat_add 1
  have hrest :
      0 ≤ ∑' n : ℕ, integratedTerm (n + 1 + 3) :=
    tsum_nonneg (fun n => (integratedTerm_pos _).le)
  calc
    0 < integratedTerm 3 +
        ∑' n : ℕ, integratedTerm (n + 1 + 3) :=
      add_pos_of_pos_of_nonneg (integratedTerm_pos 3) hrest
    _ = ∑' n : ℕ, integratedTerm (n + 3) := by
      simpa using hsplit

theorem gap4 :
    remainder < remainderBound := by
  rw [remainder_eq_tail]
  have hstrict :
      integratedTerm (1 + 3) <
        integratedTerm 3 * (1 / 4 : ℝ) ^ 1 := by
    norm_num [integratedTerm, centralCoefficient, Nat.choose]
  have hsumlt :
      (∑' n : ℕ, integratedTerm (n + 3)) <
        ∑' n : ℕ, integratedTerm 3 * (1 / 4 : ℝ) ^ n :=
    tail_summable.tsum_lt_tsum tail_term_le_majorant hstrict
      majorant_summable
  calc
    (∑' n : ℕ, integratedTerm (n + 3)) <
        ∑' n : ℕ, integratedTerm 3 * (1 / 4 : ℝ) ^ n :=
      hsumlt
    _ = remainderBound := by
      rw [remainderBound, tsum_mul_left]
      norm_num [integratedTerm, centralCoefficient, Nat.choose]

theorem gap5 :
    remainderBound < looseBound := by
  rw [remainderBound, looseBound,
    tsum_geometric_of_norm_lt_one
      (by norm_num [Real.norm_eq_abs] :
        ‖(1 / 2 ^ 2 : ℝ)‖ < 1)]
  norm_num [centralCoefficient, Nat.choose]

theorem gap6 :
    looseBound < (1 / 10 ^ 3 : ℝ) := by
  norm_num [looseBound]

theorem gap7 :
    (0 : ℝ) < 1 / 10 ^ 3 := by
  norm_num

theorem gap8 :
    Approx targetIntegral (507 / 1000 : ℝ)
      (1 / 1000 : ℝ) := by
  have hpos := gap3
  have hbound := lt_trans gap4 gap5
  norm_num [looseBound] at hbound
  have heq : targetIntegral = partialIntegral + remainder := by
    unfold remainder
    ring
  rw [Approx, abs_lt, heq]
  norm_num [partialIntegral, integratedTerm, centralCoefficient,
    Nat.choose, Finset.sum_range_succ]
  constructor <;> linarith

end

end ProofGap.Exercise2932_11
