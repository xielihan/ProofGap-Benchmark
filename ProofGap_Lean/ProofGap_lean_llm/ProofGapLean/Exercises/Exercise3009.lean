import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace ProofGap.Exercise3009

noncomputable section

open Filter
open scoped BigOperators Topology

def coeff (a d : ℝ) (n : ℕ) : ℝ :=
  (∏ k ∈ Finset.range n, (a + (k : ℝ) * d)) /
    (∏ k ∈ Finset.range n, ((k + 1 : ℕ) : ℝ) * d)

def term (a d x : ℝ) (n : ℕ) : ℝ := coeff a d n * x ^ n

def seriesFunction (a d x : ℝ) : ℝ :=
  ∑' n : ℕ, term a d x (n + 1)

def convergenceDomain (a d : ℝ) : Set ℝ :=
  {x | Summable (fun n : ℕ => term a d x (n + 1))}

def powerSeriesRadius (a d : ℝ) : ℝ :=
  sSup {r : ℝ | 0 ≤ r ∧
    ∀ x : ℝ, |x| < r → Summable (fun n : ℕ => term a d x (n + 1))}

def binomialClosedForm (a d x : ℝ) : ℝ :=
  Real.rpow (1 - x) (-a / d) - 1

private theorem coeff_succ (a d : ℝ) (n : ℕ) (hd : d ≠ 0) :
    coeff a d (n + 1) =
      coeff a d n * (a + (n : ℝ) * d) / (((n + 1 : ℕ) : ℝ) * d) := by
  unfold coeff
  simp only [Finset.prod_range_succ]
  field_simp [hd]
  simp only [mul_comm d]
  ring

private theorem multichoose_succ (r : ℝ) (n : ℕ) :
    Ring.multichoose r (n + 1) =
      Ring.multichoose r n * (r + n) / (n + 1) := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero (n + 1)),
    Ring.factorial_nsmul_multichoose_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval, ascPochhammer_succ_eval,
    ← Polynomial.ascPochhammer_smeval_eq_eval,
    ← Ring.factorial_nsmul_multichoose_eq_ascPochhammer]
  simp only [Nat.factorial_succ, mul_nsmul, nsmul_eq_mul, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  field_simp

private theorem coeff_eq_multichoose (a d : ℝ) (n : ℕ) (hd : d ≠ 0) :
    coeff a d n = Ring.multichoose (a / d) n := by
  induction n with
  | zero => simp [coeff, Ring.multichoose_zero_right]
  | succ n ih =>
      rw [show n + 1 = Nat.succ n by rfl]
      rw [coeff_succ a d n hd, ih, multichoose_succ]
      field_simp [hd]
      push_cast
      ring

private theorem coeff_hasSum (a d x : ℝ) (hd : d ≠ 0) (hx : |x| < 1) :
    HasSum (fun n : ℕ => coeff a d n * x ^ n)
      (Real.rpow (1 - x) (-a / d)) := by
  have hs := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero
    (a / d)).hasSum (show x ∈ Metric.eball (0 : ℝ) (1 : ENNReal) by
      simpa [Metric.mem_eball, edist_dist] using hx)
  convert hs using 1
  · ext n
    rw [FormalMultilinearSeries.ofScalars_apply_eq]
    simp only [smul_eq_mul]
    rw [coeff_eq_multichoose a d n hd, Ring.multichoose_eq]
  · have hnonneg : 0 ≤ 1 - x := by linarith [(abs_lt.mp hx).2]
    simp only [zero_add]
    rw [show -a / d = -(a / d) by ring]
    change (1 - x) ^ (-(a / d)) = 1 / (1 - x) ^ (a / d)
    rw [Real.rpow_neg hnonneg]
    simp [one_div]

private theorem derivCoeff_hasSum (a d x : ℝ) (hd : d ≠ 0) (hx : |x| < 1) :
    HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * coeff a d (n + 1) * x ^ n)
      (deriv (fun y : ℝ => 1 / (1 - y) ^ (a / d)) x) := by
  let p : FormalMultilinearSeries ℝ ℝ ℝ :=
    .ofScalars ℝ (fun n => Ring.choose (a / d + n - 1) n)
  have hp : HasFPowerSeriesOnBall (fun y : ℝ => 1 / (1 - y) ^ (a / d))
      p 0 1 := Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (a / d)
  have hball : x ∈ Metric.eball (0 : ℝ) (1 : ENNReal) := by
    simpa [Metric.mem_eball, edist_dist] using hx
  have hsMaps := hp.fderiv.hasSum hball
  have hs := (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).hasSum hsMaps
  convert hs using 1
  · ext n
    simp only [p, FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [map_smul, ContinuousLinearMap.apply_apply,
      FormalMultilinearSeries.derivSeries_coeff_one]
    simp only [p, FormalMultilinearSeries.coeff_ofScalars, nsmul_eq_mul,
      smul_eq_mul, one_mul]
    rw [coeff_eq_multichoose a d (n + 1) hd, Ring.multichoose_eq]
    ring
  · simp [fderiv_apply_one_eq_deriv]

private theorem seriesFunction_eq_rpow (a d x : ℝ) (hd : d ≠ 0) (hx : |x| < 1) :
    seriesFunction a d x = (1 - x) ^ (-(a / d)) - 1 := by
  have hs := (hasSum_nat_add_iff' 1).mpr (coeff_hasSum a d x hd hx)
  unfold seriesFunction
  have ht : HasSum (fun n : ℕ => term a d x (n + 1))
      ((1 - x) ^ (-(a / d)) - 1) := by
    simpa [term, coeff, show -a / d = -(a / d) by ring] using hs
  exact ht.tsum_eq

private theorem seriesFunction_eq_one_div (a d x : ℝ) (hd : d ≠ 0) (hx : |x| < 1) :
    seriesFunction a d x = 1 / (1 - x) ^ (a / d) - 1 := by
  rw [seriesFunction_eq_rpow a d x hd hx]
  have hnonneg : 0 ≤ 1 - x := by linarith [(abs_lt.mp hx).2]
  rw [Real.rpow_neg hnonneg]
  simp [one_div]

private theorem deriv_seriesFunction_eq_tsum (a d x : ℝ) (hd : d ≠ 0) (hx : |x| < 1) :
    deriv (seriesFunction a d) x =
      ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * coeff a d (n + 1) * x ^ n := by
  have hopen : IsOpen {y : ℝ | |y| < 1} :=
    isOpen_lt continuous_abs continuous_const
  have heq : seriesFunction a d =ᶠ[𝓝 x]
      (fun y : ℝ => 1 / (1 - y) ^ (a / d) - 1) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact seriesFunction_eq_one_div a d y hd hy
  calc
    deriv (seriesFunction a d) x =
        deriv (fun y : ℝ => 1 / (1 - y) ^ (a / d) - 1) x := heq.deriv_eq
    _ = deriv (fun y : ℝ => 1 / (1 - y) ^ (a / d)) x := by simp
    _ = ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * coeff a d (n + 1) * x ^ n :=
      (derivCoeff_hasSum a d x hd hx).tsum_eq.symm

private theorem seriesFunction_ode (a d x : ℝ) (hd : d ≠ 0) (hx : |x| < 1) :
    (1 - x) * deriv (seriesFunction a d) x =
      a / d + (a / d) * seriesFunction a d x := by
  have hbase : 0 < 1 - x := by linarith [(abs_lt.mp hx).2]
  have hinner : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    convert (hasDerivAt_const x 1).sub (hasDerivAt_id x) using 1 <;> simp
  have hpow : HasDerivAt (fun y : ℝ => (1 - y) ^ (-(a / d)))
      ((-1) * (-(a / d)) * (1 - x) ^ (-(a / d) - 1)) x :=
    hinner.rpow_const (Or.inl hbase.ne')
  have hopen : IsOpen {y : ℝ | |y| < 1} :=
    isOpen_lt continuous_abs continuous_const
  have heq : seriesFunction a d =ᶠ[𝓝 x]
      (fun y : ℝ => (1 - y) ^ (-(a / d)) - 1) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact seriesFunction_eq_rpow a d y hd hy
  have hderiv : deriv (seriesFunction a d) x =
      (-1) * (-(a / d)) * (1 - x) ^ (-(a / d) - 1) :=
    ((hpow.sub_const 1).congr_of_eventuallyEq heq).deriv
  rw [hderiv, seriesFunction_eq_rpow a d x hd hx,
    Real.rpow_sub_one hbase.ne']
  field_simp [hd, hbase.ne']
  ring

private theorem coeff_ne_zero (a d : ℝ) (hd : d ≠ 0)
    (hnonterm : ∀ m : ℕ, a ≠ -(m : ℝ) * d) (n : ℕ) :
    coeff a d n ≠ 0 := by
  unfold coeff
  apply div_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    intro hkzero
    apply hnonterm k
    linear_combination hkzero
  · apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    exact mul_ne_zero (by positivity) hd

private theorem coeff_pos (a d : ℝ) (ha : 0 < a) (hd : 0 < d) (n : ℕ) :
    0 < coeff a d n := by
  unfold coeff
  positivity

private theorem rational_ratio_tendsto (a d : ℝ) (hd : d ≠ 0) :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * d / (a + (n : ℝ) * d))
      atTop (𝓝 1) := by
  have hnum : Tendsto (fun n : ℕ => d + d / (n : ℝ)) atTop (𝓝 d) := by
    convert tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat d) using 1 <;>
      simp
  have hden : Tendsto (fun n : ℕ => d + a / (n : ℝ)) atTop (𝓝 d) := by
    convert tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat a) using 1 <;>
      simp
  have hquot : Tendsto
      (fun n : ℕ => (d + d / (n : ℝ)) / (d + a / (n : ℝ)))
      atTop (𝓝 1) := by
    simpa [hd] using hnum.div hden hd
  apply hquot.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hnCast : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp [hnCast]
  push_cast
  ring

private theorem raabe_rational_tendsto (a d : ℝ) (hd : d ≠ 0) :
    Tendsto (fun n : ℕ => ((d - a) * (n : ℝ)) / (a + (n : ℝ) * d))
      atTop (𝓝 ((d - a) / d)) := by
  have hden : Tendsto (fun n : ℕ => d + a / (n : ℝ)) atTop (𝓝 d) := by
    convert tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat a) using 1 <;>
      simp
  have hquot : Tendsto (fun n : ℕ => (d - a) / (d + a / (n : ℝ)))
      atTop (𝓝 ((d - a) / d)) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => d - a) atTop (𝓝 (d - a))).div
      hden hd
  apply hquot.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hnCast : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp [hnCast]
  ring

private theorem coeff_eq_zero_of_lt (a d : ℝ) (m n : ℕ)
    (hm : a = -(m : ℝ) * d) (h : m < n) : coeff a d n = 0 := by
  unfold coeff
  rw [show (∏ k ∈ Finset.range n, (a + (k : ℝ) * d)) = 0 by
    apply Finset.prod_eq_zero (Finset.mem_range.mpr h)
    rw [hm]
    ring]
  exact zero_div _

theorem gap1 (a d x : ℝ) (m : ℕ) (hd : d ≠ 0)
    (hm : a = -(m : ℝ) * d) :
    (∑' n : ℕ, term a d x (n + 1)) =
      ∑ n ∈ Finset.Icc 1 m, term a d x n := by
  rw [tsum_eq_sum (s := Finset.range m)]
  · have hIcc : Finset.Icc 1 m = Finset.Ico 1 (m + 1) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIcc, Finset.sum_Ico_eq_sum_range]
    simp [Nat.add_comm]
  · intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    rw [term, coeff_eq_zero_of_lt a d m (n + 1) hm (Nat.lt_succ_of_le hn), zero_mul]

theorem gap2 (a d : ℝ) (m : ℕ) (hd : d ≠ 0)
    (hm : a = -(m : ℝ) * d) :
    convergenceDomain a d = Set.univ := by
  ext x
  simp only [convergenceDomain, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  apply summable_of_hasFiniteSupport
  refine (Set.finite_Iio m).subset ?_
  intro n hn
  simp only [Function.mem_support] at hn
  simp only [Set.mem_Iio]
  by_contra hlt
  have hle : m ≤ n := Nat.not_lt.mp hlt
  apply hn
  rw [term, coeff_eq_zero_of_lt a d m (n + 1) hm]
  · simp
  · omega

theorem gap3 (a d : ℝ) (hd : d ≠ 0)
    (hnonterm : ∀ m : ℕ, a ≠ -(m : ℝ) * d) :
    Tendsto (fun n : ℕ => |coeff a d n / coeff a d (n + 1)|) atTop (𝓝 1) ∧
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * d / (a + (n : ℝ) * d))
      atTop (𝓝 1) := by
  have hratio : ∀ n : ℕ, coeff a d n / coeff a d (n + 1) =
      ((n + 1 : ℕ) : ℝ) * d / (a + (n : ℝ) * d) := by
    intro n
    have hfactor : a + (n : ℝ) * d ≠ 0 := by
      intro hzero
      apply hnonterm n
      linear_combination hzero
    rw [coeff_succ a d n hd]
    field_simp [coeff_ne_zero a d hd hnonterm n, hfactor, hd]
  have hplain : Tendsto (fun n : ℕ => coeff a d n / coeff a d (n + 1))
      atTop (𝓝 1) := by
    apply (rational_ratio_tendsto a d hd).congr'
    exact Filter.Eventually.of_forall fun n => (hratio n).symm
  refine ⟨?_, rational_ratio_tendsto a d hd⟩
  simpa using (continuous_abs.tendsto 1).comp hplain

theorem gap4 (a d : ℝ) (hd : d ≠ 0) :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * d / (a + (n : ℝ) * d))
      atTop (𝓝 1) := by
  exact rational_ratio_tendsto a d hd

theorem gap5 (a d : ℝ) (hd : d ≠ 0)
    (hnonterm : ∀ m : ℕ, a ≠ -(m : ℝ) * d) :
    Tendsto (fun n : ℕ => |coeff a d n / coeff a d (n + 1)|)
      atTop (𝓝 1) := by
  exact (gap3 a d hd hnonterm).1

private theorem not_summable_term_of_one_lt (a d x : ℝ) (hd : d ≠ 0)
    (hnonterm : ∀ m : ℕ, a ≠ -(m : ℝ) * d) (hx : 1 < x) :
    ¬Summable (fun n : ℕ => term a d x (n + 1)) := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hcInv : Tendsto (fun n : ℕ => |coeff a d (n + 1) / coeff a d (n + 2)|)
      atTop (𝓝 1) := by
    simpa [Nat.add_assoc] using
      (gap5 a d hd hnonterm).comp (tendsto_add_atTop_nat 1)
  have hcForward : Tendsto
      (fun n : ℕ => |coeff a d (n + 2) / coeff a d (n + 1)|)
      atTop (𝓝 1) := by
    have hi := hcInv.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    have hi' : Tendsto
        (fun n : ℕ => |coeff a d (n + 1) / coeff a d (n + 2)|⁻¹)
        atTop (𝓝 1) := by simpa only [inv_one] using hi
    apply hi'.congr'
    filter_upwards with n
    rw [abs_div, abs_div]
    field_simp [coeff_ne_zero a d hd hnonterm (n + 1),
      coeff_ne_zero a d hd hnonterm (n + 2)]
  have htend : Tendsto
      (fun n : ℕ => ‖term a d x ((n + 1) + 1)‖ / ‖term a d x (n + 1)‖)
      atTop (𝓝 x) := by
    have hm := hcForward.mul (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => x) atTop (𝓝 x))
    have hm' : Tendsto
        (fun n : ℕ => |coeff a d (n + 2) / coeff a d (n + 1)| * x)
        atTop (𝓝 x) := by simpa only [one_mul] using hm
    apply hm'.congr'
    filter_upwards with n
    simp only [term, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hxpos,
      pow_succ]
    rw [abs_div]
    field_simp [coeff_ne_zero a d hd hnonterm (n + 1),
      abs_ne_zero.mpr (coeff_ne_zero a d hd hnonterm (n + 1)),
      pow_ne_zero _ hxpos.ne']
  exact not_summable_of_ratio_test_tendsto_gt_one hx htend

theorem gap6 (a d : ℝ) (hd : d ≠ 0)
    (hnonterm : ∀ m : ℕ, a ≠ -(m : ℝ) * d) :
    powerSeriesRadius a d = 1 := by
  unfold powerSeriesRadius
  let S : Set ℝ := {r : ℝ | 0 ≤ r ∧
    ∀ x : ℝ, |x| < r → Summable (fun n : ℕ => term a d x (n + 1))}
  change sSup S = 1
  have hOne : (1 : ℝ) ∈ S := by
    refine ⟨zero_le_one, ?_⟩
    intro x hx
    apply (summable_nat_add_iff 1).2
    simpa [term] using (coeff_hasSum a d x hd hx).summable
  have hupper : ∀ r ∈ S, r ≤ (1 : ℝ) := by
    intro r hrMem
    by_contra hle
    have hr : 1 < r := lt_of_not_ge hle
    let x : ℝ := (1 + r) / 2
    have hx : 1 < x := by dsimp [x]; linarith
    have hxr : x < r := by dsimp [x]; linarith
    have hxabs : |x| < r := by
      rw [abs_of_pos (zero_lt_one.trans hx)]
      exact hxr
    exact (not_summable_term_of_one_lt a d x hd hnonterm hx) (hrMem.2 x hxabs)
  have hbdd : BddAbove S := ⟨1, hupper⟩
  apply le_antisymm
  · exact csSup_le ⟨1, hOne⟩ hupper
  · exact le_csSup hbdd hOne

theorem gap7 (a d x : ℝ) (hd : d ≠ 0) (hx : |x| < 1) :
    deriv (seriesFunction a d) x =
      ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * coeff a d (n + 1) * x ^ n := by
  exact deriv_seriesFunction_eq_tsum a d x hd hx

theorem gap8 (a d x : ℝ) (hd : d ≠ 0) (hx : |x| < 1) :
    (1 - x) * deriv (seriesFunction a d) x =
      a / d + (a / d) * (∑' n : ℕ, term a d x (n + 1)) := by
  simpa [seriesFunction] using seriesFunction_ode a d x hd hx

theorem gap9 (a d x : ℝ) (hd : d ≠ 0) (hx : |x| < 1) :
    a / d + (a / d) * (∑' n : ℕ, term a d x (n + 1)) =
      a / d + (a / d) * seriesFunction a d x := by
  rfl

theorem gap10 (a d x : ℝ) (hd : d ≠ 0) (hx : |x| < 1) :
    (1 - x) * deriv (seriesFunction a d) x =
      a / d + (a / d) * seriesFunction a d x := by
  exact seriesFunction_ode a d x hd hx

theorem gap11 (a d x : ℝ) (hd : d ≠ 0) (hx : |x| < 1) :
    deriv (seriesFunction a d) x -
        (a / d) * (1 / (1 - x)) * seriesFunction a d x =
      (a / d) * (1 / (1 - x)) := by
  have hbase : 1 - x ≠ 0 := by linarith [(abs_lt.mp hx).2]
  have h := seriesFunction_ode a d x hd hx
  field_simp [hbase, hd] at h ⊢
  linear_combination h

theorem gap12 (a d : ℝ) (hd : d ≠ 0) :
    ∃ C : ℝ, ∀ x : ℝ, |x| < 1 →
      seriesFunction a d x = C * Real.rpow (1 - x) (-a / d) - 1 := by
  refine ⟨1, ?_⟩
  intro x hx
  rw [one_mul, seriesFunction_eq_rpow a d x hd hx]
  congr 2
  ring

theorem gap13 (a d x : ℝ) (hd : d ≠ 0) (hx : |x| < 1) :
    seriesFunction a d 0 = 0 := by
  rw [seriesFunction_eq_rpow a d 0 hd (by norm_num)]
  norm_num

theorem gap14 (a d : ℝ) (hd : d ≠ 0) :
    ∃ C : ℝ, C = 1 ∧ ∀ x : ℝ, |x| < 1 →
      seriesFunction a d x = C * Real.rpow (1 - x) (-a / d) - 1 := by
  refine ⟨1, rfl, ?_⟩
  intro x hx
  rw [one_mul, seriesFunction_eq_rpow a d x hd hx]
  congr 2
  ring

theorem gap15 (a d x : ℝ) (hd : d ≠ 0) (hx : |x| < 1) :
    seriesFunction a d x = binomialClosedForm a d x := by
  rw [seriesFunction_eq_rpow a d x hd hx]
  unfold binomialClosedForm
  congr 2
  ring

theorem gap16 (a d : ℝ) (hd : d ≠ 0)
    (hnonterm : ∀ m : ℕ, a ≠ -(m : ℝ) * d) :
    Tendsto
      (fun n : ℕ => (n : ℝ) * (|coeff a d n| / |coeff a d (n + 1)| - 1))
      atTop (𝓝 ((d - a) / d)) := by
  have hratio : ∀ n : ℕ, coeff a d n / coeff a d (n + 1) =
      ((n + 1 : ℕ) : ℝ) * d / (a + (n : ℝ) * d) := by
    intro n
    have hfactor : a + (n : ℝ) * d ≠ 0 := by
      intro hzero
      apply hnonterm n
      linear_combination hzero
    rw [coeff_succ a d n hd]
    field_simp [coeff_ne_zero a d hd hnonterm n, hfactor, hd]
  have hR := rational_ratio_tendsto a d hd
  apply (raabe_rational_tendsto a d hd).congr'
  filter_upwards [hR.eventually (Ioi_mem_nhds zero_lt_one)] with n hn
  have hfactor : a + (n : ℝ) * d ≠ 0 := by
    intro hzero
    apply hnonterm n
    linear_combination hzero
  have hfactor' : d * (n : ℝ) + a ≠ 0 := by
    simpa [add_comm, mul_comm] using hfactor
  rw [← abs_div, hratio n, abs_of_pos hn]
  have halg :
      (n : ℝ) *
          ((((n + 1 : ℕ) : ℝ) * d / (a + (n : ℝ) * d)) - 1) =
        ((d - a) * (n : ℝ)) / (a + (n : ℝ) * d) := by
    field_simp [hfactor, hfactor']
    push_cast
    ring
  exact halg.symm

theorem gap17 (a d : ℝ) (hd : d ≠ 0) :
    Tendsto (fun n : ℕ => ((d - a) * (n : ℝ)) / (a + (n : ℝ) * d))
      atTop (𝓝 ((d - a) / d)) := by
  exact raabe_rational_tendsto a d hd

theorem gap18 (a d : ℝ) (hd : d ≠ 0)
    (hnonterm : ∀ m : ℕ, a ≠ -(m : ℝ) * d) :
    Tendsto
      (fun n : ℕ => (n : ℝ) * (|coeff a d n| / |coeff a d (n + 1)| - 1))
      atTop (𝓝 ((d - a) / d)) := by
  exact gap16 a d hd hnonterm

theorem gap19 (a d : ℝ) (hd : 0 < d) (ha : a < 0)
    (hnonterm : ∀ m : ℕ, a ≠ -(m : ℝ) * d) :
    Summable (fun n : ℕ => coeff a d (n + 1)) := by
  obtain ⟨K, hK⟩ := exists_nat_gt (-a / d)
  have hKfac : 0 < a + (K : ℝ) * d := by
    have h := (div_lt_iff₀ hd).mp hK
    nlinarith
  have hfactor : ∀ j : ℕ, 0 <
      (a + ((K + j : ℕ) : ℝ) * d) /
        (((K + j + 1 : ℕ) : ℝ) * d) := by
    intro j
    apply div_pos
    · push_cast
      have hj : 0 ≤ (j : ℝ) := by positivity
      nlinarith
    · positivity
  have hrec : ∀ j : ℕ,
      coeff a d (K + (j + 1)) = coeff a d (K + j) *
        ((a + ((K + j : ℕ) : ℝ) * d) /
          (((K + j + 1 : ℕ) : ℝ) * d)) := by
    intro j
    rw [show K + (j + 1) = (K + j) + 1 by omega,
      coeff_succ a d (K + j) hd.ne', mul_div_assoc]
  have hcKne : coeff a d K ≠ 0 := coeff_ne_zero a d hd.ne' hnonterm K
  obtain ⟨s, hsabs, hsign⟩ : ∃ s : ℝ, |s| = 1 ∧
      ∀ j : ℕ, |coeff a d (K + j)| = s * coeff a d (K + j) := by
    rcases lt_or_gt_of_ne hcKne with hcneg | hcpos
    · refine ⟨-1, by norm_num, ?_⟩
      intro j
      have hjneg : coeff a d (K + j) < 0 := by
        induction j with
        | zero => simpa using hcneg
        | succ j ih =>
            rw [hrec j]
            exact mul_neg_of_neg_of_pos ih (hfactor j)
      rw [abs_of_neg hjneg]
      ring
    · refine ⟨1, by norm_num, ?_⟩
      intro j
      have hjpos : 0 < coeff a d (K + j) := by
        induction j with
        | zero => simpa using hcpos
        | succ j ih =>
            rw [hrec j]
            exact mul_pos ih (hfactor j)
      rw [abs_of_pos hjpos]
      ring
  let C : ℝ := ∑ i ∈ Finset.range K, |coeff a d i|
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have habsTail : Summable (fun j : ℕ => |coeff a d (K + j)|) := by
    apply summable_of_sum_range_le (fun j => abs_nonneg _)
    intro N
    let M : ℕ := K + N + 1
    let x : ℝ := 1 - 1 / (2 * (M : ℝ))
    have hMpos : 0 < (M : ℝ) := by
      dsimp [M]
      positivity
    have hx0 : 0 ≤ x := by
      dsimp [x]
      have hMone : (1 : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast (show 1 ≤ M by dsimp [M]; omega)
      have hden : 1 ≤ 2 * (M : ℝ) := by nlinarith
      exact sub_nonneg.mpr ((div_le_one₀ (by positivity)).2 hden)
    have hx1 : x < 1 := by
      dsimp [x]
      have : 0 < 1 / (2 * (M : ℝ)) := by positivity
      linarith
    have hxabs : |x| < 1 := by rwa [abs_of_nonneg hx0]
    have hsfull := coeff_hasSum a d x hd.ne' hxabs
    have hstail : HasSum
        (fun j : ℕ => coeff a d (j + K) * x ^ (j + K))
        (Real.rpow (1 - x) (-a / d) -
          ∑ i ∈ Finset.range K, coeff a d i * x ^ i) :=
      (hasSum_nat_add_iff' K).2 hsfull
    have habsHas : HasSum
        (fun j : ℕ => |coeff a d (K + j)| * x ^ (K + j))
        (s * (Real.rpow (1 - x) (-a / d) -
          ∑ i ∈ Finset.range K, coeff a d i * x ^ i)) := by
      convert hstail.mul_left s using 1
      ext j
      rw [hsign j]
      ring
    have hradNonneg : ∀ j : ℕ,
        0 ≤ |coeff a d (K + j)| * x ^ (K + j) := by
      intro j
      positivity
    have hpartRad :
        (∑ j ∈ Finset.range N, |coeff a d (K + j)| * x ^ (K + j)) ≤
          ∑' j : ℕ, |coeff a d (K + j)| * x ^ (K + j) :=
      habsHas.summable.sum_le_tsum (Finset.range N) (fun j _ => hradNonneg j)
    have hg0 : 0 ≤ Real.rpow (1 - x) (-a / d) :=
      Real.rpow_nonneg (by linarith : 0 ≤ 1 - x) _
    have hg1 : Real.rpow (1 - x) (-a / d) ≤ 1 := by
      apply Real.rpow_le_one
      · linarith
      · linarith
      · exact (div_pos (neg_pos.mpr ha) hd).le
    have hhead :
        |∑ i ∈ Finset.range K, coeff a d i * x ^ i| ≤ C := by
      calc
        |∑ i ∈ Finset.range K, coeff a d i * x ^ i| ≤
            ∑ i ∈ Finset.range K, |coeff a d i * x ^ i| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ C := by
          dsimp [C]
          apply Finset.sum_le_sum
          intro i hi
          rw [abs_mul, abs_pow, abs_of_nonneg hx0]
          have hxp : x ^ i ≤ 1 := pow_le_one₀ hx0 (le_of_lt hx1)
          simpa using mul_le_mul_of_nonneg_left hxp (abs_nonneg (coeff a d i))
    have htailBound :
        s * (Real.rpow (1 - x) (-a / d) -
          ∑ i ∈ Finset.range K, coeff a d i * x ^ i) ≤ 1 + C := by
      calc
        s * (Real.rpow (1 - x) (-a / d) -
            ∑ i ∈ Finset.range K, coeff a d i * x ^ i) ≤
            |s * (Real.rpow (1 - x) (-a / d) -
              ∑ i ∈ Finset.range K, coeff a d i * x ^ i)| := le_abs_self _
        _ = |Real.rpow (1 - x) (-a / d) -
              ∑ i ∈ Finset.range K, coeff a d i * x ^ i| := by
          rw [abs_mul, hsabs, one_mul]
        _ ≤ |Real.rpow (1 - x) (-a / d)| +
              |∑ i ∈ Finset.range K, coeff a d i * x ^ i| := abs_sub _ _
        _ ≤ 1 + C := add_le_add (by rw [abs_of_nonneg hg0]; exact hg1) hhead
    have hxpow : ∀ j < N, (1 / 2 : ℝ) ≤ x ^ (K + j) := by
      intro j hj
      let t : ℝ := 1 / (2 * (M : ℝ))
      have htpos : 0 < t := by dsimp [t]; positivity
      have ht_le_two : t ≤ 2 := by
        have hMone : (1 : ℝ) ≤ (M : ℝ) := by
          exact_mod_cast (show 1 ≤ M by dsimp [M]; omega)
        have hden : 1 ≤ 2 * (M : ℝ) := by nlinarith
        have ht_le_one : t ≤ 1 := by
          dsimp [t]
          exact (div_le_one₀ (by positivity)).2 hden
        linarith
      have heM : ((K + j : ℕ) : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast (show K + j ≤ M by dsimp [M]; omega)
      have hfrac : ((K + j : ℕ) : ℝ) / (2 * (M : ℝ)) ≤ 1 / 2 := by
        apply (div_le_iff₀ (by positivity)).2
        nlinarith
      have hlin : (1 / 2 : ℝ) ≤ 1 + ((K + j : ℕ) : ℝ) * (-t) := by
        dsimp [t]
        rw [mul_neg, mul_one_div]
        nlinarith
      have hbern := one_add_mul_le_pow (a := -t) (by linarith) (K + j)
      dsimp [x, t] at hbern ⊢
      exact hlin.trans hbern
    calc
      (∑ j ∈ Finset.range N, |coeff a d (K + j)|) ≤
          ∑ j ∈ Finset.range N,
            2 * (|coeff a d (K + j)| * x ^ (K + j)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjN := Finset.mem_range.mp hj
        have hmul := mul_le_mul_of_nonneg_left (hxpow j hjN)
          (abs_nonneg (coeff a d (K + j)))
        nlinarith
      _ = 2 * ∑ j ∈ Finset.range N,
            |coeff a d (K + j)| * x ^ (K + j) := by rw [Finset.mul_sum]
      _ ≤ 2 * ∑' j : ℕ, |coeff a d (K + j)| * x ^ (K + j) :=
        mul_le_mul_of_nonneg_left hpartRad (by norm_num)
      _ = 2 * (s * (Real.rpow (1 - x) (-a / d) -
            ∑ i ∈ Finset.range K, coeff a d i * x ^ i)) := by rw [habsHas.tsum_eq]
      _ ≤ 2 * (1 + C) := mul_le_mul_of_nonneg_left htailBound (by norm_num)
  have habsFull : Summable (fun n : ℕ => |coeff a d n|) :=
    (summable_nat_add_iff K).1 (by simpa [add_comm] using habsTail)
  have hfull : Summable (fun n : ℕ => coeff a d n) := Summable.of_abs habsFull
  exact (summable_nat_add_iff 1).2 hfull

theorem gap20 (a d : ℝ) (hd : 0 < d) (ha : 0 < a) :
    ¬Summable (fun n : ℕ => coeff a d (n + 1)) := by
  intro hs
  have hfull : Summable (fun n : ℕ => coeff a d n) :=
    (summable_nat_add_iff 1).1 hs
  let B : ℝ := ∑' n : ℕ, coeff a d n
  have hpow : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (a / d)))
      atTop atTop := by
    exact (tendsto_rpow_atTop (div_pos ha hd)).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  obtain ⟨n, hn⟩ := (hpow.eventually (eventually_gt_atTop B)).exists
  let x : ℝ := 1 - 1 / ((n + 1 : ℕ) : ℝ)
  have hx0 : 0 ≤ x := by
    dsimp [x]
    have hn1 : (1 : ℝ) ≤ (n + 1 : ℕ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    exact sub_nonneg.mpr ((div_le_one₀ (by positivity)).2 hn1)
  have hx1 : x < 1 := by
    dsimp [x]
    have : 0 < 1 / ((n + 1 : ℕ) : ℝ) := by positivity
    linarith
  have hxabs : |x| < 1 := by rwa [abs_of_nonneg hx0]
  have hsx := coeff_hasSum a d x hd.ne' hxabs
  have hle : ∀ k : ℕ, coeff a d k * x ^ k ≤ coeff a d k := by
    intro k
    have hc : 0 ≤ coeff a d k := (coeff_pos a d ha hd k).le
    have hxpow : x ^ k ≤ 1 := pow_le_one₀ hx0 (le_of_lt hx1)
    nlinarith [mul_le_mul_of_nonneg_left hxpow hc]
  have hbound : Real.rpow (1 - x) (-a / d) ≤ B := by
    rw [← hsx.tsum_eq]
    exact hsx.summable.tsum_le_tsum hle hfull
  have hclosed : Real.rpow (1 - x) (-a / d) =
      (((n + 1 : ℕ) : ℝ) ^ (a / d)) := by
    have hnpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    dsimp [x]
    rw [sub_sub_cancel, one_div, show -a / d = -(a / d) by ring,
      Real.rpow_neg (inv_nonneg.mpr hnpos.le),
      Real.inv_rpow hnpos.le, inv_inv]
  rw [hclosed] at hbound
  exact (not_le_of_gt hn) hbound

theorem gap21 (a d : ℝ) (hd : 0 < d) (ha : a < 0)
    (hnonterm : ∀ m : ℕ, a ≠ -(m : ℝ) * d) :
    Summable (fun n : ℕ => (-1 : ℝ) ^ (n + 1) * coeff a d (n + 1)) := by
  apply Summable.of_abs
  convert (gap19 a d hd ha hnonterm).abs using 1
  ext n
  simp [abs_mul, abs_pow]

theorem gap22 (a d : ℝ) (n : ℕ) (hd : 0 < d) (ha : d ≤ a) :
    coeff a d n / coeff a d (n + 1) =
      ((n + 1 : ℕ) : ℝ) * d / (a + (n : ℝ) * d) := by
  have haPos : 0 < a := hd.trans_le ha
  have hcPos := coeff_pos a d haPos hd n
  have hfactor : 0 < a + (n : ℝ) * d := by positivity
  rw [coeff_succ a d n hd.ne']
  field_simp [hcPos.ne', hfactor.ne', hd.ne']

theorem gap23 (a d : ℝ) (n : ℕ) (hd : 0 < d) (ha : d ≤ a) :
    ((n + 1 : ℕ) : ℝ) * d / (a + (n : ℝ) * d) ≤ 1 := by
  have hden : 0 < a + (n : ℝ) * d := by
    have haPos : 0 < a := hd.trans_le ha
    positivity
  apply (div_le_one₀ hden).2
  push_cast
  nlinarith

theorem gap24 (a d : ℝ) (n : ℕ) (hd : 0 < d) (ha : d ≤ a) :
    coeff a d n / coeff a d (n + 1) ≤ 1 := by
  rw [gap22 a d n hd ha]
  exact gap23 a d n hd ha

theorem gap25 (a d : ℝ) (n : ℕ) (hd : 0 < d) (ha : d ≤ a) :
    coeff a d n ≤ coeff a d (n + 1) := by
  have haPos : 0 < a := hd.trans_le ha
  have hcNext : 0 < coeff a d (n + 1) := coeff_pos a d haPos hd (n + 1)
  exact (div_le_one₀ hcNext).1 (gap24 a d n hd ha)

theorem gap26 (a d : ℝ) (n : ℕ) (hd : 0 < d) (ha : d ≤ a) :
    0 < coeff a d n := by
  exact coeff_pos a d (hd.trans_le ha) hd n

theorem gap27 (a d : ℝ) (n : ℕ) (hd : 0 < d) (ha : d ≤ a) :
    0 < coeff a d (n + 1) := by
  exact coeff_pos a d (hd.trans_le ha) hd (n + 1)

theorem gap28 (a d : ℝ) (hd : 0 < d) (ha : d ≤ a) :
    ¬Summable (fun n : ℕ => (-1 : ℝ) ^ (n + 1) * coeff a d (n + 1)) := by
  intro hs
  have hmono : Monotone (coeff a d) :=
    monotone_nat_of_le_succ (fun n => gap25 a d n hd ha)
  have hge : ∀ n : ℕ, 1 ≤ coeff a d (n + 1) := by
    intro n
    calc
      1 = coeff a d 0 := by simp [coeff]
      _ ≤ coeff a d (n + 1) := hmono (Nat.zero_le _)
  have habs : ∀ n : ℕ,
      1 ≤ |(-1 : ℝ) ^ (n + 1) * coeff a d (n + 1)| := by
    intro n
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos (gap27 a d n hd ha)]
    exact hge n
  have hz : Tendsto
      (fun n : ℕ => |(-1 : ℝ) ^ (n + 1) * coeff a d (n + 1)|)
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, abs_zero] using
      (continuous_abs.tendsto 0).comp hs.tendsto_atTop_zero
  have hev : ∀ᶠ n : ℕ in atTop,
      |(-1 : ℝ) ^ (n + 1) * coeff a d (n + 1)| < 1 := by
    simpa only [Set.mem_Iio] using
      hz.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨n, hn⟩ := hev.exists
  exact (not_lt_of_ge (habs n)) hn

theorem gap29 (a d : ℝ) (n : ℕ) (ha0 : 0 < a) (had : a < d) :
    Real.log (coeff a d n) =
      ∑ k ∈ Finset.range n,
        Real.log (1 - (d - a) / (((k + 1 : ℕ) : ℝ) * d)) := by
  have hd : 0 < d := ha0.trans had
  induction n with
  | zero => simp [coeff]
  | succ n ih =>
      have hcPos : 0 < coeff a d n := coeff_pos a d ha0 hd n
      have hnum : 0 < a + (n : ℝ) * d := by positivity
      have hden : 0 < (((n + 1 : ℕ) : ℝ) * d) := by positivity
      have hfacPos : 0 <
          (a + (n : ℝ) * d) / (((n + 1 : ℕ) : ℝ) * d) :=
        div_pos hnum hden
      rw [coeff_succ a d n hd.ne', mul_div_assoc]
      rw [Real.log_mul hcPos.ne' hfacPos.ne', ih, Finset.sum_range_succ]
      congr 1
      congr 1
      field_simp [hden.ne']
      push_cast
      ring

theorem gap30 (a d : ℝ) (ha0 : 0 < a) (had : a < d) :
    Tendsto
      (fun k : ℕ =>
        Real.log (1 - (d - a) / (((k + 1 : ℕ) : ℝ) * d)) /
          (-(d - a) / (((k + 1 : ℕ) : ℝ) * d)))
      atTop (𝓝 1) := by
  have hd : 0 < d := ha0.trans had
  let u : ℕ → ℝ := fun k => -(d - a) / (((k + 1 : ℕ) : ℝ) * d)
  have hu0 : Tendsto u atTop (𝓝 0) := by
    have hbase :=
      (tendsto_const_div_atTop_nhds_zero_nat (-(d - a) / d)).comp
        (tendsto_add_atTop_nat 1)
    apply hbase.congr'
    filter_upwards with k
    dsimp [u]
    field_simp [hd.ne']
  have hune : ∀ k : ℕ, u k ≠ 0 := by
    intro k
    dsimp [u]
    exact div_ne_zero (neg_ne_zero.mpr (sub_ne_zero.mpr had.ne'))
      (mul_ne_zero (by positivity) hd.ne')
  have hu : Tendsto u atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hu0, Eventually.of_forall hune⟩
  have hlog :=
    (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto_slope_zero
  have hcomp := hlog.comp hu
  have hcomp' : Tendsto
      ((fun t : ℝ => t⁻¹ • (Real.log (1 + t) - Real.log 1)) ∘ u)
      atTop (𝓝 1) := by simpa only [inv_one] using hcomp
  apply hcomp'.congr'
  filter_upwards with k
  dsimp [u]
  simp only [Real.log_one, sub_zero]
  have harg :
      1 + -(d - a) / (((k + 1 : ℕ) : ℝ) * d) =
        1 - (d - a) / (((k + 1 : ℕ) : ℝ) * d) := by ring
  rw [harg, div_eq_mul_inv]
  ring

theorem gap31 (a d : ℝ) (ha0 : 0 < a) (had : a < d) :
    Tendsto
      (fun N : ℕ =>
        ∑ k ∈ Finset.range N,
          Real.log (1 - (d - a) / (((k + 1 : ℕ) : ℝ) * d)))
      atTop atBot := by
  have hd : 0 < d := ha0.trans had
  have hc : 0 < (d - a) / d := div_pos (sub_pos.mpr had) hd
  have hterm : ∀ k : ℕ,
      Real.log (1 - (d - a) / (((k + 1 : ℕ) : ℝ) * d)) ≤
        (-((d - a) / d)) * (1 / (k + 1) : ℝ) := by
    intro k
    have hden : 0 < (((k + 1 : ℕ) : ℝ) * d) := by positivity
    have huLt : (d - a) / (((k + 1 : ℕ) : ℝ) * d) < 1 := by
      apply (div_lt_one hden).2
      have hk : (1 : ℝ) ≤ (k + 1 : ℕ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
      nlinarith
    calc
      Real.log (1 - (d - a) / (((k + 1 : ℕ) : ℝ) * d)) ≤
          (1 - (d - a) / (((k + 1 : ℕ) : ℝ) * d)) - 1 :=
        Real.log_le_sub_one_of_pos (sub_pos.mpr huLt)
      _ = (-((d - a) / d)) * (1 / (k + 1) : ℝ) := by
        field_simp [hd.ne']
        push_cast
        ring
  have hsum : ∀ N : ℕ,
      (∑ k ∈ Finset.range N,
          Real.log (1 - (d - a) / (((k + 1 : ℕ) : ℝ) * d))) ≤
        (-((d - a) / d)) *
          ∑ k ∈ Finset.range N, (1 / (k + 1) : ℝ) := by
    intro N
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => hterm k
  have hneg : -((d - a) / d) < 0 := neg_lt_zero.mpr hc
  have hright : Tendsto
      (fun N : ℕ => (-((d - a) / d)) *
        ∑ k ∈ Finset.range N, (1 / (k + 1) : ℝ)) atTop atBot :=
    Real.tendsto_sum_range_one_div_nat_succ_atTop.const_mul_atTop_of_neg hneg
  exact tendsto_atBot_mono hsum hright

theorem gap32 (a d : ℝ) (ha0 : 0 < a) (had : a < d) :
    Tendsto (fun n : ℕ => Real.log (coeff a d n)) atTop atBot := by
  apply (gap31 a d ha0 had).congr'
  exact Eventually.of_forall fun n => (gap29 a d n ha0 had).symm

theorem gap33 (a d : ℝ) (ha0 : 0 < a) (had : a < d) :
    Tendsto (fun n : ℕ => coeff a d n) atTop (𝓝 0) := by
  have hd : 0 < d := ha0.trans had
  have h := Real.tendsto_exp_atBot.comp (gap32 a d ha0 had)
  apply h.congr'
  exact Eventually.of_forall fun n => Real.exp_log (coeff_pos a d ha0 hd n)

theorem gap34 (a d : ℝ) (n : ℕ) (ha0 : 0 < a) (had : a < d) :
    coeff a d (n + 1) < coeff a d n := by
  have hd : 0 < d := ha0.trans had
  have hcPos : 0 < coeff a d n := coeff_pos a d ha0 hd n
  have hnum : 0 < a + (n : ℝ) * d := by positivity
  have hden : 0 < (((n + 1 : ℕ) : ℝ) * d) := by positivity
  have hfacLt :
      (a + (n : ℝ) * d) / (((n + 1 : ℕ) : ℝ) * d) < 1 := by
    apply (div_lt_one hden).2
    push_cast
    nlinarith
  rw [coeff_succ a d n hd.ne']
  calc
    coeff a d n * (a + (n : ℝ) * d) / (((n + 1 : ℕ) : ℝ) * d) =
        coeff a d n *
          ((a + (n : ℝ) * d) / (((n + 1 : ℕ) : ℝ) * d)) := by ring
    _ < coeff a d n * 1 := mul_lt_mul_of_pos_left hfacLt hcPos
    _ = coeff a d n := mul_one _

theorem gap35 (a d : ℝ) (n : ℕ) (ha0 : 0 < a) (had : a < d) :
    0 < coeff a d (n + 1) := by
  exact coeff_pos a d ha0 (ha0.trans had) (n + 1)

theorem gap36 (a d : ℝ) (n : ℕ) (ha0 : 0 < a) (had : a < d) :
    0 < coeff a d n := by
  exact coeff_pos a d ha0 (ha0.trans had) n

theorem gap37 (a d : ℝ) (ha0 : 0 < a) (had : a < d) :
    ProofGap.SeriesConverges
      (fun n : ℕ => (-1 : ℝ) ^ (n + 1) * coeff a d (n + 1)) := by
  have hanti : Antitone (fun n : ℕ => coeff a d (n + 1)) :=
    antitone_nat_of_succ_le fun n => (gap34 a d (n + 1) ha0 had).le
  have hzero : Tendsto (fun n : ℕ => coeff a d (n + 1)) atTop (𝓝 0) :=
    (gap33 a d ha0 had).comp (tendsto_add_atTop_nat 1)
  have hmonoNeg : Monotone (fun n : ℕ => -coeff a d (n + 1)) := hanti.neg
  have hzeroNeg : Tendsto (fun n : ℕ => -coeff a d (n + 1)) atTop (𝓝 0) := by
    simpa using hzero.neg
  obtain ⟨l, hl⟩ := hmonoNeg.tendsto_alternating_series_of_tendsto_zero hzeroNeg
  refine ⟨l, ?_⟩
  simpa [ProofGap.SeriesHasSum, HasSum, mul_neg, pow_succ] using hl

theorem gap38 (a d x : ℝ) (hd : d ≠ 0) (hx : |x| < 1) :
    (∑' n : ℕ, term a d x (n + 1)) = binomialClosedForm a d x := by
  exact gap15 a d x hd hx

end

end ProofGap.Exercise3009
