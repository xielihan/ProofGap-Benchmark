import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3601

noncomputable section

open Asymptotics Filter Topology

def integrand (x y t : ℝ) : ℝ :=
  Real.rpow (1 + x) (t ^ 2 * y)

def f (x y : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, integrand x y t

def exponent (t x y : ℝ) : ℝ :=
  t ^ 2 * y * Real.log (1 + x)

def exponentialTruncation (t x y : ℝ) : ℝ :=
  1 + exponent t x y + (1 / 2 : ℝ) * exponent t x y ^ 2

def logarithmicTruncation (t x y : ℝ) : ℝ :=
  1 + t ^ 2 * y * (x - x ^ 2 / 2)

def expandedTruncation (t x y : ℝ) : ℝ :=
  1 + t ^ 2 * x * y - t ^ 2 / 2 * x ^ 2 * y

def approximateIntegral (x y : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, expandedTruncation t x y

def finalApproximation (x y : ℝ) : ℝ :=
  1 + (1 / 3 : ℝ) * y * (x - x ^ 2 / 2)

def AgreesThroughDegreeThree
    (g h : ℝ → ℝ → ℝ) : Prop :=
  Asymptotics.IsLittleO (nhds (0, 0))
    (fun p : ℝ × ℝ => g p.1 p.2 - h p.1 p.2)
    (fun p : ℝ × ℝ => ‖p‖ ^ 3)

private theorem exponential_remainder :
    (fun u : ℝ =>
      Real.exp u - (1 + u + (1 / 2 : ℝ) * u ^ 2))
      =o[𝓝 0] (fun u : ℝ => u ^ 2) := by
  have h := taylor_isLittleO_univ (f := Real.exp) (x₀ := (0 : ℝ))
    (n := 2) Real.contDiff_exp
  convert h using 1
  · funext u
    simp [taylor_within_apply, iteratedDerivWithin_univ,
      iteratedDeriv_eq_iterate, Real.iter_deriv_exp]
    ring
    simp
  · funext u
    ring

private theorem log_one_plus_isBigO :
    (fun x : ℝ => Real.log (1 + x))
      =O[𝓝 0] (fun x : ℝ => x) := by
  have hd : HasDerivAt (fun x : ℝ => Real.log (1 + x)) 1 0 := by
    convert
      ((hasDerivAt_const (0 : ℝ) 1).add (hasDerivAt_id 0)).log
        (by norm_num) using 1 <;>
      norm_num
  simpa using hd.isBigO_sub

private theorem log_remainder_isBigO :
    (fun x : ℝ => Real.log (1 + x) - (x - x ^ 2 / 2))
      =O[𝓝 0] (fun x : ℝ => x ^ 3) := by
  rw [isBigO_iff]
  refine ⟨2, ?_⟩
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ)
    (show 0 < (1 / 2 : ℝ) by norm_num)] with x hx
  rw [Metric.mem_ball, Real.dist_eq] at hx
  have hxa : |x| < 1 / 2 := by simpa using hx
  have hlt : |-x| < 1 := by
    rw [abs_neg]
    linarith
  have h := Real.abs_log_sub_add_sum_range_le hlt 2
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, pow_two] at h
  have hden : 1 / (1 - |x|) ≤ 2 := by
    rw [div_le_iff₀]
    · linarith
    · linarith [abs_nonneg x]
  have hp : 0 ≤ |x| ^ 3 := pow_nonneg (abs_nonneg x) 3
  have hb :
      |Real.log (1 + x) - (x - x ^ 2 / 2)| ≤ 2 * |x| ^ 3 := by
    calc
      |Real.log (1 + x) - (x - x ^ 2 / 2)| =
          |(-x + (-x) ^ 2 / 2) + Real.log (1 - -x)| := by
        congr 1
        ring
      _ ≤ |x| ^ 3 / (1 - |x|) := by simpa [pow_two] using h
      _ = |x| ^ 3 * (1 / (1 - |x|)) := by ring
      _ ≤ |x| ^ 3 * 2 := mul_le_mul_of_nonneg_left hden hp
      _ = 2 * |x| ^ 3 := by ring
  simpa only [Real.norm_eq_abs, norm_pow] using hb

private theorem log_remainder_bound (x : ℝ) (hx : |x| < 1 / 2) :
    |Real.log (1 + x) - (x - x ^ 2 / 2)| ≤ 2 * |x| ^ 3 := by
  have hlt : |-x| < 1 := by
    rw [abs_neg]
    linarith
  have h := Real.abs_log_sub_add_sum_range_le hlt 2
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, pow_two] at h
  have hden : 1 / (1 - |x|) ≤ 2 := by
    rw [div_le_iff₀]
    · linarith
    · linarith [abs_nonneg x]
  have hp : 0 ≤ |x| ^ 3 := pow_nonneg (abs_nonneg x) 3
  calc
    |Real.log (1 + x) - (x - x ^ 2 / 2)| =
        |(-x + (-x) ^ 2 / 2) + Real.log (1 - -x)| := by
      congr 1
      ring
    _ ≤ |x| ^ 3 / (1 - |x|) := by simpa [pow_two] using h
    _ = |x| ^ 3 * (1 / (1 - |x|)) := by ring
    _ ≤ |x| ^ 3 * 2 := mul_le_mul_of_nonneg_left hden hp
    _ = 2 * |x| ^ 3 := by ring

private theorem exponent_isBigO (t : ℝ) :
    (fun p : ℝ × ℝ => exponent t p.1 p.2)
      =O[𝓝 (0, 0)] (fun p : ℝ × ℝ => ‖p‖ ^ 2) := by
  have hx :
      (fun p : ℝ × ℝ => p.1)
        =O[𝓝 (0, 0)] (fun p : ℝ × ℝ => ‖p‖) :=
    isBigO_fst_prod'.norm_right
  have hy :
      (fun p : ℝ × ℝ => p.2)
        =O[𝓝 (0, 0)] (fun p : ℝ × ℝ => ‖p‖) :=
    isBigO_snd_prod'.norm_right
  have hlog :
      (fun p : ℝ × ℝ => Real.log (1 + p.1))
        =O[𝓝 (0, 0)] (fun p : ℝ × ℝ => ‖p‖) :=
    (log_one_plus_isBigO.comp_tendsto
      (continuous_fst.tendsto (0, 0))).trans hx
  unfold exponent
  convert (hy.mul hlog).const_mul_left (t ^ 2) using 1 <;> ring

private theorem exponent_tendsto (t : ℝ) :
    Tendsto (fun p : ℝ × ℝ => exponent t p.1 p.2)
      (𝓝 (0, 0)) (𝓝 0) := by
  have hc :
      ContinuousAt (fun p : ℝ × ℝ =>
        t ^ 2 * p.2 * Real.log (1 + p.1)) (0, 0) :=
    (continuousAt_const.mul continuousAt_snd).mul (by
      have hinner :
          ContinuousAt (fun p : ℝ × ℝ => 1 + p.1) (0, 0) :=
        continuousAt_const.add continuousAt_fst
      exact hinner.log (by norm_num))
  simpa [exponent] using hc.tendsto

theorem gap1 :
    ∀ x t y : ℝ, -1 < x →
      integrand x y t = Real.exp (exponent t x y) := by
  intro x t y hx
  unfold integrand exponent
  calc
    Real.rpow (1 + x) (t ^ 2 * y) =
        Real.exp (Real.log (1 + x) * (t ^ 2 * y)) :=
      Real.rpow_def_of_pos (by linarith) _
    _ = Real.exp (t ^ 2 * y * Real.log (1 + x)) := by
      congr 1
      ring

theorem gap2 :
    ∀ t : ℝ,
      AgreesThroughDegreeThree
        (fun x y => Real.exp (exponent t x y))
        (exponentialTruncation t) := by
  intro t
  have hpow :
      (fun p : ℝ × ℝ => exponent t p.1 p.2 ^ 2)
        =O[𝓝 (0, 0)] (fun p : ℝ × ℝ => ‖p‖ ^ 4) := by
    convert (exponent_isBigO t).pow 2 using 1 <;> ring
  have hrem :
      (fun p : ℝ × ℝ =>
        Real.exp (exponent t p.1 p.2) -
          (1 + exponent t p.1 p.2 +
            (1 / 2 : ℝ) * exponent t p.1 p.2 ^ 2))
        =o[𝓝 (0, 0)] (fun p : ℝ × ℝ => ‖p‖ ^ 3) :=
    ((exponential_remainder.comp_tendsto
      (exponent_tendsto t)).trans_isBigO hpow).trans
        (isLittleO_norm_pow_norm_pow (show 3 < 4 by norm_num))
  unfold AgreesThroughDegreeThree exponentialTruncation
  exact hrem

theorem gap3 :
    ∀ t : ℝ,
      AgreesThroughDegreeThree
        (exponentialTruncation t)
        (logarithmicTruncation t) := by
  intro t
  have hx :
      (fun p : ℝ × ℝ => p.1)
        =O[𝓝 (0, 0)] (fun p : ℝ × ℝ => ‖p‖) :=
    isBigO_fst_prod'.norm_right
  have hy :
      (fun p : ℝ × ℝ => p.2)
        =O[𝓝 (0, 0)] (fun p : ℝ × ℝ => ‖p‖) :=
    isBigO_snd_prod'.norm_right
  have hlogRem :
      (fun p : ℝ × ℝ =>
        Real.log (1 + p.1) - (p.1 - p.1 ^ 2 / 2))
        =O[𝓝 (0, 0)] (fun p : ℝ × ℝ => ‖p‖ ^ 3) :=
    (log_remainder_isBigO.comp_tendsto
      (continuous_fst.tendsto (0, 0))).trans (hx.pow 3)
  have hfirst :
      (fun p : ℝ × ℝ =>
        t ^ 2 * p.2 *
          (Real.log (1 + p.1) - (p.1 - p.1 ^ 2 / 2)))
        =O[𝓝 (0, 0)] (fun p : ℝ × ℝ => ‖p‖ ^ 4) := by
    convert (hy.mul hlogRem).const_mul_left (t ^ 2) using 1 <;> ring
  have hsecond :
      (fun p : ℝ × ℝ => (1 / 2 : ℝ) * exponent t p.1 p.2 ^ 2)
        =O[𝓝 (0, 0)] (fun p : ℝ × ℝ => ‖p‖ ^ 4) := by
    convert ((exponent_isBigO t).pow 2).const_mul_left (1 / 2 : ℝ) using 1 <;>
      ring
  have hsmall :
      (fun p : ℝ × ℝ =>
        t ^ 2 * p.2 *
            (Real.log (1 + p.1) - (p.1 - p.1 ^ 2 / 2)) +
          (1 / 2 : ℝ) * exponent t p.1 p.2 ^ 2)
        =o[𝓝 (0, 0)] (fun p : ℝ × ℝ => ‖p‖ ^ 3) :=
    (hfirst.add hsecond).trans_isLittleO
      (isLittleO_norm_pow_norm_pow (show 3 < 4 by norm_num))
  unfold AgreesThroughDegreeThree exponentialTruncation logarithmicTruncation
  convert hsmall using 1
  funext p
  unfold exponent
  ring

theorem gap4 :
    ∀ t : ℝ,
      AgreesThroughDegreeThree
        (fun x y => integrand x y t)
        (logarithmicTruncation t) := by
  intro t
  have h2 := gap2 t
  have h3 := gap3 t
  unfold AgreesThroughDegreeThree at h2 h3 ⊢
  have hsum := h2.add h3
  apply hsum.congr'
  · filter_upwards [Metric.ball_mem_nhds ((0, 0) : ℝ × ℝ)
      (show 0 < (1 : ℝ) by norm_num)] with p hp
    rw [Metric.mem_ball, dist_eq_norm] at hp
    change ‖p - (0 : ℝ × ℝ)‖ < 1 at hp
    have hnorm : ‖p‖ < 1 := by simpa using hp
    rw [Prod.norm_def] at hnorm
    have hx : -1 < p.1 := by
      have habs : |p.1| < 1 :=
        lt_of_le_of_lt (le_max_left _ _) hnorm
      exact (abs_lt.mp habs).1
    rw [gap1 p.1 t p.2 hx]
    ring
  · exact Filter.Eventually.of_forall (fun _ => rfl)

theorem gap5 :
    ∀ t x y : ℝ,
      logarithmicTruncation t x y = expandedTruncation t x y := by
  intro t x y
  unfold logarithmicTruncation expandedTruncation
  ring

theorem gap6 :
    AgreesThroughDegreeThree f approximateIntegral := by
  rw [AgreesThroughDegreeThree, isLittleO_iff]
  intro c hc
  let δ : ℝ := min (1 / 4 : ℝ) (c / 6)
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hc (by norm_num))
  filter_upwards [Metric.ball_mem_nhds ((0, 0) : ℝ × ℝ) hδ] with p hp
  rw [Metric.mem_ball, dist_eq_norm] at hp
  change ‖p - (0 : ℝ × ℝ)‖ < δ at hp
  have hnorm : ‖p‖ < δ := by simpa using hp
  have hrSmall : ‖p‖ < 1 / 4 :=
    lt_of_lt_of_le hnorm (min_le_left _ _)
  have hrc : 6 * ‖p‖ < c := by
    have := lt_of_lt_of_le hnorm (min_le_right _ _)
    linarith
  have hxle : |p.1| ≤ ‖p‖ := by
    simpa [Prod.norm_def, Real.norm_eq_abs] using
      (le_max_left ‖p.1‖ ‖p.2‖)
  have hyle : |p.2| ≤ ‖p‖ := by
    simpa [Prod.norm_def, Real.norm_eq_abs] using
      (le_max_right ‖p.1‖ ‖p.2‖)
  have hxSmall : |p.1| < 1 / 2 :=
    lt_of_le_of_lt hxle (lt_trans hrSmall (by norm_num))
  have hxPos : -1 < p.1 := by
    have := (abs_lt.mp hxSmall).1
    linarith
  have hlogRem :=
    log_remainder_bound p.1 hxSmall
  have hpoly :
      |p.1 - p.1 ^ 2 / 2| ≤ |p.1| + |p.1| ^ 2 / 2 := by
    calc
      |p.1 - p.1 ^ 2 / 2| ≤ |p.1| + |p.1 ^ 2 / 2| :=
        abs_sub _ _
      _ = |p.1| + |p.1| ^ 2 / 2 := by
        rw [abs_div, abs_pow]
        norm_num
  have ha2 : |p.1| ^ 2 ≤ |p.1| / 4 := by
    have hnonneg : 0 ≤ |p.1| := abs_nonneg _
    have hquarter : |p.1| ≤ 1 / 4 := le_trans hxle hrSmall.le
    nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hquarter)]
  have ha3 : |p.1| ^ 3 ≤ |p.1| ^ 2 / 4 := by
    have hquarter : |p.1| ≤ 1 / 4 := le_trans hxle hrSmall.le
    have hsq : 0 ≤ |p.1| ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg hsq (sub_nonneg.mpr hquarter)]
  have hlog : |Real.log (1 + p.1)| ≤ 2 * |p.1| := by
    calc
      |Real.log (1 + p.1)| =
          |(p.1 - p.1 ^ 2 / 2) +
            (Real.log (1 + p.1) - (p.1 - p.1 ^ 2 / 2))| := by
        congr 1
        ring
      _ ≤ |p.1 - p.1 ^ 2 / 2| +
          |Real.log (1 + p.1) - (p.1 - p.1 ^ 2 / 2)| :=
        abs_add_le _ _
      _ ≤ (|p.1| + |p.1| ^ 2 / 2) + 2 * |p.1| ^ 3 :=
        add_le_add hpoly hlogRem
      _ ≤ 2 * |p.1| := by nlinarith
  have hInt :
      IntervalIntegrable (fun t : ℝ => integrand p.1 p.2 t)
        MeasureTheory.volume 0 1 := by
    have hcExp :
        Continuous (fun t : ℝ =>
          Real.exp (exponent t p.1 p.2)) :=
      Real.continuous_exp.comp
        (((continuous_id.pow 2).mul continuous_const).mul continuous_const)
    have heq :
        (fun t : ℝ => integrand p.1 p.2 t) =
          fun t => Real.exp (exponent t p.1 p.2) := by
      funext t
      exact gap1 p.1 t p.2 hxPos
    rw [heq]
    exact hcExp.intervalIntegrable 0 1
  have hApprox :
      IntervalIntegrable (fun t : ℝ => expandedTruncation t p.1 p.2)
        MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold expandedTruncation
    fun_prop
  rw [f, approximateIntegral,
    ← intervalIntegral.integral_sub hInt hApprox]
  have hpoint :
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ‖integrand p.1 p.2 t - expandedTruncation t p.1 p.2‖
          ≤ c * ‖p‖ ^ 3 := by
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at ht
      exact ⟨ht.1.le, ht.2⟩
    have htAbs : |t| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [htIcc.1, htIcc.2]
    have htSq : |t| ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg (abs_nonneg t)
        (sub_nonneg.mpr htAbs)]
    have heBound :
        |exponent t p.1 p.2| ≤ 2 * ‖p‖ ^ 2 := by
      rw [exponent, abs_mul, abs_mul, abs_pow]
      calc
        |t| ^ 2 * |p.2| * |Real.log (1 + p.1)| ≤
            1 * ‖p‖ * (2 * |p.1|) := by gcongr
        _ ≤ 1 * ‖p‖ * (2 * ‖p‖) := by gcongr
        _ = 2 * ‖p‖ ^ 2 := by ring
    have heOne : ‖exponent t p.1 p.2‖ ≤ 1 := by
      rw [Real.norm_eq_abs]
      calc
        |exponent t p.1 p.2| ≤ 2 * ‖p‖ ^ 2 := heBound
        _ ≤ 1 := by
          have hr : 0 ≤ ‖p‖ := norm_nonneg _
          have hrs : ‖p‖ ≤ 1 / 4 := hrSmall.le
          nlinarith [mul_nonneg hr (sub_nonneg.mpr hrs)]
    have hExp :
        |Real.exp (exponent t p.1 p.2) - 1 -
            exponent t p.1 p.2| ≤ 4 * ‖p‖ ^ 4 := by
      have hb := Real.norm_exp_sub_one_sub_id_le heOne
      rw [Real.norm_eq_abs, Real.norm_eq_abs] at hb
      calc
        |Real.exp (exponent t p.1 p.2) - 1 -
            exponent t p.1 p.2| ≤ |exponent t p.1 p.2| ^ 2 := hb
        _ ≤ (2 * ‖p‖ ^ 2) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) heBound 2
        _ = 4 * ‖p‖ ^ 4 := by ring
    have hLogTerm :
        |t ^ 2 * p.2 *
          (Real.log (1 + p.1) - (p.1 - p.1 ^ 2 / 2))|
            ≤ 2 * ‖p‖ ^ 4 := by
      rw [abs_mul, abs_mul, abs_pow]
      calc
        |t| ^ 2 * |p.2| *
            |Real.log (1 + p.1) - (p.1 - p.1 ^ 2 / 2)| ≤
            1 * ‖p‖ * (2 * |p.1| ^ 3) := by gcongr
        _ ≤ 1 * ‖p‖ * (2 * ‖p‖ ^ 3) := by
          gcongr
        _ = 2 * ‖p‖ ^ 4 := by ring
    have herr :
        integrand p.1 p.2 t - expandedTruncation t p.1 p.2 =
          (Real.exp (exponent t p.1 p.2) - 1 -
            exponent t p.1 p.2) +
          t ^ 2 * p.2 *
            (Real.log (1 + p.1) - (p.1 - p.1 ^ 2 / 2)) := by
      rw [gap1 p.1 t p.2 hxPos]
      unfold exponent expandedTruncation
      ring
    rw [herr, Real.norm_eq_abs]
    calc
      |(Real.exp (exponent t p.1 p.2) - 1 -
          exponent t p.1 p.2) +
          t ^ 2 * p.2 *
            (Real.log (1 + p.1) - (p.1 - p.1 ^ 2 / 2))| ≤
          |Real.exp (exponent t p.1 p.2) - 1 -
            exponent t p.1 p.2| +
          |t ^ 2 * p.2 *
            (Real.log (1 + p.1) - (p.1 - p.1 ^ 2 / 2))| :=
        abs_add_le _ _
      _ ≤ 4 * ‖p‖ ^ 4 + 2 * ‖p‖ ^ 4 :=
        add_le_add hExp hLogTerm
      _ = (6 * ‖p‖) * ‖p‖ ^ 3 := by ring
      _ ≤ c * ‖p‖ ^ 3 :=
        mul_le_mul_of_nonneg_right hrc.le (pow_nonneg (norm_nonneg _) 3)
  have hb :=
    intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  simpa using hb

theorem gap7 :
    ∀ x y : ℝ, approximateIntegral x y = finalApproximation x y := by
  intro x y
  have hpow :
      (∫ t in (0 : ℝ)..1, t ^ 2) = (1 / 3 : ℝ) := by
    have hderiv :
        ∀ t ∈ Set.uIcc (0 : ℝ) 1,
          HasDerivAt (fun s : ℝ => s ^ 3 / 3) (t ^ 2) t := by
      intro t ht
      convert (hasDerivAt_pow 3 t).div_const 3 using 1 <;> ring
    have hint :
        IntervalIntegrable (fun t : ℝ => t ^ 2)
          MeasureTheory.volume 0 1 :=
      (continuous_id.pow 2).intervalIntegrable 0 1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    norm_num
  have heq :
      (fun t : ℝ => expandedTruncation t x y) =
        fun t => 1 + t ^ 2 * (x * y - x ^ 2 * y / 2) := by
    funext t
    unfold expandedTruncation
    ring
  unfold approximateIntegral finalApproximation
  change (∫ t in (0 : ℝ)..1, expandedTruncation t x y) =
    1 + (1 / 3 : ℝ) * y * (x - x ^ 2 / 2)
  rw [heq]
  have hsqInt :
      IntervalIntegrable
        (fun t : ℝ => t ^ 2 * (x * y - x ^ 2 * y / 2))
        MeasureTheory.volume 0 1 :=
    ((continuous_id.pow 2).mul continuous_const).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add intervalIntegrable_const hsqInt]
  rw [intervalIntegral.integral_const,
    intervalIntegral.integral_mul_const, hpow]
  norm_num
  ring

theorem gap8 :
    AgreesThroughDegreeThree f finalApproximation := by
  have h := gap6
  unfold AgreesThroughDegreeThree at h ⊢
  apply h.congr'
  · exact Filter.Eventually.of_forall (fun p => by
      change f p.1 p.2 - approximateIntegral p.1 p.2 =
        f p.1 p.2 - finalApproximation p.1 p.2
      rw [gap7 p.1 p.2])
  · exact Filter.Eventually.of_forall (fun _ => rfl)

end

end ProofGap.Exercise3601
