import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise3718_1

noncomputable section

open Filter Topology
open scoped Interval

private def radial (x : ℝ) : ℝ :=
  Real.sqrt (1 - x ^ 2)

def integrand (α x : ℝ) : ℝ :=
  Real.exp (α * Real.sqrt (1 - x ^ 2))

def integralFunction (α : ℝ) : ℝ :=
  ∫ x in Real.sin α..Real.cos α, integrand α x

def leibnizDerivative (α : ℝ) : ℝ :=
  -Real.sin α * Real.exp (α * |Real.sin α|) -
      Real.cos α * Real.exp (α * |Real.cos α|) +
    ∫ x in Real.sin α..Real.cos α,
      Real.sqrt (1 - x ^ 2) * Real.exp (α * Real.sqrt (1 - x ^ 2))

private lemma radial_nonneg (x : ℝ) : 0 ≤ radial x :=
  Real.sqrt_nonneg _

private lemma radial_le_one (x : ℝ) : radial x ≤ 1 := by
  unfold radial
  rw [Real.sqrt_le_one]
  nlinarith [sq_nonneg x]

private lemma parameter_deriv (a x : ℝ) :
    HasDerivAt (fun t => integrand t x)
      (radial x * integrand a x) a := by
  unfold integrand radial
  simpa [Function.comp_def, mul_comm] using
    (Real.hasDerivAt_exp (a * radial x)).comp a
      ((hasDerivAt_id a).mul_const (radial x))

private lemma parameter_deriv_bound (a z x : ℝ)
    (hz : z ∈ Set.Icc (a - 1) (a + 1)) :
    ‖radial x * integrand z x‖ ≤ Real.exp (|a| + 1) := by
  have hc0 := radial_nonneg x
  have hc1 := radial_le_one x
  have hzle : z ≤ |a| + 1 := by
    linarith [hz.2, le_abs_self a]
  have hzc : z * radial x ≤ |a| + 1 := by
    by_cases hz0 : 0 ≤ z
    · have hm := mul_le_mul_of_nonneg_left hc1 hz0
      nlinarith
    · have hm : z * radial x ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hz0) hc0
      exact hm.trans (by positivity)
  unfold integrand radial at *
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hc0,
    abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul hc1 (Real.exp_le_exp.mpr hzc)
    (Real.exp_nonneg _) zero_le_one) |>.trans_eq (one_mul _)

private lemma parameter_lipschitz (a t x : ℝ)
    (ht : t ∈ Set.Icc (a - 1) (a + 1)) :
    ‖integrand t x - integrand a x‖ ≤
      Real.exp (|a| + 1) * ‖t - a‖ := by
  exact Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.Icc (a - 1) (a + 1))
    (f := fun z => integrand z x)
    (fun z hz => (parameter_deriv z x).differentiableAt)
    (fun z hz => by
      rw [(parameter_deriv z x).deriv]
      exact parameter_deriv_bound a z x hz)
    (convex_Icc _ _)
    (by constructor <;> linarith)
    ht

private lemma correction_remainder_hasDerivAt
    (a : ℝ) (b : ℝ → ℝ)
    (hb : ∀ t, |b t - b a| ≤ |t - a|) :
    HasDerivAt
      (fun t =>
        ∫ x in b a..b t, integrand t x - integrand a x) 0 a := by
  let R : ℝ → ℝ :=
    fun t => ∫ x in b a..b t, integrand t x - integrand a x
  change HasDerivAt R 0 a
  rw [hasDerivAt_iff_tendsto]
  have hupper :
      Tendsto (fun t : ℝ => Real.exp (|a| + 1) * |t - a|)
        (𝓝 a) (𝓝 0) := by
    have hc : ContinuousAt
        (fun t : ℝ => Real.exp (|a| + 1) * |t - a|) a := by
      fun_prop
    change Tendsto (fun t : ℝ => Real.exp (|a| + 1) * |t - a|)
      (𝓝 a) (𝓝 (Real.exp (|a| + 1) * |a - a|)) at hc
    simpa using hc
  have hRa : R a = 0 := by
    simp [R]
  refine squeeze_zero'
    (Eventually.of_forall fun t =>
      mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
    ?_ hupper
  filter_upwards [Metric.ball_mem_nhds a zero_lt_one] with t ht
  rw [Metric.mem_ball, Real.dist_eq] at ht
  have htIcc : t ∈ Set.Icc (a - 1) (a + 1) := by
    constructor <;> linarith [le_abs_self (t - a), neg_le_abs (t - a)]
  have hR :
      ‖R t‖ ≤
        (Real.exp (|a| + 1) * ‖t - a‖) * |b t - b a| := by
    unfold R
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    exact parameter_lipschitz a t x htIcc
  have hba := hb t
  rw [hRa]
  simp only [sub_zero, smul_zero]
  by_cases hta : t = a
  · subst t
    simp
  · have habs : 0 < |t - a| := abs_pos.mpr (sub_ne_zero.mpr hta)
    rw [Real.norm_eq_abs] at hR ⊢
    calc
      |t - a|⁻¹ *
          ‖∫ x in b a..b t, integrand t x - integrand a x‖ ≤
          |t - a|⁻¹ *
            ((Real.exp (|a| + 1) * |t - a|) * |b t - b a|) :=
        mul_le_mul_of_nonneg_left hR (inv_nonneg.mpr (abs_nonneg _))
      _ ≤ |t - a|⁻¹ *
            ((Real.exp (|a| + 1) * |t - a|) * |t - a|) := by
        gcongr
      _ = Real.exp (|a| + 1) * |t - a| := by
        field_simp [habs.ne']

private lemma upper_correction (a : ℝ) :
    HasDerivAt
      (fun t =>
        ∫ x in Real.cos a..Real.cos t, integrand t x)
      (-Real.sin a * integrand a (Real.cos a)) a := by
  let base : ℝ → ℝ :=
    fun t => ∫ x in Real.cos a..Real.cos t, integrand a x
  let rem : ℝ → ℝ :=
    fun t =>
      ∫ x in Real.cos a..Real.cos t, integrand t x - integrand a x
  have hcont : Continuous (integrand a) := by
    unfold integrand
    fun_prop
  have hbase :
      HasDerivAt base (-Real.sin a * integrand a (Real.cos a)) a := by
    dsimp [base]
    convert
      ((hcont.integral_hasStrictDerivAt
        (Real.cos a) (Real.cos a)).hasDerivAt.comp
          a (Real.hasDerivAt_cos a)) using 1 <;> ring
  have hrem : HasDerivAt rem 0 a := by
    dsimp [rem]
    exact correction_remainder_hasDerivAt a Real.cos
      (fun t => Real.abs_cos_sub_cos_le t a)
  have heq :
      (fun t => ∫ x in Real.cos a..Real.cos t, integrand t x) =
        fun t => base t + rem t := by
    funext t
    dsimp [base, rem]
    rw [← intervalIntegral.integral_add
      (hcont.intervalIntegrable _ _)
      ((by
        unfold integrand
        fun_prop :
          Continuous (fun x => integrand t x - integrand a x)
        ).intervalIntegrable _ _)]
    congr 1
    funext x
    ring
  rw [heq]
  convert hbase.add hrem using 1 <;> ring

private lemma lower_correction (a : ℝ) :
    HasDerivAt
      (fun t =>
        ∫ x in Real.sin a..Real.sin t, integrand t x)
      (Real.cos a * integrand a (Real.sin a)) a := by
  let base : ℝ → ℝ :=
    fun t => ∫ x in Real.sin a..Real.sin t, integrand a x
  let rem : ℝ → ℝ :=
    fun t =>
      ∫ x in Real.sin a..Real.sin t, integrand t x - integrand a x
  have hcont : Continuous (integrand a) := by
    unfold integrand
    fun_prop
  have hbase :
      HasDerivAt base (Real.cos a * integrand a (Real.sin a)) a := by
    dsimp [base]
    convert
      ((hcont.integral_hasStrictDerivAt
        (Real.sin a) (Real.sin a)).hasDerivAt.comp
          a (Real.hasDerivAt_sin a)) using 1 <;> ring
  have hrem : HasDerivAt rem 0 a := by
    dsimp [rem]
    exact correction_remainder_hasDerivAt a Real.sin
      (fun t => Real.abs_sin_sub_sin_le t a)
  have heq :
      (fun t => ∫ x in Real.sin a..Real.sin t, integrand t x) =
        fun t => base t + rem t := by
    funext t
    dsimp [base, rem]
    rw [← intervalIntegral.integral_add
      (hcont.intervalIntegrable _ _)
      ((by
        unfold integrand
        fun_prop :
          Continuous (fun x => integrand t x - integrand a x)
        ).intervalIntegrable _ _)]
    congr 1
    funext x
    ring
  rw [heq]
  convert hbase.add hrem using 1 <;> ring

private lemma moving_from_fixed (a : ℝ)
    (hfixed :
      HasDerivAt
        (fun t =>
          ∫ x in Real.sin a..Real.cos a, integrand t x)
        (∫ x in Real.sin a..Real.cos a,
          radial x * integrand a x) a) :
    HasDerivAt
      (fun t =>
        ∫ x in Real.sin t..Real.cos t, integrand t x)
      (-Real.sin a * integrand a (Real.cos a) -
        Real.cos a * integrand a (Real.sin a) +
        ∫ x in Real.sin a..Real.cos a,
          radial x * integrand a x) a := by
  have hu := upper_correction a
  have hl := lower_correction a
  have hsum := (hfixed.add hu).sub hl
  have heq :
      (fun t => ∫ x in Real.sin t..Real.cos t, integrand t x) =
        fun t =>
          (∫ x in Real.sin a..Real.cos a, integrand t x) +
            (∫ x in Real.cos a..Real.cos t, integrand t x) -
              ∫ x in Real.sin a..Real.sin t, integrand t x := by
    funext t
    have hcont : Continuous (integrand t) := by
      unfold integrand
      fun_prop
    calc
      (∫ x in Real.sin t..Real.cos t, integrand t x) =
          (∫ x in Real.sin t..Real.cos a, integrand t x) +
            ∫ x in Real.cos a..Real.cos t, integrand t x :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hcont.intervalIntegrable _ _)
          (hcont.intervalIntegrable _ _)).symm
      _ = ((∫ x in Real.sin t..Real.sin a, integrand t x) +
            ∫ x in Real.sin a..Real.cos a, integrand t x) +
            ∫ x in Real.cos a..Real.cos t, integrand t x := by
        rw [← intervalIntegral.integral_add_adjacent_intervals
          (hcont.intervalIntegrable _ _)
          (hcont.intervalIntegrable _ _)]
      _ = (∫ x in Real.sin a..Real.cos a, integrand t x) +
            (∫ x in Real.cos a..Real.cos t, integrand t x) -
              ∫ x in Real.sin a..Real.sin t, integrand t x := by
        rw [intervalIntegral.integral_symm
          (f := integrand t) (a := Real.sin a) (b := Real.sin t)]
        ring
  rw [heq]
  convert hsum using 1 <;> ring

theorem gap1 (α : ℝ) :
    deriv integralFunction α = leibnizDerivative α := by
  have hsqrt_cos :
      Real.sqrt (1 - Real.cos α ^ 2) = |Real.sin α| := by
    have htrig := Real.sin_sq_add_cos_sq α
    rw [show 1 - Real.cos α ^ 2 = Real.sin α ^ 2 by linarith]
    exact Real.sqrt_sq_eq_abs _
  have hsqrt_sin :
      Real.sqrt (1 - Real.sin α ^ 2) = |Real.cos α| := by
    have htrig := Real.sin_sq_add_cos_sq α
    rw [show 1 - Real.sin α ^ 2 = Real.cos α ^ 2 by linarith]
    exact Real.sqrt_sq_eq_abs _
  have hparam (a x : ℝ) :
      HasDerivAt
        (fun t : ℝ => Real.exp (t * Real.sqrt (1 - x ^ 2)))
        (Real.sqrt (1 - x ^ 2) *
          Real.exp (a * Real.sqrt (1 - x ^ 2))) a := by
    simpa [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_exp (a * Real.sqrt (1 - x ^ 2))).comp a
        ((hasDerivAt_id a).mul_const (Real.sqrt (1 - x ^ 2)))
  have hcontinuous :
      Continuous (fun p : ℝ × ℝ =>
        Real.exp (p.1 * Real.sqrt (1 - p.2 ^ 2))) := by
    fun_prop
  have hcontinuous' :
      Continuous (fun p : ℝ × ℝ =>
        Real.sqrt (1 - p.2 ^ 2) *
          Real.exp (p.1 * Real.sqrt (1 - p.2 ^ 2))) := by
    fun_prop
  have hfixed (a b : ℝ) :
      HasDerivAt
        (fun t : ℝ =>
          ∫ x in a..b, Real.exp (t * Real.sqrt (1 - x ^ 2)))
        (∫ x in a..b,
          Real.sqrt (1 - x ^ 2) *
            Real.exp (α * Real.sqrt (1 - x ^ 2))) α := by
    let s : Set ℝ := Set.Icc (α - 1) (α + 1)
    let bound : ℝ → ℝ := fun _ => Real.exp (|α| + 1)
    have hs : s ∈ 𝓝 α := by
      apply Icc_mem_nhds
      · dsimp [s]
        linarith
      · dsimp [s]
        linarith
    have hbound (x t : ℝ) (hx : x ∈ s) :
        ‖Real.sqrt (1 - t ^ 2) *
            Real.exp (x * Real.sqrt (1 - t ^ 2))‖ ≤ bound t := by
      have hc0 : 0 ≤ Real.sqrt (1 - t ^ 2) := Real.sqrt_nonneg _
      have hc1 : Real.sqrt (1 - t ^ 2) ≤ 1 := by
        rw [Real.sqrt_le_one]
        nlinarith [sq_nonneg t]
      have hxle : x ≤ |α| + 1 := by
        have hx' : x ≤ α + 1 := hx.2
        linarith [le_abs_self α]
      have hxc : x * Real.sqrt (1 - t ^ 2) ≤ |α| + 1 := by
        by_cases hx0 : 0 ≤ x
        · have hmul := mul_le_mul_of_nonneg_left hc1 hx0
          nlinarith
        · have hmul : x * Real.sqrt (1 - t ^ 2) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hx0) hc0
          have : 0 ≤ |α| + 1 := by positivity
          linarith
      dsimp [bound]
      rw [abs_mul, abs_of_nonneg hc0,
        abs_of_pos (Real.exp_pos _)]
      calc
        Real.sqrt (1 - t ^ 2) *
            Real.exp (x * Real.sqrt (1 - t ^ 2)) ≤
            1 * Real.exp (|α| + 1) := by
              exact mul_le_mul hc1 (Real.exp_le_exp.mpr hxc)
                (Real.exp_nonneg _) zero_le_one
        _ = Real.exp (|α| + 1) := one_mul _
    refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun x t : ℝ =>
        Real.exp (x * Real.sqrt (1 - t ^ 2)))
      (F' := fun x t : ℝ =>
        Real.sqrt (1 - t ^ 2) *
          Real.exp (x * Real.sqrt (1 - t ^ 2)))
      (x₀ := α) (a := a) (b := b)
      (μ := MeasureTheory.volume)
      (s := s) (bound := bound) hs ?_ ?_ ?_ ?_ ?_ ?_).2
    · filter_upwards [] with x
      exact (by fun_prop : Continuous
        (fun t : ℝ => Real.exp (x * Real.sqrt (1 - t ^ 2)))).aestronglyMeasurable
    · exact (by fun_prop : Continuous
        (fun t : ℝ => Real.exp (α * Real.sqrt (1 - t ^ 2)))).intervalIntegrable _ _
    · exact (by fun_prop : Continuous
        (fun t : ℝ => Real.sqrt (1 - t ^ 2) *
          Real.exp (α * Real.sqrt (1 - t ^ 2)))).aestronglyMeasurable
    · filter_upwards [] with t ht x hx
      exact hbound x t hx
    · exact (continuous_const.intervalIntegrable _ _)
    · filter_upwards [] with t ht x hx
      exact hparam x t
  have hfixed' :
      HasDerivAt
        (fun t =>
          ∫ x in Real.sin α..Real.cos α, integrand t x)
        (∫ x in Real.sin α..Real.cos α,
          radial x * integrand α x) α := by
    simpa [integrand, radial] using
      hfixed (Real.sin α) (Real.cos α)
  have hmain := moving_from_fixed α hfixed'
  unfold integralFunction leibnizDerivative
  rw [← hsqrt_cos, ← hsqrt_sin]
  simpa [integrand, radial] using hmain.deriv

end

end ProofGap.Exercise3718_1
