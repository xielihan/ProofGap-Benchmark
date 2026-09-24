import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise3718_5

noncomputable section

open Filter Topology
open scoped Interval

def innerIntegral (x α : ℝ) : ℝ :=
  ∫ y in x - α..x + α, Real.sin (x ^ 2 + y ^ 2 - α ^ 2)

def integralFunction (α : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..α ^ 2, innerIntegral x α

def leibnizDerivative (α : ℝ) : ℝ :=
  2 * α * innerIntegral (α ^ 2) α +
    ∫ x in (0 : ℝ)..α ^ 2, deriv (fun t => innerIntegral x t) α

def expandedDerivative (α : ℝ) : ℝ :=
  2 * α * innerIntegral (α ^ 2) α +
    ∫ x in (0 : ℝ)..α ^ 2,
      Real.sin (x ^ 2 + (x + α) ^ 2 - α ^ 2) +
        Real.sin (x ^ 2 + (x - α) ^ 2 - α ^ 2) +
        ∫ y in x - α..x + α,
          -2 * α * Real.cos (x ^ 2 + y ^ 2 - α ^ 2)

def simplifiedDerivative (α : ℝ) : ℝ :=
  2 * α * innerIntegral (α ^ 2) α +
    ∫ x in (0 : ℝ)..α ^ 2,
      Real.sin (2 * x ^ 2 + 2 * α * x) +
        Real.sin (2 * x ^ 2 - 2 * α * x) +
        ∫ y in x - α..x + α,
          -2 * α * Real.cos (x ^ 2 + y ^ 2 - α ^ 2)

def finalDerivative (α : ℝ) : ℝ :=
  2 * α * innerIntegral (α ^ 2) α +
    -- Statement correction: parenthesize the first interval integral so that
    -- the following subtraction is not captured by its binder.
    2 * (∫ x in (0 : ℝ)..α ^ 2,
      Real.sin (2 * x ^ 2) * Real.cos (2 * α * x)) -
    2 * α * ∫ x in (0 : ℝ)..α ^ 2,
      ∫ y in x - α..x + α,
        Real.cos (x ^ 2 + y ^ 2 - α ^ 2)

private def kernel (x t y : ℝ) : ℝ :=
  Real.sin (x ^ 2 + y ^ 2 - t ^ 2)

private def kernelDerivative (x t y : ℝ) : ℝ :=
  -2 * t * Real.cos (x ^ 2 + y ^ 2 - t ^ 2)

private lemma kernel_hasDerivAt (x t y : ℝ) :
    HasDerivAt (fun z => kernel x z y) (kernelDerivative x t y) t := by
  unfold kernel kernelDerivative
  convert Real.hasDerivAt_sin
    (x ^ 2 + y ^ 2 - t ^ 2) |>.comp t
      (((hasDerivAt_const t (x ^ 2 + y ^ 2)).sub
        ((hasDerivAt_id t).pow 2))) using 1 <;> simp only [id_eq] <;> ring

private lemma kernelDerivative_bound (a t x y : ℝ)
    (ht : t ∈ Set.Icc (a - 1) (a + 1)) :
    ‖kernelDerivative x t y‖ ≤ 2 * (|a| + 1) := by
  have ht_abs : |t| ≤ |a| + 1 := by
    rw [abs_le]
    constructor
    · linarith [ht.1, neg_le_abs a]
    · linarith [ht.2, le_abs_self a]
  unfold kernelDerivative
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  have hcos : |Real.cos (x ^ 2 + y ^ 2 - t ^ 2)| ≤ 1 :=
    Real.abs_cos_le_one _
  calc
    |(-2 : ℝ)| * |t| * |Real.cos (x ^ 2 + y ^ 2 - t ^ 2)| =
        2 * |t| * |Real.cos (x ^ 2 + y ^ 2 - t ^ 2)| := by norm_num
    _ ≤ 2 * |t| * 1 :=
      mul_le_mul_of_nonneg_left hcos
        (mul_nonneg (by norm_num) (abs_nonneg t))
    _ = 2 * |t| := by ring
    _ ≤ 2 * (|a| + 1) := by
      gcongr

private lemma kernel_parameter_lipschitz (a t x y : ℝ)
    (ht : t ∈ Set.Icc (a - 1) (a + 1)) :
    ‖kernel x t y - kernel x a y‖ ≤
      (2 * (|a| + 1)) * ‖t - a‖ := by
  exact Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.Icc (a - 1) (a + 1))
    (f := fun z => kernel x z y)
    (fun z hz => (kernel_hasDerivAt x z y).differentiableAt)
    (fun z hz => by
      rw [(kernel_hasDerivAt x z y).deriv]
      exact kernelDerivative_bound a z x y hz)
    (convex_Icc _ _)
    (by constructor <;> linarith)
    ht

private lemma inner_correction_remainder
    (x a : ℝ) (b : ℝ → ℝ)
    (hb : ∀ t, |b t - b a| ≤ |t - a|) :
    HasDerivAt
      (fun t => ∫ y in b a..b t, kernel x t y - kernel x a y) 0 a := by
  let R : ℝ → ℝ :=
    fun t => ∫ y in b a..b t, kernel x t y - kernel x a y
  change HasDerivAt R 0 a
  rw [hasDerivAt_iff_tendsto]
  have hupper :
      Tendsto (fun t : ℝ => (2 * (|a| + 1)) * |t - a|)
        (𝓝 a) (𝓝 0) := by
    have hc : ContinuousAt
        (fun t : ℝ => (2 * (|a| + 1)) * |t - a|) a := by
      fun_prop
    change Tendsto (fun t : ℝ => (2 * (|a| + 1)) * |t - a|)
      (𝓝 a) (𝓝 ((2 * (|a| + 1)) * |a - a|)) at hc
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
        ((2 * (|a| + 1)) * ‖t - a‖) * |b t - b a| := by
    unfold R
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y hy
    exact kernel_parameter_lipschitz a t x y htIcc
  have hba := hb t
  rw [hRa]
  simp only [sub_zero, smul_zero]
  by_cases hta : t = a
  · subst t
    simp
  · have habs : 0 < |t - a| := abs_pos.mpr (sub_ne_zero.mpr hta)
    rw [Real.norm_eq_abs] at hR ⊢
    calc
      |t - a|⁻¹ * ‖∫ y in b a..b t, kernel x t y - kernel x a y‖ ≤
          |t - a|⁻¹ *
            (((2 * (|a| + 1)) * |t - a|) * |b t - b a|) :=
        mul_le_mul_of_nonneg_left hR (inv_nonneg.mpr (abs_nonneg _))
      _ ≤ |t - a|⁻¹ *
            (((2 * (|a| + 1)) * |t - a|) * |t - a|) := by
        gcongr
      _ = (2 * (|a| + 1)) * |t - a| := by
        field_simp [habs.ne']

private lemma inner_fixed_hasDerivAt (x a : ℝ) :
    HasDerivAt
      (fun t => ∫ y in x - a..x + a, kernel x t y)
      (∫ y in x - a..x + a, kernelDerivative x a y) a := by
  let s : Set ℝ := Set.Icc (a - 1) (a + 1)
  let bound : ℝ → ℝ := fun _ => 2 * (|a| + 1)
  have hs : s ∈ 𝓝 a := by
    apply Icc_mem_nhds <;> dsimp [s] <;> linarith
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t y => kernel x t y)
    (F' := fun t y => kernelDerivative x t y)
    (x₀ := a) (a := x - a) (b := x + a)
    (μ := MeasureTheory.volume) (s := s) (bound := bound)
    hs ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [] with t
    exact (by
      unfold kernel
      fun_prop :
      Continuous (fun y => kernel x t y)).aestronglyMeasurable
  · exact (by
      unfold kernel
      fun_prop :
      Continuous (fun y => kernel x a y)).intervalIntegrable _ _
  · exact (by
      unfold kernelDerivative
      fun_prop :
      Continuous (fun y => kernelDerivative x a y)).aestronglyMeasurable
  · filter_upwards [] with y hy t ht
    exact kernelDerivative_bound a t x y ht
  · exact (continuous_const.intervalIntegrable _ _)
  · filter_upwards [] with y hy t ht
    exact kernel_hasDerivAt x t y

private lemma inner_upper_correction (x a : ℝ) :
    HasDerivAt
      (fun t => ∫ y in x + a..x + t, kernel x t y)
      (kernel x a (x + a)) a := by
  let base : ℝ → ℝ :=
    fun t => ∫ y in x + a..x + t, kernel x a y
  let rem : ℝ → ℝ :=
    fun t => ∫ y in x + a..x + t, kernel x t y - kernel x a y
  have hcont : Continuous (kernel x a) := by
    unfold kernel
    fun_prop
  have hbase : HasDerivAt base (kernel x a (x + a)) a := by
    dsimp [base]
    convert
      ((hcont.integral_hasStrictDerivAt (x + a) (x + a)).hasDerivAt.comp
        a ((hasDerivAt_const a x).add (hasDerivAt_id a))) using 1 <;> ring
  have hrem : HasDerivAt rem 0 a := by
    dsimp [rem]
    exact inner_correction_remainder x a (fun t => x + t)
      (fun t => by simp)
  have heq :
      (fun t => ∫ y in x + a..x + t, kernel x t y) =
        fun t => base t + rem t := by
    funext t
    dsimp [base, rem]
    rw [← intervalIntegral.integral_add
      (hcont.intervalIntegrable _ _)
      ((by
        unfold kernel
        fun_prop :
        Continuous (fun y => kernel x t y - kernel x a y)
        ).intervalIntegrable _ _)]
    congr 1
    funext y
    ring
  rw [heq]
  convert hbase.add hrem using 1 <;> ring

private lemma inner_lower_correction (x a : ℝ) :
    HasDerivAt
      (fun t => ∫ y in x - a..x - t, kernel x t y)
      (-kernel x a (x - a)) a := by
  let base : ℝ → ℝ :=
    fun t => ∫ y in x - a..x - t, kernel x a y
  let rem : ℝ → ℝ :=
    fun t => ∫ y in x - a..x - t, kernel x t y - kernel x a y
  have hcont : Continuous (kernel x a) := by
    unfold kernel
    fun_prop
  have hbase : HasDerivAt base (-kernel x a (x - a)) a := by
    dsimp [base]
    convert
      ((hcont.integral_hasStrictDerivAt (x - a) (x - a)).hasDerivAt.comp
        a ((hasDerivAt_const a x).sub (hasDerivAt_id a))) using 1 <;> ring
  have hrem : HasDerivAt rem 0 a := by
    dsimp [rem]
    exact inner_correction_remainder x a (fun t => x - t)
      (fun t => by rw [abs_sub_comm]; simp)
  have heq :
      (fun t => ∫ y in x - a..x - t, kernel x t y) =
        fun t => base t + rem t := by
    funext t
    dsimp [base, rem]
    rw [← intervalIntegral.integral_add
      (hcont.intervalIntegrable _ _)
      ((by
        unfold kernel
        fun_prop :
        Continuous (fun y => kernel x t y - kernel x a y)
        ).intervalIntegrable _ _)]
    congr 1
    funext y
    ring
  rw [heq]
  convert hbase.add hrem using 1 <;> ring

private lemma inner_hasDerivAt (x a : ℝ) :
    HasDerivAt (fun t => innerIntegral x t)
      (kernel x a (x + a) + kernel x a (x - a) +
        ∫ y in x - a..x + a, kernelDerivative x a y) a := by
  have hfixed := inner_fixed_hasDerivAt x a
  have hu := inner_upper_correction x a
  have hl := inner_lower_correction x a
  have hsum := (hfixed.add hu).sub hl
  have heq :
      (fun t => innerIntegral x t) =
        fun t =>
          (∫ y in x - a..x + a, kernel x t y) +
            (∫ y in x + a..x + t, kernel x t y) -
              ∫ y in x - a..x - t, kernel x t y := by
    funext t
    unfold innerIntegral
    have hcont : Continuous (kernel x t) := by
      unfold kernel
      fun_prop
    calc
      (∫ y in x - t..x + t, Real.sin (x ^ 2 + y ^ 2 - t ^ 2)) =
          (∫ y in x - t..x + a, kernel x t y) +
            ∫ y in x + a..x + t, kernel x t y := by
        change (∫ y in x - t..x + t, kernel x t y) =
          (∫ y in x - t..x + a, kernel x t y) +
            ∫ y in x + a..x + t, kernel x t y
        exact (intervalIntegral.integral_add_adjacent_intervals
          (hcont.intervalIntegrable _ _)
          (hcont.intervalIntegrable _ _)).symm
      _ = ((∫ y in x - t..x - a, kernel x t y) +
            ∫ y in x - a..x + a, kernel x t y) +
            ∫ y in x + a..x + t, kernel x t y := by
        rw [← intervalIntegral.integral_add_adjacent_intervals
          (hcont.intervalIntegrable _ _)
          (hcont.intervalIntegrable _ _)]
      _ = (∫ y in x - a..x + a, kernel x t y) +
            (∫ y in x + a..x + t, kernel x t y) -
              ∫ y in x - a..x - t, kernel x t y := by
        rw [intervalIntegral.integral_symm
          (f := kernel x t) (a := x - a) (b := x - t)]
        ring
  rw [heq]
  convert hsum using 1 <;> ring

private lemma continuous_fixed_interval_integral
    (a b : ℝ) (F : ℝ → ℝ → ℝ)
    (hF : Continuous F.uncurry) :
    Continuous (fun x => ∫ y in a..b, F x y) := by
  have hset :
      Continuous (fun x => ∫ y in Set.uIcc a b, F x y) :=
    continuous_parametric_integral_of_continuous hF isCompact_uIcc
  have heq :
      (fun x => ∫ y in a..b, F x y) =
        fun x => (if a ≤ b then 1 else -1 : ℝ) •
          ∫ y in Set.uIcc a b, F x y := by
    funext x
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
    congr 1
    rw [Set.uIoc, Set.uIcc, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [heq]
  fun_prop

private lemma innerIntegral_eq_translated (x t : ℝ) :
    innerIntegral x t =
      ∫ u in -t..t, kernel x t (u + x) := by
  have h :=
    intervalIntegral.integral_comp_add_right
      (fun y : ℝ => Real.sin (x ^ 2 + y ^ 2 - t ^ 2)) x
      (a := -t) (b := t)
  rw [show -t + x = x - t by ring, show t + x = x + t by ring] at h
  unfold innerIntegral kernel
  exact h.symm

private lemma kernelDerivative_integral_eq_translated (x t : ℝ) :
    (∫ y in x - t..x + t, kernelDerivative x t y) =
      ∫ u in -t..t, kernelDerivative x t (u + x) := by
  simpa [sub_eq_add_neg, add_comm] using
    (intervalIntegral.integral_comp_add_right
      (kernelDerivative x t) x (a := -t) (b := t))

private lemma innerIntegral_continuous (t : ℝ) :
    Continuous (fun x => innerIntegral x t) := by
  have h :
      Continuous (fun x =>
        ∫ u in -t..t, kernel x t (u + x)) := by
    apply continuous_fixed_interval_integral
    unfold kernel
    fun_prop
  convert h using 1
  funext x
  exact innerIntegral_eq_translated x t

private lemma kernelDerivative_integral_continuous (t : ℝ) :
    Continuous (fun x =>
      ∫ y in x - t..x + t, kernelDerivative x t y) := by
  have h :
      Continuous (fun x =>
        ∫ u in -t..t, kernelDerivative x t (u + x)) := by
    apply continuous_fixed_interval_integral
    unfold kernelDerivative
    fun_prop
  convert h using 1
  funext x
  exact kernelDerivative_integral_eq_translated x t

private def innerDerivative (x t : ℝ) : ℝ :=
  kernel x t (x + t) + kernel x t (x - t) +
    ∫ y in x - t..x + t, kernelDerivative x t y

private lemma innerDerivative_continuous (t : ℝ) :
    Continuous (fun x => innerDerivative x t) := by
  unfold innerDerivative
  exact ((by
    unfold kernel
    fun_prop :
    Continuous (fun x => kernel x t (x + t))).add
      (by
        unfold kernel
        fun_prop :
        Continuous (fun x => kernel x t (x - t)))).add
          (kernelDerivative_integral_continuous t)

private lemma inner_hasDerivAt' (x t : ℝ) :
    HasDerivAt (fun z => innerIntegral x z) (innerDerivative x t) t := by
  exact inner_hasDerivAt x t

private lemma innerDerivative_bound (a t x : ℝ)
    (ht : t ∈ Set.Icc (a - 1) (a + 1)) :
    ‖innerDerivative x t‖ ≤ 2 + 4 * (|a| + 1) ^ 2 := by
  have ht_abs : |t| ≤ |a| + 1 := by
    rw [abs_le]
    constructor
    · linarith [ht.1, neg_le_abs a]
    · linarith [ht.2, le_abs_self a]
  have h₁ : ‖kernel x t (x + t)‖ ≤ 1 := by
    unfold kernel
    rw [Real.norm_eq_abs]
    exact Real.abs_sin_le_one _
  have h₂ : ‖kernel x t (x - t)‖ ≤ 1 := by
    unfold kernel
    rw [Real.norm_eq_abs]
    exact Real.abs_sin_le_one _
  have hlength : |(x + t) - (x - t)| ≤ 2 * (|a| + 1) := by
    rw [show (x + t) - (x - t) = 2 * t by ring, abs_mul]
    norm_num
    gcongr
  have hI :
      ‖∫ y in x - t..x + t, kernelDerivative x t y‖ ≤
        (2 * (|a| + 1)) * |(x + t) - (x - t)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y hy
    exact kernelDerivative_bound a t x y ht
  have hI' :
      ‖∫ y in x - t..x + t, kernelDerivative x t y‖ ≤
        4 * (|a| + 1) ^ 2 := by
    calc
      ‖∫ y in x - t..x + t, kernelDerivative x t y‖ ≤
          (2 * (|a| + 1)) * |(x + t) - (x - t)| := hI
      _ ≤ (2 * (|a| + 1)) * (2 * (|a| + 1)) := by
        gcongr
      _ = 4 * (|a| + 1) ^ 2 := by ring
  unfold innerDerivative
  calc
    ‖kernel x t (x + t) + kernel x t (x - t) +
        ∫ y in x - t..x + t, kernelDerivative x t y‖ ≤
      ‖kernel x t (x + t)‖ + ‖kernel x t (x - t)‖ +
        ‖∫ y in x - t..x + t, kernelDerivative x t y‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ 1 + 1 + 4 * (|a| + 1) ^ 2 := by
      gcongr
    _ = 2 + 4 * (|a| + 1) ^ 2 := by ring

private lemma inner_parameter_lipschitz (a t x : ℝ)
    (ht : t ∈ Set.Icc (a - 1) (a + 1)) :
    ‖innerIntegral x t - innerIntegral x a‖ ≤
      (2 + 4 * (|a| + 1) ^ 2) * ‖t - a‖ := by
  exact Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.Icc (a - 1) (a + 1))
    (f := fun z => innerIntegral x z)
    (fun z hz => (inner_hasDerivAt' x z).differentiableAt)
    (fun z hz => by
      rw [(inner_hasDerivAt' x z).deriv]
      exact innerDerivative_bound a z x hz)
    (convex_Icc _ _)
    (by constructor <;> linarith)
    ht

private lemma outer_fixed_hasDerivAt (a c d : ℝ) :
    HasDerivAt
      (fun t => ∫ x in c..d, innerIntegral x t)
      (∫ x in c..d, innerDerivative x a) a := by
  let s : Set ℝ := Set.Icc (a - 1) (a + 1)
  let bound : ℝ → ℝ := fun _ => 2 + 4 * (|a| + 1) ^ 2
  have hs : s ∈ 𝓝 a := by
    apply Icc_mem_nhds <;> dsimp [s] <;> linarith
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t x => innerIntegral x t)
    (F' := fun t x => innerDerivative x t)
    (x₀ := a) (a := c) (b := d)
    (μ := MeasureTheory.volume) (s := s) (bound := bound)
    hs ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [] with t
    exact (innerIntegral_continuous t).aestronglyMeasurable
  · exact (innerIntegral_continuous a).intervalIntegrable _ _
  · exact (innerDerivative_continuous a).aestronglyMeasurable
  · filter_upwards [] with x hx t ht
    exact innerDerivative_bound a t x ht
  · exact (continuous_const.intervalIntegrable _ _)
  · filter_upwards [] with x hx t ht
    exact inner_hasDerivAt' x t

private lemma square_endpoint_local_bound (a t : ℝ)
    (ht : |t - a| < 1) :
    |t ^ 2 - a ^ 2| ≤ (2 * |a| + 1) * |t - a| := by
  have hsum : |t + a| ≤ 2 * |a| + 1 := by
    calc
      |t + a| = |(t - a) + 2 * a| := by congr 1 <;> ring
      _ ≤ |t - a| + |2 * a| := by
        simpa [Real.norm_eq_abs] using
          (norm_add_le (t - a) (2 * a))
      _ ≤ 1 + 2 * |a| := by
        rw [abs_mul]
        norm_num
        linarith
      _ = 2 * |a| + 1 := by ring
  rw [show t ^ 2 - a ^ 2 = (t + a) * (t - a) by ring, abs_mul]
  exact mul_le_mul_of_nonneg_right hsum (abs_nonneg _)

private lemma outer_correction_remainder (a : ℝ) :
    HasDerivAt
      (fun t =>
        ∫ x in a ^ 2..t ^ 2, innerIntegral x t - innerIntegral x a) 0 a := by
  let L : ℝ := 2 + 4 * (|a| + 1) ^ 2
  let K : ℝ := 2 * |a| + 1
  let R : ℝ → ℝ :=
    fun t => ∫ x in a ^ 2..t ^ 2, innerIntegral x t - innerIntegral x a
  change HasDerivAt R 0 a
  rw [hasDerivAt_iff_tendsto]
  have hupper :
      Tendsto (fun t : ℝ => (L * K) * |t - a|) (𝓝 a) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => (L * K) * |t - a|) a := by
      fun_prop
    change Tendsto (fun t : ℝ => (L * K) * |t - a|)
      (𝓝 a) (𝓝 ((L * K) * |a - a|)) at hc
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
      ‖R t‖ ≤ (L * ‖t - a‖) * |t ^ 2 - a ^ 2| := by
    unfold R L
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    exact inner_parameter_lipschitz a t x htIcc
  have hsquare := square_endpoint_local_bound a t ht
  rw [hRa]
  simp only [sub_zero, smul_zero]
  by_cases hta : t = a
  · subst t
    simp
  · have habs : 0 < |t - a| := abs_pos.mpr (sub_ne_zero.mpr hta)
    rw [Real.norm_eq_abs] at hR ⊢
    calc
      |t - a|⁻¹ * ‖∫ x in a ^ 2..t ^ 2,
          innerIntegral x t - innerIntegral x a‖ ≤
          |t - a|⁻¹ * ((L * |t - a|) * |t ^ 2 - a ^ 2|) :=
        mul_le_mul_of_nonneg_left hR (inv_nonneg.mpr (abs_nonneg _))
      _ ≤ |t - a|⁻¹ *
          ((L * |t - a|) * ((2 * |a| + 1) * |t - a|)) := by
        gcongr
      _ = (L * K) * |t - a| := by
        dsimp [K]
        field_simp [habs.ne']
        <;> ring

private lemma outer_upper_correction (a : ℝ) :
    HasDerivAt
      (fun t => ∫ x in a ^ 2..t ^ 2, innerIntegral x t)
      (2 * a * innerIntegral (a ^ 2) a) a := by
  let base : ℝ → ℝ :=
    fun t => ∫ x in a ^ 2..t ^ 2, innerIntegral x a
  let rem : ℝ → ℝ :=
    fun t =>
      ∫ x in a ^ 2..t ^ 2, innerIntegral x t - innerIntegral x a
  have hcont : Continuous (fun x => innerIntegral x a) :=
    innerIntegral_continuous a
  have hbase :
      HasDerivAt base (2 * a * innerIntegral (a ^ 2) a) a := by
    dsimp [base]
    convert
      ((hcont.integral_hasStrictDerivAt (a ^ 2) (a ^ 2)).hasDerivAt.comp
        a ((hasDerivAt_id a).pow 2)) using 1 <;>
          simp only [id_eq] <;> ring
  have hrem : HasDerivAt rem 0 a := by
    dsimp [rem]
    exact outer_correction_remainder a
  have heq :
      (fun t => ∫ x in a ^ 2..t ^ 2, innerIntegral x t) =
        fun t => base t + rem t := by
    funext t
    dsimp [base, rem]
    have hdiff :
        Continuous (fun x => innerIntegral x t - innerIntegral x a) :=
      (innerIntegral_continuous t).sub (innerIntegral_continuous a)
    rw [← intervalIntegral.integral_add
      (hcont.intervalIntegrable _ _)
      (hdiff.intervalIntegrable _ _)]
    congr 1
    funext x
    ring
  rw [heq]
  convert hbase.add hrem using 1 <;> ring

private lemma integralFunction_hasDerivAt (a : ℝ) :
    HasDerivAt integralFunction
      (2 * a * innerIntegral (a ^ 2) a +
        ∫ x in 0..a ^ 2, innerDerivative x a) a := by
  have hfixed := outer_fixed_hasDerivAt a 0 (a ^ 2)
  have hu := outer_upper_correction a
  have hsum := hfixed.add hu
  have heq :
      integralFunction =
        fun t =>
          (∫ x in 0..a ^ 2, innerIntegral x t) +
            ∫ x in a ^ 2..t ^ 2, innerIntegral x t := by
    funext t
    unfold integralFunction
    exact (intervalIntegral.integral_add_adjacent_intervals
      ((innerIntegral_continuous t).intervalIntegrable _ _)
      ((innerIntegral_continuous t).intervalIntegrable _ _)).symm
  rw [heq]
  convert hsum using 1 <;> ring

private def cosineInner (x a : ℝ) : ℝ :=
  ∫ y in x - a..x + a, Real.cos (x ^ 2 + y ^ 2 - a ^ 2)

private lemma cosineInner_eq_translated (x a : ℝ) :
    cosineInner x a =
      ∫ u in -a..a, Real.cos (x ^ 2 + (u + x) ^ 2 - a ^ 2) := by
  have h :=
    intervalIntegral.integral_comp_add_right
      (fun y : ℝ => Real.cos (x ^ 2 + y ^ 2 - a ^ 2)) x
      (a := -a) (b := a)
  rw [show -a + x = x - a by ring, show a + x = x + a by ring] at h
  unfold cosineInner
  exact h.symm

private lemma cosineInner_continuous (a : ℝ) :
    Continuous (fun x => cosineInner x a) := by
  have h :
      Continuous (fun x =>
        ∫ u in -a..a, Real.cos (x ^ 2 + (u + x) ^ 2 - a ^ 2)) := by
    apply continuous_fixed_interval_integral
    fun_prop
  convert h using 1
  funext x
  exact cosineInner_eq_translated x a

theorem gap1 (α : ℝ) :
    deriv integralFunction α = leibnizDerivative α := by
  unfold leibnizDerivative
  rw [show (∫ x in 0..α ^ 2, deriv (fun t => innerIntegral x t) α) =
      ∫ x in 0..α ^ 2, innerDerivative x α by
    congr 1
    funext x
    exact (inner_hasDerivAt' x α).deriv]
  exact (integralFunction_hasDerivAt α).deriv

theorem gap2 (α : ℝ) :
    deriv integralFunction α = expandedDerivative α := by
  rw [gap1]
  unfold leibnizDerivative expandedDerivative
  simp_rw [(inner_hasDerivAt' _ α).deriv]
  unfold innerIntegral innerDerivative kernel kernelDerivative
  congr 3 <;> ring

theorem gap3 (α : ℝ) :
    deriv integralFunction α = simplifiedDerivative α := by
  rw [gap2]
  unfold expandedDerivative simplifiedDerivative
  congr 3
  funext x
  congr 1 <;> ring

theorem gap4 (α : ℝ) :
    deriv integralFunction α = finalDerivative α := by
  rw [gap3]
  have htrig (x : ℝ) :
      Real.sin (2 * x ^ 2 + 2 * α * x) +
          Real.sin (2 * x ^ 2 - 2 * α * x) =
        2 * (Real.sin (2 * x ^ 2) * Real.cos (2 * α * x)) := by
    rw [Real.sin_add, Real.sin_sub]
    ring
  have hinner (x : ℝ) :
      (∫ y in x - α..x + α,
        -2 * α * Real.cos (x ^ 2 + y ^ 2 - α ^ 2)) =
        -2 * α * cosineInner x α := by
    unfold cosineInner
    exact intervalIntegral.integral_const_mul
      (-2 * α) (fun y : ℝ =>
        Real.cos (x ^ 2 + y ^ 2 - α ^ 2))
  have hpoint (x : ℝ) :
      Real.sin (2 * x ^ 2 + 2 * α * x) +
          Real.sin (2 * x ^ 2 - 2 * α * x) +
          (∫ y in x - α..x + α,
            -2 * α * Real.cos (x ^ 2 + y ^ 2 - α ^ 2)) =
        2 * (Real.sin (2 * x ^ 2) * Real.cos (2 * α * x)) -
          2 * α * cosineInner x α := by
    rw [htrig, hinner]
    ring
  have hf :
      Continuous (fun x : ℝ =>
        Real.sin (2 * x ^ 2) * Real.cos (2 * α * x)) := by
    fun_prop
  have hg : Continuous (fun x => cosineInner x α) :=
    cosineInner_continuous α
  have hmain :
      (∫ x in 0..α ^ 2,
        Real.sin (2 * x ^ 2 + 2 * α * x) +
          Real.sin (2 * x ^ 2 - 2 * α * x) +
          ∫ y in x - α..x + α,
            -2 * α * Real.cos (x ^ 2 + y ^ 2 - α ^ 2)) =
        2 * (∫ x in 0..α ^ 2,
          Real.sin (2 * x ^ 2) * Real.cos (2 * α * x)) -
        2 * α * ∫ x in 0..α ^ 2, cosineInner x α := by
    calc
      (∫ x in 0..α ^ 2,
        Real.sin (2 * x ^ 2 + 2 * α * x) +
          Real.sin (2 * x ^ 2 - 2 * α * x) +
          ∫ y in x - α..x + α,
            -2 * α * Real.cos (x ^ 2 + y ^ 2 - α ^ 2)) =
          ∫ x in 0..α ^ 2,
            2 * (Real.sin (2 * x ^ 2) * Real.cos (2 * α * x)) -
              2 * α * cosineInner x α := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact hpoint x
      _ = (∫ x in 0..α ^ 2,
            2 * (Real.sin (2 * x ^ 2) * Real.cos (2 * α * x))) -
          ∫ x in 0..α ^ 2, 2 * α * cosineInner x α := by
        exact intervalIntegral.integral_sub
          ((hf.const_mul 2).intervalIntegrable _ _)
          ((hg.const_mul (2 * α)).intervalIntegrable _ _)
      _ = 2 * (∫ x in 0..α ^ 2,
            Real.sin (2 * x ^ 2) * Real.cos (2 * α * x)) -
          2 * α * ∫ x in 0..α ^ 2, cosineInner x α := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  unfold simplifiedDerivative finalDerivative
  rw [hmain]
  unfold cosineInner
  ring

end

end ProofGap.Exercise3718_5
