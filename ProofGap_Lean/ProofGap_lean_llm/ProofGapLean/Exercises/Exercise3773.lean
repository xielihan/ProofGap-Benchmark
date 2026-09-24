import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3773

noncomputable section

open Filter MeasureTheory Set
open scoped Interval Topology

def HasImproperIntegralFrom (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Tendsto (fun A : ℝ => ∫ x in a..A, f x) atTop (nhds L)

def ImproperlyIntegrableFrom (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∃ L : ℝ, HasImproperIntegralFrom f a L

def improperIntegralFrom (f : ℝ → ℝ) (a : ℝ) : ℝ :=
  sInf {L : ℝ | HasImproperIntegralFrom f a L}

def damped (f : ℝ → ℝ) (α x : ℝ) : ℝ :=
  Real.exp (-(α * x)) * f x

def AbelHypotheses (f : ℝ → ℝ) : Prop :=
  (∀ A : ℝ, IntervalIntegrable f volume 0 A) ∧
    ImproperlyIntegrableFrom f 0

private lemma local_intervalIntegrable
    (f : ℝ → ℝ) (hf : AbelHypotheses f) (a b : ℝ) :
    IntervalIntegrable f volume a b :=
  (hf.1 a).symm.trans (hf.1 b)

private lemma improperIntegralFrom_eq_of_has
    (f : ℝ → ℝ) (a L : ℝ)
    (hL : HasImproperIntegralFrom f a L) :
    improperIntegralFrom f a = L := by
  have hset :
      {K : ℝ | HasImproperIntegralFrom f a K} = {L} := by
    ext K
    simp only [mem_setOf_eq, mem_singleton_iff]
    constructor
    · intro hK
      exact tendsto_nhds_unique hK hL
    · rintro rfl
      exact hL
  unfold improperIntegralFrom
  rw [hset]
  simp

private lemma has_improperIntegralFrom_value
    (f : ℝ → ℝ) (a : ℝ)
    (hf : ImproperlyIntegrableFrom f a) :
    HasImproperIntegralFrom f a (improperIntegralFrom f a) := by
  rcases hf with ⟨L, hL⟩
  rw [improperIntegralFrom_eq_of_has f a L hL]
  exact hL

private lemma hasImproperIntegralFrom_shift
    (f : ℝ → ℝ)
    (hlocal : ∀ A : ℝ, IntervalIntegrable f volume 0 A)
    (L a : ℝ) (hL : HasImproperIntegralFrom f 0 L) :
    HasImproperIntegralFrom f a
      (L - ∫ x in (0 : ℝ)..a, f x) := by
  have heq :
      (fun A : ℝ => ∫ x in a..A, f x) =
        fun A : ℝ =>
          (∫ x in (0 : ℝ)..A, f x) -
            ∫ x in (0 : ℝ)..a, f x := by
    funext A
    have hadd :=
      intervalIntegral.integral_add_adjacent_intervals
        (hlocal a) ((hlocal a).symm.trans (hlocal A))
    linarith
  unfold HasImproperIntegralFrom at hL ⊢
  rw [heq]
  exact hL.sub_const _

private lemma improperIntegralFrom_shift_eq
    (f : ℝ → ℝ)
    (hlocal : ∀ A : ℝ, IntervalIntegrable f volume 0 A)
    (L a : ℝ) (hL : HasImproperIntegralFrom f 0 L) :
    improperIntegralFrom f a =
      L - ∫ x in (0 : ℝ)..a, f x :=
  improperIntegralFrom_eq_of_has f a _
    (hasImproperIntegralFrom_shift f hlocal L a hL)

private lemma improperIntegralFrom_tail_tendsto
    (f : ℝ → ℝ)
    (hlocal : ∀ A : ℝ, IntervalIntegrable f volume 0 A)
    (L : ℝ) (hL : HasImproperIntegralFrom f 0 L) :
    Tendsto (improperIntegralFrom f) atTop (𝓝 0) := by
  have heq :
      improperIntegralFrom f =
        fun A : ℝ =>
          L - ∫ x in (0 : ℝ)..A, f x := by
    funext A
    exact improperIntegralFrom_shift_eq f hlocal L A hL
  unfold HasImproperIntegralFrom at hL
  rw [heq]
  have hconst :
      Tendsto (fun _ : ℝ => L) atTop (𝓝 L) :=
    tendsto_const_nhds
  have h := hconst.sub hL
  simpa using h

private def primitive0 (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, f t

private lemma partial_continuous
    (f : ℝ → ℝ) (hf : AbelHypotheses f) :
    Continuous (primitive0 f) := by
  simpa [primitive0] using
    (intervalIntegral.continuous_primitive
      (fun a b => local_intervalIntegrable f hf a b) 0)

private lemma partial_bounded_nonneg
    (f : ℝ → ℝ) (hf : AbelHypotheses f) (L : ℝ)
    (hL : HasImproperIntegralFrom f 0 L) :
    ∃ M : ℝ, 0 < M ∧
      ∀ x : ℝ, 0 ≤ x → |primitive0 f x| ≤ M := by
  have hnear :
      ∀ᶠ x : ℝ in atTop, dist (primitive0 f x) L < 1 := by
    unfold HasImproperIntegralFrom at hL
    change Tendsto (primitive0 f) atTop (𝓝 L) at hL
    exact (Metric.tendsto_nhds.1 hL) 1 zero_lt_one
  rcases eventually_atTop.1 hnear with ⟨B, hB⟩
  let T : ℝ := max B 0
  have hBT : B ≤ T := by
    exact le_max_left _ _
  have h0T : 0 ≤ T := by
    exact le_max_right _ _
  have hcont :
      ContinuousOn (primitive0 f) (Icc (0 : ℝ) T) :=
    (partial_continuous f hf).continuousOn
  obtain ⟨C, hC⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn hcont
  let M : ℝ := 1 + |L| + |C|
  have hM : 0 < M := by
    dsimp [M]
    positivity
  refine ⟨M, hM, ?_⟩
  intro x hx
  by_cases hTx : T ≤ x
  · have hxB : B ≤ x := hBT.trans hTx
    have hclose := hB x hxB
    rw [Real.dist_eq] at hclose
    calc
      |primitive0 f x| ≤ |primitive0 f x - L| + |L| := by
        have := abs_add_le (primitive0 f x - L) L
        simpa using this
      _ ≤ 1 + |L| := add_le_add (le_of_lt hclose) le_rfl
      _ ≤ M := by
        dsimp [M]
        linarith [abs_nonneg C]
  · have hxT : x ≤ T := le_of_not_ge hTx
    have hCx := hC x ⟨hx, hxT⟩
    rw [Real.norm_eq_abs] at hCx
    exact hCx.trans (by
      dsimp [M]
      have hCle : C ≤ |C| := le_abs_self C
      nlinarith [abs_nonneg L])

private def weight (α x : ℝ) : ℝ :=
  Real.exp (-α * x)

private def weightDeriv (α x : ℝ) : ℝ :=
  -α * weight α x

private lemma weight_hasDerivAt (α x : ℝ) :
    HasDerivAt (weight α) (weightDeriv α x) x := by
  unfold weightDeriv
  convert
    (Real.hasDerivAt_exp (-α * x)).comp x
      ((hasDerivAt_const x (-α)).mul (hasDerivAt_id x)) using 1
  simp [weight, mul_comm]

private lemma weight_absolutelyContinuous
    (α a b : ℝ) :
    AbsolutelyContinuousOnInterval (weight α) a b := by
  have hdcont : Continuous (weightDeriv α) := by
    unfold weightDeriv weight
    fun_prop
  have hdint : IntervalIntegrable (weightDeriv α) volume a b :=
    hdcont.intervalIntegrable a b
  have hprim :
      AbsolutelyContinuousOnInterval
        (fun x => ∫ t in a..x, weightDeriv α t) a b :=
    hdint.absolutelyContinuousOnInterval_intervalIntegral
      left_mem_uIcc
  have hconst :
      AbsolutelyContinuousOnInterval
        (fun _ : ℝ => weight α a) a b :=
    (LipschitzWith.const (weight α a)).lipschitzOnWith
      |>.absolutelyContinuousOnInterval
  have hac :
      AbsolutelyContinuousOnInterval
        (fun x =>
          weight α a + ∫ t in a..x, weightDeriv α t) a b := by
    simpa only [Pi.add_apply] using hconst.add hprim
  have heq :
      (fun x =>
        weight α a + ∫ t in a..x, weightDeriv α t) =
        weight α := by
    funext x
    have hFTC :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := a) (b := x)
        (fun t _ => weight_hasDerivAt α t)
        (hdcont.intervalIntegrable a x)
    rw [hFTC]
    ring
  rwa [heq] at hac

private lemma weighted_partial_formula
    (f : ℝ → ℝ) (hf : AbelHypotheses f)
    (α b : ℝ) :
    (∫ x in (0 : ℝ)..b, weight α x * f x) =
      weight α b * primitive0 f b +
        α * ∫ x in (0 : ℝ)..b,
          weight α x * primitive0 f x := by
  let Q : ℝ → ℝ :=
    fun x => ∫ t in (0 : ℝ)..x, f t
  have hfab := hf.1 b
  have hQac :
      AbsolutelyContinuousOnInterval Q 0 b :=
    hfab.absolutelyContinuousOnInterval_intervalIntegral
      left_mem_uIcc
  have hwac := weight_absolutelyContinuous α 0 b
  have hparts :=
    hwac.integral_mul_deriv_eq_deriv_mul hQac
  have hleft :
      (∫ x in (0 : ℝ)..b, weight α x * deriv Q x) =
        ∫ x in (0 : ℝ)..b, weight α x * f x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hfab.ae_hasDerivAt_integral] with x hx hxu
    have hxu' : x ∈ uIcc (0 : ℝ) b :=
      uIoc_subset_uIcc hxu
    rw [(hx hxu' 0 left_mem_uIcc).deriv]
  have hright :
      (∫ x in (0 : ℝ)..b, deriv (weight α) x * Q x) =
        ∫ x in (0 : ℝ)..b, weightDeriv α x * Q x := by
    apply intervalIntegral.integral_congr
    intro x _
    change
      deriv (weight α) x * Q x =
        weightDeriv α x * Q x
    rw [(weight_hasDerivAt α x).deriv]
  rw [hleft, hright] at hparts
  have hQ0 : Q 0 = 0 := by
    simp [Q]
  rw [hQ0, mul_zero, sub_zero] at hparts
  have hconst :
      (∫ x in (0 : ℝ)..b, weightDeriv α x * Q x) =
        -α * ∫ x in (0 : ℝ)..b, weight α x * Q x := by
    unfold weightDeriv
    simpa only [mul_assoc] using
      intervalIntegral.integral_const_mul
        (-α) (fun x => weight α x * Q x)
  rw [hconst] at hparts
  change
    (∫ x in (0 : ℝ)..b, weight α x * f x) =
      weight α b * Q b +
        α * ∫ x in (0 : ℝ)..b, weight α x * Q x
  simpa [Q, primitive0] using (show
    (∫ x in (0 : ℝ)..b, weight α x * f x) =
      weight α b * Q b +
        α * ∫ x in (0 : ℝ)..b, weight α x * Q x by
      linarith)

private def kernel (f : ℝ → ℝ) (α x : ℝ) : ℝ :=
  α * weight α x * primitive0 f x

private def dampedValue (f : ℝ → ℝ) (α : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), kernel f α x

private lemma kernel_integrableOn
    (f : ℝ → ℝ) (hf : AbelHypotheses f)
    (M α : ℝ)
    (hM : ∀ x : ℝ, 0 ≤ x → |primitive0 f x| ≤ M)
    (hα : 0 < α) :
    IntegrableOn (kernel f α) (Ioi (0 : ℝ)) := by
  have hw :
      IntegrableOn (weight α) (Ioi (0 : ℝ)) := by
    convert
      (integrableOn_exp_mul_Ioi
        (show -α < 0 by linarith) 0) using 1
  have hPmeas :
      AEStronglyMeasurable (primitive0 f)
        (volume.restrict (Ioi (0 : ℝ))) :=
    (partial_continuous f hf).aestronglyMeasurable
  have hbound :
      ∀ᵐ x : ℝ ∂(volume.restrict (Ioi (0 : ℝ))),
        ‖primitive0 f x‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simpa [Real.norm_eq_abs] using hM x hx.le
  have hPw :
      Integrable
        (fun x => primitive0 f x * weight α x)
        (volume.restrict (Ioi (0 : ℝ))) :=
    hw.bdd_mul hPmeas hbound
  have hscaled := hPw.const_mul α
  change
    IntegrableOn
      (fun x => α * weight α x * primitive0 f x)
      (Ioi (0 : ℝ))
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hscaled

private lemma damped_hasImproperIntegral
    (f : ℝ → ℝ) (hf : AbelHypotheses f)
    (L M α : ℝ)
    (hL : HasImproperIntegralFrom f 0 L)
    (hM : ∀ x : ℝ, 0 ≤ x → |primitive0 f x| ≤ M)
    (hα : 0 < α) :
    HasImproperIntegralFrom (damped f α) 0
      (dampedValue f α) := by
  have hboundary :
      Tendsto
        (fun b => weight α b * primitive0 f b)
        atTop (𝓝 0) := by
    have hw :
        Tendsto (weight α) atTop (𝓝 0) := by
      have harg :
          Tendsto (fun x : ℝ => -α * x) atTop atBot := by
        simpa only [id_eq] using
          tendsto_id.const_mul_atTop_of_neg
            (neg_lt_zero.mpr hα)
      exact Real.tendsto_exp_atBot.comp harg
    unfold HasImproperIntegralFrom at hL
    change Tendsto (primitive0 f) atTop (𝓝 L) at hL
    simpa using hw.mul hL
  have hkint :=
    kernel_integrableOn f hf M α hM hα
  have hkernel :
      Tendsto
        (fun b : ℝ =>
          ∫ x in (0 : ℝ)..b, kernel f α x)
        atTop (𝓝 (dampedValue f α)) := by
    simpa [dampedValue] using
      (intervalIntegral_tendsto_integral_Ioi
        0 hkint tendsto_id)
  have hsum :=
    hboundary.add hkernel
  have hsum' :
      Tendsto
        (fun x =>
          weight α x * primitive0 f x +
            ∫ t in (0 : ℝ)..x, kernel f α t)
        atTop (𝓝 (dampedValue f α)) := by
    simpa using hsum
  unfold HasImproperIntegralFrom
  apply hsum'.congr'
  filter_upwards with b
  have hformula :=
    weighted_partial_formula f hf α b
  have hk :
      (∫ x in (0 : ℝ)..b, kernel f α x) =
        α * ∫ x in (0 : ℝ)..b,
          weight α x * primitive0 f x := by
    unfold kernel
    simpa only [mul_assoc] using
      intervalIntegral.integral_const_mul
        α (fun x => weight α x * primitive0 f x)
  rw [hk]
  simpa [damped, weight] using hformula.symm

private lemma damped_improperlyIntegrable
    (f : ℝ → ℝ) (hf : AbelHypotheses f)
    (α : ℝ) (hα : 0 ≤ α) :
    ImproperlyIntegrableFrom (damped f α) 0 := by
  have hL :=
    has_improperIntegralFrom_value f 0 hf.2
  rcases hα.eq_or_lt with rfl | hα
  · refine ⟨improperIntegralFrom f 0, ?_⟩
    have hd0 : damped f 0 = f := by
      funext x
      simp [damped]
    rw [hd0]
    exact hL
  · obtain ⟨M, hMpos, hM⟩ :=
      partial_bounded_nonneg f hf
        (improperIntegralFrom f 0) hL
    exact
      ⟨dampedValue f α,
        damped_hasImproperIntegral f hf
          (improperIntegralFrom f 0) M α hL hM hα⟩

private lemma damped_intervalIntegrable
    (f : ℝ → ℝ) (hf : AbelHypotheses f)
    (α a b : ℝ) :
    IntervalIntegrable (damped f α) volume a b := by
  have hw : Continuous (fun x : ℝ => Real.exp (-(α * x))) := by
    fun_prop
  simpa [damped] using
    (local_intervalIntegrable f hf a b).continuousOn_mul
      hw.continuousOn

private lemma dampedValue_scaled
    (f : ℝ → ℝ) (α : ℝ) (hα : 0 < α) :
    dampedValue f α =
      ∫ t in Ioi (0 : ℝ),
        Real.exp (-t) * primitive0 f (t / α) := by
  let g : ℝ → ℝ :=
    fun x => weight α x * primitive0 f x
  have hcv :=
    integral_comp_mul_left_Ioi g 0 (inv_pos.mpr hα)
  have hα0 : α ≠ 0 := ne_of_gt hα
  have hsimp :
      (fun t : ℝ => g (α⁻¹ * t)) =
        fun t : ℝ =>
          Real.exp (-t) * primitive0 f (t / α) := by
    funext t
    change
      Real.exp (-α * (α⁻¹ * t)) *
          primitive0 f (α⁻¹ * t) =
        Real.exp (-t) * primitive0 f (t / α)
    rw [show α⁻¹ * t = t / α by ring]
    rw [show -α * (t / α) = -t by field_simp]
  rw [hsimp] at hcv
  unfold dampedValue kernel
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  simpa [g, hα0, smul_eq_mul] using hcv.symm

private lemma dampedValue_tendsto
    (f : ℝ → ℝ) (hf : AbelHypotheses f)
    (L M : ℝ)
    (hL : HasImproperIntegralFrom f 0 L)
    (hM : ∀ x : ℝ, 0 ≤ x → |primitive0 f x| ≤ M) :
    Tendsto (dampedValue f) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  let F : ℝ → ℝ → ℝ :=
    fun α x =>
      Real.exp (-x) * primitive0 f (x / α)
  let B : ℝ → ℝ :=
    fun x => M * Real.exp (-x)
  have hFmeas :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
        AEStronglyMeasurable (F α)
          (volume.restrict (Ioi (0 : ℝ))) := by
    filter_upwards [self_mem_nhdsWithin] with α hα
    have hα0 : α ≠ 0 := ne_of_gt hα
    have hcdiv : Continuous (fun x : ℝ => x / α) := by
      fun_prop
    exact
      ((show Continuous (fun x : ℝ => Real.exp (-x)) by
          fun_prop).mul
        ((partial_continuous f hf).comp hcdiv))
        |>.aestronglyMeasurable
  have hbound :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
        ∀ᵐ x : ℝ ∂(volume.restrict (Ioi (0 : ℝ))),
          ‖F α x‖ ≤ B x := by
    filter_upwards [self_mem_nhdsWithin] with α hα
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    dsimp [F, B]
    rw [abs_mul,
      abs_of_pos (Real.exp_pos _)]
    have hPx :=
      hM (x / α) (div_nonneg hx.le hα.le)
    have hexp : 0 ≤ Real.exp (-x) :=
      (Real.exp_pos _).le
    nlinarith
  have hBint :
      Integrable B (volume.restrict (Ioi (0 : ℝ))) := by
    have hb :=
      (integrableOn_exp_neg_Ioi 0).const_mul M
    simpa [B] using hb
  have hlim :
      ∀ᵐ x : ℝ ∂(volume.restrict (Ioi (0 : ℝ))),
        Tendsto (fun α => F α x)
          (𝓝[>] (0 : ℝ))
          (𝓝 (Real.exp (-x) * L)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have harg :
        Tendsto (fun α : ℝ => x / α)
          (𝓝[>] (0 : ℝ)) atTop := by
      simpa [div_eq_mul_inv, mul_comm] using
        (tendsto_inv_nhdsGT_zero.atTop_mul_const
          (show 0 < x from hx))
    unfold HasImproperIntegralFrom at hL
    change Tendsto (primitive0 f) atTop (𝓝 L) at hL
    exact tendsto_const_nhds.mul (hL.comp harg)
  have hDCT :=
    tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Ioi (0 : ℝ)))
      B hFmeas hbound hBint hlim
  have htarget :
      (∫ x in Ioi (0 : ℝ), Real.exp (-x) * L) = L := by
    rw [integral_mul_const,
      integral_exp_neg_Ioi_zero, one_mul]
  rw [htarget] at hDCT
  apply hDCT.congr'
  filter_upwards [self_mem_nhdsWithin] with α hα
  exact (dampedValue_scaled f α hα).symm

private lemma abel_tendsto
    (f : ℝ → ℝ) (hf : AbelHypotheses f) :
    Tendsto
      (fun α : ℝ =>
        improperIntegralFrom (damped f α) 0)
      (𝓝[>] (0 : ℝ))
      (𝓝 (improperIntegralFrom f 0)) := by
  have hL :=
    has_improperIntegralFrom_value f 0 hf.2
  obtain ⟨M, hMpos, hM⟩ :=
    partial_bounded_nonneg f hf
      (improperIntegralFrom f 0) hL
  have hdv :=
    dampedValue_tendsto f hf
      (improperIntegralFrom f 0) M hL hM
  apply hdv.congr'
  filter_upwards [self_mem_nhdsWithin] with α hα
  have hhas :=
    damped_hasImproperIntegral f hf
      (improperIntegralFrom f 0) M α hL hM hα
  exact
    (improperIntegralFrom_eq_of_has
      (damped f α) 0 (dampedValue f α) hhas).symm

theorem gap1 (f : ℝ → ℝ) (hf : ImproperlyIntegrableFrom f 0) :
    ∃ L : ℝ, HasImproperIntegralFrom f 0 L := by
  exact hf

theorem gap2 (f : ℝ → ℝ) (hf : AbelHypotheses f)
    (α ε : ℝ) (hα : 0 ≤ α) (hε : 0 < ε) :
    ∃ η A₀ : ℝ, 0 < η ∧ 0 < A₀ ∧
      |∫ x in (0 : ℝ)..η, damped f α x| < ε / 5 ∧
      |improperIntegralFrom (damped f α) A₀| < ε / 5 := by
  have hd :=
    damped_improperlyIntegrable f hf α hα
  have hdHas :=
    has_improperIntegralFrom_value (damped f α) 0 hd
  have hleftCont :
      Continuous
        (fun η : ℝ =>
          ∫ x in (0 : ℝ)..η, damped f α x) :=
    intervalIntegral.continuous_primitive
      (fun a b => damped_intervalIntegrable f hf α a b) 0
  have hleftT :
      Tendsto
        (fun η : ℝ =>
          ∫ x in (0 : ℝ)..η, damped f α x)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hfull :=
      (hleftCont.continuousAt :
        Tendsto
          (fun η : ℝ =>
            ∫ x in (0 : ℝ)..η, damped f α x)
          (𝓝 0)
          (𝓝 (∫ x in (0 : ℝ)..(0 : ℝ),
            damped f α x)))
    simpa using hfull.mono_left inf_le_left
  have hleftEv :
      ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ),
        |∫ x in (0 : ℝ)..η, damped f α x| < ε / 5 := by
    have hdist :=
      (Metric.tendsto_nhds.1 hleftT)
        (ε / 5) (by positivity)
    simpa [Real.dist_eq] using hdist
  have hηmem :
      ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), 0 < η := by
    exact self_mem_nhdsWithin
  rcases (hleftEv.and hηmem).exists with
    ⟨η, hleft, hη⟩
  have htailT :
      Tendsto
        (improperIntegralFrom (damped f α))
        atTop (𝓝 0) :=
    improperIntegralFrom_tail_tendsto
      (damped f α)
      (fun A => damped_intervalIntegrable f hf α 0 A)
      (improperIntegralFrom (damped f α) 0) hdHas
  have htailEv :
      ∀ᶠ A : ℝ in atTop,
        |improperIntegralFrom (damped f α) A| < ε / 5 := by
    have hdist :=
      (Metric.tendsto_nhds.1 htailT)
        (ε / 5) (by positivity)
    simpa [Real.dist_eq] using hdist
  rcases
      (htailEv.and (eventually_gt_atTop (0 : ℝ))).exists with
    ⟨A₀, htail, hA₀⟩
  exact ⟨η, A₀, hη, hA₀, hleft, htail⟩

theorem gap3 (f : ℝ → ℝ) (x : ℝ) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ |f x| ≤ M₀ := by
  refine ⟨|f x| + 1, by positivity, ?_⟩
  linarith

theorem gap4 (η A₀ M₀ ε : ℝ) (hη : 0 ≤ η) (hηA₀ : η ≤ A₀)
    (hA₀ : 0 < A₀) (hM₀ : 0 < M₀) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ α : ℝ, 0 < α → α < δ →
        ∀ x ∈ Set.Icc η A₀,
          0 ≤ 1 - Real.exp (-(α * x)) ∧
            1 - Real.exp (-(α * x)) < ε / (5 * A₀ * M₀) := by
  let C : ℝ := ε / (5 * A₀ * M₀)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  let δ : ℝ := C / A₀
  have hδ : 0 < δ := div_pos hC hA₀
  refine ⟨δ, hδ, ?_⟩
  intro α hα hαδ x hx
  have hx0 : 0 ≤ x := hη.trans hx.1
  have ht0 : 0 ≤ α * x :=
    mul_nonneg hα.le hx0
  have hαA₀ : α * A₀ < C := by
    exact (lt_div_iff₀ hA₀).1 hαδ
  have hαx : α * x < C := by
    exact
      (mul_le_mul_of_nonneg_left hx.2 hα.le).trans_lt
        hαA₀
  constructor
  · exact
      sub_nonneg.mpr
        (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht0))
  · have hlinear :=
      Real.add_one_le_exp (-(α * x))
    linarith

theorem gap5 (f : ℝ → ℝ) (α η A₀ : ℝ)
    (hf : AbelHypotheses f)
    (hd : ImproperlyIntegrableFrom (damped f α) 0) :
    |improperIntegralFrom (damped f α) 0 - improperIntegralFrom f 0| =
      |(∫ x in η..A₀, (Real.exp (-(α * x)) - 1) * f x) +
        improperIntegralFrom (damped f α) A₀ -
        improperIntegralFrom f A₀ +
        (∫ x in (0 : ℝ)..η, damped f α x) -
        ∫ x in (0 : ℝ)..η, f x| := by
  have hfHas :=
    has_improperIntegralFrom_value f 0 hf.2
  have hdHas :=
    has_improperIntegralFrom_value (damped f α) 0 hd
  have htailF :=
    improperIntegralFrom_shift_eq
      f hf.1 (improperIntegralFrom f 0) A₀ hfHas
  have htailD :=
    improperIntegralFrom_shift_eq
      (damped f α)
      (fun A => damped_intervalIntegrable f hf α 0 A)
      (improperIntegralFrom (damped f α) 0) A₀ hdHas
  have hsplitF :=
    intervalIntegral.integral_add_adjacent_intervals
      (hf.1 η) (local_intervalIntegrable f hf η A₀)
  have hsplitD :=
    intervalIntegral.integral_add_adjacent_intervals
      (damped_intervalIntegrable f hf α 0 η)
      (damped_intervalIntegrable f hf α η A₀)
  have hmid :
      (∫ x in η..A₀,
        (Real.exp (-(α * x)) - 1) * f x) =
        (∫ x in η..A₀, damped f α x) -
          ∫ x in η..A₀, f x := by
    calc
      (∫ x in η..A₀,
          (Real.exp (-(α * x)) - 1) * f x) =
          ∫ x in η..A₀, damped f α x - f x := by
        apply intervalIntegral.integral_congr
        intro x _
        unfold damped
        ring
      _ = (∫ x in η..A₀, damped f α x) -
          ∫ x in η..A₀, f x := by
        exact
          intervalIntegral.integral_sub
            (damped_intervalIntegrable f hf α η A₀)
            (local_intervalIntegrable f hf η A₀)
  congr 1
  rw [htailD, htailF, hmid]
  linarith

theorem gap6 (f : ℝ → ℝ) (α η A₀ M₀ ε : ℝ)
    (hf : AbelHypotheses f)
    (hd : ImproperlyIntegrableFrom (damped f α) 0)
    (hη : 0 ≤ η) (hηA₀ : η ≤ A₀) (hA₀ : 0 < A₀)
    (hM₀ : 0 < M₀) (hε : 0 < ε)
    (hbound : ∀ x ∈ Set.Icc η A₀, |f x| ≤ M₀)
    (hexp : ∀ x ∈ Set.Icc η A₀,
      |Real.exp (-(α * x)) - 1| < ε / (5 * A₀ * M₀))
    (hleftD : |∫ x in (0 : ℝ)..η, damped f α x| < ε / 5)
    (hleft : |∫ x in (0 : ℝ)..η, f x| < ε / 5)
    (htailD : |improperIntegralFrom (damped f α) A₀| < ε / 5)
    (htail : |improperIntegralFrom f A₀| < ε / 5) :
    |improperIntegralFrom (damped f α) 0 - improperIntegralFrom f 0| <
      M₀ * A₀ * (ε / (5 * A₀ * M₀)) +
        ε / 5 + ε / 5 + ε / 5 + ε / 5 := by
  let C : ℝ := ε / (5 * A₀ * M₀)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  let mid : ℝ :=
    ∫ x in η..A₀,
      (Real.exp (-(α * x)) - 1) * f x
  have hpoint :
      ∀ x ∈ Ι η A₀,
        ‖(Real.exp (-(α * x)) - 1) * f x‖ ≤
          M₀ * C := by
    intro x hx
    have hxI : x ∈ Icc η A₀ := by
      have hxU : x ∈ uIcc η A₀ :=
        uIoc_subset_uIcc hx
      simpa [uIcc, hηA₀] using hxU
    rw [Real.norm_eq_abs, abs_mul]
    have he := (hexp x hxI).le
    have hfx := hbound x hxI
    calc
      |Real.exp (-(α * x)) - 1| * |f x| ≤ C * M₀ :=
        mul_le_mul he hfx (abs_nonneg _) hC.le
      _ = M₀ * C := by ring
  have hmid :
      |mid| ≤ M₀ * A₀ * C := by
    have hnorm :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        hpoint
    rw [Real.norm_eq_abs] at hnorm
    have hlen :
        |A₀ - η| = A₀ - η :=
      abs_of_nonneg (sub_nonneg.mpr hηA₀)
    calc
      |mid| ≤ (M₀ * C) * |A₀ - η| := by
        exact hnorm
      _ = (M₀ * C) * (A₀ - η) := by
        rw [hlen]
      _ ≤ (M₀ * C) * A₀ := by
        exact
          mul_le_mul_of_nonneg_left
            (by linarith) (mul_nonneg hM₀.le hC.le)
      _ = M₀ * A₀ * C := by ring
  have hid :=
    gap5 f α η A₀ hf hd
  rw [hid]
  have htri :
      |mid +
          improperIntegralFrom (damped f α) A₀ -
          improperIntegralFrom f A₀ +
          (∫ x in (0 : ℝ)..η, damped f α x) -
          ∫ x in (0 : ℝ)..η, f x| ≤
        |mid| +
          |improperIntegralFrom (damped f α) A₀| +
          |improperIntegralFrom f A₀| +
          |∫ x in (0 : ℝ)..η, damped f α x| +
          |∫ x in (0 : ℝ)..η, f x| := by
    have h₁ :=
      abs_sub
        (mid +
          improperIntegralFrom (damped f α) A₀ -
          improperIntegralFrom f A₀ +
          (∫ x in (0 : ℝ)..η, damped f α x))
        (∫ x in (0 : ℝ)..η, f x)
    have h₂ :=
      abs_add_le
        (mid +
          improperIntegralFrom (damped f α) A₀ -
          improperIntegralFrom f A₀)
        (∫ x in (0 : ℝ)..η, damped f α x)
    have h₃ :=
      abs_sub
        (mid + improperIntegralFrom (damped f α) A₀)
        (improperIntegralFrom f A₀)
    have h₄ :=
      abs_add_le mid
        (improperIntegralFrom (damped f α) A₀)
    linarith
  calc
    |mid +
        improperIntegralFrom (damped f α) A₀ -
        improperIntegralFrom f A₀ +
        (∫ x in (0 : ℝ)..η, damped f α x) -
        ∫ x in (0 : ℝ)..η, f x| ≤
      |mid| +
        |improperIntegralFrom (damped f α) A₀| +
        |improperIntegralFrom f A₀| +
        |∫ x in (0 : ℝ)..η, damped f α x| +
        |∫ x in (0 : ℝ)..η, f x| := htri
    _ < M₀ * A₀ * C +
        ε / 5 + ε / 5 + ε / 5 + ε / 5 := by
      linarith
    _ = M₀ * A₀ * (ε / (5 * A₀ * M₀)) +
        ε / 5 + ε / 5 + ε / 5 + ε / 5 := by
      rfl

theorem gap7 (M₀ A₀ ε : ℝ) (hM₀ : 0 < M₀) (hA₀ : 0 < A₀) :
    M₀ * A₀ * (ε / (5 * A₀ * M₀)) +
        ε / 5 + ε / 5 + ε / 5 + ε / 5 = ε := by
  field_simp [hM₀.ne', hA₀.ne']
  ring

theorem gap8 (f : ℝ → ℝ) (hf : AbelHypotheses f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ α : ℝ, 0 < α → α < δ →
        |improperIntegralFrom (damped f α) 0 -
          improperIntegralFrom f 0| < ε := by
  have ht :=
    abel_tendsto f hf
  rw [Metric.tendsto_nhdsWithin_nhds] at ht
  rcases ht ε hε with ⟨δ, hδ, hclose⟩
  refine ⟨δ, hδ, ?_⟩
  intro α hα hαδ
  have hdist : dist α 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hα]
    exact hαδ
  have hv := hclose hα hdist
  simpa [Real.dist_eq] using hv

theorem gap9 (f : ℝ → ℝ) (hf : AbelHypotheses f) :
    Tendsto (fun α : ℝ => improperIntegralFrom (damped f α) 0)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (improperIntegralFrom f 0)) := by
  exact abel_tendsto f hf

theorem gap10 (f : ℝ → ℝ) (hf : AbelHypotheses f) :
    Tendsto (fun α : ℝ => improperIntegralFrom (damped f α) 0)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (improperIntegralFrom f 0)) := by
  exact gap9 f hf

end

end ProofGap.Exercise3773
