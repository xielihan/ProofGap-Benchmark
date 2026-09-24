import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod

namespace ProofGap.Exercise3881

noncomputable section

open Filter MeasureTheory Set
open scoped Interval Topology

private def fourierValue (x : ℝ) : ℝ :=
  if |x| < 1 then 1 else if 1 < |x| then 0 else 1 / 2

private def ImproperHasValue (g : ℝ → ℝ) (L : ℝ) : Prop :=
  Tendsto (fun R => ∫ lam in (0 : ℝ)..R, g lam) atTop (𝓝 L)

def HasImproperIntegral (a : ℝ) (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Tendsto (fun b : ℝ => ∫ x in a..b, f x) atTop (nhds L)

def improperIntegral (a : ℝ) (f : ℝ → ℝ) : ℝ :=
  sInf {L : ℝ | HasImproperIntegral a f L}

def boxFunction (x : ℝ) : ℝ :=
  if |x| < 1 then 1 else 0

def PiecewiseContinuousAtUnit (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Iio (-1)) ∧
    ContinuousOn f (Set.Ioo (-1) 1) ∧
      ContinuousOn f (Set.Ioi 1)

def cosineCoefficient (f : ℝ → ℝ) (lam : ℝ) : ℝ :=
  2 / Real.pi * improperIntegral 0
    (fun ξ => f ξ * Real.cos (lam * ξ))

def sineCoefficient (f : ℝ → ℝ) (lam : ℝ) : ℝ :=
  1 / Real.pi * ∫ ξ : ℝ, f ξ * Real.sin (lam * ξ)

private def dirichletTailKernel (x : ℝ) : ℝ :=
  Real.cos x / x ^ 2

private def dirichletLimit : ℝ :=
  (∫ x in (0 : ℝ)..1, Real.sinc x) + Real.cos 1 -
    ∫ x in Set.Ioi (1 : ℝ), dirichletTailKernel x

private lemma integrableOn_dirichletTailKernel :
    IntegrableOn dirichletTailKernel (Set.Ioi (1 : ℝ)) := by
  have hrpow :
      IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Set.Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  refine hrpow.mono'
    (by
      exact
        (show ContinuousOn dirichletTailKernel (Set.Ioi (1 : ℝ)) by
          unfold dirichletTailKernel
          exact Real.continuous_cos.continuousOn.div
            (continuousOn_id.pow 2)
            (fun x hx => pow_ne_zero 2
              (ne_of_gt (zero_lt_one.trans hx)))).aestronglyMeasurable
          measurableSet_Ioi)
    ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : 0 < x := zero_lt_one.trans hx
  unfold dirichletTailKernel
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (sq_pos_of_pos hxpos)]
  have hcos := Real.abs_cos_le_one x
  calc
    |Real.cos x| / x ^ 2 ≤ 1 / x ^ 2 :=
      div_le_div_of_nonneg_right hcos (sq_nonneg x)
    _ = x ^ (-2 : ℝ) := by
      rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
        Real.rpow_neg (le_of_lt hxpos), Real.rpow_two]
      simp [one_div]

private lemma sinc_eq_source_ae :
    ∀ᵐ x : ℝ ∂volume, Real.sinc x = Real.sin x / x := by
  filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
  exact Real.sinc_of_ne_zero hx

private lemma integral_sinc_eq_source (b : ℝ) :
    (∫ x in (0 : ℝ)..b, Real.sinc x) =
      ∫ x in (0 : ℝ)..b, Real.sin x / x := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [sinc_eq_source_ae] with x hx _
  exact hx

private lemma dirichlet_partial_formula (b : ℝ) (hb : 1 ≤ b) :
    (∫ x in (0 : ℝ)..b, Real.sinc x) =
      (∫ x in (0 : ℝ)..1, Real.sinc x) + Real.cos 1 -
        Real.cos b / b -
        ∫ x in (1 : ℝ)..b, dirichletTailKernel x := by
  have hsplit :
      (∫ x in (0 : ℝ)..b, Real.sinc x) =
        (∫ x in (0 : ℝ)..1, Real.sinc x) +
          ∫ x in (1 : ℝ)..b, Real.sinc x := by
    rw [← intervalIntegral.integral_add_adjacent_intervals]
    · exact Real.continuous_sinc.intervalIntegrable (μ := volume) 0 1
    · exact Real.continuous_sinc.intervalIntegrable (μ := volume) 1 b
  have hsinc :
      (∫ x in (1 : ℝ)..b, Real.sinc x) =
        ∫ x in (1 : ℝ)..b, (1 / x) * Real.sin x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hxbounds : x ∈ Set.Icc (1 : ℝ) b := by
      simpa [Set.uIcc_of_le hb] using hx
    have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans_le hxbounds.1)
    rw [Real.sinc_of_ne_zero hx0]
    ring
  have hparts :
      (∫ x in (1 : ℝ)..b, (1 / x) * Real.sin x) =
        Real.cos 1 - Real.cos b / b -
          ∫ x in (1 : ℝ)..b, dirichletTailKernel x := by
    have hu'cont :
        ContinuousOn (fun x : ℝ => (-1 : ℝ) / x ^ 2) [[(1 : ℝ), b]] := by
      exact
        (show ContinuousOn (fun _ : ℝ => (-1 : ℝ)) [[(1 : ℝ), b]] from
            continuousOn_const).div
          (continuousOn_id.pow 2)
          (fun x hx => by
            have hxbounds : x ∈ Set.Icc (1 : ℝ) b := by
              simpa [Set.uIcc_of_le hb] using hx
            exact pow_ne_zero 2 (ne_of_gt
              (zero_lt_one.trans_le hxbounds.1)))
    have hu'int :
        IntervalIntegrable (fun x : ℝ => (-1 : ℝ) / x ^ 2)
          volume 1 b :=
      hu'cont.intervalIntegrable
    have hv'int :
        IntervalIntegrable (fun x : ℝ => Real.sin x) volume 1 b :=
      Real.continuous_sin.intervalIntegrable 1 b
    have h :=
      intervalIntegral.integral_mul_deriv_eq_deriv_mul
        (a := (1 : ℝ)) (b := b)
        (u := fun x : ℝ => 1 / x)
        (u' := fun x : ℝ => (-1 : ℝ) / x ^ 2)
        (v := fun x : ℝ => -Real.cos x)
        (v' := fun x : ℝ => Real.sin x)
        (fun x hx => by
          have hxbounds : x ∈ Set.Icc (1 : ℝ) b := by
            simpa [Set.uIcc_of_le hb] using hx
          have hx0 : x ≠ 0 := ne_of_gt
            (zero_lt_one.trans_le hxbounds.1)
          convert hasDerivAt_inv hx0 using 1 <;> field_simp)
        (fun x _ => by simpa using Real.hasDerivAt_cos x |>.neg)
        hu'int hv'int
    have htailEq :
        (∫ x in (1 : ℝ)..b, ((-1 : ℝ) / x ^ 2) * (-Real.cos x)) =
          ∫ x in (1 : ℝ)..b, dirichletTailKernel x := by
      apply intervalIntegral.integral_congr
      intro x _
      unfold dirichletTailKernel
      ring
    rw [htailEq] at h
    convert h using 1 <;> ring
  rw [hsplit, hsinc, hparts]
  ring

private lemma tendsto_cos_div_atTop :
    Tendsto (fun b : ℝ => Real.cos b / b) atTop (𝓝 0) := by
  apply tendsto_bdd_div_atTop_nhds_zero
  · filter_upwards with b
    exact (abs_le.mp (Real.abs_cos_le_one b)).1
  · filter_upwards with b
    exact (abs_le.mp (Real.abs_cos_le_one b)).2
  · exact tendsto_id

private lemma sinc_partial_tendsto_dirichletLimit :
    Tendsto (fun b : ℝ => ∫ x in (0 : ℝ)..b, Real.sinc x)
      atTop (𝓝 dirichletLimit) := by
  have htail :
      Tendsto
        (fun b : ℝ => ∫ x in (1 : ℝ)..b, dirichletTailKernel x)
        atTop
        (𝓝 (∫ x in Set.Ioi (1 : ℝ), dirichletTailKernel x)) :=
    intervalIntegral_tendsto_integral_Ioi 1
      integrableOn_dirichletTailKernel tendsto_id
  have hlim :
      Tendsto
        (fun b : ℝ =>
          (∫ x in (0 : ℝ)..1, Real.sinc x) + Real.cos 1 -
            Real.cos b / b -
            ∫ x in (1 : ℝ)..b, dirichletTailKernel x)
        atTop (𝓝 dirichletLimit) := by
    have hbase :
        Tendsto
          (fun _ : ℝ =>
            (∫ x in (0 : ℝ)..1, Real.sinc x) + Real.cos 1)
          atTop
          (𝓝 ((∫ x in (0 : ℝ)..1, Real.sinc x) + Real.cos 1)) :=
      tendsto_const_nhds
    simpa [dirichletLimit] using
      (hbase.sub tendsto_cos_div_atTop).sub htail
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb
  exact (dirichlet_partial_formula b hb).symm

private lemma source_partial_tendsto_dirichletLimit :
    Tendsto (fun b : ℝ => ∫ x in (0 : ℝ)..b, Real.sin x / x)
      atTop (𝓝 dirichletLimit) := by
  apply sinc_partial_tendsto_dirichletLimit.congr'
  filter_upwards with b
  exact integral_sinc_eq_source b

private def dampedKernel (t x : ℝ) : ℝ :=
  Real.exp (-t * x) * Real.sinc x

private def dampedProduct (t s x : ℝ) : ℝ :=
  Real.exp (-t * x) * Real.cos (s * x)

private lemma integrableOn_dampedKernel {t : ℝ} (ht : 0 < t) :
    IntegrableOn (dampedKernel t) (Set.Ioi (0 : ℝ)) := by
  have hexp :
      IntegrableOn (fun x : ℝ => Real.exp ((-t) * x))
        (Set.Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_Ioi (neg_neg_of_pos ht) 0
  refine hexp.mono'
    (by
      exact
        (show Continuous (dampedKernel t) by
          unfold dampedKernel
          fun_prop).aestronglyMeasurable)
    ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  unfold dampedKernel
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-t * x) * |Real.sinc x| ≤ Real.exp (-t * x) * 1 :=
      mul_le_mul_of_nonneg_left
        (Real.abs_sinc_le_one x) (Real.exp_pos _).le
    _ = Real.exp (-t * x) := mul_one _

private lemma integrable_dampedProduct {t : ℝ} (ht : 0 < t) :
    Integrable
      (Function.uncurry (dampedProduct t))
      ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod
        (volume.restrict (Set.Ioi (0 : ℝ)))) := by
  have hs :
      Integrable (fun _ : ℝ => (1 : ℝ))
        (volume.restrict (Set.uIoc (0 : ℝ) 1)) :=
    (by
      simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        (integrableOn_const (C := (1 : ℝ)) measure_Ioc_lt_top.ne :
          IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 1)))
  have hx :
      Integrable (fun x : ℝ => Real.exp ((-t) * x))
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
    integrableOn_exp_mul_Ioi (neg_neg_of_pos ht) 0
  have hbase := hs.mul_prod hx
  refine hbase.mono'
    (by
      exact
        (show Continuous (Function.uncurry (dampedProduct t)) by
          unfold dampedProduct Function.uncurry
          fun_prop).aestronglyMeasurable)
    ?_
  filter_upwards with z
  unfold dampedProduct Function.uncurry
  simp only [one_mul, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-t * z.2) * |Real.cos (z.1 * z.2)| ≤
        Real.exp (-t * z.2) * 1 :=
      mul_le_mul_of_nonneg_left
        (Real.abs_cos_le_one (z.1 * z.2)) (Real.exp_pos _).le
    _ = Real.exp (-t * z.2) := mul_one _

private lemma integral_cos_scale (x : ℝ) (hx : x ≠ 0) :
    (∫ s in (0 : ℝ)..1, Real.cos (s * x)) =
      Real.sin x / x := by
  have h :=
    intervalIntegral.mul_integral_comp_mul_right
      (f := Real.cos) (a := (0 : ℝ)) (b := 1) (c := x)
  rw [integral_cos] at h
  simp only [zero_mul, one_mul, Real.sin_zero, sub_zero] at h
  apply (eq_div_iff hx).2
  simpa [mul_comm] using h

private lemma integral_damped_cos {t : ℝ} (ht : 0 < t) (s : ℝ) :
    (∫ x in Set.Ioi (0 : ℝ),
      Real.exp (-t * x) * Real.cos (s * x)) =
        t / (t ^ 2 + s ^ 2) := by
  have hden : 0 < t ^ 2 + s ^ 2 := by
    nlinarith [sq_pos_of_pos ht, sq_nonneg s]
  let P : ℝ → ℝ := fun x =>
    Real.exp (-t * x) *
        (-t * Real.cos (s * x) + s * Real.sin (s * x)) /
      (t ^ 2 + s ^ 2)
  have hderiv : ∀ x : ℝ,
      HasDerivAt P
        (Real.exp (-t * x) * Real.cos (s * x)) x := by
    intro x
    have hlin_t : HasDerivAt (fun y : ℝ => -t * y) (-t) x :=
      by simpa only [id_eq, mul_one] using
        (hasDerivAt_id x).const_mul (-t)
    have hlin_s : HasDerivAt (fun y : ℝ => s * y) s x :=
      by simpa only [id_eq, mul_one] using
        (hasDerivAt_id x).const_mul s
    have hexp :
        HasDerivAt (fun y : ℝ => Real.exp (-t * y))
          (-t * Real.exp (-t * x)) x := by
      convert (Real.hasDerivAt_exp (-t * x)).comp x hlin_t using 1
      ring
    have hcos :
        HasDerivAt (fun y : ℝ => Real.cos (s * y))
          (-s * Real.sin (s * x)) x := by
      convert (Real.hasDerivAt_cos (s * x)).comp x hlin_s using 1
      ring
    have hsin :
        HasDerivAt (fun y : ℝ => Real.sin (s * y))
          (s * Real.cos (s * x)) x := by
      convert (Real.hasDerivAt_sin (s * x)).comp x hlin_s using 1
      ring
    have hnum :=
      (hcos.const_mul (-t)).add (hsin.const_mul s)
    dsimp [P]
    convert (hexp.mul hnum).div_const (t ^ 2 + s ^ 2) using 1
    dsimp only [Pi.add_apply]
    field_simp [hden.ne']
    ring
  have hint :
      IntegrableOn
        (fun x : ℝ => Real.exp (-t * x) * Real.cos (s * x))
        (Set.Ioi (0 : ℝ)) := by
    have hexp :
        IntegrableOn (fun x : ℝ => Real.exp ((-t) * x))
          (Set.Ioi (0 : ℝ)) :=
      integrableOn_exp_mul_Ioi (neg_neg_of_pos ht) 0
    refine hexp.mono'
      (by
        exact
          (show Continuous
              (fun x : ℝ => Real.exp (-t * x) * Real.cos (s * x)) by
            fun_prop).aestronglyMeasurable)
      ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp only [Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-t * x) * |Real.cos (s * x)| ≤
          Real.exp (-t * x) * 1 :=
        mul_le_mul_of_nonneg_left
          (Real.abs_cos_le_one (s * x)) (Real.exp_pos _).le
      _ = Real.exp (-t * x) := mul_one _
  have hexp0 :
      Tendsto (fun x : ℝ => Real.exp (-t * x)) atTop (𝓝 0) := by
    exact Real.tendsto_exp_atBot.comp
      (tendsto_const_nhds.neg_mul_atTop (neg_neg_of_pos ht) tendsto_id)
  have hcos0 :
      Tendsto
        (fun x : ℝ => Real.exp (-t * x) * Real.cos (s * x))
        atTop (𝓝 0) := by
    have h :=
      bdd_le_mul_tendsto_zero
        (show ∀ᶠ x : ℝ in atTop, (-1 : ℝ) ≤ Real.cos (s * x) by
          filter_upwards with x
          exact (abs_le.mp (Real.abs_cos_le_one (s * x))).1)
        (show ∀ᶠ x : ℝ in atTop, Real.cos (s * x) ≤ (1 : ℝ) by
          filter_upwards with x
          exact (abs_le.mp (Real.abs_cos_le_one (s * x))).2)
        hexp0
    simpa [mul_comm] using h
  have hsin0 :
      Tendsto
        (fun x : ℝ => Real.exp (-t * x) * Real.sin (s * x))
        atTop (𝓝 0) := by
    have h :=
      bdd_le_mul_tendsto_zero
        (show ∀ᶠ x : ℝ in atTop, (-1 : ℝ) ≤ Real.sin (s * x) by
          filter_upwards with x
          exact (abs_le.mp (Real.abs_sin_le_one (s * x))).1)
        (show ∀ᶠ x : ℝ in atTop, Real.sin (s * x) ≤ (1 : ℝ) by
          filter_upwards with x
          exact (abs_le.mp (Real.abs_sin_le_one (s * x))).2)
        hexp0
    simpa [mul_comm] using h
  have hP0 : Tendsto P atTop (𝓝 0) := by
    have hsum :=
      (hcos0.const_mul (-t / (t ^ 2 + s ^ 2))).add
        (hsin0.const_mul (s / (t ^ 2 + s ^ 2)))
    have hsum0 :
        Tendsto
          (fun x : ℝ =>
            (-t / (t ^ 2 + s ^ 2)) *
                (Real.exp (-t * x) * Real.cos (s * x)) +
              (s / (t ^ 2 + s ^ 2)) *
                (Real.exp (-t * x) * Real.sin (s * x)))
          atTop (𝓝 0) := by
      simpa using hsum
    apply hsum0.congr'
    filter_upwards with x
    dsimp [P]
    field_simp [hden.ne']
  have hFTC :=
    integral_Ioi_of_hasDerivAt_of_tendsto'
      (a := (0 : ℝ)) (m := (0 : ℝ))
      (fun x _ => hderiv x) hint hP0
  rw [hFTC]
  simp [P]
  ring

private lemma dampedIntegral_formula {t : ℝ} (ht : 0 < t) :
    (∫ x in Set.Ioi (0 : ℝ), dampedKernel t x) =
      Real.arctan (1 / t) := by
  calc
    (∫ x in Set.Ioi (0 : ℝ), dampedKernel t x) =
        ∫ x in Set.Ioi (0 : ℝ),
          Real.exp (-t * x) *
            (∫ s in (0 : ℝ)..1, Real.cos (s * x)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change Real.exp (-t * x) * Real.sinc x =
        Real.exp (-t * x) *
          (∫ s in (0 : ℝ)..1, Real.cos (s * x))
      rw [integral_cos_scale x (ne_of_gt hx)]
      rw [Real.sinc_of_ne_zero (ne_of_gt hx)]
    _ = ∫ x in Set.Ioi (0 : ℝ),
          ∫ s in (0 : ℝ)..1, dampedProduct t s x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      change Real.exp (-t * x) *
          (∫ s in (0 : ℝ)..1, Real.cos (s * x)) =
        ∫ s in (0 : ℝ)..1, dampedProduct t s x
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s _
      rfl
    _ = ∫ s in (0 : ℝ)..1,
          ∫ x in Set.Ioi (0 : ℝ), dampedProduct t s x := by
      exact
        (intervalIntegral_integral_swap
          (μ := volume.restrict (Set.Ioi (0 : ℝ)))
          (integrable_dampedProduct ht)).symm
    _ = ∫ s in (0 : ℝ)..1, t / (t ^ 2 + s ^ 2) := by
      apply intervalIntegral.integral_congr
      intro s _
      exact integral_damped_cos ht s
    _ = Real.arctan (1 / t) := by
      rw [integral_div_sq_add_sq]
      simp

private def sincPartial (x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..x, Real.sinc u

private lemma sincPartial_tendsto :
    Tendsto sincPartial atTop (𝓝 dirichletLimit) := by
  exact sinc_partial_tendsto_dirichletLimit

private lemma hasDerivAt_sincPartial (x : ℝ) :
    HasDerivAt sincPartial (Real.sinc x) x := by
  unfold sincPartial
  exact intervalIntegral.integral_hasDerivAt_right
    (Real.continuous_sinc.intervalIntegrable 0 x)
    Real.continuous_sinc.aestronglyMeasurable.stronglyMeasurableAtFilter
    Real.continuous_sinc.continuousAt

private lemma continuous_sincPartial :
    Continuous sincPartial :=
  continuous_iff_continuousAt.2
    (fun x => (hasDerivAt_sincPartial x).continuousAt)

private lemma exists_sincPartial_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x → |sincPartial x| ≤ C := by
  have hev :
      ∀ᶠ x : ℝ in atTop,
        dist (sincPartial x) dirichletLimit < 1 :=
    sincPartial_tendsto.eventually
      (Metric.ball_mem_nhds dirichletLimit zero_lt_one)
  rcases eventually_atTop.1 hev with ⟨A, hA⟩
  let C : ℝ := max |A| (|dirichletLimit| + 1)
  have hC : 0 < C := by
    dsimp [C]
    exact lt_of_lt_of_le (by positivity)
      (le_max_right |A| (|dirichletLimit| + 1))
  refine ⟨C, hC, ?_⟩
  intro x hx
  by_cases hAx : A ≤ x
  · have hdist := hA x hAx
    have htri :
        |sincPartial x| ≤
          |sincPartial x - dirichletLimit| + |dirichletLimit| := by
      calc
        |sincPartial x| =
            |(sincPartial x - dirichletLimit) + dirichletLimit| := by ring_nf
        _ ≤ |sincPartial x - dirichletLimit| + |dirichletLimit| :=
          abs_add_le _ _
    have hsmall :
        |sincPartial x - dirichletLimit| < 1 := by
      simpa [Real.dist_eq] using hdist
    have hsum :
        |sincPartial x - dirichletLimit| + |dirichletLimit| ≤
          |dirichletLimit| + 1 := by
      linarith
    exact htri.trans
      (hsum.trans (le_max_right |A| (|dirichletLimit| + 1)))
  · have hxA : x < A := lt_of_not_ge hAx
    have hnorm :
        |sincPartial x| ≤ (1 : ℝ) * |x - 0| := by
      unfold sincPartial
      simpa [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_of_norm_le_const
          (a := (0 : ℝ)) (b := x) (C := (1 : ℝ))
          (f := Real.sinc)
          (fun u _ => by
            simpa [Real.norm_eq_abs] using Real.abs_sinc_le_one u))
    have hxleA : x ≤ |A| := by
      exact hxA.le.trans (le_abs_self A)
    calc
      |sincPartial x| ≤ x := by
        simpa [abs_of_pos hx] using hnorm
      _ ≤ |A| := hxleA
      _ ≤ C := le_max_left _ _

private lemma abel_identity {t : ℝ} (ht : 0 < t) :
    (∫ x in Set.Ioi (0 : ℝ), dampedKernel t x) =
      t * ∫ x in Set.Ioi (0 : ℝ),
        Real.exp (-t * x) * sincPartial x := by
  rcases exists_sincPartial_bound with ⟨C, hC, hbound⟩
  have hexp :
      IntegrableOn (fun x : ℝ => Real.exp ((-t) * x))
        (Set.Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_Ioi (neg_neg_of_pos ht) 0
  have hu'v :
      IntegrableOn
        (fun x : ℝ => (-t * Real.exp (-t * x)) * sincPartial x)
        (Set.Ioi (0 : ℝ)) := by
    have hmajorant :
        IntegrableOn
          (fun x : ℝ => (t * C) * Real.exp ((-t) * x))
          (Set.Ioi (0 : ℝ)) :=
      hexp.const_mul (t * C)
    refine hmajorant.mono'
      (by
        exact
          ((show Continuous
              (fun x : ℝ => -t * Real.exp (-t * x)) by
                fun_prop).mul
            continuous_sincPartial).aestronglyMeasurable)
      ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg,
      abs_of_pos ht, abs_of_pos (Real.exp_pos _)]
    calc
      t * Real.exp (-t * x) * |sincPartial x| ≤
          t * Real.exp (-t * x) * C :=
        mul_le_mul_of_nonneg_left (hbound x hx0)
          (mul_nonneg ht.le (Real.exp_pos _).le)
      _ = t * C * Real.exp (-t * x) := by ring
  have hu : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => Real.exp (-t * y))
        (-t * Real.exp (-t * x)) x := by
    intro x _
    convert (Real.hasDerivAt_exp (-t * x)).comp x
      ((hasDerivAt_id x).const_mul (-t)) using 1 <;> ring
  have hv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt sincPartial (Real.sinc x) x :=
    fun x _ => hasDerivAt_sincPartial x
  have hzero :
      Tendsto
        ((fun x : ℝ => Real.exp (-t * x)) * sincPartial)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc :
        Tendsto
          ((fun x : ℝ => Real.exp (-t * x)) * sincPartial)
          (𝓝 (0 : ℝ))
          (𝓝 (((fun x : ℝ => Real.exp (-t * x)) * sincPartial) 0)) :=
      ((show Continuous (fun x : ℝ => Real.exp (-t * x)) by
          fun_prop).mul continuous_sincPartial).continuousAt
    simpa [sincPartial] using hc.mono_left inf_le_left
  have hexp0 :
      Tendsto (fun x : ℝ => Real.exp (-t * x)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_const_nhds.neg_mul_atTop (neg_neg_of_pos ht) tendsto_id)
  have hinfty :
      Tendsto
        ((fun x : ℝ => Real.exp (-t * x)) * sincPartial)
        atTop (𝓝 0) := by
    have hmul :=
      bdd_le_mul_tendsto_zero
        (show ∀ᶠ x : ℝ in atTop, -C ≤ sincPartial x by
          filter_upwards [Ioi_mem_atTop (0 : ℝ)] with x hx
          exact (abs_le.mp (hbound x hx)).1)
        (show ∀ᶠ x : ℝ in atTop, sincPartial x ≤ C by
          filter_upwards [Ioi_mem_atTop (0 : ℝ)] with x hx
          exact (abs_le.mp (hbound x hx)).2)
        hexp0
    apply hmul.congr'
    filter_upwards with x
    simp only [Pi.mul_apply]
    ring
  have hparts :=
    integral_Ioi_mul_deriv_eq_deriv_mul
      (a := (0 : ℝ))
      (u := fun x : ℝ => Real.exp (-t * x))
      (u' := fun x : ℝ => -t * Real.exp (-t * x))
      (v := sincPartial)
      (v' := Real.sinc)
      hu hv (integrableOn_dampedKernel ht) hu'v hzero hinfty
  unfold dampedKernel at hparts ⊢
  rw [show
      (∫ x in Set.Ioi (0 : ℝ),
          (-t * Real.exp (-t * x)) * sincPartial x) =
        -t * ∫ x in Set.Ioi (0 : ℝ),
          Real.exp (-t * x) * sincPartial x by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    ring] at hparts
  linarith

private lemma abel_change_variables {t : ℝ} (ht : 0 < t) :
    t * ∫ x in Set.Ioi (0 : ℝ),
        Real.exp (-t * x) * sincPartial x =
      ∫ u in Set.Ioi (0 : ℝ),
        Real.exp (-u) * sincPartial (u / t) := by
  let g : ℝ → ℝ := fun u =>
    Real.exp (-u) * sincPartial (u / t)
  have h :=
    integral_comp_mul_left_Ioi g 0 ht
  have hleft :
      (∫ x in Set.Ioi (0 : ℝ), g (t * x)) =
        ∫ x in Set.Ioi (0 : ℝ),
          Real.exp (-t * x) * sincPartial x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    dsimp [g]
    rw [mul_div_cancel_left₀ x ht.ne']
    congr 2
    ring
  rw [hleft] at h
  change
    t * ∫ x in Set.Ioi (0 : ℝ),
        Real.exp (-t * x) * sincPartial x =
      ∫ u in Set.Ioi (0 : ℝ), g u
  rw [h]
  simp [smul_eq_mul, ht.ne']

private lemma abel_integrals_tendsto :
    Tendsto
      (fun t : ℝ =>
        ∫ u in Set.Ioi (0 : ℝ),
          Real.exp (-u) * sincPartial (u / t))
      (𝓝[>] (0 : ℝ)) (𝓝 dirichletLimit) := by
  rcases exists_sincPartial_bound with ⟨C, hC, hbound⟩
  let F : ℝ → ℝ → ℝ := fun t u =>
    Real.exp (-u) * sincPartial (u / t)
  let bound : ℝ → ℝ := fun u => C * Real.exp (-u)
  have hbound_int :
      Integrable bound (volume.restrict (Set.Ioi (0 : ℝ))) := by
    exact (integrableOn_exp_neg_Ioi 0).const_mul C
  have hmeas :
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        AEStronglyMeasurable
          (F t) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    exact
      ((show Continuous (fun u : ℝ => Real.exp (-u)) by
          fun_prop).mul
        (continuous_sincPartial.comp
          (continuous_id.div_const t))).aestronglyMeasurable
  have hdom :
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
          ‖F t u‖ ≤ bound u := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    dsimp [F, bound]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-u) * |sincPartial (u / t)| ≤
          Real.exp (-u) * C :=
        mul_le_mul_of_nonneg_left
          (hbound (u / t) (div_pos hu ht)) (Real.exp_pos _).le
      _ = C * Real.exp (-u) := by ring
  have hlim :
      ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
        Tendsto (fun t : ℝ => F t u)
          (𝓝[>] (0 : ℝ))
          (𝓝 (Real.exp (-u) * dirichletLimit)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hdiv :
        Tendsto (fun t : ℝ => u / t)
          (𝓝[>] (0 : ℝ)) atTop := by
      simpa [div_eq_mul_inv] using
        tendsto_inv_nhdsGT_zero.const_mul_atTop hu
    have hS :=
      sincPartial_tendsto.comp hdiv
    dsimp [F]
    exact tendsto_const_nhds.mul hS
  have hDCT :=
    tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      bound hmeas hdom hbound_int hlim
  have hvalue :
      (∫ u in Set.Ioi (0 : ℝ),
        Real.exp (-u) * dirichletLimit) = dirichletLimit := by
    rw [integral_mul_const]
    rw [integral_exp_neg_Ioi_zero]
    simp
  simpa [F, hvalue] using hDCT

private lemma dampedIntegral_tendsto_dirichletLimit :
    Tendsto
      (fun t : ℝ => ∫ x in Set.Ioi (0 : ℝ), dampedKernel t x)
      (𝓝[>] (0 : ℝ)) (𝓝 dirichletLimit) := by
  apply abel_integrals_tendsto.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [abel_identity ht, abel_change_variables ht]

private lemma dirichletLimit_eq :
    dirichletLimit = Real.pi / 2 := by
  have hatan :
      Tendsto (fun t : ℝ => Real.arctan (1 / t))
        (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi / 2)) := by
    simpa [one_div] using
      (tendsto_nhds_of_tendsto_nhdsWithin
        (Real.tendsto_arctan_atTop.comp tendsto_inv_nhdsGT_zero))
  have hdamped :
      Tendsto
        (fun t : ℝ => ∫ x in Set.Ioi (0 : ℝ), dampedKernel t x)
        (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi / 2)) := by
    apply hatan.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (dampedIntegral_formula ht).symm
  exact tendsto_nhds_unique
    dampedIntegral_tendsto_dirichletLimit hdamped

-- The value of the preceding convergent improper integral is identified below.
private lemma sinc_improper :
    ImproperHasValue (fun x : ℝ => Real.sin x / x) (Real.pi / 2) := by
  unfold ImproperHasValue
  rw [← dirichletLimit_eq]
  exact source_partial_tendsto_dirichletLimit

private lemma scaled_sinc_partial_eq {α : ℝ} (hα : 0 < α) (b : ℝ) :
    (∫ x in (0 : ℝ)..b, Real.sin (α * x) / x) =
      ∫ u in (0 : ℝ)..(α * b), Real.sin u / u := by
  calc
    (∫ x in (0 : ℝ)..b, Real.sin (α * x) / x) =
        ∫ x in (0 : ℝ)..b, α * Real.sinc (α * x) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [volume.ae_ne (0 : ℝ)] with x hx _
      have hαx : α * x ≠ 0 := mul_ne_zero hα.ne' hx
      rw [Real.sinc_of_ne_zero hαx]
      field_simp
    _ = α * ∫ x in (0 : ℝ)..b, Real.sinc (α * x) := by
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ u in (0 : ℝ)..(α * b), Real.sinc u := by
      simpa using
        (intervalIntegral.mul_integral_comp_mul_left
          (f := Real.sinc) (a := (0 : ℝ)) (b := b) (c := α))
    _ = ∫ u in (0 : ℝ)..(α * b), Real.sin u / u :=
      integral_sinc_eq_source (α * b)

private lemma sinc_improper_pos {α : ℝ} (hα : 0 < α) :
    ImproperHasValue (fun x : ℝ => Real.sin (α * x) / x)
      (Real.pi / 2) := by
  have hone := sinc_improper
  unfold ImproperHasValue at hone ⊢
  have hscale :
      Tendsto (fun b : ℝ => α * b) atTop atTop :=
    tendsto_id.const_mul_atTop hα
  have hlim := hone.comp hscale
  apply hlim.congr'
  filter_upwards with b
  exact (scaled_sinc_partial_eq hα b).symm

private lemma neg_scaled_sinc_partial_eq {α : ℝ} (b : ℝ) :
    (∫ x in (0 : ℝ)..b, Real.sin (α * x) / x) =
      -(∫ x in (0 : ℝ)..b, Real.sin ((-α) * x) / x) := by
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro x _
  change Real.sin (α * x) / x = -(Real.sin ((-α) * x) / x)
  rw [show α * x = -((-α) * x) by ring, Real.sin_neg]
  ring

private lemma sinc_improper_neg {α : ℝ} (hα : α < 0) :
    ImproperHasValue (fun x : ℝ => Real.sin (α * x) / x)
      (-Real.pi / 2) := by
  have hpos := sinc_improper_pos (neg_pos.mpr hα)
  unfold ImproperHasValue at hpos ⊢
  have hneg := hpos.neg
  have hneg' :
      Tendsto
        (fun b : ℝ =>
          -(∫ x in (0 : ℝ)..b, Real.sin ((-α) * x) / x))
        atTop (𝓝 (-Real.pi / 2)) := by
    convert hneg using 1 <;> ring
  apply hneg'.congr'
  filter_upwards with b
  exact (neg_scaled_sinc_partial_eq b).symm

private lemma sinc_improper_zero :
    ImproperHasValue (fun x : ℝ => Real.sin (0 * x) / x) 0 := by
  unfold ImproperHasValue
  simp

private lemma sin_div_intervalIntegrable
    (a u v : ℝ) :
    IntervalIntegrable
      (fun x : ℝ => Real.sin (a * x) / x) volume u v := by
  by_cases ha : a = 0
  · subst a
    simp
  · have hc :
        Continuous (fun x : ℝ => a * Real.sinc (a * x)) := by
      fun_prop
    refine (hc.intervalIntegrable u v).congr_ae ?_
    filter_upwards
      [ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with x hx
    rw [Real.sinc_of_ne_zero (mul_ne_zero ha hx)]
    field_simp

private lemma fourier_partial_eq (x R : ℝ) :
    (∫ lam in (0 : ℝ)..R,
        2 / Real.pi * (Real.sin lam / lam) * Real.cos (lam * x)) =
      1 / Real.pi *
        ((∫ lam in (0 : ℝ)..R,
            Real.sin ((1 + x) * lam) / lam) +
          ∫ lam in (0 : ℝ)..R,
            Real.sin ((1 - x) * lam) / lam) := by
  rw [← intervalIntegral.integral_add
      (sin_div_intervalIntegrable (1 + x) 0 R)
      (sin_div_intervalIntegrable (1 - x) 0 R),
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro lam _
  by_cases hlam : lam = 0
  · simp [hlam]
  change
    2 / Real.pi * (Real.sin lam / lam) * Real.cos (lam * x) =
      1 / Real.pi *
        (Real.sin ((1 + x) * lam) / lam +
          Real.sin ((1 - x) * lam) / lam)
  rw [show (1 + x) * lam = lam + lam * x by ring,
    show (1 - x) * lam = lam - lam * x by ring,
    Real.sin_add, Real.sin_sub]
  field_simp [Real.pi_ne_zero, hlam]
  ring

private lemma fourier_limit_of_scaled
    (x A B : ℝ)
    (hA :
      ImproperHasValue
        (fun lam : ℝ => Real.sin ((1 + x) * lam) / lam) A)
    (hB :
      ImproperHasValue
        (fun lam : ℝ => Real.sin ((1 - x) * lam) / lam) B) :
    ImproperHasValue
      (fun lam : ℝ =>
        2 / Real.pi * (Real.sin lam / lam) * Real.cos (lam * x))
      (1 / Real.pi * (A + B)) := by
  unfold ImproperHasValue at hA hB ⊢
  have hsum := (hA.add hB).const_mul (1 / Real.pi)
  apply hsum.congr'
  filter_upwards with R
  exact (fourier_partial_eq x R).symm

/-- Semantic source: `results/stage1_gpt55/09_重积分与含参积分/exercise_3881_autoformalization_result/exercise_3881.md`. -/
private theorem originalProblem :
    ∀ x : ℝ,
      ImproperHasValue
        (fun lam =>
          2 / Real.pi * (Real.sin lam / lam) * Real.cos (lam * x))
        (fourierValue x) := by
  intro x
  unfold fourierValue
  by_cases hinside : |x| < 1
  · rw [if_pos hinside]
    have hx₀ : 0 < 1 + x := by
      have := neg_lt_of_abs_lt hinside
      linarith
    have hx₁ : 0 < 1 - x := by
      have := lt_of_abs_lt hinside
      linarith
    have h :=
      fourier_limit_of_scaled x (Real.pi / 2) (Real.pi / 2)
        (sinc_improper_pos hx₀) (sinc_improper_pos hx₁)
    convert h using 1 <;> field_simp [Real.pi_ne_zero] <;> ring
  · rw [if_neg hinside]
    by_cases houtside : 1 < |x|
    · rw [if_pos houtside]
      by_cases hx : 0 ≤ x
      · have hxgt : 1 < x := by
          simpa [abs_of_nonneg hx] using houtside
        have h :=
          fourier_limit_of_scaled x (Real.pi / 2) (-Real.pi / 2)
            (sinc_improper_pos (by linarith))
            (sinc_improper_neg (by linarith))
        convert h using 1 <;> field_simp [Real.pi_ne_zero] <;> ring
      · have hxlt : x < -1 := by
          rw [abs_of_neg (lt_of_not_ge hx)] at houtside
          linarith
        have h :=
          fourier_limit_of_scaled x (-Real.pi / 2) (Real.pi / 2)
            (sinc_improper_neg (by linarith))
            (sinc_improper_pos (by linarith))
        convert h using 1 <;> field_simp [Real.pi_ne_zero] <;> ring
    · rw [if_neg houtside]
      have habs : |x| = 1 :=
        le_antisymm (le_of_not_gt houtside) (le_of_not_gt hinside)
      have hsq : x ^ 2 = 1 := by
        nlinarith [sq_abs x]
      have hfac : (x - 1) * (x + 1) = 0 := by
        nlinarith
      rcases mul_eq_zero.mp hfac with hx | hx
      · have hxone : x = 1 := by linarith
        subst x
        have h :=
          fourier_limit_of_scaled (1 : ℝ) (Real.pi / 2) 0
            (sinc_improper_pos (by norm_num))
            (by simpa using sinc_improper_zero)
        convert h using 1 <;> field_simp [Real.pi_ne_zero] <;> ring
      · have hxnegone : x = -1 := by linarith
        subst x
        have h :=
          fourier_limit_of_scaled (-1 : ℝ) 0 (Real.pi / 2)
            (by simpa using sinc_improper_zero)
            (sinc_improper_pos (by norm_num))
        convert h using 1 <;> field_simp [Real.pi_ne_zero] <;> ring

private theorem boxFunction_eventually_one
    {x : ℝ} (hx : |x| < 1) :
    boxFunction =ᶠ[nhds x] fun _ => 1 := by
  have hopen :
      IsOpen {y : ℝ | |y| < 1} :=
    isOpen_lt continuous_abs continuous_const
  filter_upwards [hopen.eventually_mem hx] with y hy
  simp [boxFunction, hy]

private theorem boxFunction_eventually_zero
    {x : ℝ} (hx : 1 < |x|) :
    boxFunction =ᶠ[nhds x] fun _ => 0 := by
  have hopen :
      IsOpen {y : ℝ | 1 < |y|} :=
    isOpen_lt continuous_const continuous_abs
  filter_upwards [hopen.eventually_mem hx] with y hy
  simp [boxFunction, not_lt_of_ge hy.le]

private theorem deriv_boxFunction_eq_zero_of_abs_lt
    {x : ℝ} (hx : |x| < 1) :
    deriv boxFunction x = 0 := by
  rw [(boxFunction_eventually_one hx).deriv_eq]
  simp

private theorem deriv_boxFunction_eq_zero_of_one_lt_abs
    {x : ℝ} (hx : 1 < |x|) :
    deriv boxFunction x = 0 := by
  rw [(boxFunction_eventually_zero hx).deriv_eq]
  simp

private theorem boxFunction_eq_indicator :
    boxFunction =
      (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) := by
  funext x
  by_cases hx : |x| < 1
  ·
    rw [boxFunction, if_pos hx]
    exact
      (Set.indicator_of_mem
        (s := Ioo (-1 : ℝ) 1) (a := x) ((abs_lt).1 hx)
        (fun _ : ℝ => (1 : ℝ))).symm
  ·
    rw [boxFunction, if_neg hx]
    exact
      (Set.indicator_of_notMem
        (s := Ioo (-1 : ℝ) 1) (a := x)
        (by simpa [abs_lt] using hx)
        (fun _ : ℝ => (1 : ℝ))).symm

theorem gap1 :
    PiecewiseContinuousAtUnit boxFunction := by
  unfold PiecewiseContinuousAtUnit
  refine ⟨?_, ?_, ?_⟩
  ·
    apply (continuousOn_const :
      ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Iio (-1))).congr
    intro x hx
    have hxlt : x < -1 := hx
    have habs : 1 < |x| := by
      rw [abs_of_neg (by linarith : x < 0)]
      linarith
    symm
    simp [boxFunction, not_lt_of_ge habs.le]
  ·
    apply (continuousOn_const :
      ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Ioo (-1) 1)).congr
    intro x hx
    have habs : |x| < 1 := (abs_lt).2 hx
    symm
    simp [boxFunction, habs]
  ·
    apply (continuousOn_const :
      ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Ioi 1)).congr
    intro x hx
    have hxgt : 1 < x := hx
    have habs : 1 < |x| := by
      rw [abs_of_pos (by linarith)]
      exact hxgt
    symm
    simp [boxFunction, not_lt_of_ge habs.le]

theorem gap2 :
    PiecewiseContinuousAtUnit (deriv boxFunction) := by
  unfold PiecewiseContinuousAtUnit
  refine ⟨?_, ?_, ?_⟩
  ·
    apply (continuousOn_const :
      ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Iio (-1))).congr
    intro x hx
    have hxlt : x < -1 := hx
    have habs : 1 < |x| := by
      rw [abs_of_neg (by linarith : x < 0)]
      linarith
    exact deriv_boxFunction_eq_zero_of_one_lt_abs habs
  ·
    apply (continuousOn_const :
      ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Ioo (-1) 1)).congr
    intro x hx
    exact deriv_boxFunction_eq_zero_of_abs_lt ((abs_lt).2 hx)
  ·
    apply (continuousOn_const :
      ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Ioi 1)).congr
    intro x hx
    have hxgt : 1 < x := hx
    have habs : 1 < |x| := by
      rw [abs_of_pos (by linarith)]
      exact hxgt
    exact deriv_boxFunction_eq_zero_of_one_lt_abs habs

theorem gap3 :
    Integrable boxFunction := by
  rw [boxFunction_eq_indicator]
  exact
    (integrableOn_const
      (C := (1 : ℝ)) measure_Ioo_lt_top.ne).integrable_indicator
        measurableSet_Ioo

theorem gap4 :
    Function.Even boxFunction := by
  intro x
  simp [boxFunction]

private theorem boxSin_integrable (lam : ℝ) :
    Integrable
      (fun ξ => boxFunction ξ * Real.sin (lam * ξ)) := by
  apply gap3.mul_bdd (c := 1)
  · exact
      (Real.continuous_sin.comp
        (continuous_const.mul continuous_id)).aestronglyMeasurable
  · filter_upwards with ξ
    simpa [Real.norm_eq_abs] using
      Real.abs_sin_le_one (lam * ξ)

private theorem boxCos_integrable (lam : ℝ) :
    Integrable
      (fun ξ => boxFunction ξ * Real.cos (lam * ξ)) := by
  apply gap3.mul_bdd (c := 1)
  · exact
      (Real.continuous_cos.comp
        (continuous_const.mul continuous_id)).aestronglyMeasurable
  · filter_upwards with ξ
    simpa [Real.norm_eq_abs] using
      Real.abs_cos_le_one (lam * ξ)

theorem gap5 (lam : ℝ) :
    sineCoefficient boxFunction lam = 0 := by
  let r : ℝ → ℝ := fun ξ =>
    boxFunction ξ * Real.sin (lam * ξ)
  have hneg := integral_neg_eq_self r volume
  have hpoint (ξ : ℝ) : r (-ξ) = -r ξ := by
    dsimp [r]
    rw [gap4 ξ]
    rw [show lam * -ξ = -(lam * ξ) by ring, Real.sin_neg]
    ring
  simp_rw [hpoint, integral_neg] at hneg
  have hintegral : (∫ ξ : ℝ, r ξ) = 0 := by
    linarith
  unfold sineCoefficient
  change 1 / Real.pi * (∫ ξ : ℝ, r ξ) = 0
  rw [hintegral, mul_zero]

theorem gap6 (lam : ℝ) :
    cosineCoefficient boxFunction lam =
      2 / Real.pi * improperIntegral 0
        (fun ξ => boxFunction ξ * Real.cos (lam * ξ)) := by
  rfl

private theorem improperIntegral_eq_of_hasImproperIntegral
    {a : ℝ} {f : ℝ → ℝ} {L : ℝ}
    (hL : HasImproperIntegral a f L) :
    improperIntegral a f = L := by
  unfold improperIntegral
  have hs : {y : ℝ | HasImproperIntegral a f y} = {L} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hy
      exact tendsto_nhds_unique hy hL
    · rintro rfl
      exact hL
  rw [hs, csInf_singleton]

private theorem boxCos_partial_eq (lam b : ℝ) (hb : 1 ≤ b) :
    (∫ ξ in (0 : ℝ)..b,
        boxFunction ξ * Real.cos (lam * ξ)) =
      ∫ ξ in (0 : ℝ)..1, Real.cos (lam * ξ) := by
  have hsplit :
      (∫ ξ in (0 : ℝ)..b,
          boxFunction ξ * Real.cos (lam * ξ)) =
        (∫ ξ in (0 : ℝ)..1,
          boxFunction ξ * Real.cos (lam * ξ)) +
        ∫ ξ in (1 : ℝ)..b,
          boxFunction ξ * Real.cos (lam * ξ) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals]
    · exact (boxCos_integrable lam).intervalIntegrable
    · exact (boxCos_integrable lam).intervalIntegrable
  have hfirst :
      (∫ ξ in (0 : ℝ)..1,
          boxFunction ξ * Real.cos (lam * ξ)) =
        ∫ ξ in (0 : ℝ)..1, Real.cos (lam * ξ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne (1 : ℝ)] with ξ hne hmem
    have hbounds : ξ ∈ Icc (0 : ℝ) 1 := by
      have hu : ξ ∈ Set.uIcc (0 : ℝ) 1 :=
        Set.uIoc_subset_uIcc hmem
      rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hu
      exact hu
    have hlt : ξ < 1 :=
      lt_of_le_of_ne hbounds.2 hne
    have habs : |ξ| < 1 := by
      rw [abs_of_nonneg hbounds.1]
      exact hlt
    rw [boxFunction, if_pos habs, one_mul]
  have htail :
      (∫ ξ in (1 : ℝ)..b,
          boxFunction ξ * Real.cos (lam * ξ)) = 0 := by
    rw [← intervalIntegral.integral_zero]
    apply intervalIntegral.integral_congr
    intro ξ hmem
    have hbounds : ξ ∈ Icc (1 : ℝ) b := by
      simpa [Set.uIcc_of_le hb] using hmem
    have hlow : 1 ≤ ξ := hbounds.1
    have hnot : ¬ |ξ| < 1 := by
      rw [abs_of_nonneg (by linarith : 0 ≤ ξ)]
      exact not_lt_of_ge hlow
    unfold boxFunction
    change (if |ξ| < 1 then 1 else 0) *
      Real.cos (lam * ξ) = 0
    rw [if_neg hnot, zero_mul]
  rw [hsplit, hfirst, htail, add_zero]

private theorem boxCos_hasImproperIntegral (lam : ℝ) :
    HasImproperIntegral 0
      (fun ξ => boxFunction ξ * Real.cos (lam * ξ))
      (∫ ξ in (0 : ℝ)..1, Real.cos (lam * ξ)) := by
  unfold HasImproperIntegral
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb
  exact (boxCos_partial_eq lam b hb).symm

theorem gap7 (lam : ℝ) :
    2 / Real.pi * improperIntegral 0
        (fun ξ => boxFunction ξ * Real.cos (lam * ξ)) =
      2 / Real.pi * ∫ ξ in (0 : ℝ)..1, Real.cos (lam * ξ) := by
  rw [improperIntegral_eq_of_hasImproperIntegral
    (boxCos_hasImproperIntegral lam)]

private theorem cos_interval_formula
    (lam : ℝ) (hlam : lam ≠ 0) :
    (∫ ξ in (0 : ℝ)..1, Real.cos (lam * ξ)) =
      Real.sin lam / lam := by
  have hderiv : ∀ ξ : ℝ,
      HasDerivAt (fun y : ℝ => Real.sin (lam * y) / lam)
        (Real.cos (lam * ξ)) ξ := by
    intro ξ
    simpa [hlam] using
      (((Real.hasDerivAt_sin (lam * ξ)).comp ξ
        ((hasDerivAt_const ξ lam).mul (hasDerivAt_id ξ))).div_const lam)
  have hint :
      IntervalIntegrable (fun ξ : ℝ => Real.cos (lam * ξ))
        volume (0 : ℝ) 1 :=
    (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).intervalIntegrable _ _
  calc
    (∫ ξ in (0 : ℝ)..1, Real.cos (lam * ξ)) =
        Real.sin (lam * 1) / lam -
          Real.sin (lam * 0) / lam := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun ξ _ => hderiv ξ) hint
    _ = Real.sin lam / lam := by simp

theorem gap8 (lam : ℝ) (hlam : lam ≠ 0) :
    2 / Real.pi * ∫ ξ in (0 : ℝ)..1, Real.cos (lam * ξ) =
      2 * Real.sin lam / (Real.pi * lam) := by
  rw [cos_interval_formula lam hlam]
  field_simp [Real.pi_ne_zero, hlam]

theorem gap9 (lam : ℝ) (hlam : lam ≠ 0) :
    cosineCoefficient boxFunction lam =
      2 * Real.sin lam / (Real.pi * lam) := by
  calc
    cosineCoefficient boxFunction lam =
        2 / Real.pi * improperIntegral 0
          (fun ξ => boxFunction ξ * Real.cos (lam * ξ)) :=
      gap6 lam
    _ = 2 / Real.pi *
          ∫ ξ in (0 : ℝ)..1, Real.cos (lam * ξ) :=
      gap7 lam
    _ = _ := gap8 lam hlam

private theorem fourierValue_eq_boxFunction_of_ne
    (x : ℝ) (hx : |x| ≠ 1) :
    fourierValue x = boxFunction x := by
  by_cases hinside : |x| < 1
  · simp [fourierValue, boxFunction, hinside]
  ·
    have houtside : 1 < |x| :=
      lt_of_le_of_ne (le_of_not_gt hinside) hx.symm
    simp [fourierValue, boxFunction, hinside, houtside]

private theorem fourier_improper_formula (x : ℝ) :
    2 / Real.pi * improperIntegral 0
        (fun lam => Real.sin lam / lam * Real.cos (lam * x)) =
      fourierValue x := by
  let g : ℝ → ℝ := fun lam =>
    Real.sin lam / lam * Real.cos (lam * x)
  have horiginal := originalProblem x
  unfold ImproperHasValue at horiginal
  have hscaled :
      Tendsto
        (fun R : ℝ => 2 / Real.pi *
          ∫ lam in (0 : ℝ)..R, g lam)
        atTop (nhds (fourierValue x)) := by
    apply horiginal.congr'
    filter_upwards with R
    calc
      (∫ lam in (0 : ℝ)..R,
          2 / Real.pi * (Real.sin lam / lam) *
            Real.cos (lam * x)) =
          ∫ lam in (0 : ℝ)..R,
            2 / Real.pi * g lam := by
        apply intervalIntegral.integral_congr
        intro lam hmem
        dsimp [g]
        ring
      _ = 2 / Real.pi *
          ∫ lam in (0 : ℝ)..R, g lam := by
        rw [intervalIntegral.integral_const_mul]
  have hunscaled :=
    hscaled.const_mul (Real.pi / 2)
  have hhas :
      HasImproperIntegral 0 g
        (Real.pi / 2 * fourierValue x) := by
    unfold HasImproperIntegral
    convert hunscaled using 1 <;>
      field_simp [Real.pi_ne_zero] <;> ring
  have himproper :=
    improperIntegral_eq_of_hasImproperIntegral hhas
  change 2 / Real.pi * improperIntegral 0 g =
    fourierValue x
  rw [himproper]
  field_simp [Real.pi_ne_zero]

theorem gap10 (x : ℝ) (hx : |x| ≠ 1) :
    boxFunction x =
      2 / Real.pi * improperIntegral 0
        (fun lam => Real.sin lam / lam * Real.cos (lam * x)) := by
  rw [← fourierValue_eq_boxFunction_of_ne x hx]
  exact (fourier_improper_formula x).symm

theorem gap11 :
    Tendsto boxFunction (nhdsWithin 1 (Set.Iio 1)) (nhds 1) ∧
      Tendsto boxFunction (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) ∧
        ((1 : ℝ) + 0) / 2 = 1 / 2 := by
  refine ⟨?_, ?_, by norm_num⟩
  ·
    apply tendsto_const_nhds.congr'
    have hpos :
        ∀ᶠ x : ℝ in nhdsWithin 1 (Iio 1), 0 < x :=
      (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        inf_le_left
    filter_upwards [self_mem_nhdsWithin, hpos] with x hxlt hxpos
    have habs : |x| < 1 := by
      rw [abs_of_pos hxpos]
      exact hxlt
    symm
    simp [boxFunction, habs]
  ·
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hxgt
    have hxgt' : 1 < x := hxgt
    have habs : 1 < |x| := by
      rw [abs_of_pos (by linarith : 0 < x)]
      exact hxgt'
    symm
    simp [boxFunction, not_lt_of_ge habs.le]

theorem gap12 :
    Tendsto boxFunction (nhdsWithin (-1) (Set.Iio (-1))) (nhds 0) ∧
      Tendsto boxFunction (nhdsWithin (-1) (Set.Ioi (-1))) (nhds 1) ∧
        ((0 : ℝ) + 1) / 2 = 1 / 2 := by
  refine ⟨?_, ?_, by norm_num⟩
  ·
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hxlt
    have hxlt' : x < -1 := hxlt
    have habs : 1 < |x| := by
      rw [abs_of_neg (by linarith : x < 0)]
      linarith
    symm
    simp [boxFunction, not_lt_of_ge habs.le]
  ·
    apply tendsto_const_nhds.congr'
    have hneg :
        ∀ᶠ x : ℝ in nhdsWithin (-1) (Ioi (-1)), x < 0 :=
      (eventually_lt_nhds (show (-1 : ℝ) < 0 by norm_num)).filter_mono
        inf_le_left
    filter_upwards [self_mem_nhdsWithin, hneg] with x hxgt hxneg
    have hxgt' : -1 < x := hxgt
    have habs : |x| < 1 := by
      rw [abs_of_neg hxneg]
      linarith
    symm
    simp [boxFunction, habs]

theorem gap13 :
    2 / Real.pi * improperIntegral 0
        (fun lam => Real.sin lam / lam * Real.cos lam) =
      1 / 2 := by
  simpa [fourierValue] using fourier_improper_formula (1 : ℝ)

private theorem sincTwo_improper_formula :
    improperIntegral 0
        (fun lam => Real.sin (2 * lam) / lam) =
      Real.pi / 2 := by
  have hprivate :
      ImproperHasValue
        (fun lam : ℝ => Real.sin (2 * lam) / lam)
        (Real.pi / 2) :=
    sinc_improper_pos (by norm_num)
  have hhas :
      HasImproperIntegral 0
        (fun lam : ℝ => Real.sin (2 * lam) / lam)
        (Real.pi / 2) := by
    simpa [HasImproperIntegral, ImproperHasValue] using hprivate
  exact improperIntegral_eq_of_hasImproperIntegral hhas

theorem gap14 :
    2 / Real.pi * improperIntegral 0
        (fun lam => Real.sin lam / lam * Real.cos lam) =
      1 / Real.pi * improperIntegral 0
        (fun lam => Real.sin (2 * lam) / lam) := by
  rw [gap13, sincTwo_improper_formula]
  field_simp [Real.pi_ne_zero]

theorem gap15 :
    1 / Real.pi * improperIntegral 0
        (fun lam => Real.sin (2 * lam) / lam) =
      1 / Real.pi * (Real.pi / 2) := by
  rw [sincTwo_improper_formula]

theorem gap16 :
    1 / Real.pi * (Real.pi / 2) = (1 : ℝ) / 2 := by
  field_simp [Real.pi_ne_zero]

theorem gap17 :
    2 / Real.pi * improperIntegral 0
        (fun lam => Real.sin lam / lam * Real.cos lam) =
      1 / 2 := by
  exact gap13

end

end ProofGap.Exercise3881
