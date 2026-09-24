import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace ProofGap.Exercise4163

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

abbrev Point := ℝ × ℝ

def strip : Set Point :=
  {z | 0 ≤ z.2 ∧ z.2 ≤ 1}

def kernel (p x y : ℝ) : ℝ :=
  1 / Real.rpow (1 + x ^ 2 + y ^ 2) p

def weightedAbsIntegral (φ : ℝ → ℝ → ℝ) (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in strip, ENNReal.ofReal (|φ z.1 z.2| * kernel p z.1 z.2)

def benchmarkIntegral (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in strip, ENNReal.ofReal (kernel p z.1 z.2)

def iteratedFull (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ y in Set.Icc (0 : ℝ) 1,
    ∫⁻ x : ℝ, ENNReal.ofReal (kernel p x y)

def iteratedHalf (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ y in Set.Icc (0 : ℝ) 1,
    ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (kernel p x y)

def oneDimensionalIntegral (a p : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Set.Ioi (0 : ℝ),
    ENNReal.ofReal (1 / Real.rpow (a ^ 2 + x ^ 2) p)

private theorem strip_measurable : MeasurableSet strip := by
  unfold strip
  measurability

private theorem strip_eq_prod :
    strip = Set.univ ×ˢ Set.Icc (0 : ℝ) 1 := by
  ext z
  simp [strip]

private theorem measurable_rpow (s : ℝ) :
    Measurable (fun x : ℝ => Real.rpow x s) := by
  apply measurable_of_continuousOn_compl_singleton 0
  exact continuousOn_id.rpow_const
    (fun x hx => Or.inl (by simpa using hx))

private theorem kernel_pos (p x y : ℝ) :
    0 < kernel p x y := by
  unfold kernel
  exact one_div_pos.2
    (Real.rpow_pos_of_pos (by positivity : 0 < 1 + x ^ 2 + y ^ 2) p)

private theorem kernel_measurable (p : ℝ) :
    Measurable (fun z : ℝ × ℝ => kernel p z.1 z.2) := by
  unfold kernel
  have hbase : Measurable
      (fun z : ℝ × ℝ => 1 + z.1 ^ 2 + z.2 ^ 2) :=
    (measurable_const.add (measurable_fst.pow_const 2)).add
      (measurable_snd.pow_const 2)
  exact measurable_const.div ((measurable_rpow p).comp hbase)

private theorem kernel_ofReal_measurable (p y : ℝ) :
    Measurable (fun x : ℝ => ENNReal.ofReal (kernel p x y)) := by
  exact ((kernel_measurable p).comp
    (measurable_id.prodMk measurable_const)).ennreal_ofReal

theorem gap1 (φ : ℝ → ℝ → ℝ) (p : ℝ)
    (hφ : ∀ x y, |φ x y| ≤ 1) :
    weightedAbsIntegral φ p ≤ benchmarkIntegral p := by
  unfold weightedAbsIntegral benchmarkIntegral
  apply setLIntegral_mono' strip_measurable
  intro z hz
  exact ENNReal.ofReal_le_ofReal (by
    have hk := (kernel_pos p z.1 z.2).le
    calc
      |φ z.1 z.2| * kernel p z.1 z.2 ≤
          1 * kernel p z.1 z.2 :=
        mul_le_mul_of_nonneg_right (hφ z.1 z.2) hk
      _ = kernel p z.1 z.2 := one_mul _)

theorem gap2 (p : ℝ) :
    benchmarkIntegral p = iteratedFull p := by
  unfold benchmarkIntegral iteratedFull
  rw [strip_eq_prod, Measure.volume_eq_prod]
  simpa only [setLIntegral_univ] using
    (setLIntegral_prod_symm
      (μ := volume) (ν := volume)
      (s := Set.univ) (t := Set.Icc (0 : ℝ) 1)
      (fun z : ℝ × ℝ => ENNReal.ofReal (kernel p z.1 z.2))
      (kernel_measurable p).ennreal_ofReal.aemeasurable)

private theorem half_line_symmetry (p y : ℝ) :
    (∫⁻ x : ℝ, ENNReal.ofReal (kernel p x y)) =
      2 * ∫⁻ x in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (kernel p x y) := by
  let f : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (kernel p x y)
  have hf : Measurable f := kernel_ofReal_measurable p y
  have heven (x : ℝ) : f (-x) = f x := by
    unfold f kernel
    congr 2
    ring
  have hnegRaw :=
    (Measure.measurePreserving_neg (volume : Measure ℝ))
      |>.setLIntegral_comp_preimage
        (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi hf
  have hneg :
      (∫⁻ x in Set.Iio (0 : ℝ), f x) =
        ∫⁻ x in Set.Ioi (0 : ℝ), f x := by
    simpa [heven] using hnegRaw
  have hleft :
      (∫⁻ x in Set.Iic (0 : ℝ), f x) =
        ∫⁻ x in Set.Ioi (0 : ℝ), f x := by
    rw [← setLIntegral_congr Iio_ae_eq_Iic]
    exact hneg
  have hsplit :=
    lintegral_add_compl (μ := volume) f
      (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))
  rw [Set.compl_Ioi] at hsplit
  change (∫⁻ x : ℝ, f x) =
    2 * ∫⁻ x in Set.Ioi (0 : ℝ), f x
  rw [← hsplit, hleft]
  exact (two_mul _).symm

theorem gap3 (p : ℝ) :
    iteratedFull p = 2 * iteratedHalf p := by
  unfold iteratedFull iteratedHalf
  simp_rw [half_line_symmetry p]
  have hinner : Measurable
      (fun y : ℝ =>
        ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (kernel p x y)) :=
    (kernel_measurable p).ennreal_ofReal.lintegral_prod_left'
      (μ := volume.restrict (Set.Ioi (0 : ℝ)))
  rw [lintegral_const_mul 2 hinner]

theorem gap4 (p : ℝ) :
    benchmarkIntegral p = 2 * iteratedHalf p := by
  rw [gap2, gap3]

private theorem sqrt_two_sq :
    (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
  Real.sq_sqrt (by norm_num)

theorem gap5 (p y : ℝ) (hp : 0 ≤ p) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    oneDimensionalIntegral (Real.sqrt 2) p ≤
      ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (kernel p x y) := by
  unfold oneDimensionalIntegral
  apply setLIntegral_mono' measurableSet_Ioi
  intro x hx
  exact ENNReal.ofReal_le_ofReal (by
    have hy2 : y ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg hy.1 (sub_nonneg.2 hy.2)]
    have hbase :
        1 + x ^ 2 + y ^ 2 ≤ (Real.sqrt 2) ^ 2 + x ^ 2 := by
      rw [sqrt_two_sq]
      linarith
    have hr :=
      Real.rpow_le_rpow (by positivity : 0 ≤ 1 + x ^ 2 + y ^ 2)
        hbase hp
    unfold kernel
    exact one_div_le_one_div_of_le
      (Real.rpow_pos_of_pos (by positivity : 0 < 1 + x ^ 2 + y ^ 2) p) hr)

theorem gap6 (p y : ℝ) (hp : 0 ≤ p) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    (∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (kernel p x y)) ≤
      oneDimensionalIntegral 1 p := by
  unfold oneDimensionalIntegral
  apply setLIntegral_mono' measurableSet_Ioi
  intro x hx
  exact ENNReal.ofReal_le_ofReal (by
    have hbase : (1 : ℝ) ^ 2 + x ^ 2 ≤ 1 + x ^ 2 + y ^ 2 := by
      nlinarith [sq_nonneg y]
    have hr :=
      Real.rpow_le_rpow (by positivity : 0 ≤ (1 : ℝ) ^ 2 + x ^ 2)
        hbase hp
    unfold kernel
    exact one_div_le_one_div_of_le
      (Real.rpow_pos_of_pos (by positivity : 0 < (1 : ℝ) ^ 2 + x ^ 2) p) hr)

theorem gap7 (p : ℝ) (hp : 0 ≤ p) :
    oneDimensionalIntegral (Real.sqrt 2) p ≤
      oneDimensionalIntegral 1 p := by
  unfold oneDimensionalIntegral
  apply setLIntegral_mono' measurableSet_Ioi
  intro x hx
  exact ENNReal.ofReal_le_ofReal (by
    have hbase : (1 : ℝ) ^ 2 + x ^ 2 ≤
        (Real.sqrt 2) ^ 2 + x ^ 2 := by
      rw [sqrt_two_sq]
      norm_num
    have hr :=
      Real.rpow_le_rpow (by positivity : 0 ≤ (1 : ℝ) ^ 2 + x ^ 2)
        hbase hp
    exact one_div_le_one_div_of_le
      (Real.rpow_pos_of_pos (by positivity : 0 < (1 : ℝ) ^ 2 + x ^ 2) p) hr)

private theorem tendsto_rpow_one
    (f : ℝ → ℝ) (p : ℝ)
    (hf : Tendsto f atTop (nhds 1)) :
    Tendsto (fun x => Real.rpow (f x) p) atTop (nhds 1) := by
  have hlog :
      Tendsto (fun x => Real.log (f x)) atTop (nhds 0) := by
    simpa using
      (Real.continuousAt_log one_ne_zero).tendsto.comp hf
  have hmul :
      Tendsto (fun x => Real.log (f x) * p) atTop (nhds 0) := by
    simpa using hlog.mul_const p
  have hexp :
      Tendsto (fun x => Real.exp (Real.log (f x) * p))
        atTop (nhds 1) := by
    simpa using Real.continuous_exp.continuousAt.tendsto.comp hmul
  apply hexp.congr'
  have hpos : ∀ᶠ x in atTop, 0 < f x :=
    hf.eventually (Ioi_mem_nhds zero_lt_one)
  filter_upwards [hpos] with x hx
  exact (Real.rpow_def_of_pos hx p).symm

theorem gap8 (p : ℝ) :
    ∀ a : ℝ,
      Tendsto
        (fun x : ℝ =>
          Real.rpow x (2 * p) /
            Real.rpow (a ^ 2 + x ^ 2) p)
        atTop (nhds 1) := by
  intro a
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hfrac :
      Tendsto (fun x : ℝ => a ^ 2 / x ^ 2) atTop (nhds 0) := by
    have hsq : Tendsto (fun x : ℝ => x⁻¹ ^ 2) atTop (nhds 0) := by
      simpa using hinv.pow 2
    simpa [div_eq_mul_inv, inv_pow] using tendsto_const_nhds.mul hsq
  have hbase :
      Tendsto (fun x : ℝ => 1 + a ^ 2 / x ^ 2)
        atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hfrac
  have hrpow :
      Tendsto (fun x : ℝ => Real.rpow (1 + a ^ 2 / x ^ 2) p)
        atTop (nhds 1) :=
    tendsto_rpow_one _ p hbase
  have hinvrpow :
      Tendsto (fun x : ℝ => 1 / Real.rpow (1 + a ^ 2 / x ^ 2) p)
        atTop (nhds 1) := by
    simpa [one_div] using hrpow.inv₀ one_ne_zero
  apply hinvrpow.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hxpow : Real.rpow (x ^ 2) p ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (sq_pos_of_pos hx) p)
  have hbasepos : 0 ≤ 1 + a ^ 2 / x ^ 2 := by positivity
  have hsum :
      a ^ 2 + x ^ 2 = x ^ 2 * (1 + a ^ 2 / x ^ 2) := by
    field_simp [hx.ne']
    ring
  have hden :
      Real.rpow (a ^ 2 + x ^ 2) p =
        Real.rpow (x ^ 2) p *
          Real.rpow (1 + a ^ 2 / x ^ 2) p := by
    rw [hsum]
    exact Real.mul_rpow (sq_nonneg x) hbasepos
  have hnum :
      Real.rpow x (2 * p) = Real.rpow (x ^ 2) p := by
    calc
      Real.rpow x (2 * p) =
          Real.rpow (Real.rpow x (2 : ℝ)) p :=
        Real.rpow_mul hx.le 2 p
      _ = Real.rpow (x ^ 2) p :=
        congrArg (fun t : ℝ => Real.rpow t p)
          (Real.rpow_natCast x 2)
  rw [hden, hnum]
  field_simp [hxpow]

private def oneDimReal (a p x : ℝ) : ℝ :=
  1 / Real.rpow (a ^ 2 + x ^ 2) p

private theorem oneDimReal_pos (a p x : ℝ) (ha : 0 < a) :
    0 < oneDimReal a p x := by
  unfold oneDimReal
  exact one_div_pos.2
    (Real.rpow_pos_of_pos (by nlinarith [sq_pos_of_pos ha, sq_nonneg x]) p)

private theorem oneDimReal_continuous (a p : ℝ) (ha : 0 < a) :
    Continuous (oneDimReal a p) := by
  unfold oneDimReal
  apply Continuous.div continuous_const
  · apply Continuous.rpow_const
    · fun_prop
    · intro x
      exact Or.inl (ne_of_gt (by
        nlinarith [sq_pos_of_pos ha, sq_nonneg x] :
          0 < a ^ 2 + x ^ 2))
  · intro x
    exact ne_of_gt
      (Real.rpow_pos_of_pos (by
        nlinarith [sq_pos_of_pos ha, sq_nonneg x] :
          0 < a ^ 2 + x ^ 2) p)

private theorem oneDimReal_integrable_iff (a p : ℝ) (ha : 0 < a) :
    IntegrableOn (oneDimReal a p) (Set.Ioi (0 : ℝ)) ↔
      (1 : ℝ) / 2 < p := by
  let g : ℝ → ℝ := fun x => Real.rpow x (-2 * p)
  let ratio : ℝ → ℝ := fun x =>
    Real.rpow x (2 * p) / Real.rpow (a ^ 2 + x ^ 2) p
  have hratio : Tendsto ratio atTop (nhds 1) := by
    exact gap8 p a
  have hnear :
      ∀ᶠ x : ℝ in atTop, (1 / 2 : ℝ) < ratio x ∧ ratio x < 2 :=
    hratio.eventually
      (Ioo_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2))
  have hfg (x : ℝ) (hx : 0 < x) :
      oneDimReal a p x = ratio x * g x := by
    have hxp : Real.rpow x (2 * p) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hx (2 * p))
    have hden : Real.rpow (a ^ 2 + x ^ 2) p ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos
        (by nlinarith [sq_pos_of_pos ha, sq_nonneg x]) p)
    have hneg :
        Real.rpow x (-(2 * p)) = (Real.rpow x (2 * p))⁻¹ :=
      Real.rpow_neg hx.le (2 * p)
    unfold oneDimReal ratio g
    rw [show -2 * p = -(2 * p) by ring, hneg]
    field_simp [hxp, hden]
  have hfO : oneDimReal a p =O[atTop] g := by
    apply Asymptotics.IsBigO.of_bound 2
    filter_upwards [hnear, eventually_gt_atTop (0 : ℝ)] with x hr hx
    have hfpos := oneDimReal_pos a p x ha
    have hgpos : 0 < g x := by
      unfold g
      exact Real.rpow_pos_of_pos hx _
    simp only [Real.norm_eq_abs, abs_of_pos hfpos, abs_of_pos hgpos]
    rw [hfg x hx]
    nlinarith
  have hgO : g =O[atTop] oneDimReal a p := by
    apply Asymptotics.IsBigO.of_bound 2
    filter_upwards [hnear, eventually_gt_atTop (0 : ℝ)] with x hr hx
    have hfpos := oneDimReal_pos a p x ha
    have hgpos : 0 < g x := by
      unfold g
      exact Real.rpow_pos_of_pos hx _
    simp only [Real.norm_eq_abs, abs_of_pos hgpos, abs_of_pos hfpos]
    rw [hfg x hx]
    nlinarith
  have hfstrong :
      StronglyMeasurableAtFilter (oneDimReal a p) atTop volume :=
    (oneDimReal_continuous a p ha).stronglyMeasurable
      |>.stronglyMeasurableAtFilter
  have hgmeas : Measurable g := by
    unfold g
    exact measurable_rpow _
  have hgstrong :
      StronglyMeasurableAtFilter g atTop volume :=
    hgmeas.stronglyMeasurable.stronglyMeasurableAtFilter
  constructor
  · intro hfint
    have hfat : IntegrableAtFilter (oneDimReal a p) atTop :=
      ⟨Set.Ioi (0 : ℝ), Ioi_mem_atTop 0, hfint⟩
    have hgat : IntegrableAtFilter g atTop :=
      hgO.integrableAtFilter hgstrong hfat
    have hpow :
        -2 * p < -1 := by
      exact integrableAtFilter_rpow_atTop_iff.mp hgat
    linarith
  · intro hp
    have hgat : IntegrableAtFilter g atTop := by
      apply integrableAtFilter_rpow_atTop_iff.mpr
      linarith
    have hlocal :
        LocallyIntegrableOn (oneDimReal a p) (Set.Ici (0 : ℝ)) :=
      (oneDimReal_continuous a p ha).continuousOn.locallyIntegrableOn
        measurableSet_Ici
    have hici :
        IntegrableOn (oneDimReal a p) (Set.Ici (0 : ℝ)) :=
      hlocal.integrableOn_of_isBigO_atTop hfO hgat
    exact hici.mono_set Set.Ioi_subset_Ici_self

private theorem oneDimensionalIntegral_ne_top_iff (a p : ℝ) (ha : 0 < a) :
    oneDimensionalIntegral a p ≠ ⊤ ↔
      (1 : ℝ) / 2 < p := by
  have hm :
      AEStronglyMeasurable (oneDimReal a p)
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (oneDimReal_continuous a p ha).aestronglyMeasurable
  have hn :
      0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] oneDimReal a p :=
    ae_of_all _ fun x => (oneDimReal_pos a p x ha).le
  unfold oneDimensionalIntegral
  change
    (∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (oneDimReal a p x)) ≠ ⊤ ↔
      (1 : ℝ) / 2 < p
  rw [lintegral_ofReal_ne_top_iff_integrable hm hn]
  exact oneDimReal_integrable_iff a p ha

theorem gap9 (a p : ℝ) (ha : 0 < a) :
    ∃ finiteValue : ℝ≥0∞,
      finiteValue ≠ ⊤ ∧
        oneDimensionalIntegral a p =
          if (1 : ℝ) / 2 < p then finiteValue else ⊤ := by
  by_cases hp : (1 : ℝ) / 2 < p
  · refine ⟨oneDimensionalIntegral a p,
      (oneDimensionalIntegral_ne_top_iff a p ha).2 hp, ?_⟩
    rw [if_pos hp]
  · have htop : oneDimensionalIntegral a p = ⊤ := by
      by_contra hne
      exact hp ((oneDimensionalIntegral_ne_top_iff a p ha).1 hne)
    refine ⟨0, ENNReal.zero_ne_top, ?_⟩
    rw [if_neg hp]
    exact htop

theorem gap10 (φ : ℝ → ℝ → ℝ) (C p : ℝ)
    (hC : 0 ≤ C) (hφ : ∀ x y, |φ x y| ≤ C)
    (hp : (1 : ℝ) / 2 < p) :
    weightedAbsIntegral φ p ≠ ⊤ := by
  have hp0 : 0 ≤ p := by linarith
  have hone : oneDimensionalIntegral 1 p ≠ ⊤ :=
    (oneDimensionalIntegral_ne_top_iff 1 p (by norm_num)).2 hp
  have hhalf_le :
      iteratedHalf p ≤ oneDimensionalIntegral 1 p := by
    unfold iteratedHalf
    calc
      (∫⁻ y in Set.Icc (0 : ℝ) 1,
          ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (kernel p x y)) ≤
          ∫⁻ _y in Set.Icc (0 : ℝ) 1,
            oneDimensionalIntegral 1 p := by
        apply setLIntegral_mono' measurableSet_Icc
        intro y hy
        exact gap6 p y hp0 hy
      _ = oneDimensionalIntegral 1 p := by
        simp [setLIntegral_const, Real.volume_Icc]
  have hhalf : iteratedHalf p ≠ ⊤ :=
    ne_top_of_le_ne_top hone hhalf_le
  have hbenchmark : benchmarkIntegral p ≠ ⊤ := by
    rw [gap4]
    exact ENNReal.mul_ne_top (by norm_num) hhalf
  have hweighted :
      weightedAbsIntegral φ p ≤
        ENNReal.ofReal C * benchmarkIntegral p := by
    unfold weightedAbsIntegral benchmarkIntegral
    calc
      (∫⁻ z in strip,
          ENNReal.ofReal (|φ z.1 z.2| * kernel p z.1 z.2)) ≤
          ∫⁻ z in strip,
            ENNReal.ofReal C *
              ENNReal.ofReal (kernel p z.1 z.2) := by
        apply setLIntegral_mono' strip_measurable
        intro z hz
        rw [← ENNReal.ofReal_mul hC]
        exact ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right
            (hφ z.1 z.2) (kernel_pos p z.1 z.2).le)
      _ = ENNReal.ofReal C *
          ∫⁻ z in strip, ENNReal.ofReal (kernel p z.1 z.2) := by
        rw [lintegral_const_mul]
        exact (kernel_measurable p).ennreal_ofReal
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbenchmark) hweighted

end

end ProofGap.Exercise4163
