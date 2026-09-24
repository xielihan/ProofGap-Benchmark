import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Prod

namespace ProofGap.Exercise4169

noncomputable section

open Filter MeasureTheory
open scoped ENNReal

abbrev Point := ℝ × ℝ

def region : Set Point :=
  {z | 1 ≤ z.1 ∧ 1 ≤ z.1 * z.2}

def integrand (p q x y : ℝ) : ℝ :=
  1 / (Real.rpow x p * Real.rpow y q)

def integralValue (p q : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in region, ENNReal.ofReal (integrand p q z.1 z.2)

def innerIntegral (q x : ℝ) : ℝ≥0∞ :=
  ∫⁻ y in Set.Ici (1 / x),
    ENNReal.ofReal (1 / Real.rpow y q)

def iteratedIntegral (p q : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Set.Ici (1 : ℝ),
    ENNReal.ofReal (1 / Real.rpow x p) * innerIntegral q x

def outerPowerIntegral (p q : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Set.Ici (1 : ℝ),
    ENNReal.ofReal (Real.rpow x (q - p - 1))

private theorem measurableSet_region : MeasurableSet region := by
  unfold region
  measurability

private theorem measurable_rpow (s : ℝ) :
    Measurable (fun x : ℝ => Real.rpow x s) := by
  apply measurable_of_continuousOn_compl_singleton 0
  exact continuousOn_id.rpow_const
    (fun x hx => Or.inl (by simpa using hx))

private theorem measurable_integrand_ofReal (p q : ℝ) :
    Measurable
      (fun z : Point => ENNReal.ofReal (integrand p q z.1 z.2)) := by
  unfold integrand
  exact (measurable_const.div
    (((measurable_rpow p).comp measurable_fst).mul
      ((measurable_rpow q).comp measurable_snd))).ennreal_ofReal

private theorem ofReal_integrand_factor
    (p q x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    ENNReal.ofReal (integrand p q x y) =
      ENNReal.ofReal (1 / Real.rpow x p) *
        ENNReal.ofReal (1 / Real.rpow y q) := by
  have hxp : 0 ≤ 1 / Real.rpow x p :=
    (one_div_pos.mpr (Real.rpow_pos_of_pos hx p)).le
  unfold integrand
  rw [show 1 / (Real.rpow x p * Real.rpow y q) =
      (1 / Real.rpow x p) * (1 / Real.rpow y q) by
        field_simp [ne_of_gt (Real.rpow_pos_of_pos hx p),
          ne_of_gt (Real.rpow_pos_of_pos hy q)]]
  exact ENNReal.ofReal_mul hxp

private theorem integralValue_eq_iterated
    (p q : ℝ) :
    integralValue p q = iteratedIntegral p q := by
  unfold integralValue iteratedIntegral innerIntegral
  rw [Measure.volume_eq_prod]
  rw [← lintegral_indicator measurableSet_region]
  rw [lintegral_prod]
  · rw [← lintegral_indicator measurableSet_Ici]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ Set.Ici (1 : ℝ)
    · rw [Set.indicator_of_mem hx]
      rw [← lintegral_indicator measurableSet_Ici]
      have hmeasY :
          Measurable (fun y : ℝ =>
            ENNReal.ofReal (1 / Real.rpow y q)) :=
        (measurable_const.div (measurable_rpow q)).ennreal_ofReal
      rw [← lintegral_const_mul
        (ENNReal.ofReal (1 / Real.rpow x p))
        (hmeasY.indicator measurableSet_Ici)]
      apply lintegral_congr
      intro y
      by_cases hy : y ∈ Set.Ici (1 / x)
      · rw [Set.indicator_of_mem hy]
        have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
        have hy0 : 0 < y := by
          have : 0 < 1 / x := one_div_pos.mpr hx0
          exact this.trans_le hy
        have hz : (x, y) ∈ region := by
          constructor
          · exact hx
          · have := (div_le_iff₀ hx0).mp hy
            simpa only [mul_comm] using this
        rw [Set.indicator_of_mem hz]
        exact ofReal_integrand_factor p q x y hx0 hy0
      · rw [Set.indicator_of_notMem hy]
        have hz : (x, y) ∉ region := by
          intro hz
          apply hy
          have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
          exact (div_le_iff₀ hx0).2 (by simpa [mul_comm] using hz.2)
        rw [Set.indicator_of_notMem hz]
        simp
    · rw [Set.indicator_of_notMem hx]
      have hzero :
          (fun y : ℝ => region.indicator
            (fun z : Point =>
              ENNReal.ofReal (integrand p q z.1 z.2)) (x, y)) =
            (fun _ => 0) := by
        funext y
        rw [Set.indicator_of_notMem]
        intro hz
        exact hx hz.1
      rw [hzero, lintegral_zero]
  · exact (measurable_integrand_ofReal p q).aemeasurable.indicator
      measurableSet_region

private theorem reciprocal_eq_rpow (q y : ℝ) (hy : 0 < y) :
    1 / Real.rpow y q = Real.rpow y (-q) := by
  simpa [one_div] using (Real.rpow_neg hy.le q).symm

private theorem innerIntegral_finite
    (q x : ℝ) (hq : 1 < q) (hx : 1 ≤ x) :
    innerIntegral q x =
      ENNReal.ofReal (Real.rpow x (q - 1) / (q - 1)) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have ha : 0 < 1 / x := one_div_pos.mpr hx0
  unfold innerIntegral
  rw [← setLIntegral_congr
    (Ioi_ae_eq_Ici : Set.Ioi (1 / x) =ᵐ[volume] Set.Ici (1 / x))]
  rw [setLIntegral_congr_fun measurableSet_Ioi
    (fun y hy => congrArg ENNReal.ofReal
      (reciprocal_eq_rpow q y (ha.trans hy)))]
  have hi : IntegrableOn (fun y : ℝ => Real.rpow y (-q))
      (Set.Ioi (1 / x)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) ha
  have hn : 0 ≤ᵐ[volume.restrict (Set.Ioi (1 / x))]
      (fun y : ℝ => Real.rpow y (-q)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact Real.rpow_nonneg (ha.trans hy).le _
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn]
  have hval :
      (∫ y in Set.Ioi (1 / x), Real.rpow y (-q)) =
        -Real.rpow (1 / x) (-q + 1) / (-q + 1) := by
    simpa using
      (integral_Ioi_rpow_of_lt (a := -q) (c := 1 / x)
        (by linarith) ha)
  rw [hval]
  apply congrArg ENNReal.ofReal
  have hqne : -q + 1 ≠ 0 := by linarith
  have hqne' : q - 1 ≠ 0 := by linarith
  have hrpow :
      Real.rpow (1 / x) (-q + 1) =
        Real.rpow x (q - 1) := by
    rw [one_div]
    calc
      Real.rpow x⁻¹ (-q + 1) =
          (Real.rpow x (-q + 1))⁻¹ :=
        Real.inv_rpow hx0.le (-q + 1)
      _ = Real.rpow x (-(-q + 1)) :=
        (Real.rpow_neg hx0.le (-q + 1)).symm
      _ = Real.rpow x (q - 1) := by congr 1 <;> ring
  rw [hrpow]
  field_simp [hqne, hqne', ne_of_gt (Real.rpow_pos_of_pos hx0 (q - 1))]
  ring

private theorem innerIntegral_top
    (q x : ℝ) (hq : q ≤ 1) (hx : 1 ≤ x) :
    innerIntegral q x = ⊤ := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have ha : 0 < 1 / x := one_div_pos.mpr hx0
  unfold innerIntegral
  rw [← setLIntegral_congr
    (Ioi_ae_eq_Ici : Set.Ioi (1 / x) =ᵐ[volume] Set.Ici (1 / x))]
  rw [setLIntegral_congr_fun measurableSet_Ioi
    (fun y hy => congrArg ENNReal.ofReal
      (reciprocal_eq_rpow q y (ha.trans hy)))]
  have hm : AEStronglyMeasurable (fun y : ℝ => Real.rpow y (-q))
      (volume.restrict (Set.Ioi (1 / x))) := by
    exact (continuousOn_id.rpow_const
      (fun y hy => Or.inl (ne_of_gt (ha.trans hy)))).aestronglyMeasurable
        measurableSet_Ioi
  have hn : 0 ≤ᵐ[volume.restrict (Set.Ioi (1 / x))]
      (fun y : ℝ => Real.rpow y (-q)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact Real.rpow_nonneg (ha.trans hy).le _
  by_contra htop
  have hi : IntegrableOn (fun y : ℝ => Real.rpow y (-q))
      (Set.Ioi (1 / x)) :=
    (lintegral_ofReal_ne_top_iff_integrable hm hn).mp htop
  have hcond := (integrableOn_Ioi_rpow_iff ha).mp hi
  linarith

private theorem outer_eq_rpow
    (p q x : ℝ) (hq : 1 < q) (hx : 1 ≤ x) :
    ENNReal.ofReal (1 / Real.rpow x p) *
        ENNReal.ofReal (Real.rpow x (q - 1) / (q - 1)) =
      ENNReal.ofReal (1 / (q - 1)) *
        ENNReal.ofReal (Real.rpow x (q - p - 1)) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hpnonneg : 0 ≤ 1 / Real.rpow x p :=
    (one_div_pos.mpr (Real.rpow_pos_of_pos hx0 p)).le
  have hpow_nonneg : 0 ≤ Real.rpow x (q - 1) :=
    (Real.rpow_pos_of_pos hx0 _).le
  have hreal :
      (1 / Real.rpow x p) * (Real.rpow x (q - 1) / (q - 1)) =
        (1 / (q - 1)) * Real.rpow x (q - p - 1) := by
    rw [show Real.rpow x (q - p - 1) =
        Real.rpow x (q - 1) / Real.rpow x p by
          rw [show q - p - 1 = (q - 1) - p by ring]
          exact Real.rpow_sub hx0 (q - 1) p]
    ring
  rw [← ENNReal.ofReal_mul hpnonneg]
  rw [← ENNReal.ofReal_mul
    ((one_div_pos.mpr (sub_pos.mpr hq)).le :
      0 ≤ (1 / (q - 1) : ℝ))]
  exact congrArg ENNReal.ofReal hreal

private theorem integralValue_factor
    (p q : ℝ) (hq : 1 < q) :
    integralValue p q =
      ENNReal.ofReal (1 / (q - 1)) * outerPowerIntegral p q := by
  rw [integralValue_eq_iterated]
  unfold iteratedIntegral outerPowerIntegral
  calc
    (∫⁻ x in Set.Ici (1 : ℝ),
        ENNReal.ofReal (1 / Real.rpow x p) * innerIntegral q x) =
        ∫⁻ x in Set.Ici (1 : ℝ),
          ENNReal.ofReal (1 / Real.rpow x p) *
            ENNReal.ofReal (Real.rpow x (q - 1) / (q - 1)) := by
      apply setLIntegral_congr_fun measurableSet_Ici
      intro x hx
      simpa using congrArg
        (fun t => ENNReal.ofReal (1 / Real.rpow x p) * t)
        (innerIntegral_finite q x hq hx)
    _ = ∫⁻ x in Set.Ici (1 : ℝ),
          ENNReal.ofReal (1 / (q - 1)) *
            ENNReal.ofReal (Real.rpow x (q - p - 1)) := by
      apply setLIntegral_congr_fun measurableSet_Ici
      intro x hx
      exact outer_eq_rpow p q x hq hx
    _ = ENNReal.ofReal (1 / (q - 1)) *
          ∫⁻ x in Set.Ici (1 : ℝ),
            ENNReal.ofReal (Real.rpow x (q - p - 1)) := by
      rw [lintegral_const_mul]
      exact (measurable_rpow _).ennreal_ofReal

private theorem lintegral_rpow_finite
    (s : ℝ) (hs : s < -1) :
    (∫⁻ x in Set.Ici (1 : ℝ), ENNReal.ofReal (Real.rpow x s)) =
      ENNReal.ofReal (-1 / (s + 1)) := by
  rw [← setLIntegral_congr
    (Ioi_ae_eq_Ici : Set.Ioi (1 : ℝ) =ᵐ[volume] Set.Ici 1)]
  have hi : IntegrableOn (fun x : ℝ => Real.rpow x s)
      (Set.Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt hs zero_lt_one
  have hn : 0 ≤ᵐ[volume.restrict (Set.Ioi (1 : ℝ))]
      (fun x : ℝ => Real.rpow x s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact Real.rpow_nonneg (zero_lt_one.trans hx).le _
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn]
  have hval :
      (∫ x in Set.Ioi (1 : ℝ), Real.rpow x s) =
        -Real.rpow 1 (s + 1) / (s + 1) := by
    simpa using
      (integral_Ioi_rpow_of_lt (a := s) (c := (1 : ℝ))
        hs zero_lt_one)
  rw [hval]
  simp

private theorem lintegral_rpow_top
    (s : ℝ) (hs : -1 ≤ s) :
    (∫⁻ x in Set.Ici (1 : ℝ), ENNReal.ofReal (Real.rpow x s)) = ⊤ := by
  rw [← setLIntegral_congr
    (Ioi_ae_eq_Ici : Set.Ioi (1 : ℝ) =ᵐ[volume] Set.Ici 1)]
  have hm : AEStronglyMeasurable (fun x : ℝ => Real.rpow x s)
      (volume.restrict (Set.Ioi (1 : ℝ))) := by
    exact (continuousOn_id.rpow_const
      (fun x hx => Or.inl (ne_of_gt (zero_lt_one.trans hx)))).aestronglyMeasurable
        measurableSet_Ioi
  have hn : 0 ≤ᵐ[volume.restrict (Set.Ioi (1 : ℝ))]
      (fun x : ℝ => Real.rpow x s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact Real.rpow_nonneg (zero_lt_one.trans hx).le _
  by_contra htop
  have hi : IntegrableOn (fun x : ℝ => Real.rpow x s)
      (Set.Ioi (1 : ℝ)) :=
    (lintegral_ofReal_ne_top_iff_integrable hm hn).mp htop
  have hcond := (integrableOn_Ioi_rpow_iff zero_lt_one).mp hi
  linarith

private theorem integralValue_top_low_q
    (p q : ℝ) (hq : q ≤ 1) :
    integralValue p q = ⊤ := by
  rw [integralValue_eq_iterated]
  unfold iteratedIntegral
  have heq :
      (∫⁻ x in Set.Ici (1 : ℝ),
          ENNReal.ofReal (1 / Real.rpow x p) * innerIntegral q x) =
        ∫⁻ _x in Set.Ici (1 : ℝ), ⊤ := by
    apply setLIntegral_congr_fun measurableSet_Ici
    intro x hx
    change ENNReal.ofReal (1 / Real.rpow x p) * innerIntegral q x = ⊤
    rw [innerIntegral_top q x hq hx]
    have hx0 : 0 < x := zero_lt_one.trans_le hx
    have hpos : 0 < ENNReal.ofReal (1 / Real.rpow x p) := by
      rw [ENNReal.ofReal_pos]
      exact one_div_pos.mpr (Real.rpow_pos_of_pos hx0 p)
    exact ENNReal.mul_top hpos.ne'
  rw [heq]
  simp

private theorem integralValue_top_high_q
    (p q : ℝ) (hq : 1 < q) (hpq : p ≤ q) :
    integralValue p q = ⊤ := by
  rw [integralValue_factor p q hq]
  have hout : outerPowerIntegral p q = ⊤ := by
    unfold outerPowerIntegral
    exact lintegral_rpow_top (q - p - 1) (by linarith)
  rw [hout]
  have hpos : 0 < ENNReal.ofReal (1 / (q - 1)) := by
    rw [ENNReal.ofReal_pos]
    exact one_div_pos.mpr (sub_pos.mpr hq)
  exact ENNReal.mul_top hpos.ne'

theorem gap1 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    integralValue p q = iteratedIntegral p q := by
  exact integralValue_eq_iterated p q

theorem gap2 (q x : ℝ) (hq : 1 < q) (hx : 1 ≤ x) :
    innerIntegral q x =
      ENNReal.ofReal (Real.rpow x (q - 1) / (q - 1)) := by
  exact innerIntegral_finite q x hq hx

theorem gap3 (p q : ℝ)
    (hp : 0 < p) (hq0 : 0 < q) (hq : q ≤ 1) :
    integralValue p q = ⊤ := by
  exact integralValue_top_low_q p q hq

theorem gap4 (p q : ℝ) (hp : 0 < p) (hq : 1 < q) :
    integralValue p q =
      ENNReal.ofReal (1 / (q - 1)) * outerPowerIntegral p q := by
  exact integralValue_factor p q hq

theorem gap5 (p q : ℝ) (hq : 1 < q) (hpq : q < p) :
    ENNReal.ofReal (1 / (q - 1)) * outerPowerIntegral p q =
      ENNReal.ofReal (1 / ((p - q) * (q - 1))) := by
  unfold outerPowerIntegral
  rw [lintegral_rpow_finite (q - p - 1) (by linarith)]
  rw [← ENNReal.ofReal_mul
    ((one_div_pos.mpr (sub_pos.mpr hq)).le :
      0 ≤ (1 / (q - 1) : ℝ))]
  congr 1
  have h₁ : q - p - 1 + 1 ≠ 0 := by linarith
  have h₂ : q - 1 ≠ 0 := by linarith
  have h₃ : p - q ≠ 0 := by linarith
  field_simp [h₁, h₂, h₃]
  ring

theorem gap6 (p q : ℝ) (hq : 1 < q) (hpq : q < p) :
    integralValue p q =
      ENNReal.ofReal (1 / ((p - q) * (q - 1))) := by
  rw [integralValue_factor p q hq]
  unfold outerPowerIntegral
  rw [lintegral_rpow_finite (q - p - 1) (by linarith)]
  rw [← ENNReal.ofReal_mul
    ((one_div_pos.mpr (sub_pos.mpr hq)).le :
      0 ≤ (1 / (q - 1) : ℝ))]
  congr 1
  have h₁ : q - p - 1 + 1 ≠ 0 := by linarith
  have h₂ : q - 1 ≠ 0 := by linarith
  have h₃ : p - q ≠ 0 := by linarith
  field_simp [h₁, h₂, h₃]
  ring

theorem gap7 (p q : ℝ)
    (hp : 0 < p) (hq : 1 < q) (hpq : p ≤ q) :
    integralValue p q = ⊤ := by
  exact integralValue_top_high_q p q hq hpq

theorem gap8 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    integralValue p q =
      if q < p ∧ 1 < q then
        ENNReal.ofReal (1 / ((p - q) * (q - 1)))
      else
        ⊤ := by
  by_cases hq1 : 1 < q
  · by_cases hpq : q < p
    · simp [hq1, hpq]
      rw [integralValue_factor p q hq1]
      unfold outerPowerIntegral
      rw [lintegral_rpow_finite (q - p - 1) (by linarith)]
      rw [← ENNReal.ofReal_mul
        ((one_div_pos.mpr (sub_pos.mpr hq1)).le :
          0 ≤ (1 / (q - 1) : ℝ))]
      congr 1
      have h₁ : q - p - 1 + 1 ≠ 0 := by linarith
      have h₂ : q - 1 ≠ 0 := by linarith
      have h₃ : p - q ≠ 0 := by linarith
      field_simp [h₁, h₂, h₃]
      ring
    · have hpq' : p ≤ q := le_of_not_gt hpq
      simp [hq1, hpq, integralValue_top_high_q p q hq1 hpq']
  · have hq' : q ≤ 1 := le_of_not_gt hq1
    simp [hq1, integralValue_top_low_q p q hq']

end

end ProofGap.Exercise4169
