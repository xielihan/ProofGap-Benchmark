import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4162

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

def kernel (p q x y : ℝ) : ℝ :=
  1 / ((1 + Real.rpow |x| p) * (1 + Real.rpow |y| q))

def totalIntegral (p q : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (kernel p q z.1 z.2)

def positiveQuadrantIntegral (p q : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ),
    ENNReal.ofReal (kernel p q z.1 z.2)

def oneDimensionalIntegral (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Set.Ioi (0 : ℝ),
    ENNReal.ofReal (1 / (1 + Real.rpow x p))

private def factor (p x : ℝ) : ℝ :=
  1 / (1 + Real.rpow |x| p)

private def factorE (p x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (factor p x)

private def fullIntegral (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ x : ℝ, factorE p x

private theorem factor_pos (p x : ℝ) : 0 < factor p x := by
  unfold factor
  have hpow : 0 ≤ Real.rpow |x| p :=
    Real.rpow_nonneg (abs_nonneg x) _
  exact one_div_pos.mpr (by linarith)

private theorem factor_nonneg (p x : ℝ) : 0 ≤ factor p x :=
  (factor_pos p x).le

private theorem measurable_rpow_abs (p : ℝ) :
    Measurable (fun x : ℝ => Real.rpow |x| p) := by
  apply measurable_of_continuousOn_compl_singleton 0
  exact continuousOn_id.abs.rpow_const
    (fun x hx => Or.inl (by simpa using hx))

private theorem measurable_factorE (p : ℝ) :
    Measurable (factorE p) := by
  unfold factorE factor
  exact (measurable_const.div
    (measurable_const.add (measurable_rpow_abs p))).ennreal_ofReal

private theorem kernel_factor (p q x y : ℝ) :
    ENNReal.ofReal (kernel p q x y) =
      factorE p x * factorE q y := by
  have hpx := factor_nonneg p x
  have hreal :
      kernel p q x y = factor p x * factor q y := by
    unfold kernel factor
    have hx : 1 + Real.rpow |x| p ≠ 0 := by
      exact ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one
        (Real.rpow_nonneg (abs_nonneg x) p))
    have hy : 1 + Real.rpow |y| q ≠ 0 := by
      exact ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one
        (Real.rpow_nonneg (abs_nonneg y) q))
    field_simp [hx, hy]
  rw [hreal]
  exact ENNReal.ofReal_mul hpx

private theorem factorE_even (p x : ℝ) :
    factorE p (-x) = factorE p x := by
  simp [factorE, factor, abs_neg]

private theorem factorE_pos (p x : ℝ) :
    0 < factorE p x := by
  unfold factorE
  rw [ENNReal.ofReal_pos]
  exact factor_pos p x

private theorem positive_factor_integral (p : ℝ) :
    (∫⁻ x in Set.Ioi (0 : ℝ), factorE p x) =
      oneDimensionalIntegral p := by
  unfold oneDimensionalIntegral
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only [factorE, factor]
  rw [abs_of_pos hx]

private theorem negative_half_eq_positive (p : ℝ) :
    (∫⁻ x in Set.Iio (0 : ℝ), factorE p x) =
      ∫⁻ x in Set.Ioi (0 : ℝ), factorE p x := by
  let e : ℝ ≃ᵐ ℝ :=
    { toFun := fun x => -x
      invFun := fun x => -x
      left_inv := neg_neg
      right_inv := neg_neg
      measurable_toFun := measurable_id.neg
      measurable_invFun := measurable_id.neg }
  have hmp : MeasurePreserving e :=
    Measure.measurePreserving_neg (volume : Measure ℝ)
  have hpre : e ⁻¹' Set.Ioi (0 : ℝ) = Set.Iio (0 : ℝ) := by
    ext x
    simp [e]
  have hchange :=
    hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding
      (factorE p) (Set.Ioi (0 : ℝ))
  rw [hpre] at hchange
  calc
    (∫⁻ x in Set.Iio (0 : ℝ), factorE p x) =
        ∫⁻ x in Set.Iio (0 : ℝ), factorE p (e x) := by
      apply setLIntegral_congr_fun measurableSet_Iio
      intro x hx
      exact (factorE_even p x).symm
    _ = ∫⁻ x in Set.Ioi (0 : ℝ), factorE p x := hchange

private theorem fullIntegral_eq_two_mul (p : ℝ) :
    fullIntegral p = 2 * oneDimensionalIntegral p := by
  unfold fullIntegral
  rw [← setLIntegral_univ]
  rw [← Set.Iic_union_Ioi (a := (0 : ℝ))]
  rw [lintegral_union measurableSet_Ioi (Set.Iic_disjoint_Ioi le_rfl)]
  rw [← setLIntegral_congr
    (Iio_ae_eq_Iic : Set.Iio (0 : ℝ) =ᵐ[volume] Set.Iic 0)]
  rw [negative_half_eq_positive, positive_factor_integral]
  rw [two_mul]

private theorem totalIntegral_eq_full_product (p q : ℝ) :
    totalIntegral p q = fullIntegral p * fullIntegral q := by
  unfold totalIntegral fullIntegral
  rw [Measure.volume_eq_prod]
  rw [lintegral_prod]
  · simp_rw [kernel_factor]
    have hq : Measurable (factorE q) := measurable_factorE q
    calc
      (∫⁻ x : ℝ, ∫⁻ y : ℝ, factorE p x * factorE q y) =
          ∫⁻ x : ℝ, factorE p x * ∫⁻ y : ℝ, factorE q y := by
        apply lintegral_congr
        intro x
        rw [lintegral_const_mul (factorE p x) hq]
      _ = (∫⁻ x : ℝ, factorE p x) *
          ∫⁻ y : ℝ, factorE q y := by
        rw [lintegral_mul_const
          (∫⁻ y : ℝ, factorE q y) (measurable_factorE p)]
  · have hpq : Measurable
        (fun z : ℝ × ℝ => factorE p z.1 * factorE q z.2) :=
      ((measurable_factorE p).comp measurable_fst).mul
        ((measurable_factorE q).comp measurable_snd)
    exact hpq.aemeasurable.congr
      (Filter.Eventually.of_forall fun z => (kernel_factor p q z.1 z.2).symm)

private theorem positiveQuadrant_eq_product (p q : ℝ) :
    positiveQuadrantIntegral p q =
      oneDimensionalIntegral p * oneDimensionalIntegral q := by
  unfold positiveQuadrantIntegral
  rw [Measure.volume_eq_prod]
  have hpq : Measurable
      (fun z : ℝ × ℝ => factorE p z.1 * factorE q z.2) :=
    ((measurable_factorE p).comp measurable_fst).mul
      ((measurable_factorE q).comp measurable_snd)
  rw [show
    (fun z : ℝ × ℝ => ENNReal.ofReal (kernel p q z.1 z.2)) =
      fun z => factorE p z.1 * factorE q z.2 by
        funext z
        exact kernel_factor p q z.1 z.2]
  rw [setLIntegral_prod _ hpq.aemeasurable]
  have hq : Measurable (factorE q) := measurable_factorE q
  calc
    (∫⁻ x in Set.Ioi (0 : ℝ),
        ∫⁻ y in Set.Ioi (0 : ℝ), factorE p x * factorE q y) =
        ∫⁻ x in Set.Ioi (0 : ℝ),
          factorE p x * ∫⁻ y in Set.Ioi (0 : ℝ), factorE q y := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact lintegral_const_mul (factorE p x) hq
    _ = (∫⁻ x in Set.Ioi (0 : ℝ), factorE p x) *
        ∫⁻ y in Set.Ioi (0 : ℝ), factorE q y := by
      rw [lintegral_mul_const
        (∫⁻ y in Set.Ioi (0 : ℝ), factorE q y)
        (measurable_factorE p)]
    _ = oneDimensionalIntegral p * oneDimensionalIntegral q := by
      rw [positive_factor_integral, positive_factor_integral]

private theorem lintegral_rpow_top (s : ℝ) (hs : -1 ≤ s) :
    (∫⁻ x in Set.Ioi (1 : ℝ), ENNReal.ofReal (Real.rpow x s)) = ⊤ := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => Real.rpow x s)
      (volume.restrict (Set.Ioi (1 : ℝ))) := by
    exact (continuousOn_id.rpow_const
      (fun x hx => Or.inl (ne_of_gt (zero_lt_one.trans hx)))).aestronglyMeasurable
        measurableSet_Ioi
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (1 : ℝ))]
      (fun x : ℝ => Real.rpow x s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact Real.rpow_nonneg (le_of_lt (zero_lt_one.trans hx)) _
  by_contra htop
  have hi : IntegrableOn (fun x : ℝ => Real.rpow x s)
      (Set.Ioi (1 : ℝ)) :=
    (lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg).mp htop
  have hs' := (integrableOn_Ioi_rpow_iff zero_lt_one).mp hi
  linarith

private theorem reciprocal_integrable_of_one_lt (p : ℝ) (hp : 1 < p) :
    IntegrableOn (fun x : ℝ => 1 / (1 + Real.rpow x p))
      (Set.Ioi (0 : ℝ)) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1),
    integrableOn_union]
  constructor
  · have hc : ContinuousOn
        (fun x : ℝ => 1 / (1 + Real.rpow x p))
        (Set.Ioc (0 : ℝ) 1) := by
      apply ContinuousOn.div continuousOn_const
      · exact continuousOn_const.add
          (continuousOn_id.rpow_const
            (fun x hx => Or.inl (ne_of_gt hx.1)))
      · intro x
        intro hx
        have hpow : 0 ≤ Real.rpow x p :=
          Real.rpow_nonneg hx.1.le _
        linarith
    have hmeas : AEStronglyMeasurable
        (fun x : ℝ => 1 / (1 + Real.rpow x p))
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      hc.aestronglyMeasurable measurableSet_Ioc
    have hone : IntegrableOn (fun _x : ℝ => (1 : ℝ))
        (Set.Ioc (0 : ℝ) 1) :=
      integrableOn_const measure_Ioc_lt_top.ne
    change Integrable
      (fun x : ℝ => 1 / (1 + Real.rpow x p))
      (volume.restrict (Set.Ioc (0 : ℝ) 1))
    change Integrable (fun _x : ℝ => (1 : ℝ))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) at hone
    refine hone.mono hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hpow : 0 ≤ Real.rpow x p := Real.rpow_nonneg hx.1.le _
    have hden : 0 < 1 + Real.rpow x p := by linarith
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hden),
      norm_one]
    rw [div_le_iff₀ hden]
    simpa only [one_mul] using le_add_of_nonneg_right hpow
  · have hg : IntegrableOn (fun x : ℝ => Real.rpow x (-p))
        (Set.Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    have hfmeas : AEStronglyMeasurable
        (fun x : ℝ => 1 / (1 + Real.rpow x p))
        (volume.restrict (Set.Ioi (1 : ℝ))) := by
      have hc : ContinuousOn
          (fun x : ℝ => 1 / (1 + Real.rpow x p))
          (Set.Ioi (1 : ℝ)) := by
        apply ContinuousOn.div continuousOn_const
        · exact continuousOn_const.add
            (continuousOn_id.rpow_const
              (fun x hx => Or.inl (ne_of_gt (zero_lt_one.trans hx))))
        · intro x hx
          have hpow : 0 < Real.rpow x p :=
            Real.rpow_pos_of_pos (zero_lt_one.trans hx) _
          linarith
      exact hc.aestronglyMeasurable measurableSet_Ioi
    change Integrable (fun x : ℝ => Real.rpow x (-p))
      (volume.restrict (Set.Ioi (1 : ℝ))) at hg
    change Integrable (fun x : ℝ => 1 / (1 + Real.rpow x p))
      (volume.restrict (Set.Ioi (1 : ℝ)))
    refine hg.mono hfmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hpow : 0 < Real.rpow x p := Real.rpow_pos_of_pos hx0 _
    have hden : 0 < 1 + Real.rpow x p := by positivity
    have hnegpow : 0 < Real.rpow x (-p) :=
      Real.rpow_pos_of_pos hx0 _
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hden),
      Real.norm_eq_abs, abs_of_pos hnegpow]
    have hneg :
        Real.rpow x (-p) = (Real.rpow x p)⁻¹ :=
      Real.rpow_neg hx0.le p
    rw [hneg]
    simpa [one_div] using
      one_div_le_one_div_of_le hpow (le_add_of_nonneg_left zero_le_one)

private theorem oneDimensionalIntegral_ne_top_of_one_lt
    (p : ℝ) (hp : 1 < p) :
    oneDimensionalIntegral p ≠ ⊤ := by
  unfold oneDimensionalIntegral
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => 1 / (1 + Real.rpow x p))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hc : ContinuousOn
        (fun x : ℝ => 1 / (1 + Real.rpow x p))
        (Set.Ioi (0 : ℝ)) := by
      apply ContinuousOn.div continuousOn_const
      · exact continuousOn_const.add
          (continuousOn_id.rpow_const
            (fun x hx => Or.inl (ne_of_gt hx)))
      · intro x
        intro hx
        have hpow : 0 ≤ Real.rpow x p := Real.rpow_nonneg hx.le _
        linarith
    exact hc.aestronglyMeasurable measurableSet_Ioi
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun x : ℝ => 1 / (1 + Real.rpow x p)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact one_div_nonneg.mpr
      (add_nonneg zero_le_one (Real.rpow_nonneg hx.le p))
  exact (lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg).2
    (reciprocal_integrable_of_one_lt p hp)

private theorem oneDimensionalIntegral_eq_top_of_not_one_lt
    (p : ℝ) (hp : ¬1 < p) :
    oneDimensionalIntegral p = ⊤ := by
  have hp1 : p ≤ 1 := le_of_not_gt hp
  unfold oneDimensionalIntegral
  have htail :
      (∫⁻ x in Set.Ioi (1 : ℝ),
          ENNReal.ofReal (1 / (1 + Real.rpow x p))) = ⊤ := by
    by_cases hp0 : 0 ≤ p
    · have hlow :
          (∫⁻ x in Set.Ioi (1 : ℝ),
              ENNReal.ofReal ((1 / 2 : ℝ) * Real.rpow x (-p))) = ⊤ := by
        rw [show
          (fun x : ℝ => ENNReal.ofReal ((1 / 2 : ℝ) * Real.rpow x (-p))) =
            fun x => ENNReal.ofReal (1 / 2 : ℝ) *
              ENNReal.ofReal (Real.rpow x (-p)) by
                funext x
                rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]]
        rw [lintegral_const_mul'
          (ENNReal.ofReal (1 / 2 : ℝ))
          (fun x => ENNReal.ofReal (Real.rpow x (-p)))
          ENNReal.ofReal_ne_top]
        rw [lintegral_rpow_top (-p) (by linarith)]
        exact ENNReal.mul_top (by norm_num)
      apply top_unique
      rw [← hlow]
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 < x := zero_lt_one.trans hx
      have hpow1 : 1 ≤ Real.rpow x p :=
        Real.one_le_rpow hx.le hp0
      have hpowpos : 0 < Real.rpow x p := Real.rpow_pos_of_pos hx0 _
      apply ENNReal.ofReal_le_ofReal
      have hneg :
          Real.rpow x (-p) = (Real.rpow x p)⁻¹ :=
        Real.rpow_neg hx0.le p
      rw [hneg]
      have hden : 0 < 1 + Real.rpow x p := by positivity
      field_simp [hpowpos.ne', hden.ne']
      nlinarith
    · have hpneg : p < 0 := lt_of_not_ge hp0
      have hlow :
          (∫⁻ _x in Set.Ioi (1 : ℝ), ENNReal.ofReal (1 / 2 : ℝ)) = ⊤ := by
        rw [setLIntegral_const]
        simp
      apply top_unique
      rw [← hlow]
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 < x := zero_lt_one.trans hx
      have hpowle : Real.rpow x p ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hx.le hpneg.le
      have hpow0 : 0 ≤ Real.rpow x p := Real.rpow_nonneg hx0.le _
      apply ENNReal.ofReal_le_ofReal
      have hden : 0 < 1 + Real.rpow x p := by positivity
      field_simp [hden.ne']
      nlinarith
  apply top_unique
  calc
    ⊤ = ∫⁻ x in Set.Ioi (1 : ℝ),
        ENNReal.ofReal (1 / (1 + Real.rpow x p)) := htail.symm
    _ ≤ ∫⁻ x in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (1 / (1 + Real.rpow x p)) :=
      lintegral_mono_set (Set.Ioi_subset_Ioi (by norm_num))

private theorem oneDimensionalIntegral_pos (p : ℝ) :
    oneDimensionalIntegral p ≠ 0 := by
  unfold oneDimensionalIntegral
  have hf : Measurable
      (fun x : ℝ => ENNReal.ofReal (1 / (1 + Real.rpow x p))) := by
    have hrpow : Measurable (fun x : ℝ => Real.rpow x p) := by
      apply measurable_of_continuousOn_compl_singleton 0
      exact continuousOn_id.rpow_const
        (fun x hx => Or.inl (by simpa using hx))
    exact (measurable_const.div (measurable_const.add hrpow)).ennreal_ofReal
  apply pos_iff_ne_zero.mp
  rw [setLIntegral_pos_iff hf]
  have hsub :
      Set.Ioi (0 : ℝ) ⊆
        Function.support
          (fun x : ℝ => ENNReal.ofReal (1 / (1 + Real.rpow x p))) ∩
            Set.Ioi (0 : ℝ) := by
    intro x hx
    refine ⟨?_, hx⟩
    simp only [Function.mem_support]
    exact ne_of_gt (by
      rw [ENNReal.ofReal_pos]
      exact one_div_pos.mpr
        (add_pos_of_pos_of_nonneg zero_lt_one
          (Real.rpow_nonneg hx.le p)))
  have hvol : 0 < volume (Set.Ioi (0 : ℝ)) := by simp
  exact hvol.trans_le (measure_mono hsub)

theorem gap1 (p q : ℝ) :
    totalIntegral p q = 4 * positiveQuadrantIntegral p q := by
  rw [totalIntegral_eq_full_product,
    fullIntegral_eq_two_mul, fullIntegral_eq_two_mul,
    positiveQuadrant_eq_product]
  ring

theorem gap2 (p q : ℝ) :
    4 * positiveQuadrantIntegral p q =
      4 * oneDimensionalIntegral p * oneDimensionalIntegral q := by
  rw [positiveQuadrant_eq_product]
  ring

theorem gap3 (p q : ℝ) :
    totalIntegral p q =
      4 * oneDimensionalIntegral p * oneDimensionalIntegral q := by
  rw [gap1, gap2]

theorem gap4 (p : ℝ) (hp : 0 < p) :
    Tendsto
      (fun x : ℝ =>
        Real.rpow x p * (1 / (1 + Real.rpow x p)))
      atTop (nhds 1) := by
  have hpow : Tendsto (fun x : ℝ => Real.rpow x p) atTop atTop :=
    tendsto_rpow_atTop hp
  have hden : Tendsto (fun x : ℝ => 1 + Real.rpow x p) atTop atTop :=
    by
      simpa only [add_comm] using
        hpow.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
  have hinv : Tendsto
      (fun x : ℝ => (1 + Real.rpow x p)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hden
  have hlim : Tendsto
      (fun x : ℝ => 1 - (1 + Real.rpow x p)⁻¹)
      atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub hinv
  have heq :
      (fun x : ℝ =>
        Real.rpow x p * (1 / (1 + Real.rpow x p))) =ᶠ[atTop]
      (fun x : ℝ => 1 - (1 + Real.rpow x p)⁻¹) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hpow0 : 0 ≤ Real.rpow x p := Real.rpow_nonneg hx.le _
    have hne : 1 + Real.rpow x p ≠ 0 := by linarith
    field_simp [hne]
    ring
  simpa only [sub_zero] using hlim.congr' heq.symm

theorem gap5 (p : ℝ) :
    ∃ finiteValue : ℝ≥0∞,
      finiteValue ≠ ⊤ ∧
        oneDimensionalIntegral p =
          if 1 < p then finiteValue else ⊤ := by
  by_cases hp : 1 < p
  · refine ⟨oneDimensionalIntegral p,
      oneDimensionalIntegral_ne_top_of_one_lt p hp, ?_⟩
    simp [hp]
  · refine ⟨0, ENNReal.zero_ne_top, ?_⟩
    simp [hp, oneDimensionalIntegral_eq_top_of_not_one_lt p hp]

theorem gap6 (q : ℝ) :
    ∃ finiteValue : ℝ≥0∞,
      finiteValue ≠ ⊤ ∧
        oneDimensionalIntegral q =
          if 1 < q then finiteValue else ⊤ := by
  exact gap5 q

theorem gap7 (p q : ℝ) :
    ∃ finiteValue : ℝ≥0∞,
      finiteValue ≠ ⊤ ∧
        totalIntegral p q =
          if 1 < p ∧ 1 < q then finiteValue else ⊤ := by
  by_cases hp : 1 < p
  · by_cases hq : 1 < q
    · let v : ℝ≥0∞ :=
        4 * oneDimensionalIntegral p * oneDimensionalIntegral q
      have hv : v ≠ ⊤ := by
        dsimp [v]
        exact ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (by norm_num)
            (oneDimensionalIntegral_ne_top_of_one_lt p hp))
          (oneDimensionalIntegral_ne_top_of_one_lt q hq)
      refine ⟨v, hv, ?_⟩
      simp [hp, hq, gap3, v]
    · have hqtop :=
        oneDimensionalIntegral_eq_top_of_not_one_lt q hq
      have hpzero := oneDimensionalIntegral_pos p
      refine ⟨0, ENNReal.zero_ne_top, ?_⟩
      rw [gap3, hqtop]
      simp [hp, hq, hpzero]
  · have hptop :=
      oneDimensionalIntegral_eq_top_of_not_one_lt p hp
    have hqzero := oneDimensionalIntegral_pos q
    refine ⟨0, ENNReal.zero_ne_top, ?_⟩
    rw [gap3, hptop]
    simp [hp, hqzero]

end

end ProofGap.Exercise4162
