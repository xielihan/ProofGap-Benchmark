import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod

namespace ProofGap.Exercise4170

noncomputable section

open Filter MeasureTheory
open scoped ENNReal

abbrev Point := ℝ × ℝ

def region : Set Point :=
  {z | 0 ≤ z.1 ∧ z.1 ≤ 1 ∧ 1 ≤ z.1 + z.2}

def integrand (p x y : ℝ) : ℝ :=
  1 / Real.rpow (x + y) p

def integralValue (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in region, ENNReal.ofReal (integrand p z.1 z.2)

def innerIntegral (p x : ℝ) : ℝ≥0∞ :=
  ∫⁻ y in Set.Ici (1 - x), ENNReal.ofReal (integrand p x y)

def iteratedIntegral (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Set.Icc (0 : ℝ) 1, innerIntegral p x

def constantOuterIntegral (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ _x in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (1 / (p - 1))

private theorem innerIntegral_eq_canonical (p x : ℝ) :
    innerIntegral p x =
      ∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal (1 / Real.rpow t p) := by
  unfold innerIntegral integrand
  rw [← setLIntegral_congr (Ioi_ae_eq_Ici : Set.Ioi (1 - x) =ᵐ[volume] Set.Ici (1 - x))]
  have h :=
    ((measurePreserving_add_right volume x).restrict_preimage_emb
      (MeasurableEquiv.addRight x).measurableEmbedding (Set.Ioi (1 : ℝ))).lintegral_comp_emb
      (MeasurableEquiv.addRight x).measurableEmbedding
      (fun t : ℝ => ENNReal.ofReal (1 / Real.rpow t p))
  have hpre : (fun y : ℝ => y + x) ⁻¹' Set.Ioi (1 : ℝ) = Set.Ioi (1 - x) := by
    ext y
    change (1 < y + x) ↔ (1 - x < y)
    constructor <;> intro hy <;> linarith
  rw [hpre] at h
  simpa only [Function.comp_apply, add_comm] using h

private theorem measurableSet_region : MeasurableSet region := by
  unfold region
  measurability

private theorem measurable_integrand_ofReal (p : ℝ) :
    Measurable (fun z : Point => ENNReal.ofReal (integrand p z.1 z.2)) := by
  have hrpow : Measurable (fun t : ℝ => Real.rpow t p) := by
    apply measurable_of_continuousOn_compl_singleton 0
    exact continuousOn_id.rpow_const (fun t ht => Or.inl (by simpa using ht))
  exact (measurable_const.div
    (hrpow.comp (measurable_fst.add measurable_snd))).ennreal_ofReal

private theorem canonical_lintegral_eq_top (p : ℝ) (hp : p ≤ 1) :
    (∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal (1 / Real.rpow t p)) = ⊤ := by
  have hpow : Set.EqOn (fun t : ℝ => 1 / Real.rpow t p)
      (fun t => t ^ (-p)) (Set.Ioi (1 : ℝ)) := by
    intro t ht
    simpa [one_div] using
      (Real.rpow_neg (le_of_lt (zero_lt_one.trans ht)) p).symm
  rw [setLIntegral_congr_fun measurableSet_Ioi
    (fun t ht => congrArg ENNReal.ofReal (hpow ht))]
  have hmeas : AEStronglyMeasurable (fun t : ℝ => t ^ (-p))
      (volume.restrict (Set.Ioi (1 : ℝ))) := by
    exact (continuousOn_id.rpow_const
      (fun t ht => Or.inl (ne_of_gt (zero_lt_one.trans ht)))).aestronglyMeasurable
        measurableSet_Ioi
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (1 : ℝ))]
      (fun t : ℝ => t ^ (-p)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (le_of_lt (zero_lt_one.trans ht)) _
  by_contra htop
  have hi : IntegrableOn (fun t : ℝ => t ^ (-p)) (Set.Ioi (1 : ℝ)) :=
    (lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg).mp htop
  have hp' := (integrableOn_Ioi_rpow_iff zero_lt_one).mp hi
  linarith

theorem gap1 (p : ℝ) :
    integralValue p = iteratedIntegral p := by
  unfold integralValue iteratedIntegral innerIntegral
  rw [Measure.volume_eq_prod]
  rw [← lintegral_indicator measurableSet_region]
  rw [lintegral_prod]
  · rw [← lintegral_indicator measurableSet_Icc]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
    · simp only [Set.indicator_of_mem hx]
      rw [← lintegral_indicator measurableSet_Ici]
      apply lintegral_congr
      intro y
      by_cases hy : y ∈ Set.Ici (1 - x)
      · simp only [Set.indicator_of_mem hy]
        have hz : (x, y) ∈ region := by
          simp only [region, Set.mem_setOf_eq, Set.mem_Icc] at hx ⊢
          exact ⟨hx.1, hx.2, by linarith [Set.mem_Ici.mp hy]⟩
        rw [Set.indicator_of_mem hz]
      · simp only [Set.indicator_of_notMem hy]
        have hz : (x, y) ∉ region := by
          simp only [region, Set.mem_setOf_eq, Set.mem_Icc] at hx
          intro hz
          apply hy
          exact Set.mem_Ici.mpr (by linarith [hz.2.2])
        rw [Set.indicator_of_notMem hz]
    · simp only [Set.indicator_of_notMem hx]
      have hzero :
          (fun y : ℝ => region.indicator
            (fun z : Point => ENNReal.ofReal (integrand p z.1 z.2)) (x, y)) =
            (fun _ => 0) := by
        funext y
        have hz : (x, y) ∉ region := by
          simp only [region, Set.mem_setOf_eq, Set.mem_Icc] at hx
          intro hz
          exact hx ⟨hz.1, hz.2.1⟩
        rw [Set.indicator_of_notMem hz]
      rw [hzero, lintegral_zero]
  · exact (measurable_integrand_ofReal p).aemeasurable.indicator measurableSet_region

theorem gap2 (p x : ℝ) (hp : 1 < p) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    innerIntegral p x = ENNReal.ofReal (1 / (p - 1)) := by
  rw [innerIntegral_eq_canonical]
  have hpow : Set.EqOn (fun t : ℝ => 1 / Real.rpow t p)
      (fun t => t ^ (-p)) (Set.Ioi (1 : ℝ)) := by
    intro t ht
    simpa [one_div] using
      (Real.rpow_neg (le_of_lt (zero_lt_one.trans ht)) p).symm
  rw [setLIntegral_congr_fun measurableSet_Ioi
    (fun t ht => congrArg ENNReal.ofReal (hpow ht))]
  have hi : IntegrableOn (fun t : ℝ => t ^ (-p)) (Set.Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (1 : ℝ))]
      (fun t : ℝ => t ^ (-p)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (le_of_lt (zero_lt_one.trans ht)) _
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnonneg]
  rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
  apply congrArg ENNReal.ofReal
  norm_num
  have h₁ : -p + 1 ≠ 0 := by linarith
  have h₂ : p - 1 ≠ 0 := by linarith
  field_simp [h₁, h₂]
  ring

theorem gap3 (p : ℝ) (hp : p ≤ 1) :
    integralValue p = ⊤ := by
  rw [gap1]
  unfold iteratedIntegral
  have hinner : ∀ x : ℝ, innerIntegral p x = ⊤ := fun x =>
    (innerIntegral_eq_canonical p x).trans (canonical_lintegral_eq_top p hp)
  simp_rw [hinner]
  simp [Real.volume_Icc]

theorem gap4 (p : ℝ) (hp : 1 < p) :
    integralValue p = constantOuterIntegral p := by
  rw [gap1]
  unfold iteratedIntegral constantOuterIntegral
  apply setLIntegral_congr_fun measurableSet_Icc
  intro x hx
  exact gap2 p x hp hx

theorem gap5 (p : ℝ) (hp : 1 < p) :
    constantOuterIntegral p = ENNReal.ofReal (1 / (p - 1)) := by
  unfold constantOuterIntegral
  simp [Real.volume_Icc]

theorem gap6 (p : ℝ) (hp : 1 < p) :
    integralValue p = ENNReal.ofReal (1 / (p - 1)) := by
  exact (gap4 p hp).trans (gap5 p hp)

theorem gap7 (p : ℝ) :
    integralValue p =
      if 1 < p then ENNReal.ofReal (1 / (p - 1)) else ⊤ := by
  by_cases hp : 1 < p
  · simp [hp, gap6 p hp]
  · have hp' : p ≤ 1 := le_of_not_gt hp
    simp [hp, gap3 p hp']

end

end ProofGap.Exercise4170
