import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4196

noncomputable section

open MeasureTheory

def cube : Set (ℝ × ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ z.1 ≤ 1 ∧
    0 ≤ z.2.1 ∧ z.2.1 ≤ 1 ∧
    0 ≤ z.2.2 ∧ z.2.2 ≤ 1}

def integrand (p q r : ℝ) (z : ℝ × ℝ × ℝ) : ℝ :=
  1 /
    (Real.rpow z.1 p * Real.rpow z.2.1 q *
      Real.rpow z.2.2 r)

def oneDimensional (p : ℝ) : ℝ :=
  ∫ x in Set.Ioc (0 : ℝ) 1, 1 / Real.rpow x p

def tripleIntegral (p q r : ℝ) : ℝ :=
  ∫ z in cube, integrand p q r z

private def factor (p x : ℝ) : ℝ := Real.rpow x (-p)

private theorem explicit_rpow_neg {x : ℝ} (hx : 0 ≤ x) (p : ℝ) :
    Real.rpow x (-p) = (Real.rpow x p)⁻¹ := by
  change x ^ (-p) = (x ^ p)⁻¹
  exact Real.rpow_neg hx p

private theorem cube_eq :
    cube = Set.Icc (0 : ℝ) 1 ×ˢ
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
  ext z
  simp only [cube, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Icc]
  tauto

private theorem measurableSet_cube : MeasurableSet cube := by
  rw [cube_eq]
  exact measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)

private theorem integrand_eq_factor (p q r : ℝ) :
    Set.EqOn (integrand p q r)
      (fun z => factor p z.1 * (factor q z.2.1 * factor r z.2.2)) cube := by
  intro z hz
  rcases hz with ⟨hx0, hx1, hy0, hy1, hz0, hz1⟩
  rw [integrand]
  simp only [factor]
  rw [explicit_rpow_neg hx0, explicit_rpow_neg hy0, explicit_rpow_neg hz0]
  simp only [one_div, mul_inv_rev]
  ring

private theorem integrand_one_eq_factor (p : ℝ) :
    Set.EqOn (fun x : ℝ => 1 / Real.rpow x p) (factor p) (Set.Ioc 0 1) := by
  intro x hx
  rw [factor, explicit_rpow_neg hx.1.le]
  simp only [one_div]

private theorem factor_integrable_iff (p : ℝ) :
    IntegrableOn (factor p) (Set.Icc (0 : ℝ) 1) ↔ p < 1 := by
  rw [integrableOn_Icc_iff_integrableOn_Ioo]
  rw [show factor p = fun x : ℝ => x ^ (-p) by
    funext x
    rfl]
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)]
  constructor <;> intro h <;> linarith

private theorem oneDimensional_value (p : ℝ) (hp : p < 1) :
    oneDimensional p = 1 / (1 - p) := by
  rw [oneDimensional]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (integrand_one_eq_factor p)]
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [show factor p = fun x : ℝ => x ^ (-p) by
    funext x
    rfl]
  rw [integral_rpow (Or.inl (by linarith : -1 < -p))]
  rw [Real.one_rpow, Real.zero_rpow (by linarith : -p + 1 ≠ 0)]
  field_simp
  ring

private theorem factor_integral_eq_oneDimensional (p : ℝ) :
    (∫ x in Set.Icc (0 : ℝ) 1, factor p x) = oneDimensional p := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [oneDimensional]
  exact
    (MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      (integrand_one_eq_factor p)).symm

private theorem integrable_mul_prod_iff
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {f : α → ℝ} {g : β → ℝ}
    (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (hf0 : ∀ᵐ x ∂μ, f x ≠ 0) (hg0 : ∀ᵐ y ∂ν, g y ≠ 0) :
    Integrable (fun z => f z.1 * g z.2) (μ.prod ν) ↔
      Integrable f μ ∧ Integrable g ν := by
  constructor
  · intro h
    have hνu : ν Set.univ ≠ 0 := by
      simpa [Measure.measure_univ_eq_zero] using hν
    have hallg :
        ∀ᵐ y ∂ν, g y ≠ 0 ∧ Integrable (fun x => f x * g y) μ :=
      by
        filter_upwards [hg0, h.prod_left_ae] with y hy0 hy
        exact ⟨hy0, hy⟩
    obtain ⟨y, -, hy0, hy⟩ :=
      Measure.exists_mem_of_measure_ne_zero_of_ae
        (p := fun y => g y ≠ 0 ∧ Integrable (fun x => f x * g y) μ)
        hνu (by simpa only [Measure.restrict_univ] using hallg)
    have hf : Integrable f μ := by
      have hs := hy.const_mul (g y)⁻¹
      convert hs using 1
      funext x
      field_simp
    have hμu : μ Set.univ ≠ 0 := by
      simpa [Measure.measure_univ_eq_zero] using hμ
    have hallf :
        ∀ᵐ x ∂μ, f x ≠ 0 ∧ Integrable (fun y => f x * g y) ν :=
      by
        filter_upwards [hf0, h.prod_right_ae] with x hx0 hx
        exact ⟨hx0, hx⟩
    obtain ⟨x, -, hx0, hx⟩ :=
      Measure.exists_mem_of_measure_ne_zero_of_ae
        (p := fun x => f x ≠ 0 ∧ Integrable (fun y => f x * g y) ν)
        hμu (by simpa only [Measure.restrict_univ] using hallf)
    have hg : Integrable g ν := by
      have hs := hx.const_mul (f x)⁻¹
      convert hs using 1
      funext y
      field_simp
    exact ⟨hf, hg⟩
  · rintro ⟨hf, hg⟩
    exact hf.mul_prod hg

private abbrev unitMeasure : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

private theorem unitMeasure_ne_zero : unitMeasure ≠ 0 := by
  intro h
  have hz : volume (Set.Icc (0 : ℝ) 1) = 0 :=
    Measure.restrict_eq_zero.mp h
  rw [Real.volume_Icc] at hz
  norm_num at hz

private theorem unitMeasure_prod_ne_zero :
    unitMeasure.prod unitMeasure ≠ 0 := by
  intro h
  have hu := congrArg (fun m : Measure (ℝ × ℝ) => m Set.univ) h
  simp [unitMeasure, Real.volume_Icc, ← Set.univ_prod_univ] at hu

private theorem factor_ne_zero_ae (p : ℝ) :
    ∀ᵐ x ∂unitMeasure, factor p x ≠ 0 := by
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc,
    Measure.ae_ne unitMeasure 0] with x hxmem hx0
  change Real.rpow x (-p) ≠ 0
  change x ^ (-p) ≠ 0
  exact ne_of_gt (Real.rpow_pos_of_pos (lt_of_le_of_ne hxmem.1 (Ne.symm hx0)) _)

private theorem measurable_factor (p : ℝ) : Measurable (factor p) := by
  have h : Measurable (fun x : ℝ => x ^ (-p)) :=
    measurable_id.pow measurable_const
  convert h using 1

private theorem pair_factor_ne_zero_ae (q r : ℝ) :
    ∀ᵐ z ∂unitMeasure.prod unitMeasure,
      factor q z.1 * factor r z.2 ≠ 0 := by
  apply (Measure.ae_prod_iff_ae_ae ?_).2
  · filter_upwards [factor_ne_zero_ae q] with x hx
    filter_upwards [factor_ne_zero_ae r] with y hy
    exact mul_ne_zero hx hy
  · change MeasurableSet
      ((fun z : ℝ × ℝ => factor q z.1 * factor r z.2) ⁻¹' ({0}ᶜ))
    exact (measurableSet_singleton 0).compl.preimage
      ((measurable_factor q).comp measurable_fst |>.mul
        ((measurable_factor r).comp measurable_snd))

private theorem integrableOn_integrand_iff_factors (p q r : ℝ) :
    IntegrableOn (integrand p q r) cube ↔
      Integrable
        (fun z => factor p z.1 * (factor q z.2.1 * factor r z.2.2))
        (unitMeasure.prod (unitMeasure.prod unitMeasure)) := by
  rw [MeasureTheory.integrableOn_congr_fun
    (integrand_eq_factor p q r) measurableSet_cube]
  rw [cube_eq]
  simp only [IntegrableOn]
  rw [Measure.volume_eq_prod ℝ (ℝ × ℝ)]
  rw [← Measure.prod_restrict]
  rw [Measure.volume_eq_prod ℝ ℝ]
  rw [← Measure.prod_restrict]

theorem gap1 (p q r : ℝ)
    (hp : p < 1) (hq : q < 1) (hr : r < 1) :
    tripleIntegral p q r =
      oneDimensional p * oneDimensional q * oneDimensional r := by
  rw [tripleIntegral]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_cube
    (integrand_eq_factor p q r)]
  rw [cube_eq]
  rw [Measure.volume_eq_prod ℝ (ℝ × ℝ)]
  rw [MeasureTheory.setIntegral_prod_mul
    (factor p) (fun z : ℝ × ℝ => factor q z.1 * factor r z.2)
    (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)]
  rw [Measure.volume_eq_prod ℝ ℝ]
  rw [MeasureTheory.setIntegral_prod_mul
    (factor q) (factor r) (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1)]
  rw [factor_integral_eq_oneDimensional, factor_integral_eq_oneDimensional,
    factor_integral_eq_oneDimensional]
  ring

theorem gap2 (p q r : ℝ) :
    (IntegrableOn (integrand p q r) cube ↔
      p < 1 ∧ q < 1 ∧ r < 1) ∧
    (p < 1 ∧ q < 1 ∧ r < 1 →
      tripleIntegral p q r =
        1 / ((1 - p) * (1 - q) * (1 - r))) := by
  constructor
  · rw [integrableOn_integrand_iff_factors]
    rw [integrable_mul_prod_iff unitMeasure_ne_zero unitMeasure_prod_ne_zero
      (factor_ne_zero_ae p) (pair_factor_ne_zero_ae q r)]
    rw [integrable_mul_prod_iff unitMeasure_ne_zero unitMeasure_ne_zero
      (factor_ne_zero_ae q) (factor_ne_zero_ae r)]
    change
      (IntegrableOn (factor p) (Set.Icc (0 : ℝ) 1) ∧
          IntegrableOn (factor q) (Set.Icc (0 : ℝ) 1) ∧
          IntegrableOn (factor r) (Set.Icc (0 : ℝ) 1)) ↔
        p < 1 ∧ q < 1 ∧ r < 1
    rw [factor_integrable_iff, factor_integrable_iff, factor_integrable_iff]
  · rintro ⟨hp, hq, hr⟩
    rw [gap1 p q r hp hq hr, oneDimensional_value p hp,
      oneDimensional_value q hq, oneDimensional_value r hr]
    have hp0 : 1 - p ≠ 0 := by linarith
    have hq0 : 1 - q ≠ 0 := by linarith
    have hr0 : 1 - r ≠ 0 := by linarith
    field_simp

end

end ProofGap.Exercise4196
