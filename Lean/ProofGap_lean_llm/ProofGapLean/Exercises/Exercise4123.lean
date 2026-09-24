import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4123

noncomputable section

open MeasureTheory
open scoped Interval

def forwardMap (a b c : ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (p.1 / a,
    p.1 / a + p.2.1 / b,
    p.1 / a + p.2.1 / b + p.2.2 / c)

def inverseMap (a b c : ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (a * p.1, b * (p.2.1 - p.1), c * (p.2.2 - p.2.1))

def forwardJacobian (a b c : ℝ) : ℝ :=
  1 / (a * b * c)

def inverseJacobian (a b c : ℝ) : ℝ :=
  a * b * c

def lowerBound (w : ℝ) : ℝ :=
  (2 / Real.pi) * w * Real.arcsin w

def parameterDomain : Set (ℝ × ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧
    lowerBound p.2.2 ≤ p.2.1 ∧ p.2.1 ≤ 1 ∧
    -1 ≤ p.2.2 ∧ p.2.2 ≤ 1}

/-- The full-dimensional region intended by the source's subsequent volume computation. -/
def region (a b c : ℝ) : Set (ℝ × ℝ × ℝ) :=
  inverseMap a b c '' parameterDomain

def volume (a b c : ℝ) : ℝ :=
  ∫ _ in region a b c, (1 : ℝ)

def betaFn (x y : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    Real.rpow t (x - 1) * Real.rpow (1 - t) (y - 1)

private def coordinateEquiv :
    (ℝ × ℝ × ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) :=
  { toFun := fun p => ![p.1, p.2.1, p.2.2]
    invFun := fun x => (x 0, x 1, x 2)
    left_inv := by
      intro p
      ext <;> simp
    right_inv := by
      intro x
      funext i
      fin_cases i <;> simp
    map_add' := by
      intro p q
      funext i
      fin_cases i <;> simp
    map_smul' := by
      intro r p
      funext i
      fin_cases i <;> simp }

private def inverseLinear (a b c : ℝ) :
    (ℝ × ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ × ℝ) :=
  let A : Matrix (Fin 3) (Fin 3) ℝ :=
    ![![a, 0, 0], ![(-b), b, 0], ![0, (-c), c] ]
  (coordinateEquiv.symm : (Fin 3 → ℝ) →ₗ[ℝ] (ℝ × ℝ × ℝ)) ∘ₗ
    Matrix.toLin' A ∘ₗ
      (coordinateEquiv : (ℝ × ℝ × ℝ) →ₗ[ℝ] (Fin 3 → ℝ))

@[simp] private theorem inverseLinear_apply
    (a b c : ℝ) (p : ℝ × ℝ × ℝ) :
    inverseLinear a b c p = inverseMap a b c p := by
  ext <;>
    simp [inverseLinear, coordinateEquiv, inverseMap,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;>
    ring

private theorem inverseLinear_det (a b c : ℝ) :
    LinearMap.det (inverseLinear a b c) = a * b * c := by
  let A : Matrix (Fin 3) (Fin 3) ℝ :=
    ![![a, 0, 0], ![(-b), b, 0], ![0, (-c), c] ]
  change
    LinearMap.det
        ((coordinateEquiv.symm :
            (Fin 3 → ℝ) →ₗ[ℝ] (ℝ × ℝ × ℝ)) ∘ₗ
          Matrix.toLin' A ∘ₗ
            (coordinateEquiv :
              (ℝ × ℝ × ℝ) →ₗ[ℝ] (Fin 3 → ℝ))) =
      a * b * c
  have hconj :
      LinearMap.det
          ((coordinateEquiv.symm :
              (Fin 3 → ℝ) →ₗ[ℝ] (ℝ × ℝ × ℝ)) ∘ₗ
            Matrix.toLin' A ∘ₗ
              (coordinateEquiv :
                (ℝ × ℝ × ℝ) →ₗ[ℝ] (Fin 3 → ℝ))) =
        LinearMap.det (Matrix.toLin' A) := by
    simpa only [LinearEquiv.symm_symm] using
      (LinearMap.det_conj (Matrix.toLin' A) coordinateEquiv.symm)
  rw [hconj]
  simp only [LinearMap.det_toLin']
  rw [Matrix.det_fin_three]
  simp [A]

private def orderedParameterDomain : Set (ℝ × ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧
    -1 ≤ p.2.1 ∧ p.2.1 ≤ 1 ∧
    lowerBound p.2.1 ≤ p.2.2 ∧ p.2.2 ≤ 1}

private def swapLastLinear :
    (ℝ × ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ × ℝ) :=
  let A : Matrix (Fin 3) (Fin 3) ℝ :=
    ![![1, 0, 0], ![0, 0, 1], ![0, 1, 0] ]
  (coordinateEquiv.symm : (Fin 3 → ℝ) →ₗ[ℝ] (ℝ × ℝ × ℝ)) ∘ₗ
    Matrix.toLin' A ∘ₗ
      (coordinateEquiv : (ℝ × ℝ × ℝ) →ₗ[ℝ] (Fin 3 → ℝ))

@[simp] private theorem swapLastLinear_apply (p : ℝ × ℝ × ℝ) :
    swapLastLinear p = (p.1, p.2.2, p.2.1) := by
  ext <;>
    simp [swapLastLinear, coordinateEquiv, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private theorem swapLastLinear_det :
    LinearMap.det swapLastLinear = -1 := by
  let A : Matrix (Fin 3) (Fin 3) ℝ :=
    ![![1, 0, 0], ![0, 0, 1], ![0, 1, 0] ]
  change
    LinearMap.det
        ((coordinateEquiv.symm :
            (Fin 3 → ℝ) →ₗ[ℝ] (ℝ × ℝ × ℝ)) ∘ₗ
          Matrix.toLin' A ∘ₗ
            (coordinateEquiv :
              (ℝ × ℝ × ℝ) →ₗ[ℝ] (Fin 3 → ℝ))) =
      -1
  have hconj :
      LinearMap.det
          ((coordinateEquiv.symm :
              (Fin 3 → ℝ) →ₗ[ℝ] (ℝ × ℝ × ℝ)) ∘ₗ
            Matrix.toLin' A ∘ₗ
              (coordinateEquiv :
                (ℝ × ℝ × ℝ) →ₗ[ℝ] (Fin 3 → ℝ))) =
        LinearMap.det (Matrix.toLin' A) := by
    simpa only [LinearEquiv.symm_symm] using
      (LinearMap.det_conj (Matrix.toLin' A) coordinateEquiv.symm)
  rw [hconj]
  simp only [LinearMap.det_toLin']
  rw [Matrix.det_fin_three]
  simp [A]

private theorem swapLast_image_parameterDomain :
    swapLastLinear '' parameterDomain = orderedParameterDomain := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases hp with ⟨hu0, hu1, hv0, hv1, hw0, hw1⟩
    simpa [orderedParameterDomain] using
      (show
        0 ≤ p.1 ∧ p.1 ≤ 1 ∧
          -1 ≤ p.2.2 ∧ p.2.2 ≤ 1 ∧
          lowerBound p.2.2 ≤ p.2.1 ∧ p.2.1 ≤ 1
        from ⟨hu0, hu1, hw0, hw1, hv0, hv1⟩)
  · intro hq
    let p : ℝ × ℝ × ℝ := (q.1, q.2.2, q.2.1)
    refine ⟨p, ?_, ?_⟩
    · rcases hq with ⟨hu0, hu1, hw0, hw1, hv0, hv1⟩
      simpa [p, parameterDomain] using
        (show
          0 ≤ q.1 ∧ q.1 ≤ 1 ∧
            lowerBound q.2.1 ≤ q.2.2 ∧ q.2.2 ≤ 1 ∧
            -1 ≤ q.2.1 ∧ q.2.1 ≤ 1
          from ⟨hu0, hu1, hv0, hv1, hw0, hw1⟩)
    · rcases q with ⟨u, w, v⟩
      simp [p]

private theorem parameterDomain_integral_eq_ordered :
    (∫ _p in parameterDomain, (1 : ℝ)) =
      ∫ _p in orderedParameterDomain, (1 : ℝ) := by
  letI : Measure.IsAddHaarMeasure
      (MeasureTheory.volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  letI : Measure.IsAddHaarMeasure
      (MeasureTheory.volume : Measure (ℝ × (ℝ × ℝ))) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hm :=
    Measure.addHaar_image_linearMap
      (MeasureTheory.volume : Measure (ℝ × (ℝ × ℝ)))
      swapLastLinear parameterDomain
  rw [swapLast_image_parameterDomain, swapLastLinear_det] at hm
  norm_num at hm
  rw [MeasureTheory.integral_const, MeasureTheory.integral_const]
  simp only [smul_eq_mul, mul_one]
  rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def]
  simpa only [Measure.restrict_apply_univ] using
    congrArg ENNReal.toReal hm.symm

private theorem parameterDomain_iteratedIntegral :
    (∫ _p in parameterDomain, (1 : ℝ)) =
      ∫ u in (0 : ℝ)..1,
        ∫ w in (-1 : ℝ)..1,
          ∫ v in lowerBound w..1, (1 : ℝ) := by
  classical
  have hs : MeasurableSet orderedParameterDomain := by
    unfold orderedParameterDomain lowerBound
    measurability
  have hlower_le {w : ℝ} (hw0 : -1 ≤ w) (hw1 : w ≤ 1) :
      lowerBound w ≤ 1 := by
    unfold lowerBound
    have harcsin_le :
        Real.arcsin w ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two w
    have harcsin_ge :
        -Real.pi / 2 ≤ Real.arcsin w :=
      by simpa [neg_div] using Real.neg_pi_div_two_le_arcsin w
    have hpi : 0 < Real.pi := Real.pi_pos
    by_cases hw : 0 ≤ w
    · have : w * Real.arcsin w ≤ 1 * (Real.pi / 2) := by
        exact mul_le_mul hw1 harcsin_le
          (Real.arcsin_nonneg.mpr hw) (by norm_num)
      field_simp [Real.pi_ne_zero]
      nlinarith
    · have hw' : w ≤ 0 := le_of_not_ge hw
      have ha : Real.arcsin w ≤ 0 := Real.arcsin_nonpos.mpr hw'
      have hprod : w * Real.arcsin w ≤ Real.pi / 2 := by
        have hwabs : -w ≤ 1 := by linarith
        have haabs : -Real.arcsin w ≤ Real.pi / 2 := by linarith
        nlinarith [mul_le_mul hwabs haabs (by linarith) (by linarith)]
      field_simp [Real.pi_ne_zero]
      nlinarith
  have hlower_ge {w : ℝ} (hw0 : -1 ≤ w) (hw1 : w ≤ 1) :
      -1 ≤ lowerBound w := by
    have hprod : 0 ≤ w * Real.arcsin w := by
      by_cases hw : 0 ≤ w
      · exact mul_nonneg hw (Real.arcsin_nonneg.mpr hw)
      · have hw' : w ≤ 0 := le_of_not_ge hw
        exact mul_nonneg_of_nonpos_of_nonpos hw'
          (Real.arcsin_nonpos.mpr hw')
    unfold lowerBound
    have hcoef : 0 ≤ 2 / Real.pi := by positivity
    nlinarith [mul_nonneg hcoef hprod]
  have hsubset :
      orderedParameterDomain ⊆
        Set.Icc (0 : ℝ) 1 ×ˢ
          (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) := by
    intro q hq
    rcases hq with ⟨hu0, hu1, hw0, hw1, hv0, hv1⟩
    have hvneg : -1 ≤ q.2.2 :=
      le_trans (hlower_ge hw0 hw1) hv0
    exact ⟨⟨hu0, hu1⟩, ⟨⟨hw0, hw1⟩, hvneg, hv1⟩⟩
  have hbox :
      IntegrableOn (fun _q : ℝ × ℝ × ℝ => (1 : ℝ))
        (Set.Icc (0 : ℝ) 1 ×ˢ
          (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1))
        MeasureTheory.volume :=
    ((continuous_const :
      Continuous (fun _q : ℝ × ℝ × ℝ => (1 : ℝ))).continuousOn).integrableOn_compact
          (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  have hri :
      IntegrableOn (fun _q : ℝ × ℝ × ℝ => (1 : ℝ))
        orderedParameterDomain MeasureTheory.volume :=
    hbox.mono_set hsubset
  have hind :
      Integrable
        (orderedParameterDomain.indicator
          (fun _q : ℝ × ℝ × ℝ => (1 : ℝ)))
        MeasureTheory.volume :=
    (integrable_indicator_iff hs).2 hri
  change
    Integrable
      (orderedParameterDomain.indicator
        (fun _q : ℝ × ℝ × ℝ => (1 : ℝ)))
      (MeasureTheory.volume.prod
        (MeasureTheory.volume.prod MeasureTheory.volume)) at hind
  have hprod :
      (∫ q : ℝ × ℝ × ℝ,
          orderedParameterDomain.indicator (fun _q => (1 : ℝ)) q
            ∂MeasureTheory.volume.prod
              (MeasureTheory.volume.prod MeasureTheory.volume)) =
        ∫ u : ℝ, ∫ w : ℝ, ∫ v : ℝ,
          orderedParameterDomain.indicator
            (fun _q => (1 : ℝ)) (u, w, v) := by
    rw [MeasureTheory.integral_prod _ hind]
    apply integral_congr_ae
    filter_upwards [hind.prod_right_ae] with u hu
    change
      (∫ wv : ℝ × ℝ,
          orderedParameterDomain.indicator (fun _q => (1 : ℝ)) (u, wv)
            ∂MeasureTheory.volume.prod MeasureTheory.volume) =
        ∫ w : ℝ, ∫ v : ℝ,
          orderedParameterDomain.indicator (fun _q => (1 : ℝ)) (u, w, v)
    rw [MeasureTheory.integral_prod _ hu]
  have hsections :
      (∫ u : ℝ, ∫ w : ℝ, ∫ v : ℝ,
          orderedParameterDomain.indicator
            (fun _q => (1 : ℝ)) (u, w, v)) =
        ∫ u in Set.Icc (0 : ℝ) 1,
          ∫ w in Set.Icc (-1 : ℝ) 1,
            ∫ v in Set.Icc (lowerBound w) 1, (1 : ℝ) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with u
    by_cases hu : u ∈ Set.Icc (0 : ℝ) 1
    · rw [Set.indicator_of_mem hu]
      rw [← MeasureTheory.integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards with w
      by_cases hw : w ∈ Set.Icc (-1 : ℝ) 1
      · rw [Set.indicator_of_mem hw]
        rw [← MeasureTheory.integral_indicator measurableSet_Icc]
        apply integral_congr_ae
        filter_upwards with v
        by_cases hv : v ∈ Set.Icc (lowerBound w) 1
        · have hp : (u, w, v) ∈ orderedParameterDomain :=
            ⟨hu.1, hu.2, hw.1, hw.2, hv.1, hv.2⟩
          simp only [Set.indicator_of_mem hv,
            Set.indicator_of_mem hp]
        · have hnp : (u, w, v) ∉ orderedParameterDomain := by
            intro hp
            exact hv ⟨hp.2.2.2.2.1, hp.2.2.2.2.2⟩
          simp [Set.indicator, hv, hnp]
      · have hwr :
            (Set.Icc (-1 : ℝ) 1).indicator
              (fun w =>
                ∫ v in Set.Icc (lowerBound w) 1, (1 : ℝ)) w = 0 := by
          simp [Set.indicator, hw]
        rw [hwr, ← integral_zero]
        apply integral_congr_ae
        filter_upwards with v
        have hnp : (u, w, v) ∉ orderedParameterDomain := by
          intro hp
          exact hw ⟨hp.2.2.1, hp.2.2.2.1⟩
        simp [Set.indicator, hnp]
    · have hur :
          (Set.Icc (0 : ℝ) 1).indicator
            (fun u =>
              ∫ w in Set.Icc (-1 : ℝ) 1,
                ∫ v in Set.Icc (lowerBound w) 1, (1 : ℝ)) u = 0 := by
        simp [Set.indicator, hu]
      rw [hur, ← integral_zero]
      apply integral_congr_ae
      filter_upwards with w
      rw [← integral_zero]
      apply integral_congr_ae
      filter_upwards with v
      have hnp : (u, w, v) ∉ orderedParameterDomain := by
        intro hp
        exact hu ⟨hp.1, hp.2.1⟩
      simp [Set.indicator, hnp]
  calc
    (∫ _p in parameterDomain, (1 : ℝ)) =
        ∫ _p in orderedParameterDomain, (1 : ℝ) :=
      parameterDomain_integral_eq_ordered
    _ = ∫ q : ℝ × ℝ × ℝ,
          orderedParameterDomain.indicator (fun _q => (1 : ℝ)) q := by
      rw [MeasureTheory.integral_indicator hs]
    _ = ∫ u : ℝ, ∫ w : ℝ, ∫ v : ℝ,
          orderedParameterDomain.indicator
            (fun _q => (1 : ℝ)) (u, w, v) := hprod
    _ = ∫ u in Set.Icc (0 : ℝ) 1,
          ∫ w in Set.Icc (-1 : ℝ) 1,
            ∫ v in Set.Icc (lowerBound w) 1, (1 : ℝ) := hsections
    _ = ∫ u in (0 : ℝ)..1,
          ∫ w in (-1 : ℝ)..1,
            ∫ v in lowerBound w..1, (1 : ℝ) := by
      rw [intervalIntegral.integral_of_le
        (by norm_num : (0 : ℝ) ≤ 1)]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro u hu
      dsimp only
      rw [intervalIntegral.integral_of_le
        (by norm_num : (-1 : ℝ) ≤ 1)]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro w hw
      dsimp only
      rw [intervalIntegral.integral_of_le
        (hlower_le hw.1.le hw.2)]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]

private theorem singularRadial_intervalIntegrable :
    IntervalIntegrable
      (fun w : ℝ => w ^ 2 / Real.sqrt (1 - w ^ 2))
      MeasureTheory.volume 0 1 := by
  have hbase :
      IntervalIntegrable
        (fun t : ℝ => Real.rpow (1 - t) (-1 / 2 : ℝ))
        MeasureTheory.volume 0 1 := by
    have h := (intervalIntegral.intervalIntegrable_rpow'
      (a := (0 : ℝ)) (b := 1) (r := (-1 / 2 : ℝ))
      (by norm_num)).comp_sub_left 1
    norm_num at h ⊢
    exact h.symm
  apply hbase.mono_fun
  · exact
      ((measurable_id.pow_const 2).div
        ((measurable_const.sub
          (measurable_id.pow_const 2)).sqrt)).aestronglyMeasurable
  · filter_upwards
      [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with w hw
    rw [Set.uIoc_of_le zero_le_one] at hw
    have hw0 : 0 ≤ w := hw.1.le
    have hw1 : w ≤ 1 := hw.2
    have hsub0 : 0 ≤ 1 - w := sub_nonneg.mpr hw1
    have hsquare_le : w ^ 2 ≤ w := by
      nlinarith [mul_nonneg hw0 (sub_nonneg.mpr hw1)]
    have hsubsq0 : 0 ≤ 1 - w ^ 2 := by linarith
    have hrpow_eq :
        Real.rpow (1 - w) (-1 / 2 : ℝ) =
          1 / Real.sqrt (1 - w) := by
      rw [Real.rpow_eq_pow,
        show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
        Real.rpow_neg hsub0 (1 / 2 : ℝ),
        ← Real.sqrt_eq_rpow]
      simp only [one_div]
    by_cases hweq : w = 1
    · subst w
      norm_num [Real.rpow_zero]
    · have hwlt : w < 1 := lt_of_le_of_ne hw1 hweq
      have hsqrtpos : 0 < Real.sqrt (1 - w) :=
        Real.sqrt_pos.2 (sub_pos.mpr hwlt)
      have hsqrtle :
          Real.sqrt (1 - w) ≤ Real.sqrt (1 - w ^ 2) :=
        Real.sqrt_le_sqrt (by linarith)
      have hinv :
          1 / Real.sqrt (1 - w ^ 2) ≤
            1 / Real.sqrt (1 - w) :=
        one_div_le_one_div_of_le hsqrtpos hsqrtle
      have hw2le : w ^ 2 ≤ 1 := le_trans hsquare_le hw1
      have hjnonneg :
          0 ≤ w ^ 2 / Real.sqrt (1 - w ^ 2) :=
        div_nonneg (sq_nonneg w) (Real.sqrt_nonneg _)
      have hrnonneg :
          0 ≤ Real.rpow (1 - w) (-1 / 2 : ℝ) :=
        Real.rpow_nonneg hsub0 _
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hjnonneg, abs_of_nonneg hrnonneg, hrpow_eq]
      exact
        (div_le_div_of_nonneg_right hw2le
          (Real.sqrt_nonneg _)).trans hinv

private theorem twice_singularRadial_eq_beta :
    2 * (∫ w in (0 : ℝ)..1,
      w ^ 2 / Real.sqrt (1 - w ^ 2)) =
      ∫ t in (0 : ℝ)..1,
        Real.rpow t (1 / 2 : ℝ) *
          Real.rpow (1 - t) (-1 / 2 : ℝ) := by
  let sqMap : ℝ → ℝ := fun w => w ^ 2
  let sqDeriv : ℝ → ℝ := fun w => 2 * w
  let g : ℝ → ℝ := fun t =>
    t ^ (1 / 2 : ℝ) * (1 - t) ^ (-1 / 2 : ℝ)
  have hsing :
      IntervalIntegrable (fun t : ℝ => (1 - t) ^ (-1 / 2 : ℝ))
        MeasureTheory.volume 0 1 := by
    have h := (intervalIntegral.intervalIntegrable_rpow'
      (a := (0 : ℝ)) (b := 1) (r := (-1 / 2 : ℝ))
      (by norm_num)).comp_sub_left 1
    norm_num at h ⊢
    exact h.symm
  have hgInt :
      IntervalIntegrable g MeasureTheory.volume 0 1 := by
    have hroot :
        Continuous (fun t : ℝ => t ^ (1 / 2 : ℝ)) :=
      Real.continuous_rpow_const (by norm_num)
    have hmul :=
      hsing.mul_continuousOn hroot.continuousOn
    exact hmul.congr (by
      intro t ht
      dsimp [g]
      ring)
  have hsquare :
      ContinuousOn sqMap (Set.uIcc (0 : ℝ) 1) := by
    dsimp [sqMap]
    fun_prop
  have hsquareDeriv :
      ∀ w ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
        HasDerivWithinAt sqMap (sqDeriv w) (Set.Ioi w) w := by
    intro w hw
    dsimp [sqMap, sqDeriv]
    convert (hasDerivAt_pow 2 w).hasDerivWithinAt using 1 <;> ring
  have hgcont :
      ContinuousOn g
        (sqMap '' Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1)) := by
    apply continuousOn_of_forall_continuousAt
    intro t ht
    rcases ht with ⟨w, hw, rfl⟩
    simp only [min_eq_left zero_le_one, max_eq_right zero_le_one,
      Set.mem_Ioo] at hw
    have hw0 : 0 < w ^ 2 := sq_pos_of_pos hw.1
    have hw1 : w ^ 2 < 1 := by nlinarith
    dsimp [g]
    exact
      (Real.continuousAt_rpow_const _ _ (Or.inl hw0.ne')).mul
        ((continuousAt_const.sub
          continuousAt_id).rpow_const
            (Or.inl (sub_ne_zero.mpr hw1.ne')))
  have himage :
      sqMap '' Set.uIcc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le zero_le_one]
    ext t
    constructor
    · rintro ⟨w, hw, rfl⟩
      dsimp [sqMap]
      exact ⟨sq_nonneg w, by
        nlinarith [mul_nonneg hw.1 (sub_nonneg.mpr hw.2)]⟩
    · intro ht
      refine ⟨Real.sqrt t, ?_, ?_⟩
      · exact ⟨Real.sqrt_nonneg t,
          Real.sqrt_le_one.2 ht.2⟩
      · dsimp [sqMap]
        rw [Real.sq_sqrt ht.1]
  have hgOn :
      IntegrableOn g
        (sqMap '' Set.uIcc (0 : ℝ) 1) MeasureTheory.volume := by
    rw [himage]
    have hIoc :
        IntegrableOn g (Set.Ioc (0 : ℝ) 1)
          MeasureTheory.volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hgInt
    exact hIoc.congr_set_ae MeasureTheory.Ioc_ae_eq_Icc.symm
  have hsourceEq :
      Set.EqOn
        (fun w => (g ∘ sqMap) w * sqDeriv w)
        (fun w => 2 * (w ^ 2 / Real.sqrt (1 - w ^ 2)))
        (Set.Icc (0 : ℝ) 1) := by
    intro w hw
    have hw0 : 0 ≤ w := hw.1
    have hsub0 : 0 ≤ 1 - w ^ 2 := by
      nlinarith [mul_nonneg hw.1 (sub_nonneg.mpr hw.2)]
    have hroot : (w ^ 2) ^ (1 / 2 : ℝ) = w := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hw0]
    have hinv :
        (1 - w ^ 2) ^ (-1 / 2 : ℝ) =
          1 / Real.sqrt (1 - w ^ 2) := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
        Real.rpow_neg hsub0 (1 / 2 : ℝ),
        ← Real.sqrt_eq_rpow]
      simp only [one_div]
    dsimp [g, sqMap, sqDeriv, Function.comp_def]
    rw [hroot, hinv]
    ring
  have hsourceOn :
      IntegrableOn (fun w => (g ∘ sqMap) w * sqDeriv w)
        (Set.uIcc (0 : ℝ) 1) MeasureTheory.volume := by
    rw [Set.uIcc_of_le zero_le_one]
    have htwo :
        IntervalIntegrable
          (fun w : ℝ => 2 * (w ^ 2 / Real.sqrt (1 - w ^ 2)))
          MeasureTheory.volume 0 1 :=
      singularRadial_intervalIntegrable.const_mul 2
    have hIoc :
        IntegrableOn
          (fun w : ℝ => 2 * (w ^ 2 / Real.sqrt (1 - w ^ 2)))
          (Set.Ioc (0 : ℝ) 1) MeasureTheory.volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 htwo
    have hIcc := hIoc.congr_set_ae
      MeasureTheory.Ioc_ae_eq_Icc.symm
    exact hIcc.congr_fun hsourceEq.symm measurableSet_Icc
  have hsub :=
    intervalIntegral.integral_comp_mul_deriv'''
      hsquare hsquareDeriv hgcont hgOn hsourceOn
  have hleft :
      (∫ w in (0 : ℝ)..1,
        (g ∘ sqMap) w * sqDeriv w) =
        2 * ∫ w in (0 : ℝ)..1,
          w ^ 2 / Real.sqrt (1 - w ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro w hw
    rw [Set.uIcc_of_le zero_le_one] at hw
    exact hsourceEq hw
  rw [hleft] at hsub
  norm_num [sqMap] at hsub
  simpa [g, Real.rpow_eq_pow] using hsub

private theorem betaFn_three_halves_one_half :
    betaFn (3 / 2) (1 / 2) = Real.pi / 2 := by
  rw [← Complex.ofReal_inj]
  have hbeta :
      (betaFn (3 / 2) (1 / 2) : ℂ) =
        Complex.betaIntegral (3 / 2) (1 / 2) := by
    rw [betaFn, ← intervalIntegral.integral_ofReal,
      Complex.betaIntegral]
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [Set.uIcc_of_le zero_le_one, Set.mem_Icc] at hx
    dsimp only
    push_cast
    norm_num
    have hxpow :
        (((x ^ (1 / 2 : ℝ)) : ℝ) : ℂ) =
          (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ) :=
      Complex.ofReal_cpow hx.1 (1 / 2 : ℝ)
    have honepow :
        ((((1 - x) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ) =
          ((1 - x : ℝ) : ℂ) ^ ((-(1 / 2 : ℝ)) : ℂ) :=
      by
        convert
          Complex.ofReal_cpow
            (sub_nonneg.mpr hx.2) (-(1 / 2 : ℝ))
          using 1 <;> norm_num
    rw [hxpow, honepow]
    push_cast
    norm_num
  rw [hbeta]
  rw [Complex.betaIntegral_eq_Gamma_mul_div
    (3 / 2) (1 / 2) (by norm_num) (by norm_num)]
  have h32 : (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) := by norm_num
  have h12 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  have hsum :
      ((3 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) =
        ((2 : ℝ) : ℂ) := by norm_num
  rw [h32, h12, hsum]
  rw [Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal]
  push_cast
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
    Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0),
    Real.Gamma_one_half_eq]
  rw [show (2 : ℝ) = (1 : ℕ) + 1 by norm_num,
    Real.Gamma_nat_eq_factorial]
  norm_num
  have hsqrt :
      Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_pos.le
  calc
    (1 / 2 : ℂ) * (Real.sqrt Real.pi : ℂ) *
          (Real.sqrt Real.pi : ℂ) =
        (1 / 2 : ℂ) *
          ((Real.sqrt Real.pi * Real.sqrt Real.pi : ℝ) : ℂ) := by
      push_cast
      ring
    _ = (1 / 2 : ℂ) * (Real.pi : ℂ) := by rw [hsqrt]
    _ = (Real.pi : ℂ) / 2 := by ring

private theorem singularRadial_value :
    (∫ w in (0 : ℝ)..1,
      w ^ 2 / Real.sqrt (1 - w ^ 2)) =
      Real.pi / 4 := by
  have h := twice_singularRadial_eq_beta
  have hbeta :
      (∫ t in (0 : ℝ)..1,
        Real.rpow t (1 / 2 : ℝ) *
          Real.rpow (1 - t) (-1 / 2 : ℝ)) =
        betaFn (3 / 2) (1 / 2) := by
    norm_num [betaFn]
  rw [hbeta, betaFn_three_halves_one_half] at h
  linarith

private theorem arcsinMoment_value :
    (∫ w in (0 : ℝ)..1, w * Real.arcsin w) =
      Real.pi / 8 := by
  let F : ℝ → ℝ := fun w => (w ^ 2 / 2) * Real.arcsin w
  let f : ℝ → ℝ := fun w =>
    w * Real.arcsin w +
      (1 / 2) * (w ^ 2 / Real.sqrt (1 - w ^ 2))
  have hmoment :
      IntervalIntegrable (fun w : ℝ => w * Real.arcsin w)
        MeasureTheory.volume 0 1 :=
    (continuous_id.mul Real.continuous_arcsin).intervalIntegrable 0 1
  have hsingularHalf :
      IntervalIntegrable
        (fun w : ℝ =>
          (1 / 2) * (w ^ 2 / Real.sqrt (1 - w ^ 2)))
        MeasureTheory.volume 0 1 :=
    singularRadial_intervalIntegrable.const_mul (1 / 2)
  have hf :
      IntervalIntegrable f MeasureTheory.volume 0 1 := by
    exact hmoment.add hsingularHalf
  have hcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
    dsimp [F]
    fun_prop
  have hderiv :
      ∀ w ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt F (f w) w := by
    intro w hw
    rcases hw with ⟨hw0, hw1⟩
    have hasin :
        HasDerivAt Real.arcsin
          (1 / Real.sqrt (1 - w ^ 2)) w :=
      Real.hasDerivAt_arcsin (by linarith) (by linarith)
    have hsq :
        HasDerivAt (fun x : ℝ => x ^ 2 / 2) w w := by
      convert (hasDerivAt_pow 2 w).div_const 2 using 1 <;> ring
    dsimp [F, f]
    convert hsq.mul hasin using 1 <;> ring
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (by norm_num : (0 : ℝ) ≤ 1) hcont hderiv hf
  have hsplit :
      (∫ w in (0 : ℝ)..1, f w) =
        (∫ w in (0 : ℝ)..1, w * Real.arcsin w) +
          (1 / 2) *
            ∫ w in (0 : ℝ)..1,
              w ^ 2 / Real.sqrt (1 - w ^ 2) := by
    dsimp [f]
    rw [intervalIntegral.integral_add hmoment hsingularHalf,
      intervalIntegral.integral_const_mul]
  rw [hsplit, singularRadial_value] at hftc
  norm_num [F, Real.arcsin_zero, Real.arcsin_one] at hftc
  linarith

theorem gap1 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    forwardJacobian a b c =
      1 / (a * b * c) := by
  rfl

theorem gap2 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    forwardMap a b c '' region a b c =
      parameterDomain := by
  apply Set.Subset.antisymm
  · rintro q ⟨p, ⟨u, hu, rfl⟩, rfl⟩
    have ha0 : a ≠ 0 := ha.ne'
    have hb0 : b ≠ 0 := hb.ne'
    have hc0 : c ≠ 0 := hc.ne'
    simpa [forwardMap, inverseMap, ha0, hb0, hc0] using hu
  · intro q hq
    refine ⟨inverseMap a b c q, ⟨q, hq, rfl⟩, ?_⟩
    have ha0 : a ≠ 0 := ha.ne'
    have hb0 : b ≠ 0 := hb.ne'
    have hc0 : c ≠ 0 := hc.ne'
    rcases q with ⟨u, v, w⟩
    simp [forwardMap, inverseMap, ha0, hb0, hc0]

theorem gap3 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    inverseJacobian a b c = a * b * c := by
  rfl

theorem gap4 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      a * b * c *
        ∫ u in (0 : ℝ)..1,
          ∫ w in (-1 : ℝ)..1,
            ∫ v in lowerBound w..1, (1 : ℝ) := by
  letI : Measure.IsAddHaarMeasure
      (MeasureTheory.volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  letI : Measure.IsAddHaarMeasure
      (MeasureTheory.volume : Measure (ℝ × (ℝ × ℝ))) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have habc : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
  have himage :
      inverseLinear a b c '' parameterDomain = region a b c := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, (inverseLinear_apply a b c p).symm⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, inverseLinear_apply a b c p⟩
  have hm :=
    Measure.addHaar_image_linearMap
      (MeasureTheory.volume : Measure (ℝ × (ℝ × ℝ)))
      (inverseLinear a b c) parameterDomain
  rw [himage, inverseLinear_det, abs_of_pos habc] at hm
  have hregion :
      (∫ _p in region a b c, (1 : ℝ)) =
        (MeasureTheory.volume (region a b c)).toReal := by
    rw [MeasureTheory.integral_const]
    simp only [smul_eq_mul, mul_one]
    rw [MeasureTheory.measureReal_def]
    simp
  have hparam :
      (MeasureTheory.volume parameterDomain).toReal =
        ∫ _p in parameterDomain, (1 : ℝ) := by
    rw [MeasureTheory.integral_const]
    simp only [smul_eq_mul, mul_one]
    rw [MeasureTheory.measureReal_def]
    simp
  unfold volume
  rw [hregion]
  rw [hm, ENNReal.toReal_mul, ENNReal.toReal_ofReal habc.le]
  rw [hparam, parameterDomain_iteratedIntegral]

theorem gap5 (a b c : ℝ) :
    a * b * c *
        (∫ u in (0 : ℝ)..1,
          ∫ w in (-1 : ℝ)..1,
            ∫ v in lowerBound w..1, (1 : ℝ)) =
      2 * a * b * c *
        ∫ w in (0 : ℝ)..1,
          (1 - lowerBound w) := by
  let f : ℝ → ℝ := fun w => 1 - lowerBound w
  have hf : Continuous f := by
    dsimp [f, lowerBound]
    fun_prop
  have hnested :
      (∫ u in (0 : ℝ)..1,
        ∫ w in (-1 : ℝ)..1,
          ∫ v in lowerBound w..1, (1 : ℝ)) =
        ∫ w in (-1 : ℝ)..1, f w := by
    have hpoint (u : ℝ) :
        (∫ w in (-1 : ℝ)..1,
          ∫ v in lowerBound w..1, (1 : ℝ)) =
          ∫ w in (-1 : ℝ)..1, f w := by
      apply intervalIntegral.integral_congr
      intro w hw
      dsimp [f]
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul, mul_one]
    calc
      (∫ u in (0 : ℝ)..1,
          ∫ w in (-1 : ℝ)..1,
            ∫ v in lowerBound w..1, (1 : ℝ)) =
          ∫ u in (0 : ℝ)..1,
            (∫ w in (-1 : ℝ)..1, f w) := by
        apply intervalIntegral.integral_congr
        intro u hu
        exact hpoint u
      _ = ∫ w in (-1 : ℝ)..1, f w := by
        rw [intervalIntegral.integral_const]
        norm_num [smul_eq_mul]
  have heven (w : ℝ) : f (-w) = f w := by
    dsimp [f, lowerBound]
    rw [Real.arcsin_neg]
    ring
  have hneg :
      (∫ w in (-1 : ℝ)..0, f w) =
        ∫ w in (0 : ℝ)..1, f w := by
    calc
      (∫ w in (-1 : ℝ)..0, f w) =
          ∫ w in (0 : ℝ)..1, f (-w) :=
        by
          simpa using
            (intervalIntegral.integral_comp_neg
              (a := (0 : ℝ)) (b := 1) f).symm
      _ = ∫ w in (0 : ℝ)..1, f w := by
        apply intervalIntegral.integral_congr
        intro w hw
        exact heven w
  have hsplit :
      (∫ w in (-1 : ℝ)..1, f w) =
        (∫ w in (-1 : ℝ)..0, f w) +
          ∫ w in (0 : ℝ)..1, f w := by
    exact
      (intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable (-1) 0)
        (hf.intervalIntegrable 0 1)).symm
  rw [hnested, hsplit, hneg]
  ring

theorem gap6 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      2 * a * b * c *
        ∫ w in (0 : ℝ)..1,
          (1 - lowerBound w) := by
  rw [gap4 a b c ha hb hc, gap5]

theorem gap7 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      2 * a * b * c -
        4 * a * b * c / Real.pi *
          ∫ w in (0 : ℝ)..1, w * Real.arcsin w := by
  rw [gap6 a b c ha hb hc]
  have hconst :
      IntervalIntegrable (fun _w : ℝ => (1 : ℝ))
        MeasureTheory.volume 0 1 :=
    intervalIntegrable_const
  have harcsin :
      IntervalIntegrable (fun w : ℝ => w * Real.arcsin w)
        MeasureTheory.volume 0 1 :=
    (continuous_id.mul Real.continuous_arcsin).intervalIntegrable 0 1
  rw [show (fun w : ℝ => 1 - lowerBound w) =
      fun w => 1 - (2 / Real.pi) * (w * Real.arcsin w) by
    funext w
    simp [lowerBound]
    ring]
  rw [intervalIntegral.integral_sub hconst
      (harcsin.const_mul (2 / Real.pi)),
    intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul]
  simp only [smul_eq_mul]
  ring

theorem gap8 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      a * b * c +
        2 * a * b * c / Real.pi *
          ∫ w in (0 : ℝ)..1,
            w ^ 2 / Real.sqrt (1 - w ^ 2) := by
  rw [gap7 a b c ha hb hc, arcsinMoment_value,
    singularRadial_value]
  field_simp [Real.pi_ne_zero]
  ring

theorem gap9 (a b c : ℝ) :
    a * b * c +
        2 * a * b * c / Real.pi *
          (∫ w in (0 : ℝ)..1,
            w ^ 2 / Real.sqrt (1 - w ^ 2)) =
      a * b * c +
        a * b * c / Real.pi *
          ∫ t in (0 : ℝ)..1,
            Real.rpow t (1 / 2 : ℝ) *
              Real.rpow (1 - t) (-1 / 2 : ℝ) := by
  rw [← twice_singularRadial_eq_beta]
  ring

theorem gap10 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      a * b * c +
        a * b * c / Real.pi *
          ∫ t in (0 : ℝ)..1,
            Real.rpow t (1 / 2 : ℝ) *
              Real.rpow (1 - t) (-1 / 2 : ℝ) := by
  exact (gap8 a b c ha hb hc).trans (gap9 a b c)

theorem gap11 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      a * b * c +
        a * b * c * betaFn (3 / 2) (1 / 2) / Real.pi := by
  rw [gap10 a b c ha hb hc]
  have hbeta :
      (∫ t in (0 : ℝ)..1,
        Real.rpow t (1 / 2 : ℝ) *
          Real.rpow (1 - t) (-1 / 2 : ℝ)) =
        betaFn (3 / 2) (1 / 2) := by
    norm_num [betaFn]
  rw [hbeta]
  ring

theorem gap12 (a b c : ℝ) :
    a * b * c +
        a * b * c * betaFn (3 / 2) (1 / 2) / Real.pi =
      (3 / 2 : ℝ) * a * b * c := by
  rw [betaFn_three_halves_one_half]
  field_simp [Real.pi_ne_zero]
  ring

theorem gap13 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c = (3 / 2 : ℝ) * a * b * c := by
  exact (gap11 a b c ha hb hc).trans (gap12 a b c)

end

end ProofGap.Exercise4123
