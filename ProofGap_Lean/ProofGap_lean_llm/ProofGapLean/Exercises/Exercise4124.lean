import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4124

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
  w * Real.exp (-w)

def parameterDomain : Set (ℝ × ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ p.2.2 ∧
    lowerBound p.2.2 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2 ∧
    0 ≤ p.2.2 ∧ p.2.2 ≤ 1}

/-- The full-dimensional region intended by the source's subsequent volume computation. -/
def region (a b c : ℝ) : Set (ℝ × ℝ × ℝ) :=
  inverseMap a b c '' parameterDomain

def volume (a b c : ℝ) : ℝ :=
  ∫ _ in region a b c, (1 : ℝ)

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
    0 ≤ p.2.1 ∧ p.2.1 ≤ p.1 ∧
    lowerBound p.1 ≤ p.2.2 ∧ p.2.2 ≤ p.1}

private def rotateLinear :
    (ℝ × ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ × ℝ) :=
  let A : Matrix (Fin 3) (Fin 3) ℝ :=
    ![![0, 0, 1], ![1, 0, 0], ![0, 1, 0] ]
  (coordinateEquiv.symm : (Fin 3 → ℝ) →ₗ[ℝ] (ℝ × ℝ × ℝ)) ∘ₗ
    Matrix.toLin' A ∘ₗ
      (coordinateEquiv : (ℝ × ℝ × ℝ) →ₗ[ℝ] (Fin 3 → ℝ))

@[simp] private theorem rotateLinear_apply (p : ℝ × ℝ × ℝ) :
    rotateLinear p = (p.2.2, p.1, p.2.1) := by
  ext <;>
    simp [rotateLinear, coordinateEquiv, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private theorem rotateLinear_det :
    LinearMap.det rotateLinear = 1 := by
  let A : Matrix (Fin 3) (Fin 3) ℝ :=
    ![![0, 0, 1], ![1, 0, 0], ![0, 1, 0] ]
  change
    LinearMap.det
        ((coordinateEquiv.symm :
            (Fin 3 → ℝ) →ₗ[ℝ] (ℝ × ℝ × ℝ)) ∘ₗ
          Matrix.toLin' A ∘ₗ
            (coordinateEquiv :
              (ℝ × ℝ × ℝ) →ₗ[ℝ] (Fin 3 → ℝ))) =
      1
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

private theorem rotate_image_parameterDomain :
    rotateLinear '' parameterDomain = orderedParameterDomain := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases hp with ⟨hu0, huw, hv0, hvw, hw0, hw1⟩
    simpa [orderedParameterDomain] using
      (show
        0 ≤ p.2.2 ∧ p.2.2 ≤ 1 ∧
          0 ≤ p.1 ∧ p.1 ≤ p.2.2 ∧
          lowerBound p.2.2 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2
        from ⟨hw0, hw1, hu0, huw, hv0, hvw⟩)
  · intro hq
    let p : ℝ × ℝ × ℝ := (q.2.1, q.2.2, q.1)
    refine ⟨p, ?_, ?_⟩
    · rcases hq with ⟨hw0, hw1, hu0, huw, hv0, hvw⟩
      simpa [p, parameterDomain] using
        (show
          0 ≤ q.2.1 ∧ q.2.1 ≤ q.1 ∧
            lowerBound q.1 ≤ q.2.2 ∧ q.2.2 ≤ q.1 ∧
            0 ≤ q.1 ∧ q.1 ≤ 1
          from ⟨hu0, huw, hv0, hvw, hw0, hw1⟩)
    · rcases q with ⟨w, u, v⟩
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
      rotateLinear parameterDomain
  rw [rotate_image_parameterDomain, rotateLinear_det] at hm
  norm_num at hm
  rw [MeasureTheory.integral_const, MeasureTheory.integral_const]
  simp only [smul_eq_mul, mul_one]
  rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def]
  simpa only [Measure.restrict_apply_univ] using
    congrArg ENNReal.toReal hm.symm

private theorem parameterDomain_iteratedIntegral :
    (∫ _p in parameterDomain, (1 : ℝ)) =
      ∫ w in (0 : ℝ)..1,
        ∫ u in (0 : ℝ)..w,
          ∫ v in lowerBound w..w, (1 : ℝ) := by
  classical
  have hs : MeasurableSet orderedParameterDomain := by
    unfold orderedParameterDomain lowerBound
    measurability
  have hlower_nonneg {w : ℝ} (hw : 0 ≤ w) :
      0 ≤ lowerBound w := by
    unfold lowerBound
    positivity
  have hlower_le {w : ℝ} (hw0 : 0 ≤ w) :
      lowerBound w ≤ w := by
    unfold lowerBound
    have he : Real.exp (-w) ≤ 1 :=
      (Real.exp_le_one_iff.mpr (by linarith))
    simpa using (mul_le_mul_of_nonneg_left he hw0)
  have hsubset :
      orderedParameterDomain ⊆
        Set.Icc (0 : ℝ) 1 ×ˢ
          (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro q hq
    rcases hq with ⟨hw0, hw1, hu0, huw, hv0, hvw⟩
    have hu1 : q.2.1 ≤ 1 := le_trans huw hw1
    have hvnonneg : 0 ≤ q.2.2 :=
      le_trans (hlower_nonneg hw0) hv0
    have hv1 : q.2.2 ≤ 1 := le_trans hvw hw1
    exact ⟨⟨hw0, hw1⟩, ⟨⟨hu0, hu1⟩, hvnonneg, hv1⟩⟩
  have hbox :
      IntegrableOn (fun _q : ℝ × ℝ × ℝ => (1 : ℝ))
        (Set.Icc (0 : ℝ) 1 ×ˢ
          (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
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
        ∫ w : ℝ, ∫ u : ℝ, ∫ v : ℝ,
          orderedParameterDomain.indicator
            (fun _q => (1 : ℝ)) (w, u, v) := by
    rw [MeasureTheory.integral_prod _ hind]
    apply integral_congr_ae
    filter_upwards [hind.prod_right_ae] with w hw
    change
      (∫ uv : ℝ × ℝ,
          orderedParameterDomain.indicator (fun _q => (1 : ℝ)) (w, uv)
            ∂MeasureTheory.volume.prod MeasureTheory.volume) =
        ∫ u : ℝ, ∫ v : ℝ,
          orderedParameterDomain.indicator (fun _q => (1 : ℝ)) (w, u, v)
    rw [MeasureTheory.integral_prod _ hw]
  have hsections :
      (∫ w : ℝ, ∫ u : ℝ, ∫ v : ℝ,
          orderedParameterDomain.indicator
            (fun _q => (1 : ℝ)) (w, u, v)) =
        ∫ w in Set.Icc (0 : ℝ) 1,
          ∫ u in Set.Icc (0 : ℝ) w,
            ∫ v in Set.Icc (lowerBound w) w, (1 : ℝ) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with w
    by_cases hw : w ∈ Set.Icc (0 : ℝ) 1
    · rw [Set.indicator_of_mem hw]
      rw [← MeasureTheory.integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards with u
      by_cases hu : u ∈ Set.Icc (0 : ℝ) w
      · rw [Set.indicator_of_mem hu]
        rw [← MeasureTheory.integral_indicator measurableSet_Icc]
        apply integral_congr_ae
        filter_upwards with v
        by_cases hv : v ∈ Set.Icc (lowerBound w) w
        · have hp : (w, u, v) ∈ orderedParameterDomain :=
            ⟨hw.1, hw.2, hu.1, hu.2, hv.1, hv.2⟩
          simp only [Set.indicator_of_mem hv,
            Set.indicator_of_mem hp]
        · have hnp : (w, u, v) ∉ orderedParameterDomain := by
            intro hp
            exact hv ⟨hp.2.2.2.2.1, hp.2.2.2.2.2⟩
          simp [Set.indicator, hv, hnp]
      · have hur :
            (Set.Icc (0 : ℝ) w).indicator
              (fun u =>
                ∫ v in Set.Icc (lowerBound w) w, (1 : ℝ)) u = 0 := by
          simp [Set.indicator, hu]
        rw [hur, ← integral_zero]
        apply integral_congr_ae
        filter_upwards with v
        have hnp : (w, u, v) ∉ orderedParameterDomain := by
          intro hp
          exact hu ⟨hp.2.2.1, hp.2.2.2.1⟩
        simp [Set.indicator, hnp]
    · have hwr :
          (Set.Icc (0 : ℝ) 1).indicator
            (fun w =>
              ∫ u in Set.Icc (0 : ℝ) w,
                ∫ v in Set.Icc (lowerBound w) w, (1 : ℝ)) w = 0 := by
        simp [Set.indicator, hw]
      rw [hwr, ← integral_zero]
      apply integral_congr_ae
      filter_upwards with u
      rw [← integral_zero]
      apply integral_congr_ae
      filter_upwards with v
      have hnp : (w, u, v) ∉ orderedParameterDomain := by
        intro hp
        exact hw ⟨hp.1, hp.2.1⟩
      simp [Set.indicator, hnp]
  calc
    (∫ _p in parameterDomain, (1 : ℝ)) =
        ∫ _p in orderedParameterDomain, (1 : ℝ) :=
      parameterDomain_integral_eq_ordered
    _ =
        ∫ q : ℝ × ℝ × ℝ,
          orderedParameterDomain.indicator (fun _q => (1 : ℝ)) q := by
      rw [MeasureTheory.integral_indicator hs]
    _ = ∫ w : ℝ, ∫ u : ℝ, ∫ v : ℝ,
          orderedParameterDomain.indicator
            (fun _q => (1 : ℝ)) (w, u, v) := hprod
    _ = ∫ w in Set.Icc (0 : ℝ) 1,
          ∫ u in Set.Icc (0 : ℝ) w,
            ∫ v in Set.Icc (lowerBound w) w, (1 : ℝ) := hsections
    _ = ∫ w in (0 : ℝ)..1,
          ∫ u in (0 : ℝ)..w,
            ∫ v in lowerBound w..w, (1 : ℝ) := by
      rw [intervalIntegral.integral_of_le
        (by norm_num : (0 : ℝ) ≤ 1)]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro w hw
      dsimp only
      rw [intervalIntegral.integral_of_le hw.1.le]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro u hu
      dsimp only
      rw [intervalIntegral.integral_of_le
        (hlower_le hw.1.le)]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]

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
        ∫ w in (0 : ℝ)..1,
          ∫ u in (0 : ℝ)..w,
            ∫ v in lowerBound w..w, (1 : ℝ) := by
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
        (∫ w in (0 : ℝ)..1,
          ∫ u in (0 : ℝ)..w,
            ∫ v in lowerBound w..w, (1 : ℝ)) =
      a * b * c *
        ∫ w in (0 : ℝ)..1,
          (w ^ 2 - w ^ 2 * Real.exp (-w)) := by
  congr 1
  apply intervalIntegral.integral_congr
  intro w hw
  change
    (∫ u in (0 : ℝ)..w,
      ∫ v in lowerBound w..w, (1 : ℝ)) =
      w ^ 2 - w ^ 2 * Real.exp (-w)
  have hv :
      (∫ v in lowerBound w..w, (1 : ℝ)) =
        w - lowerBound w := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul, mul_one]
  rw [hv, intervalIntegral.integral_const]
  simp only [smul_eq_mul, lowerBound]
  ring

theorem gap6 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      a * b * c *
        ∫ w in (0 : ℝ)..1,
          (w ^ 2 - w ^ 2 * Real.exp (-w)) := by
  rw [gap4 a b c ha hb hc, gap5]

theorem gap7 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      a * b * c *
        ((1 / 3 : ℝ) - 2 + 5 * Real.exp (-1)) := by
  rw [gap6 a b c ha hb hc]
  congr 1
  let F : ℝ → ℝ := fun w =>
    w ^ 3 / 3 + (w ^ 2 + 2 * w + 2) * Real.exp (-w)
  have hderiv (w : ℝ) :
      HasDerivAt F (w ^ 2 - w ^ 2 * Real.exp (-w)) w := by
    dsimp [F]
    have hp :
        HasDerivAt (fun x : ℝ => x ^ 2 + 2 * x + 2)
          (2 * w + 2) w := by
      convert
        (((hasDerivAt_pow 2 w).add
          ((hasDerivAt_id w).const_mul 2)).add_const 2)
        using 1 <;> ring
    have he :
        HasDerivAt (fun x : ℝ => Real.exp (-x))
          (-Real.exp (-w)) w := by
      convert
        ((Real.hasDerivAt_exp (-w)).comp w (hasDerivAt_id w).neg)
        using 1 <;> ring
    convert
      ((hasDerivAt_pow 3 w).div_const 3).add (hp.mul he)
      using 1 <;> ring
  have hint :
      IntervalIntegrable
        (fun w : ℝ => w ^ 2 - w ^ 2 * Real.exp (-w))
        MeasureTheory.volume 0 1 :=
    (((continuous_id.pow 2).sub
      ((continuous_id.pow 2).mul
        (Real.continuous_exp.comp continuous_neg))).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun w hw => hderiv w) hint]
  simp [F]
  ring

theorem gap8 (a b c : ℝ) :
    a * b * c *
        ((1 / 3 : ℝ) - 2 + 5 * Real.exp (-1)) =
      5 * a * b * c *
        (1 / Real.exp 1 - (1 / 3 : ℝ)) := by
  rw [Real.exp_neg]
  ring

theorem gap9 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume a b c =
      5 * a * b * c *
        (1 / Real.exp 1 - (1 / 3 : ℝ)) := by
  rw [gap7 a b c ha hb hc, gap8]

end

end ProofGap.Exercise4124
