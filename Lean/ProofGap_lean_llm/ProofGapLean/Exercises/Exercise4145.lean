import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4145

noncomputable section

open MeasureTheory Set
open scoped Interval

abbrev Point3 := ℝ × ℝ × ℝ

def solid (a b c : ℝ) : Set Point3 :=
  {p |
    0 ≤ p.2.2 ∧ p.2.2 ≤ c ∧
      p.1 ^ 2 / a ^ 2 + p.2.1 ^ 2 / b ^ 2 ≤ p.2.2 ^ 2 / c ^ 2}

def inertiaXY (a b c : ℝ) : ℝ :=
  ∫ p in solid a b c, p.2.2 ^ 2

def inertiaYZ (a b c : ℝ) : ℝ :=
  ∫ p in solid a b c, p.1 ^ 2

def inertiaZX (a b c : ℝ) : ℝ :=
  ∫ p in solid a b c, p.2.1 ^ 2

private def unitCone : Set Point3 :=
  {p |
    0 ≤ p.2.2 ∧ p.2.2 ≤ 1 ∧
      p.1 ^ 2 + p.2.1 ^ 2 ≤ p.2.2 ^ 2}

private def scale1 (a : ℝ) : ℝ →L[ℝ] ℝ :=
  a • ContinuousLinearMap.id ℝ ℝ

private def scale3 (a b c : ℝ) :
    Point3 →L[ℝ] Point3 :=
  (scale1 a).prodMap ((scale1 b).prodMap (scale1 c))

@[simp] private theorem scale1_apply (a x : ℝ) :
    scale1 a x = a * x := by
  simp [scale1]

@[simp] private theorem scale3_apply (a b c : ℝ) (p : Point3) :
    scale3 a b c p = (a * p.1, b * p.2.1, c * p.2.2) := by
  rcases p with ⟨x, y, z⟩
  simp [scale3]

private theorem det_scale1 (a : ℝ) :
    (scale1 a).det = a := by
  rw [ContinuousLinearMap.det]
  rw [LinearMap.det_ring]
  simp [scale1]

private theorem det_scale3 (a b c : ℝ) :
    (scale3 a b c).det = a * b * c := by
  unfold scale3
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_prodMap,
    LinearMap.det_prodMap, ContinuousLinearMap.coe_prodMap,
    LinearMap.det_prodMap]
  change (scale1 a).det * ((scale1 b).det * (scale1 c).det) = _
  rw [det_scale1, det_scale1, det_scale1]
  ring

private theorem unitCone_closed : IsClosed unitCone := by
  have hz : Continuous (fun p : Point3 => p.2.2) :=
    continuous_snd.comp continuous_snd
  have hr : Continuous (fun p : Point3 => p.1 ^ 2 + p.2.1 ^ 2) :=
    (continuous_fst.pow 2).add ((continuous_fst.comp continuous_snd).pow 2)
  unfold unitCone
  simpa only [Set.setOf_and] using
    (isClosed_le continuous_const hz).inter
      ((isClosed_le hz continuous_const).inter
        (isClosed_le hr (hz.pow 2)))

private theorem unitCone_compact : IsCompact unitCone := by
  apply (isCompact_Icc :
    IsCompact
      (Set.Icc ((-1 : ℝ), ((-1 : ℝ), (0 : ℝ)))
        (1, (1, 1)))).of_isClosed_subset unitCone_closed
  rintro ⟨x, y, z⟩ h
  change 0 ≤ z ∧ z ≤ 1 ∧ x ^ 2 + y ^ 2 ≤ z ^ 2 at h
  have hz2 : z ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg h.1 (sub_nonneg.mpr h.2.1)]
  have hx2 : x ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg y]
  have hy2 : y ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg x]
  exact
    ⟨⟨by nlinarith [sq_nonneg (x + 1)],
        by nlinarith [sq_nonneg (y + 1)], h.1⟩,
      ⟨by nlinarith [sq_nonneg (x - 1)],
        by nlinarith [sq_nonneg (y - 1)], h.2.1⟩⟩

private theorem scale_image_unitCone (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    scale3 a b c '' unitCone = solid a b c := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hx : (a * p.1) ^ 2 / a ^ 2 = p.1 ^ 2 := by
      field_simp [ha.ne']
    have hy : (b * p.2.1) ^ 2 / b ^ 2 = p.2.1 ^ 2 := by
      field_simp [hb.ne']
    have hz : (c * p.2.2) ^ 2 / c ^ 2 = p.2.2 ^ 2 := by
      field_simp [hc.ne']
    change
      0 ≤ c * p.2.2 ∧ c * p.2.2 ≤ c ∧
        (a * p.1) ^ 2 / a ^ 2 + (b * p.2.1) ^ 2 / b ^ 2 ≤
          (c * p.2.2) ^ 2 / c ^ 2
    change
      0 ≤ p.2.2 ∧ p.2.2 ≤ 1 ∧
        p.1 ^ 2 + p.2.1 ^ 2 ≤ p.2.2 ^ 2 at hp
    exact
      ⟨mul_nonneg hc.le hp.1,
        by nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hp.2.1)],
        by simpa [hx, hy, hz] using hp.2.2⟩
  · intro hq
    let p : Point3 :=
      (q.1 / a, q.2.1 / b, q.2.2 / c)
    have hmap : scale3 a b c p = q := by
      simp only [scale3_apply]
      apply Prod.ext
      · dsimp [p]
        field_simp [ha.ne']
      · apply Prod.ext
        · dsimp [p]
          field_simp [hb.ne']
        · dsimp [p]
          field_simp [hc.ne']
    refine ⟨p, ?_, hmap⟩
    change
      0 ≤ q.2.2 / c ∧ q.2.2 / c ≤ 1 ∧
        (q.1 / a) ^ 2 + (q.2.1 / b) ^ 2 ≤ (q.2.2 / c) ^ 2
    change
      0 ≤ q.2.2 ∧ q.2.2 ≤ c ∧
        q.1 ^ 2 / a ^ 2 + q.2.1 ^ 2 / b ^ 2 ≤ q.2.2 ^ 2 / c ^ 2 at hq
    refine
      ⟨div_nonneg hq.1 hc.le, (div_le_one hc).2 hq.2.1, ?_⟩
    simpa only [div_pow] using hq.2.2

private theorem scale3_injOn (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Set.InjOn (scale3 a b c) unitCone := by
  intro p hp q hq heq
  have h1 : a * p.1 = a * q.1 := by
    simpa using congrArg Prod.fst heq
  have h21 : b * p.2.1 = b * q.2.1 := by
    simpa using congrArg (fun t => t.2.1) heq
  have h22 : c * p.2.2 = c * q.2.2 := by
    simpa using congrArg (fun t => t.2.2) heq
  apply Prod.ext
  · exact mul_left_cancel₀ ha.ne' h1
  · apply Prod.ext
    · exact mul_left_cancel₀ hb.ne' h21
    · exact mul_left_cancel₀ hc.ne' h22

private theorem scale_set_integral
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (g : Point3 → ℝ) :
    (∫ p in solid a b c, g p) =
      ∫ p in unitCone, a * b * c * g (scale3 a b c p) := by
  letI : Measure.IsAddHaarMeasure
      (MeasureTheory.volume : Measure (ℝ × ℝ)) := by
    change Measure.IsAddHaarMeasure
      ((MeasureTheory.volume : Measure ℝ).prod
        (MeasureTheory.volume : Measure ℝ))
    exact Measure.prod.instIsAddHaarMeasure _ _
  letI : Measure.IsAddHaarMeasure
      (MeasureTheory.volume : Measure Point3) := by
    change Measure.IsAddHaarMeasure
      ((MeasureTheory.volume : Measure ℝ).prod
        (MeasureTheory.volume : Measure (ℝ × ℝ)))
    exact Measure.prod.instIsAddHaarMeasure _ _
  have hchange :=
    integral_image_eq_integral_abs_det_fderiv_smul
      (μ := MeasureTheory.volume) unitCone_closed.measurableSet
      (f := scale3 a b c) (f' := fun _ => scale3 a b c)
      (fun p hp => (scale3 a b c).hasFDerivAt.hasFDerivWithinAt)
      (scale3_injOn a b c ha hb hc) g
  rw [scale_image_unitCone a b c ha hb hc] at hchange
  have habc : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
  simpa only [det_scale3, abs_of_pos habc, smul_eq_mul] using hchange

private def disk (z : ℝ) : Set (ℝ × ℝ) :=
  {q | q.1 ^ 2 + q.2 ^ 2 ≤ z ^ 2}

private theorem disk_closed (z : ℝ) : IsClosed (disk z) := by
  unfold disk
  exact isClosed_le
    ((continuous_fst.pow 2).add (continuous_snd.pow 2))
    continuous_const

private theorem disk_compact (z : ℝ) (hz : 0 ≤ z) :
    IsCompact (disk z) := by
  apply (isCompact_Icc :
    IsCompact (Set.Icc ((-z, -z) : ℝ × ℝ) (z, z))).of_isClosed_subset
      (disk_closed z)
  intro q hq
  change q.1 ^ 2 + q.2 ^ 2 ≤ z ^ 2 at hq
  have hx : q.1 ^ 2 ≤ z ^ 2 := by nlinarith [sq_nonneg q.2]
  have hy : q.2 ^ 2 ≤ z ^ 2 := by nlinarith [sq_nonneg q.1]
  exact
    ⟨⟨by nlinarith [sq_nonneg (q.1 + z)],
        by nlinarith [sq_nonneg (q.2 + z)]⟩,
      ⟨by nlinarith [sq_nonneg (q.1 - z)],
        by nlinarith [sq_nonneg (q.2 - z)]⟩⟩

private theorem disk_integral_eq_iterated
    (z : ℝ) (hz : 0 ≤ z) (g : ℝ × ℝ → ℝ) (hg : Continuous g) :
    (∫ q in disk z, g q) =
      ∫ x in (-z)..z,
        ∫ y in (-Real.sqrt (z ^ 2 - x ^ 2))..
            Real.sqrt (z ^ 2 - x ^ 2),
          g (x, y) := by
  classical
  have hd : MeasurableSet (disk z) := (disk_closed z).measurableSet
  have hi : Integrable ((disk z).indicator g) volume := by
    rw [integrable_indicator_iff hd]
    exact hg.continuousOn.integrableOn_compact (disk_compact z hz)
  change Integrable ((disk z).indicator g) (volume.prod volume) at hi
  have hprod :
      (∫ q : ℝ × ℝ, (disk z).indicator g q ∂volume.prod volume) =
        ∫ x : ℝ, ∫ y : ℝ, (disk z).indicator g (x, y) := by
    exact MeasureTheory.integral_prod _ hi
  have hsections :
      (∫ x : ℝ, ∫ y : ℝ, (disk z).indicator g (x, y)) =
        ∫ x in Set.Icc (-z) z,
          ∫ y in Set.Icc (-Real.sqrt (z ^ 2 - x ^ 2))
              (Real.sqrt (z ^ 2 - x ^ 2)),
            g (x, y) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Set.Icc (-z) z
    · rw [Set.indicator_of_mem hx]
      have harg : 0 ≤ z ^ 2 - x ^ 2 := by
        nlinarith [mul_nonneg (by linarith [hx.1] : 0 ≤ x + z)
          (by linarith [hx.2] : 0 ≤ z - x)]
      rw [← MeasureTheory.integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards with y
      by_cases hy :
          y ∈ Set.Icc (-Real.sqrt (z ^ 2 - x ^ 2))
            (Real.sqrt (z ^ 2 - x ^ 2))
      · have hyabs : |y| ≤ Real.sqrt (z ^ 2 - x ^ 2) :=
          (abs_le).2 hy
        have hy2 : y ^ 2 ≤ z ^ 2 - x ^ 2 := by
          rw [← Real.sq_sqrt harg]
          simpa [sq_abs] using
            ((sq_le_sq₀ (abs_nonneg y) (Real.sqrt_nonneg _)).2 hyabs)
        have hmem : (x, y) ∈ disk z := by
          change x ^ 2 + y ^ 2 ≤ z ^ 2
          linarith
        simp only [Set.indicator_of_mem hy, Set.indicator_of_mem hmem]
      · have hnot : (x, y) ∉ disk z := by
          intro hmem
          apply hy
          have hy2 : y ^ 2 ≤ z ^ 2 - x ^ 2 := by
            change x ^ 2 + y ^ 2 ≤ z ^ 2 at hmem
            linarith
          have habs :
              |y| ≤ Real.sqrt (z ^ 2 - x ^ 2) :=
            (Real.le_sqrt (abs_nonneg y) harg).2 (by simpa [sq_abs] using hy2)
          exact (abs_le).1 habs
        simp [Set.indicator, hy, hnot]
    · have hr :
          (Set.Icc (-z) z).indicator
            (fun x =>
              ∫ y in Set.Icc (-Real.sqrt (z ^ 2 - x ^ 2))
                  (Real.sqrt (z ^ 2 - x ^ 2)),
                g (x, y)) x = 0 := by
        simp [Set.indicator, hx]
      rw [hr, ← integral_zero]
      apply integral_congr_ae
      filter_upwards with y
      have hnot : (x, y) ∉ disk z := by
        intro hmem
        apply hx
        change x ^ 2 + y ^ 2 ≤ z ^ 2 at hmem
        have hx2 : x ^ 2 ≤ z ^ 2 := by
          nlinarith [sq_nonneg y]
        exact
          ⟨by nlinarith [sq_nonneg (x + z)],
            by nlinarith [sq_nonneg (x - z)]⟩
      simp [Set.indicator, hnot]
  calc
    (∫ q in disk z, g q) =
        ∫ q : ℝ × ℝ, (disk z).indicator g q := by
      rw [MeasureTheory.integral_indicator hd]
    _ = ∫ x : ℝ, ∫ y : ℝ, (disk z).indicator g (x, y) := hprod
    _ = ∫ x in Set.Icc (-z) z,
          ∫ y in Set.Icc (-Real.sqrt (z ^ 2 - x ^ 2))
              (Real.sqrt (z ^ 2 - x ^ 2)),
            g (x, y) := hsections
    _ = ∫ x in (-z)..z,
          ∫ y in (-Real.sqrt (z ^ 2 - x ^ 2))..
              Real.sqrt (z ^ 2 - x ^ 2),
            g (x, y) := by
      rw [intervalIntegral.integral_of_le (by linarith)]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      dsimp only
      rw [intervalIntegral.integral_of_le
        (neg_le_self (Real.sqrt_nonneg _))]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]

private theorem cone_integral_eq_zdisks
    (f : Point3 → ℝ) (hf : Continuous f) :
    (∫ p in unitCone, f p) =
      ∫ z in Set.Icc (0 : ℝ) 1,
        ∫ q in disk z, f (q.1, q.2, z) := by
  classical
  have hc : MeasurableSet unitCone := unitCone_closed.measurableSet
  have hi : Integrable (unitCone.indicator f) volume := by
    rw [integrable_indicator_iff hc]
    exact hf.continuousOn.integrableOn_compact unitCone_compact
  let e :=
    (MeasurableEquiv.prodAssoc :
      ((ℝ × ℝ) × ℝ) ≃ᵐ (ℝ × (ℝ × ℝ)))
  have hi' : Integrable
      (fun q : (ℝ × ℝ) × ℝ => unitCone.indicator f (e q)) := by
    simpa only [Function.comp_apply] using
      (volume_preserving_prodAssoc.integrable_comp_emb
        e.measurableEmbedding).2 hi
  have hreassoc :
      (∫ q : (ℝ × ℝ) × ℝ, unitCone.indicator f (e q)) =
        ∫ p : Point3, unitCone.indicator f p :=
    volume_preserving_prodAssoc.integral_comp' (unitCone.indicator f)
  have hfubini :
      (∫ q : (ℝ × ℝ) × ℝ, unitCone.indicator f (e q)) =
        ∫ z : ℝ, ∫ q : ℝ × ℝ,
          unitCone.indicator f (q.1, q.2, z) := by
    simpa [e] using
      (MeasureTheory.integral_prod_symm
        (fun q : (ℝ × ℝ) × ℝ => unitCone.indicator f (e q)) hi')
  have hsection (z : ℝ) :
      (∫ q : ℝ × ℝ, unitCone.indicator f (q.1, q.2, z)) =
        (Set.Icc (0 : ℝ) 1).indicator
          (fun z => ∫ q in disk z, f (q.1, q.2, z)) z := by
    by_cases hz : z ∈ Set.Icc (0 : ℝ) 1
    · rw [Set.indicator_of_mem hz,
        ← MeasureTheory.integral_indicator (disk_closed z).measurableSet]
      apply integral_congr_ae
      filter_upwards with q
      by_cases hq : q ∈ disk z
      · have hp : (q.1, q.2, z) ∈ unitCone :=
          ⟨hz.1, hz.2, hq⟩
        simp [Set.indicator, hq, hp]
      · have hp : (q.1, q.2, z) ∉ unitCone := by
          intro hp
          exact hq hp.2.2
        simp [Set.indicator, hq, hp]
    · rw [Set.indicator_of_notMem hz, ← integral_zero]
      apply integral_congr_ae
      filter_upwards with q
      have hp : (q.1, q.2, z) ∉ unitCone := by
        intro hp
        exact hz ⟨hp.1, hp.2.1⟩
      simp [Set.indicator, hp]
  calc
    (∫ p in unitCone, f p) =
        ∫ p : Point3, unitCone.indicator f p := by
      rw [MeasureTheory.integral_indicator hc]
    _ = ∫ q : (ℝ × ℝ) × ℝ, unitCone.indicator f (e q) :=
      hreassoc.symm
    _ = ∫ z : ℝ, ∫ q : ℝ × ℝ,
          unitCone.indicator f (q.1, q.2, z) := hfubini
    _ = ∫ z : ℝ,
          (Set.Icc (0 : ℝ) 1).indicator
            (fun z => ∫ q in disk z, f (q.1, q.2, z)) z := by
      apply integral_congr_ae
      filter_upwards with z
      exact hsection z
    _ = ∫ z in Set.Icc (0 : ℝ) 1,
          ∫ q in disk z, f (q.1, q.2, z) := by
      rw [MeasureTheory.integral_indicator measurableSet_Icc]

private theorem cone_integral_eq_iterated
    (f : Point3 → ℝ) (hf : Continuous f) :
    (∫ p in unitCone, f p) =
      ∫ z in (0 : ℝ)..1,
        ∫ x in (-z)..z,
          ∫ y in (-Real.sqrt (z ^ 2 - x ^ 2))..
              Real.sqrt (z ^ 2 - x ^ 2),
            f (x, y, z) := by
  rw [cone_integral_eq_zdisks f hf]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
  intro z hz
  dsimp only
  exact disk_integral_eq_iterated z hz.1.le
    (fun q : ℝ × ℝ => f (q.1, q.2, z))
    (hf.comp (continuous_fst.prodMk
      (continuous_snd.prodMk continuous_const)))

private theorem intervalIntegral_eq_sub_of_hasDerivAt
    {f F : ℝ → ℝ} (hF : ∀ x, HasDerivAt F (f x) x)
    (hf : Continuous f) (l u : ℝ) :
    intervalIntegral f l u volume = F u - F l := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _hx => hF x) (hf.intervalIntegrable (μ := volume) l u)

private theorem semicircle_integral (z : ℝ) (hz : 0 ≤ z) :
    (∫ x in (-z)..z, Real.sqrt (z ^ 2 - x ^ 2)) =
      Real.pi * z ^ 2 / 2 := by
  by_cases hz0 : z = 0
  · subst z
    simp
  let f := fun x : ℝ => Real.sqrt (z ^ 2 - x ^ 2)
  have hscaled :
      (∫ t in (-1 : ℝ)..1, f (z * t)) =
        z * (Real.pi / 2) := by
    calc
      (∫ t in (-1 : ℝ)..1, f (z * t)) =
          ∫ t in (-1 : ℝ)..1,
            z * Real.sqrt (1 - t ^ 2) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
        have harg : 0 ≤ 1 - t ^ 2 := by
          nlinarith [mul_nonneg (by linarith [ht.1] : 0 ≤ t + 1)
            (by linarith [ht.2] : 0 ≤ 1 - t)]
        dsimp only [f]
        rw [show z ^ 2 - (z * t) ^ 2 = z ^ 2 * (1 - t ^ 2) by ring]
        rw [Real.sqrt_mul (sq_nonneg z), Real.sqrt_sq_eq_abs,
          abs_of_nonneg hz]
      _ = z * ∫ t in (-1 : ℝ)..1,
          Real.sqrt (1 - t ^ 2) := by
        rw [intervalIntegral.integral_const_mul]
      _ = z * (Real.pi / 2) := by
        rw [integral_sqrt_one_sub_sq]
  calc
    (∫ x in (-z)..z, Real.sqrt (z ^ 2 - x ^ 2)) =
        z * intervalIntegral (fun t : ℝ => f (z * t)) (-1) 1 volume := by
      simpa [f, smul_eq_mul] using
        (intervalIntegral.smul_integral_comp_mul_left
          (f := f) (a := (-1 : ℝ)) (b := 1) z).symm
    _ = Real.pi * z ^ 2 / 2 := by
      rw [hscaled]
      ring

private theorem unitCone_zMoment :
    (∫ p in unitCone, p.2.2 ^ 2) = Real.pi / 5 := by
  rw [cone_integral_eq_iterated
    (fun p : Point3 => p.2.2 ^ 2) (by fun_prop)]
  have hinner (z x : ℝ) :
      (∫ _y in (-Real.sqrt (z ^ 2 - x ^ 2))..
          Real.sqrt (z ^ 2 - x ^ 2), z ^ 2) =
        2 * z ^ 2 * Real.sqrt (z ^ 2 - x ^ 2) := by
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hx (z : ℝ) (hz : z ∈ Set.uIcc (0 : ℝ) 1) :
      (∫ x in (-z)..z,
          ∫ _y in (-Real.sqrt (z ^ 2 - x ^ 2))..
              Real.sqrt (z ^ 2 - x ^ 2),
            z ^ 2) =
        Real.pi * z ^ 4 := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hz
    calc
      _ = ∫ x in (-z)..z,
            2 * z ^ 2 * Real.sqrt (z ^ 2 - x ^ 2) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact hinner z x
      _ = (2 * z ^ 2) *
            ∫ x in (-z)..z, Real.sqrt (z ^ 2 - x ^ 2) := by
        rw [intervalIntegral.integral_const_mul]
      _ = Real.pi * z ^ 4 := by
        rw [semicircle_integral z hz.1]
        ring
  calc
    _ = ∫ z in (0 : ℝ)..1, Real.pi * z ^ 4 := by
      apply intervalIntegral.integral_congr
      exact hx
    _ = Real.pi * ∫ z in (0 : ℝ)..1, z ^ 4 := by
      rw [intervalIntegral.integral_const_mul]
    _ = Real.pi / 5 := by
      rw [integral_pow]
      norm_num
      ring

private theorem unitCone_mixedMoment :
    (∫ p in unitCone, p.2.1 ^ 2 + p.1 ^ 2 / 3) =
      Real.pi / 15 := by
  rw [cone_integral_eq_iterated
    (fun p : Point3 => p.2.1 ^ 2 + p.1 ^ 2 / 3) (by fun_prop)]
  simp only [Prod.fst, Prod.snd]
  have hinner (z x : ℝ) (harg : 0 ≤ z ^ 2 - x ^ 2) :
      (∫ y in (-Real.sqrt (z ^ 2 - x ^ 2))..
          Real.sqrt (z ^ 2 - x ^ 2),
        y ^ 2 + x ^ 2 / 3) =
      (2 / 3 : ℝ) * z ^ 2 * Real.sqrt (z ^ 2 - x ^ 2) := by
    let F := fun y : ℝ => y ^ 3 / 3 + (x ^ 2 / 3) * y
    have hF (y : ℝ) :
        HasDerivAt F (y ^ 2 + x ^ 2 / 3) y := by
      dsimp only [F]
      convert
        (((hasDerivAt_id y).pow 3).const_mul (1 / 3)).add
          ((hasDerivAt_id y).const_mul (x ^ 2 / 3))
        using 1 <;> (try funext t) <;> norm_num <;> ring
    rw [intervalIntegral_eq_sub_of_hasDerivAt hF (by fun_prop)]
    dsimp only [F]
    have hs := Real.sq_sqrt harg
    let s := Real.sqrt (z ^ 2 - x ^ 2)
    have hs' : s ^ 2 = z ^ 2 - x ^ 2 := by simpa [s] using hs
    change
      (s ^ 3 / 3 + x ^ 2 / 3 * s) -
          ((-s) ^ 3 / 3 + x ^ 2 / 3 * (-s)) =
        (2 / 3 : ℝ) * z ^ 2 * s
    rw [show (-s) ^ 3 = -(s ^ 3) by ring]
    have hs3 : s ^ 3 = s * (z ^ 2 - x ^ 2) := by
      rw [show s ^ 3 = s * s ^ 2 by ring, hs']
    rw [hs3]
    ring
  have hx (z : ℝ) (hz : z ∈ Set.uIcc (0 : ℝ) 1) :
      (∫ x in (-z)..z,
          ∫ y in (-Real.sqrt (z ^ 2 - x ^ 2))..
              Real.sqrt (z ^ 2 - x ^ 2),
            y ^ 2 + x ^ 2 / 3) =
        Real.pi * z ^ 4 / 3 := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hz
    have hz0 : 0 ≤ z := hz.1
    calc
      _ = ∫ x in (-z)..z,
            (2 / 3 : ℝ) * z ^ 2 *
              Real.sqrt (z ^ 2 - x ^ 2) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le (by linarith : -z ≤ z)] at hx
        have harg : 0 ≤ z ^ 2 - x ^ 2 := by
          nlinarith [mul_nonneg (by linarith [hx.1] : 0 ≤ x + z)
            (by linarith [hx.2] : 0 ≤ z - x)]
        exact hinner z x harg
      _ = ((2 / 3 : ℝ) * z ^ 2) *
            ∫ x in (-z)..z, Real.sqrt (z ^ 2 - x ^ 2) := by
        rw [intervalIntegral.integral_const_mul]
      _ = Real.pi * z ^ 4 / 3 := by
        rw [semicircle_integral z hz0]
        ring
  calc
    _ = ∫ z in (0 : ℝ)..1, Real.pi * z ^ 4 / 3 := by
      apply intervalIntegral.integral_congr
      exact hx
    _ = (Real.pi / 3) * ∫ z in (0 : ℝ)..1, z ^ 4 := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro z hz
      ring
    _ = Real.pi / 15 := by
      rw [integral_pow]
      norm_num
      ring

private def swapXY : Point3 ≃ᵐ Point3 :=
  ((MeasurableEquiv.prodAssoc :
      (ℝ × ℝ) × ℝ ≃ᵐ ℝ × (ℝ × ℝ)).symm).trans
    ((MeasurableEquiv.prodCongr
      (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ)
      (MeasurableEquiv.refl ℝ)).trans
        (MeasurableEquiv.prodAssoc :
          (ℝ × ℝ) × ℝ ≃ᵐ ℝ × (ℝ × ℝ)))

private theorem swapXY_measurePreserving :
    MeasurePreserving swapXY volume volume := by
  have hA :
      MeasurePreserving
        ((MeasurableEquiv.prodAssoc :
          (ℝ × ℝ) × ℝ ≃ᵐ ℝ × (ℝ × ℝ)).symm) volume volume :=
    MeasurePreserving.symm _ MeasureTheory.volume_preserving_prodAssoc
  have hB :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ)
          (MeasurableEquiv.refl ℝ)) volume volume := by
    exact
      (Measure.measurePreserving_swap
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).prod
          (MeasurePreserving.id (volume : Measure ℝ))
  have hC :
      MeasurePreserving
        (MeasurableEquiv.prodAssoc :
          (ℝ × ℝ) × ℝ ≃ᵐ ℝ × (ℝ × ℝ)) volume volume :=
    MeasureTheory.volume_preserving_prodAssoc
  exact hC.comp (hB.comp hA)

private theorem swapXY_preimage_unitCone :
    swapXY ⁻¹' unitCone = unitCone := by
  ext p
  simp only [Set.mem_preimage, unitCone, Set.mem_setOf_eq]
  change
    (0 ≤ p.2.2 ∧ p.2.2 ≤ 1 ∧
      p.2.1 ^ 2 + p.1 ^ 2 ≤ p.2.2 ^ 2) ↔
    (0 ≤ p.2.2 ∧ p.2.2 ≤ 1 ∧
      p.1 ^ 2 + p.2.1 ^ 2 ≤ p.2.2 ^ 2)
  constructor <;> rintro ⟨h₁, h₂, h₃⟩ <;>
    exact ⟨h₁, h₂, by linarith⟩

private theorem unitCone_y_eq_x :
    (∫ p in unitCone, p.2.1 ^ 2) =
      ∫ p in unitCone, p.1 ^ 2 := by
  have h := swapXY_measurePreserving.setIntegral_preimage_emb
    swapXY.measurableEmbedding (fun p : Point3 => p.1 ^ 2) unitCone
  rw [swapXY_preimage_unitCone] at h
  exact h

private theorem unitCone_xMoment :
    (∫ p in unitCone, p.1 ^ 2) = Real.pi / 20 := by
  have hxInt : IntegrableOn (fun p : Point3 => p.1 ^ 2) unitCone volume :=
    (by fun_prop : Continuous (fun p : Point3 => p.1 ^ 2)).continuousOn
      |>.integrableOn_compact unitCone_compact
  have hyInt : IntegrableOn (fun p : Point3 => p.2.1 ^ 2) unitCone volume :=
    (by fun_prop : Continuous (fun p : Point3 => p.2.1 ^ 2)).continuousOn
      |>.integrableOn_compact unitCone_compact
  have hlin :
      (∫ p in unitCone, p.2.1 ^ 2 + p.1 ^ 2 / 3) =
        (∫ p in unitCone, p.2.1 ^ 2) +
          (∫ p in unitCone, p.1 ^ 2) / 3 := by
    rw [MeasureTheory.integral_add hyInt (hxInt.div_const 3)]
    rw [MeasureTheory.integral_div]
  have hsym := unitCone_y_eq_x
  have hmix := unitCone_mixedMoment
  rw [hlin, hsym] at hmix
  linarith

private theorem unitCone_yMoment :
    (∫ p in unitCone, p.2.1 ^ 2) = Real.pi / 20 := by
  rw [unitCone_y_eq_x, unitCone_xMoment]

private theorem inertiaXY_formula
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    inertiaXY a b c = Real.pi * a * b * c ^ 3 / 5 := by
  unfold inertiaXY
  rw [scale_set_integral a b c ha hb hc
    (fun p : Point3 => p.2.2 ^ 2)]
  calc
    _ = ∫ p in unitCone,
          (a * b * c * c ^ 2) * p.2.2 ^ 2 := by
      apply MeasureTheory.setIntegral_congr_fun
        unitCone_closed.measurableSet
      intro p hp
      simp only [scale3_apply]
      ring
    _ = (a * b * c * c ^ 2) *
          ∫ p in unitCone, p.2.2 ^ 2 := by
      rw [MeasureTheory.integral_const_mul]
    _ = Real.pi * a * b * c ^ 3 / 5 := by
      rw [unitCone_zMoment]
      ring

private theorem inertiaYZ_formula
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    inertiaYZ a b c = Real.pi * a ^ 3 * b * c / 20 := by
  unfold inertiaYZ
  rw [scale_set_integral a b c ha hb hc
    (fun p : Point3 => p.1 ^ 2)]
  calc
    _ = ∫ p in unitCone,
          (a * b * c * a ^ 2) * p.1 ^ 2 := by
      apply MeasureTheory.setIntegral_congr_fun
        unitCone_closed.measurableSet
      intro p hp
      simp only [scale3_apply]
      ring
    _ = (a * b * c * a ^ 2) *
          ∫ p in unitCone, p.1 ^ 2 := by
      rw [MeasureTheory.integral_const_mul]
    _ = Real.pi * a ^ 3 * b * c / 20 := by
      rw [unitCone_xMoment]
      ring

private theorem inertiaZX_formula
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    inertiaZX a b c = Real.pi * a * b ^ 3 * c / 20 := by
  unfold inertiaZX
  rw [scale_set_integral a b c ha hb hc
    (fun p : Point3 => p.2.1 ^ 2)]
  calc
    _ = ∫ p in unitCone,
          (a * b * c * b ^ 2) * p.2.1 ^ 2 := by
      apply MeasureTheory.setIntegral_congr_fun
        unitCone_closed.measurableSet
      intro p hp
      simp only [scale3_apply]
      ring
    _ = (a * b * c * b ^ 2) *
          ∫ p in unitCone, p.2.1 ^ 2 := by
      rw [MeasureTheory.integral_const_mul]
    _ = Real.pi * a * b ^ 3 * c / 20 := by
      rw [unitCone_yMoment]
      ring

private theorem cylindrical_xy_value (a b c : ℝ) :
    (∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..1,
          ∫ z in c * r..c, a * b * r * z ^ 2) =
      Real.pi * a * b * c ^ 3 / 5 := by
  have hz (r : ℝ) :
      (∫ z in c * r..c, a * b * r * z ^ 2) =
        a * b * r * (c ^ 3 - (c * r) ^ 3) / 3 := by
    calc
      _ = (a * b * r) * ∫ z in c * r..c, z ^ 2 := by
        rw [← intervalIntegral.integral_const_mul]
      _ = a * b * r * (c ^ 3 - (c * r) ^ 3) / 3 := by
        rw [integral_pow]
        norm_num
        ring
  have hr :
      (∫ r in (0 : ℝ)..1,
          a * b * r * (c ^ 3 - (c * r) ^ 3) / 3) =
        a * b * c ^ 3 / 10 := by
    let F := fun r : ℝ =>
      (a * b * c ^ 3 / 6) * r ^ 2 -
        (a * b * c ^ 3 / 15) * r ^ 5
    have hF (r : ℝ) :
        HasDerivAt F
          (a * b * r * (c ^ 3 - (c * r) ^ 3) / 3) r := by
      dsimp only [F]
      convert
        (((hasDerivAt_id r).pow 2).const_mul (a * b * c ^ 3 / 6)).sub
          (((hasDerivAt_id r).pow 5).const_mul (a * b * c ^ 3 / 15))
        using 1 <;> simp only [id_eq] <;> ring
    rw [intervalIntegral_eq_sub_of_hasDerivAt hF (by fun_prop)]
    norm_num [F]
    ring
  calc
    _ = ∫ φ in (0 : ℝ)..2 * Real.pi,
          ∫ r in (0 : ℝ)..1,
            a * b * r * (c ^ 3 - (c * r) ^ 3) / 3 := by
      apply intervalIntegral.integral_congr
      intro φ hφ
      apply intervalIntegral.integral_congr
      intro r hr
      exact hz r
    _ = ∫ _φ in (0 : ℝ)..2 * Real.pi,
          a * b * c ^ 3 / 10 := by
      apply intervalIntegral.integral_congr
      intro φ hφ
      exact hr
    _ = Real.pi * a * b * c ^ 3 / 5 := by
      simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
      ring

private theorem cylindrical_yz_value (a b c : ℝ) :
    (∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..1,
          ∫ z in c * r..c,
            a * b * r * (a * r * Real.cos φ) ^ 2) =
      Real.pi * a ^ 3 * b * c / 20 := by
  have hz (φ r : ℝ) :
      (∫ _z in c * r..c,
          a * b * r * (a * r * Real.cos φ) ^ 2) =
        a ^ 3 * b * c * Real.cos φ ^ 2 * r ^ 3 * (1 - r) := by
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hr (φ : ℝ) :
      (∫ r in (0 : ℝ)..1,
          a ^ 3 * b * c * Real.cos φ ^ 2 * r ^ 3 * (1 - r)) =
        a ^ 3 * b * c * Real.cos φ ^ 2 / 20 := by
    let F := fun r : ℝ =>
      (a ^ 3 * b * c * Real.cos φ ^ 2 / 4) * r ^ 4 -
        (a ^ 3 * b * c * Real.cos φ ^ 2 / 5) * r ^ 5
    have hF (r : ℝ) :
        HasDerivAt F
          (a ^ 3 * b * c * Real.cos φ ^ 2 * r ^ 3 * (1 - r)) r := by
      dsimp only [F]
      convert
        (((hasDerivAt_id r).pow 4).const_mul
          (a ^ 3 * b * c * Real.cos φ ^ 2 / 4)).sub
          (((hasDerivAt_id r).pow 5).const_mul
            (a ^ 3 * b * c * Real.cos φ ^ 2 / 5))
        using 1 <;> simp only [id_eq] <;> ring
    rw [intervalIntegral_eq_sub_of_hasDerivAt hF (by fun_prop)]
    norm_num [F]
    ring
  have hcos :
      (∫ φ in (0 : ℝ)..2 * Real.pi, Real.cos φ ^ 2) =
        Real.pi := by
    rw [integral_cos_sq]
    rw [Real.cos_two_pi, Real.sin_two_pi, Real.cos_zero, Real.sin_zero]
    ring
  calc
    _ = ∫ φ in (0 : ℝ)..2 * Real.pi,
          ∫ r in (0 : ℝ)..1,
            a ^ 3 * b * c * Real.cos φ ^ 2 * r ^ 3 * (1 - r) := by
      apply intervalIntegral.integral_congr
      intro φ hφ
      apply intervalIntegral.integral_congr
      intro r hr
      exact hz φ r
    _ = ∫ φ in (0 : ℝ)..2 * Real.pi,
          a ^ 3 * b * c * Real.cos φ ^ 2 / 20 := by
      apply intervalIntegral.integral_congr
      intro φ hφ
      exact hr φ
    _ = (a ^ 3 * b * c / 20) *
          ∫ φ in (0 : ℝ)..2 * Real.pi, Real.cos φ ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro φ hφ
      ring
    _ = Real.pi * a ^ 3 * b * c / 20 := by
      rw [hcos]
      ring

theorem gap1 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    inertiaXY a b c =
      ∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..1,
          ∫ z in c * r..c, a * b * r * z ^ 2 := by
  calc
    inertiaXY a b c = Real.pi * a * b * c ^ 3 / 5 :=
      inertiaXY_formula a b c ha hb hc
    _ = _ := (cylindrical_xy_value a b c).symm

theorem gap2 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..1,
          ∫ z in c * r..c, a * b * r * z ^ 2) =
      (1 : ℝ) / 5 * Real.pi * a * b * c ^ 3 := by
  rw [cylindrical_xy_value]
  ring

theorem gap3 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    inertiaXY a b c = (1 : ℝ) / 5 * Real.pi * a * b * c ^ 3 := by
  rw [inertiaXY_formula a b c ha hb hc]
  ring

theorem gap4 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    inertiaYZ a b c =
      ∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..1,
          ∫ z in c * r..c,
            a * b * r * (a * r * Real.cos φ) ^ 2 := by
  calc
    inertiaYZ a b c = Real.pi * a ^ 3 * b * c / 20 :=
      inertiaYZ_formula a b c ha hb hc
    _ = _ := (cylindrical_yz_value a b c).symm

theorem gap5 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..1,
          ∫ z in c * r..c,
            a * b * r * (a * r * Real.cos φ) ^ 2) =
      (1 : ℝ) / 20 * Real.pi * a ^ 3 * b * c := by
  rw [cylindrical_yz_value]
  ring

theorem gap6 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    inertiaYZ a b c =
      (1 : ℝ) / 20 * Real.pi * a ^ 3 * b * c := by
  rw [inertiaYZ_formula a b c ha hb hc]
  ring

theorem gap7 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    inertiaZX a b c =
      (1 : ℝ) / 20 * Real.pi * a * b ^ 3 * c := by
  rw [inertiaZX_formula a b c ha hb hc]
  ring

end

end ProofGap.Exercise4145
