import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4146

noncomputable section

open MeasureTheory
open Set
open scoped Interval

abbrev Point3 := ℝ × ℝ × ℝ

def parameterDomain (c : ℝ) : Set Point3 :=
  {q |
    -Real.pi / 2 ≤ q.1 ∧ q.1 ≤ Real.pi / 2 ∧
      0 ≤ q.2.1 ∧ q.2.1 ≤ Real.cos q.1 ∧
        -c * Real.sqrt (1 - q.2.1 ^ 2) ≤ q.2.2 ∧
          q.2.2 ≤ c * Real.sqrt (1 - q.2.1 ^ 2)}

def solid (a b c : ℝ) : Set Point3 :=
  {p |
    (p.1 / a) ^ 2 + (p.2.1 / b) ^ 2 ≤ p.1 / a ∧
      p.2.2 ^ 2 / c ^ 2 ≤
        1 - ((p.1 / a) ^ 2 + (p.2.1 / b) ^ 2)}

def inertiaXY (a b c : ℝ) : ℝ :=
  ∫ p in solid a b c, p.2.2 ^ 2

def inertiaYZ (a b c : ℝ) : ℝ :=
  ∫ p in solid a b c, p.1 ^ 2

def inertiaZX (a b c : ℝ) : ℝ :=
  ∫ p in solid a b c, p.2.1 ^ 2

private def normalizedSolid (a b c : ℝ) : Set Point3 :=
  {p |
    p.1 ^ 2 / a ^ 2 + p.2.1 ^ 2 / b ^ 2 +
        p.2.2 ^ 2 / c ^ 2 ≤ 1 ∧
      p.1 ^ 2 / a ^ 2 + p.2.1 ^ 2 / b ^ 2 ≤ p.1 / a}

private theorem solid_eq_normalizedSolid
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    solid a b c = normalizedSolid a b c := by
  ext p
  simp only [solid, normalizedSolid, Set.mem_setOf_eq, div_pow]
  constructor
  · rintro ⟨hxy, hz⟩
    exact ⟨by linarith, hxy⟩
  · rintro ⟨hxyz, hxy⟩
    exact ⟨hxy, by linarith⟩

private def unitSolid : Set Point3 :=
  {p | p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≤ 1 ∧
    p.1 ^ 2 + p.2.1 ^ 2 ≤ p.1}

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

private theorem unitSolid_closed : IsClosed unitSolid := by
  have hx : Continuous (fun p : Point3 => p.1) := continuous_fst
  have hy : Continuous (fun p : Point3 => p.2.1) :=
    continuous_fst.comp continuous_snd
  have hz : Continuous (fun p : Point3 => p.2.2) :=
    continuous_snd.comp continuous_snd
  have h1 : Continuous (fun _p : Point3 => (1 : ℝ)) :=
    continuous_const
  unfold unitSolid
  simpa only [Set.setOf_and] using
    (isClosed_le ((hx.pow 2).add (hy.pow 2) |>.add (hz.pow 2)) h1).inter
      (isClosed_le ((hx.pow 2).add (hy.pow 2)) hx)

private theorem unitSolid_compact : IsCompact unitSolid := by
  apply (isCompact_Icc :
    IsCompact
      (Set.Icc ((-1 : ℝ), ((-1 : ℝ), (-1 : ℝ)))
        (1, (1, 1)))).of_isClosed_subset unitSolid_closed
  rintro ⟨x, y, z⟩ h
  change
    x ^ 2 + y ^ 2 + z ^ 2 ≤ 1 ∧ x ^ 2 + y ^ 2 ≤ x at h
  exact
    ⟨⟨by nlinarith [sq_nonneg (x + 1), sq_nonneg y, sq_nonneg z],
        by nlinarith [sq_nonneg (y + 1), sq_nonneg x, sq_nonneg z],
        by nlinarith [sq_nonneg (z + 1), sq_nonneg x, sq_nonneg y]⟩,
      ⟨by nlinarith [sq_nonneg (x - 1), sq_nonneg y, sq_nonneg z],
        by nlinarith [sq_nonneg (y - 1), sq_nonneg x, sq_nonneg z],
        by nlinarith [sq_nonneg (z - 1), sq_nonneg x, sq_nonneg y]⟩⟩

private theorem scale_image_unitSolid (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    scale3 a b c '' unitSolid = normalizedSolid a b c := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hx : (a * p.1) ^ 2 / a ^ 2 = p.1 ^ 2 := by
      field_simp [ha.ne']
    have hy : (b * p.2.1) ^ 2 / b ^ 2 = p.2.1 ^ 2 := by
      field_simp [hb.ne']
    have hz : (c * p.2.2) ^ 2 / c ^ 2 = p.2.2 ^ 2 := by
      field_simp [hc.ne']
    have hxa : a * p.1 / a = p.1 := by
      field_simp [ha.ne']
    change
      (a * p.1) ^ 2 / a ^ 2 + (b * p.2.1) ^ 2 / b ^ 2 +
            (c * p.2.2) ^ 2 / c ^ 2 ≤ 1 ∧
        (a * p.1) ^ 2 / a ^ 2 + (b * p.2.1) ^ 2 / b ^ 2 ≤
          a * p.1 / a
    simpa only [hx, hy, hz, hxa] using hp
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
      (q.1 / a) ^ 2 + (q.2.1 / b) ^ 2 + (q.2.2 / c) ^ 2 ≤ 1 ∧
        (q.1 / a) ^ 2 + (q.2.1 / b) ^ 2 ≤ q.1 / a
    change
      q.1 ^ 2 / a ^ 2 + q.2.1 ^ 2 / b ^ 2 + q.2.2 ^ 2 / c ^ 2 ≤ 1 ∧
        q.1 ^ 2 / a ^ 2 + q.2.1 ^ 2 / b ^ 2 ≤ q.1 / a at hq
    simpa only [div_pow] using hq

private theorem scale3_injOn (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Set.InjOn (scale3 a b c) unitSolid := by
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
      ∫ p in unitSolid, a * b * c * g (scale3 a b c p) := by
  rw [solid_eq_normalizedSolid a b c ha hb hc]
  letI : Measure.IsAddHaarMeasure
      (MeasureTheory.volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  letI : Measure.IsAddHaarMeasure
      (MeasureTheory.volume : Measure Point3) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hchange :=
    integral_image_eq_integral_abs_det_fderiv_smul
      (μ := MeasureTheory.volume) unitSolid_closed.measurableSet
      (f := scale3 a b c) (f' := fun _ => scale3 a b c)
      (fun p hp => (scale3 a b c).hasFDerivAt.hasFDerivWithinAt)
      (scale3_injOn a b c ha hb hc) g
  rw [scale_image_unitSolid a b c ha hb hc] at hchange
  have habc : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
  simpa only [det_scale3, abs_of_pos habc, smul_eq_mul] using hchange

private def base : Set (ℝ × ℝ) :=
  {q | q.1 ^ 2 + q.2 ^ 2 ≤ q.1}

private theorem base_closed : IsClosed base := by
  unfold base
  exact isClosed_le
    ((continuous_fst.pow 2).add (continuous_snd.pow 2))
    continuous_fst

private theorem base_compact : IsCompact base := by
  apply (isCompact_Icc :
    IsCompact (Set.Icc ((0 : ℝ), (-1 : ℝ))
      (1, 1))).of_isClosed_subset base_closed
  intro q hq
  change q.1 ^ 2 + q.2 ^ 2 ≤ q.1 at hq
  have hx0 : 0 ≤ q.1 := by
    nlinarith [sq_nonneg q.1, sq_nonneg q.2]
  have hx1 : q.1 ≤ 1 := by
    nlinarith [sq_nonneg q.2,
      mul_nonneg hx0 (sub_nonneg.mpr (by
        nlinarith [sq_nonneg q.2] : q.1 ≤ 1))]
  have hy2 : q.2 ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (q.1 - 1)]
  exact
    ⟨⟨hx0, by nlinarith [sq_nonneg (q.2 + 1)]⟩,
      ⟨hx1, by nlinarith [sq_nonneg (q.2 - 1)]⟩⟩

private theorem unit_indicator_integrable
    (f : Point3 → ℝ) (hf : Continuous f) :
    Integrable (unitSolid.indicator f) := by
  rw [integrable_indicator_iff unitSolid_closed.measurableSet]
  exact hf.continuousOn.integrableOn_compact unitSolid_compact

private theorem unit_integral_as_plane
    (f : Point3 → ℝ) (hf : Continuous f) :
    (∫ p in unitSolid, f p) =
      ∫ q in base,
        ∫ z in (-Real.sqrt (1 - q.1 ^ 2 - q.2 ^ 2))..
            Real.sqrt (1 - q.1 ^ 2 - q.2 ^ 2),
          f (q.1, q.2, z) := by
  let e :=
    (MeasurableEquiv.prodAssoc :
      ((ℝ × ℝ) × ℝ) ≃ᵐ Point3)
  have hfi : Integrable (unitSolid.indicator f) :=
    unit_indicator_integrable f hf
  have hfi' : Integrable
      (fun q : (ℝ × ℝ) × ℝ => unitSolid.indicator f (e q)) := by
    simpa only [Function.comp_apply] using
      (volume_preserving_prodAssoc.integrable_comp_emb
        e.measurableEmbedding).2 hfi
  have hreassoc :
      (∫ q : (ℝ × ℝ) × ℝ, unitSolid.indicator f (e q)) =
        ∫ p : Point3, unitSolid.indicator f p :=
    volume_preserving_prodAssoc.integral_comp' (unitSolid.indicator f)
  rw [← integral_indicator unitSolid_closed.measurableSet]
  rw [← hreassoc]
  have hFubini :
      (∫ q : (ℝ × ℝ) × ℝ, unitSolid.indicator f (e q)) =
        ∫ q : ℝ × ℝ, ∫ z : ℝ,
          unitSolid.indicator f (e (q, z)) := by
    exact MeasureTheory.integral_prod
      (fun q : (ℝ × ℝ) × ℝ => unitSolid.indicator f (e q)) hfi'
  rw [hFubini]
  change
    (∫ q : ℝ × ℝ, ∫ z : ℝ,
      unitSolid.indicator f (q.1, q.2, z)) =
      ∫ q in base,
        ∫ z in (-Real.sqrt (1 - q.1 ^ 2 - q.2 ^ 2))..
            Real.sqrt (1 - q.1 ^ 2 - q.2 ^ 2),
          f (q.1, q.2, z)
  have hsection (q : ℝ × ℝ) :
      (∫ z : ℝ, unitSolid.indicator f (q.1, q.2, z)) =
        base.indicator
          (fun q =>
            ∫ z in (-Real.sqrt (1 - q.1 ^ 2 - q.2 ^ 2))..
                Real.sqrt (1 - q.1 ^ 2 - q.2 ^ 2),
              f (q.1, q.2, z)) q := by
    let rho : ℝ := q.1 ^ 2 + q.2 ^ 2
    by_cases hq : q ∈ base
    · have hrho0 : 0 ≤ rho :=
        add_nonneg (sq_nonneg q.1) (sq_nonneg q.2)
      have hx0 : 0 ≤ q.1 := by
        change rho ≤ q.1 at hq
        linarith
      have hx1 : q.1 ≤ 1 := by
        change rho ≤ q.1 at hq
        nlinarith [sq_nonneg q.2,
          mul_nonneg hx0 (sub_nonneg.mpr (by
            nlinarith [sq_nonneg q.2] : q.1 ≤ 1))]
      have hrho1 : rho ≤ 1 := by
        change rho ≤ q.1 at hq
        linarith
      let t : ℝ := Real.sqrt (1 - rho)
      have ht0 : 0 ≤ t := Real.sqrt_nonneg _
      have ht2 : t ^ 2 = 1 - rho :=
        Real.sq_sqrt (sub_nonneg.mpr hrho1)
      have hmem (z : ℝ) :
          (q.1, q.2, z) ∈ unitSolid ↔ z ∈ Set.Icc (-t) t := by
        change
          rho + z ^ 2 ≤ 1 ∧ rho ≤ q.1 ↔ -t ≤ z ∧ z ≤ t
        constructor
        · rintro ⟨hsphere, _⟩
          have hz2 : z ^ 2 ≤ t ^ 2 := by
            rw [ht2]
            linarith
          have habs : |z| ≤ |t| := (sq_le_sq).mp hz2
          rw [abs_of_nonneg ht0] at habs
          exact (abs_le).1 habs
        · rintro hz
          have hz2 : z ^ 2 ≤ t ^ 2 :=
            (sq_le_sq).mpr (by
              simpa [abs_of_nonneg ht0] using (abs_le).2 hz)
          rw [ht2] at hz2
          exact ⟨by linarith, hq⟩
      have hfun :
          (fun z : ℝ =>
            unitSolid.indicator f (q.1, q.2, z)) =
            (Set.Icc (-t) t).indicator
              (fun z => f (q.1, q.2, z)) := by
        funext z
        simp only [Set.indicator, hmem]
      rw [hfun, integral_indicator measurableSet_Icc]
      rw [integral_Icc_eq_integral_Ioc]
      rw [← intervalIntegral.integral_of_le (neg_le_self ht0)]
      rw [Set.indicator_of_mem hq]
      simp only [t, rho]
      congr 1 <;> ring
    · have hnone (z : ℝ) : (q.1, q.2, z) ∉ unitSolid := by
        intro hp
        exact hq hp.2
      simp [Set.indicator, hnone, hq]
  simp_rw [hsection]
  rw [integral_indicator base_closed.measurableSet]

private def polarBase : Set (ℝ × ℝ) :=
  {p |
    p.2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) ∧
      p.1 ∈ Set.Ioc (0 : ℝ) (Real.cos p.2)}

private theorem polarBase_measurable : MeasurableSet polarBase := by
  unfold polarBase
  measurability

private theorem polarBase_subset_target :
    polarBase ⊆ polarCoord.target := by
  intro p hp
  rw [polarCoord_target]
  exact
    ⟨hp.2.1,
      ⟨by linarith [hp.1.1, Real.pi_pos],
        by linarith [hp.1.2, Real.pi_pos]⟩⟩

private theorem base_polar_mem (p : ℝ × ℝ)
    (hp : p ∈ polarCoord.target) :
    polarCoord.symm p ∈ base ↔ p ∈ polarBase := by
  rcases p with ⟨r, theta⟩
  rw [polarCoord_target] at hp
  have hr : 0 < r := hp.1
  have htrig :
      (r * Real.cos theta) ^ 2 +
          (r * Real.sin theta) ^ 2 = r ^ 2 := by
    calc
      _ = r ^ 2 *
          (Real.cos theta ^ 2 + Real.sin theta ^ 2) := by ring
      _ = r ^ 2 := by rw [Real.cos_sq_add_sin_sq]; ring
  rw [polarCoord_symm_apply]
  change
    (r * Real.cos theta) ^ 2 +
        (r * Real.sin theta) ^ 2 ≤ r * Real.cos theta ↔
      theta ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) ∧
        r ∈ Set.Ioc 0 (Real.cos theta)
  rw [htrig]
  constructor
  · intro h
    have hrc : r ≤ Real.cos theta := by
      nlinarith [mul_pos hr (by
        nlinarith : 0 < r)]
    have hcpos : 0 < Real.cos theta := hr.trans_le hrc
    have htheta :
        theta ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor
      · by_contra hn
        have hneg : theta ≤ -(Real.pi / 2) := le_of_not_gt hn
        have hnonpos : Real.cos (-theta) ≤ 0 := by
          apply Real.cos_nonpos_of_pi_div_two_le_of_le
          · linarith
          · linarith [hp.2.1, Real.pi_pos]
        rw [Real.cos_neg] at hnonpos
        linarith
      · by_contra hn
        have hpos : Real.pi / 2 ≤ theta := le_of_not_gt hn
        have hnonpos : Real.cos theta ≤ 0 := by
          apply Real.cos_nonpos_of_pi_div_two_le_of_le hpos
          linarith [hp.2.2, Real.pi_pos]
        linarith
    exact ⟨htheta, hr, hrc⟩
  · rintro ⟨htheta, hr0, hrc⟩
    nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hrc)]

private def polarBox : Set (ℝ × ℝ) :=
  Set.Icc (0 : ℝ) 1 ×ˢ
    Set.Icc (-(Real.pi / 2)) (Real.pi / 2)

private theorem polarBox_compact : IsCompact polarBox :=
  isCompact_Icc.prod isCompact_Icc

private theorem polarBase_subset_box :
    polarBase ⊆ polarBox := by
  intro p hp
  exact
    ⟨⟨hp.2.1.le, hp.2.2.trans (Real.cos_le_one p.2)⟩,
      ⟨hp.1.1.le, hp.1.2.le⟩⟩

private theorem base_integral_as_polar_nested
    (h : ℝ × ℝ → ℝ) (hh : Continuous h) :
    (∫ q in base, h q) =
      ∫ theta in (-(Real.pi / 2))..(Real.pi / 2),
        ∫ r in (0 : ℝ)..Real.cos theta,
          r * h (r * Real.cos theta, r * Real.sin theta) := by
  let H : ℝ × ℝ → ℝ := fun p =>
    p.1 * h (p.1 * Real.cos p.2, p.1 * Real.sin p.2)
  have hH : Continuous H := by
    dsimp [H]
    fun_prop
  have htarget : MeasurableSet polarCoord.target := by
    rw [polarCoord_target]
    exact measurableSet_Ioi.prod measurableSet_Ioo
  have hpolar := integral_comp_polarCoord_symm (base.indicator h)
  rw [integral_indicator base_closed.measurableSet] at hpolar
  have hpoint (p : ℝ × ℝ) :
      polarCoord.target.indicator
          (fun p =>
            p.1 • base.indicator h (polarCoord.symm p)) p =
        polarBase.indicator H p := by
    by_cases hp : p ∈ polarCoord.target
    · rw [Set.indicator_of_mem hp]
      have hm := base_polar_mem p hp
      by_cases hb : polarCoord.symm p ∈ base
      · have hpb : p ∈ polarBase := hm.1 hb
        rw [Set.indicator_of_mem hb, Set.indicator_of_mem hpb]
        rcases p with ⟨r, theta⟩
        rw [polarCoord_symm_apply]
        simp only [H, smul_eq_mul]
      · have hpb : p ∉ polarBase := by
          intro hpb
          exact hb (hm.2 hpb)
        rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem hpb]
        simp
    · rw [Set.indicator_of_notMem hp]
      have hpb : p ∉ polarBase := by
        intro hpb
        exact hp (polarBase_subset_target hpb)
      rw [Set.indicator_of_notMem hpb]
  have hsets :
      (∫ p in polarCoord.target,
          p.1 • base.indicator h (polarCoord.symm p)) =
        ∫ p in polarBase, H p := by
    rw [← integral_indicator htarget,
      ← integral_indicator polarBase_measurable]
    apply integral_congr_ae
    filter_upwards with p
    exact hpoint p
  have hiOn : IntegrableOn H polarBase :=
    (hH.continuousOn.integrableOn_compact polarBox_compact).mono_set
      polarBase_subset_box
  have hi : Integrable (polarBase.indicator H) :=
    (integrable_indicator_iff polarBase_measurable).2 hiOn
  change Integrable (polarBase.indicator H)
    (volume.prod volume) at hi
  have hfub :
      (∫ p : ℝ × ℝ, polarBase.indicator H p
          ∂volume.prod volume) =
        ∫ theta : ℝ, ∫ r : ℝ,
          polarBase.indicator H (r, theta) :=
    MeasureTheory.integral_prod_symm (polarBase.indicator H) hi
  have hsection (theta : ℝ) :
      (∫ r : ℝ, polarBase.indicator H (r, theta)) =
        (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)).indicator
          (fun theta =>
            ∫ r in Set.Ioc (0 : ℝ) (Real.cos theta),
              H (r, theta)) theta := by
    by_cases ht :
        theta ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)
    · rw [Set.indicator_of_mem ht,
        ← integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      filter_upwards with r
      by_cases hr : r ∈ Set.Ioc (0 : ℝ) (Real.cos theta)
      · have hp : (r, theta) ∈ polarBase := ⟨ht, hr⟩
        simp [Set.indicator, hp, hr]
      · have hp : (r, theta) ∉ polarBase := by
          intro hp
          exact hr hp.2
        simp [Set.indicator, hp, hr]
    · rw [Set.indicator_of_notMem ht, ← integral_zero]
      apply integral_congr_ae
      filter_upwards with r
      have hp : (r, theta) ∉ polarBase := by
        intro hp
        exact ht hp.1
      simp [Set.indicator, hp]
  have hclosed_to_intervals :
      (∫ theta in Set.Ioo (-(Real.pi / 2)) (Real.pi / 2),
        ∫ r in Set.Ioc (0 : ℝ) (Real.cos theta),
          H (r, theta)) =
        ∫ theta in (-(Real.pi / 2))..(Real.pi / 2),
          ∫ r in (0 : ℝ)..Real.cos theta,
            H (r, theta) := by
    calc
      _ = ∫ theta in Set.Ioc (-(Real.pi / 2)) (Real.pi / 2),
          ∫ r in Set.Ioc (0 : ℝ) (Real.cos theta),
            H (r, theta) :=
        (integral_Ioc_eq_integral_Ioo
          (f := fun theta =>
            ∫ r in Set.Ioc (0 : ℝ) (Real.cos theta),
              H (r, theta))).symm
      _ = ∫ theta in Set.Ioc (-(Real.pi / 2)) (Real.pi / 2),
          ∫ r in (0 : ℝ)..Real.cos theta,
            H (r, theta) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
        intro theta ht
        have hc0 : 0 ≤ Real.cos theta :=
          Real.cos_nonneg_of_mem_Icc ⟨ht.1.le, ht.2⟩
        exact (intervalIntegral.integral_of_le hc0).symm
      _ = _ :=
        (intervalIntegral.integral_of_le
          (by linarith [Real.pi_pos] :
            -(Real.pi / 2) ≤ Real.pi / 2)).symm
  calc
    (∫ q in base, h q) =
        ∫ p in polarCoord.target,
          p.1 • base.indicator h (polarCoord.symm p) :=
      hpolar.symm
    _ = ∫ p in polarBase, H p := hsets
    _ = ∫ p : ℝ × ℝ, polarBase.indicator H p := by
      rw [integral_indicator polarBase_measurable]
    _ = ∫ theta : ℝ, ∫ r : ℝ,
          polarBase.indicator H (r, theta) := hfub
    _ = ∫ theta : ℝ,
        (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)).indicator
          (fun theta =>
            ∫ r in Set.Ioc (0 : ℝ) (Real.cos theta),
              H (r, theta)) theta := by
      apply integral_congr_ae
      filter_upwards with theta
      exact hsection theta
    _ = ∫ theta in Set.Ioo (-(Real.pi / 2)) (Real.pi / 2),
          ∫ r in Set.Ioc (0 : ℝ) (Real.cos theta),
            H (r, theta) := by
      rw [integral_indicator measurableSet_Ioo]
    _ = ∫ theta in (-(Real.pi / 2))..(Real.pi / 2),
          ∫ r in (0 : ℝ)..Real.cos theta,
            H (r, theta) := hclosed_to_intervals
    _ = _ := by
      rfl

private def planeZ (q : ℝ × ℝ) : ℝ :=
  (2 / 3 : ℝ) *
    Real.sqrt (1 - q.1 ^ 2 - q.2 ^ 2) ^ 3

private def planeX (q : ℝ × ℝ) : ℝ :=
  2 * q.1 ^ 2 * Real.sqrt (1 - q.1 ^ 2 - q.2 ^ 2)

private def planeY (q : ℝ × ℝ) : ℝ :=
  2 * q.2 ^ 2 * Real.sqrt (1 - q.1 ^ 2 - q.2 ^ 2)

private theorem planeZ_continuous : Continuous planeZ := by
  unfold planeZ
  fun_prop

private theorem planeX_continuous : Continuous planeX := by
  unfold planeX
  fun_prop

private theorem planeY_continuous : Continuous planeY := by
  unfold planeY
  fun_prop

private theorem unit_z_sq_as_iterated :
    (∫ p in unitSolid, p.2.2 ^ 2) =
      ∫ theta in (-(Real.pi / 2))..(Real.pi / 2),
        ∫ r in (0 : ℝ)..Real.cos theta,
          (2 / 3 : ℝ) * r * Real.sqrt (1 - r ^ 2) ^ 3 := by
  calc
    (∫ p in unitSolid, p.2.2 ^ 2) =
        ∫ q in base, planeZ q := by
      rw [unit_integral_as_plane
        (fun p : Point3 => p.2.2 ^ 2)
        ((continuous_snd.comp continuous_snd).pow 2)]
      apply MeasureTheory.setIntegral_congr_fun
        base_closed.measurableSet
      intro q hq
      unfold planeZ
      dsimp only
      rw [integral_pow]
      norm_num
      ring
    _ = ∫ theta in (-(Real.pi / 2))..(Real.pi / 2),
        ∫ r in (0 : ℝ)..Real.cos theta,
          r * planeZ
            (r * Real.cos theta, r * Real.sin theta) :=
      base_integral_as_polar_nested planeZ planeZ_continuous
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro theta ht
      apply intervalIntegral.integral_congr
      intro r hr
      unfold planeZ
      dsimp only
      have htrig :
          (r * Real.cos theta) ^ 2 +
              (r * Real.sin theta) ^ 2 = r ^ 2 := by
        calc
          _ = r ^ 2 *
              (Real.cos theta ^ 2 + Real.sin theta ^ 2) := by ring
          _ = r ^ 2 := by rw [Real.cos_sq_add_sin_sq]; ring
      rw [show
        1 - (r * Real.cos theta) ^ 2 -
            (r * Real.sin theta) ^ 2 =
          1 - r ^ 2 by linarith]
      ring

private theorem unit_x_sq_as_iterated :
    (∫ p in unitSolid, p.1 ^ 2) =
      ∫ theta in (-(Real.pi / 2))..(Real.pi / 2),
        ∫ r in (0 : ℝ)..Real.cos theta,
          2 * r ^ 3 * Real.cos theta ^ 2 *
            Real.sqrt (1 - r ^ 2) := by
  calc
    (∫ p in unitSolid, p.1 ^ 2) =
        ∫ q in base, planeX q := by
      rw [unit_integral_as_plane
        (fun p : Point3 => p.1 ^ 2) (continuous_fst.pow 2)]
      apply MeasureTheory.setIntegral_congr_fun
        base_closed.measurableSet
      intro q hq
      unfold planeX
      dsimp only
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    _ = ∫ theta in (-(Real.pi / 2))..(Real.pi / 2),
        ∫ r in (0 : ℝ)..Real.cos theta,
          r * planeX
            (r * Real.cos theta, r * Real.sin theta) :=
      base_integral_as_polar_nested planeX planeX_continuous
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro theta ht
      apply intervalIntegral.integral_congr
      intro r hr
      unfold planeX
      dsimp only
      have htrig :
          (r * Real.cos theta) ^ 2 +
              (r * Real.sin theta) ^ 2 = r ^ 2 := by
        calc
          _ = r ^ 2 *
              (Real.cos theta ^ 2 + Real.sin theta ^ 2) := by ring
          _ = r ^ 2 := by rw [Real.cos_sq_add_sin_sq]; ring
      rw [show
        1 - (r * Real.cos theta) ^ 2 -
            (r * Real.sin theta) ^ 2 =
          1 - r ^ 2 by linarith]
      ring

private theorem unit_y_sq_as_iterated :
    (∫ p in unitSolid, p.2.1 ^ 2) =
      ∫ theta in (-(Real.pi / 2))..(Real.pi / 2),
        ∫ r in (0 : ℝ)..Real.cos theta,
          2 * r ^ 3 * Real.sin theta ^ 2 *
            Real.sqrt (1 - r ^ 2) := by
  calc
    (∫ p in unitSolid, p.2.1 ^ 2) =
        ∫ q in base, planeY q := by
      rw [unit_integral_as_plane
        (fun p : Point3 => p.2.1 ^ 2)
        ((continuous_fst.comp continuous_snd).pow 2)]
      apply MeasureTheory.setIntegral_congr_fun
        base_closed.measurableSet
      intro q hq
      unfold planeY
      dsimp only
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    _ = ∫ theta in (-(Real.pi / 2))..(Real.pi / 2),
        ∫ r in (0 : ℝ)..Real.cos theta,
          r * planeY
            (r * Real.cos theta, r * Real.sin theta) :=
      base_integral_as_polar_nested planeY planeY_continuous
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro theta ht
      apply intervalIntegral.integral_congr
      intro r hr
      unfold planeY
      dsimp only
      have htrig :
          (r * Real.cos theta) ^ 2 +
              (r * Real.sin theta) ^ 2 = r ^ 2 := by
        calc
          _ = r ^ 2 *
              (Real.cos theta ^ 2 + Real.sin theta ^ 2) := by ring
          _ = r ^ 2 := by rw [Real.cos_sq_add_sin_sq]; ring
      rw [show
        1 - (r * Real.cos theta) ^ 2 -
            (r * Real.sin theta) ^ 2 =
          1 - r ^ 2 by linarith]
      ring

private theorem radial_z_formula (d : ℝ)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    (∫ r in (0 : ℝ)..d,
      (2 / 3 : ℝ) * r * Real.sqrt (1 - r ^ 2) ^ 3) =
      (2 / 15 : ℝ) *
        (1 - Real.sqrt (1 - d ^ 2) ^ 5) := by
  let F : ℝ → ℝ := fun r =>
    -(2 / 15 : ℝ) * Real.sqrt (1 - r ^ 2) ^ 5
  have hcont : ContinuousOn F (Set.Icc (0 : ℝ) d) := by
    exact (by
      dsimp [F]
      fun_prop : Continuous F).continuousOn
  have hderiv : ∀ r ∈ Set.Ioo (0 : ℝ) d,
      HasDerivAt F
        ((2 / 3 : ℝ) * r * Real.sqrt (1 - r ^ 2) ^ 3) r := by
    intro r hr
    have harg : 0 < 1 - r ^ 2 := by
      have hr1 : r < 1 := hr.2.trans_le hd1
      have hp : 0 < (1 - r) * (1 + r) :=
        mul_pos (sub_pos.mpr hr1) (by linarith [hr.1])
      nlinarith
    have hinner :
        HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * r) r := by
      convert (hasDerivAt_const r (1 : ℝ)).sub
        ((hasDerivAt_id r).pow 2) using 1 <;>
        simp only [id_eq] <;> ring
    have hsqrt :
        HasDerivAt (fun x : ℝ => Real.sqrt (1 - x ^ 2))
          (1 / (2 * Real.sqrt (1 - r ^ 2)) * (-2 * r)) r := by
      simpa only [Function.comp_apply] using
        (Real.hasDerivAt_sqrt harg.ne').comp r hinner
    have hspos : 0 < Real.sqrt (1 - r ^ 2) :=
      Real.sqrt_pos.2 harg
    dsimp [F]
    convert (hsqrt.pow 5).const_mul (-(2 / 15 : ℝ)) using 1
    norm_num
    field_simp [hspos.ne']
    ring
  have hi : IntervalIntegrable
      (fun r : ℝ =>
        (2 / 3 : ℝ) * r * Real.sqrt (1 - r ^ 2) ^ 3)
      MeasureTheory.volume 0 d :=
    (by fun_prop : Continuous
      (fun r : ℝ =>
        (2 / 3 : ℝ) * r *
          Real.sqrt (1 - r ^ 2) ^ 3)).intervalIntegrable _ _
  have hFTC :
      (∫ r in (0 : ℝ)..d,
        (2 / 3 : ℝ) * r * Real.sqrt (1 - r ^ 2) ^ 3) =
        F d - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      hd0 hcont hderiv hi
  rw [hFTC]
  dsimp [F]
  norm_num [Real.sqrt_one]
  ring

private theorem integral_even_continuous
    (f : ℝ → ℝ) (hf : Continuous f) (d : ℝ)
    (heven : ∀ x, f (-x) = f x) :
    (∫ x in (-d)..d, f x) =
      2 * ∫ x in (0 : ℝ)..d, f x := by
  have hleft :
      (∫ x in (-d)..(0 : ℝ), f x) =
        ∫ x in (0 : ℝ)..d, f x := by
    calc
      (∫ x in (-d)..(0 : ℝ), f x) =
          ∫ x in (0 : ℝ)..d, f (-x) := by
        simpa using
          (intervalIntegral.integral_comp_neg
            (f := f) (a := (0 : ℝ)) (b := d)).symm
      _ = ∫ x in (0 : ℝ)..d, f x := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact heven x
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (-d) 0)
    (hf.intervalIntegrable 0 d)]
  rw [hleft]
  ring

private theorem sqrt_one_sub_cos_sq_eq_sin {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    Real.sqrt (1 - Real.cos x ^ 2) = Real.sin x := by
  have hs : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_mem_Icc
      ⟨hx.1, hx.2.trans (by linarith [Real.pi_pos])⟩
  have hid :
      1 - Real.cos x ^ 2 = Real.sin x ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [hid, Real.sqrt_sq_eq_abs, abs_of_nonneg hs]

private theorem integral_sin_three_half :
    (∫ x in (0 : ℝ)..Real.pi / 2, Real.sin x ^ 3) =
      (2 / 3 : ℝ) := by
  rw [show (3 : ℕ) = 1 + 2 by norm_num, integral_sin_pow]
  norm_num

private theorem integral_sin_five_half :
    (∫ x in (0 : ℝ)..Real.pi / 2, Real.sin x ^ 5) =
      (8 / 15 : ℝ) := by
  rw [show (5 : ℕ) = 3 + 2 by norm_num, integral_sin_pow]
  rw [show (3 : ℕ) = 1 + 2 by norm_num, integral_sin_pow]
  norm_num

private theorem integral_sin_seven_half :
    (∫ x in (0 : ℝ)..Real.pi / 2, Real.sin x ^ 7) =
      (16 / 35 : ℝ) := by
  rw [show (7 : ℕ) = 5 + 2 by norm_num, integral_sin_pow]
  rw [show (5 : ℕ) = 3 + 2 by norm_num, integral_sin_pow]
  rw [show (3 : ℕ) = 1 + 2 by norm_num, integral_sin_pow]
  norm_num

private theorem integral_cos_sq_half :
    (∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ 2) =
      Real.pi / 4 := by
  rw [integral_cos_sq]
  norm_num
  ring

private theorem integral_sin_sq_half :
    (∫ x in (0 : ℝ)..Real.pi / 2, Real.sin x ^ 2) =
      Real.pi / 4 := by
  rw [integral_sin_sq]
  norm_num
  ring

private theorem integral_sin_three_cos_sq_half :
    (∫ x in (0 : ℝ)..Real.pi / 2,
      Real.sin x ^ 3 * Real.cos x ^ 2) =
      (2 / 15 : ℝ) := by
  calc
    _ = ∫ x in (0 : ℝ)..Real.pi / 2,
        Real.sin x ^ 3 - Real.sin x ^ 5 := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      have hcos :
          Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq x]
      rw [hcos]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_sub
        ((Real.continuous_sin.pow 3).intervalIntegrable _ _)
        ((Real.continuous_sin.pow 5).intervalIntegrable _ _)]
      rw [integral_sin_three_half, integral_sin_five_half]
      ring

private theorem integral_sin_five_cos_sq_half :
    (∫ x in (0 : ℝ)..Real.pi / 2,
      Real.sin x ^ 5 * Real.cos x ^ 2) =
      (8 / 105 : ℝ) := by
  calc
    _ = ∫ x in (0 : ℝ)..Real.pi / 2,
        Real.sin x ^ 5 - Real.sin x ^ 7 := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      have hcos :
          Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq x]
      rw [hcos]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_sub
        ((Real.continuous_sin.pow 5).intervalIntegrable _ _)
        ((Real.continuous_sin.pow 7).intervalIntegrable _ _)]
      rw [integral_sin_five_half, integral_sin_seven_half]
      ring

private def angularZ (x : ℝ) : ℝ :=
  (2 / 15 : ℝ) *
    (1 - Real.sqrt (1 - Real.cos x ^ 2) ^ 5)

private def angularR (x : ℝ) : ℝ :=
  (4 / 15 : ℝ) -
    (2 / 3 : ℝ) *
      Real.sqrt (1 - Real.cos x ^ 2) ^ 3 +
    (2 / 5 : ℝ) *
      Real.sqrt (1 - Real.cos x ^ 2) ^ 5

private def angularX (x : ℝ) : ℝ :=
  Real.cos x ^ 2 * angularR x

private def angularY (x : ℝ) : ℝ :=
  Real.sin x ^ 2 * angularR x

private theorem angularZ_continuous : Continuous angularZ := by
  unfold angularZ
  fun_prop

private theorem angularX_continuous : Continuous angularX := by
  unfold angularX angularR
  fun_prop

private theorem angularY_continuous : Continuous angularY := by
  unfold angularY angularR
  fun_prop

private theorem angularZ_even (x : ℝ) :
    angularZ (-x) = angularZ x := by
  simp [angularZ]

private theorem angularX_even (x : ℝ) :
    angularX (-x) = angularX x := by
  simp [angularX, angularR]

private theorem angularY_even (x : ℝ) :
    angularY (-x) = angularY x := by
  simp [angularY, angularR]

private theorem angularZ_positive_half :
    (∫ x in (0 : ℝ)..Real.pi / 2, angularZ x) =
      Real.pi / 15 - 16 / 225 := by
  calc
    _ = ∫ x in (0 : ℝ)..Real.pi / 2,
        (2 / 15 : ℝ) * (1 - Real.sin x ^ 5) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by positivity :
        (0 : ℝ) ≤ Real.pi / 2)] at hx
      unfold angularZ
      rw [sqrt_one_sub_cos_sq_eq_sin hx]
    _ = _ := by
      rw [intervalIntegral.integral_const_mul]
      rw [intervalIntegral.integral_sub
        (continuous_const.intervalIntegrable _ _)
        ((Real.continuous_sin.pow 5).intervalIntegrable _ _)]
      simp only [intervalIntegral.integral_const,
        smul_eq_mul, mul_one, sub_zero,
        integral_sin_five_half]
      ring

private theorem angularX_positive_half :
    (∫ x in (0 : ℝ)..Real.pi / 2, angularX x) =
      Real.pi / 15 - 92 / 1575 := by
  calc
    _ = ∫ x in (0 : ℝ)..Real.pi / 2,
        (4 / 15 : ℝ) * Real.cos x ^ 2 -
          (2 / 3 : ℝ) *
            (Real.sin x ^ 3 * Real.cos x ^ 2) +
          (2 / 5 : ℝ) *
            (Real.sin x ^ 5 * Real.cos x ^ 2) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by positivity :
        (0 : ℝ) ≤ Real.pi / 2)] at hx
      unfold angularX angularR
      rw [sqrt_one_sub_cos_sq_eq_sin hx]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add
        ((by fun_prop : Continuous
          (fun x : ℝ =>
            (4 / 15 : ℝ) * Real.cos x ^ 2 -
              (2 / 3 : ℝ) *
                (Real.sin x ^ 3 * Real.cos x ^ 2)))
          |>.intervalIntegrable _ _)
        ((by fun_prop : Continuous
          (fun x : ℝ =>
            (2 / 5 : ℝ) *
              (Real.sin x ^ 5 * Real.cos x ^ 2)))
          |>.intervalIntegrable _ _)]
      rw [intervalIntegral.integral_sub
        ((by fun_prop : Continuous
          (fun x : ℝ =>
            (4 / 15 : ℝ) * Real.cos x ^ 2))
          |>.intervalIntegrable _ _)
        ((by fun_prop : Continuous
          (fun x : ℝ =>
            (2 / 3 : ℝ) *
              (Real.sin x ^ 3 * Real.cos x ^ 2)))
          |>.intervalIntegrable _ _)]
      simp only [intervalIntegral.integral_const_mul]
      rw [integral_cos_sq_half,
        integral_sin_three_cos_sq_half,
        integral_sin_five_cos_sq_half]
      ring

private theorem angularY_positive_half :
    (∫ x in (0 : ℝ)..Real.pi / 2, angularY x) =
      Real.pi / 15 - 272 / 1575 := by
  calc
    _ = ∫ x in (0 : ℝ)..Real.pi / 2,
        (4 / 15 : ℝ) * Real.sin x ^ 2 -
          (2 / 3 : ℝ) * Real.sin x ^ 5 +
          (2 / 5 : ℝ) * Real.sin x ^ 7 := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by positivity :
        (0 : ℝ) ≤ Real.pi / 2)] at hx
      unfold angularY angularR
      rw [sqrt_one_sub_cos_sq_eq_sin hx]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add
        ((by fun_prop : Continuous
          (fun x : ℝ =>
            (4 / 15 : ℝ) * Real.sin x ^ 2 -
              (2 / 3 : ℝ) * Real.sin x ^ 5))
          |>.intervalIntegrable _ _)
        ((by fun_prop : Continuous
          (fun x : ℝ =>
            (2 / 5 : ℝ) * Real.sin x ^ 7))
          |>.intervalIntegrable _ _)]
      rw [intervalIntegral.integral_sub
        ((by fun_prop : Continuous
          (fun x : ℝ =>
            (4 / 15 : ℝ) * Real.sin x ^ 2))
          |>.intervalIntegrable _ _)
        ((by fun_prop : Continuous
          (fun x : ℝ =>
            (2 / 3 : ℝ) * Real.sin x ^ 5))
          |>.intervalIntegrable _ _)]
      simp only [intervalIntegral.integral_const_mul]
      rw [integral_sin_sq_half,
        integral_sin_five_half,
        integral_sin_seven_half]
      ring

private theorem radial_xy_formula (d : ℝ)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    (∫ r in (0 : ℝ)..d,
      2 * r ^ 3 * Real.sqrt (1 - r ^ 2)) =
      (4 / 15 : ℝ) -
        (2 / 3 : ℝ) * Real.sqrt (1 - d ^ 2) ^ 3 +
        (2 / 5 : ℝ) * Real.sqrt (1 - d ^ 2) ^ 5 := by
  let F : ℝ → ℝ := fun r =>
    -(2 / 3 : ℝ) * Real.sqrt (1 - r ^ 2) ^ 3 +
      (2 / 5 : ℝ) * Real.sqrt (1 - r ^ 2) ^ 5
  have hcont : ContinuousOn F (Set.Icc (0 : ℝ) d) := by
    exact (by
      dsimp [F]
      fun_prop : Continuous F).continuousOn
  have hderiv : ∀ r ∈ Set.Ioo (0 : ℝ) d,
      HasDerivAt F
        (2 * r ^ 3 * Real.sqrt (1 - r ^ 2)) r := by
    intro r hr
    have harg : 0 < 1 - r ^ 2 := by
      have hr1 : r < 1 := hr.2.trans_le hd1
      have hp : 0 < (1 - r) * (1 + r) :=
        mul_pos (sub_pos.mpr hr1) (by linarith [hr.1])
      nlinarith
    have hinner :
        HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * r) r := by
      convert (hasDerivAt_const r (1 : ℝ)).sub
        ((hasDerivAt_id r).pow 2) using 1 <;>
        simp only [id_eq] <;> ring
    have hsqrt :
        HasDerivAt (fun x : ℝ => Real.sqrt (1 - x ^ 2))
          (1 / (2 * Real.sqrt (1 - r ^ 2)) * (-2 * r)) r := by
      simpa only [Function.comp_apply] using
        (Real.hasDerivAt_sqrt harg.ne').comp r hinner
    have hspos : 0 < Real.sqrt (1 - r ^ 2) :=
      Real.sqrt_pos.2 harg
    have hs2 :
        Real.sqrt (1 - r ^ 2) ^ 2 = 1 - r ^ 2 :=
      Real.sq_sqrt harg.le
    dsimp [F]
    convert
      ((hsqrt.pow 3).const_mul (-(2 / 3 : ℝ))).add
        ((hsqrt.pow 5).const_mul (2 / 5 : ℝ))
      using 1
    norm_num
    field_simp [hspos.ne']
    rw [hs2]
    ring
  have hi : IntervalIntegrable
      (fun r : ℝ =>
        2 * r ^ 3 * Real.sqrt (1 - r ^ 2))
      MeasureTheory.volume 0 d :=
    (by fun_prop : Continuous
      (fun r : ℝ =>
        2 * r ^ 3 *
          Real.sqrt (1 - r ^ 2))).intervalIntegrable _ _
  have hFTC :
      (∫ r in (0 : ℝ)..d,
        2 * r ^ 3 * Real.sqrt (1 - r ^ 2)) =
        F d - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      hd0 hcont hderiv hi
  rw [hFTC]
  dsimp [F]
  norm_num [Real.sqrt_one]
  ring

private theorem angularZ_formula :
    (∫ x in (-(Real.pi / 2))..(Real.pi / 2),
      angularZ x) =
      2 / 225 * (15 * Real.pi - 16) := by
  rw [integral_even_continuous angularZ angularZ_continuous
    (Real.pi / 2) angularZ_even]
  rw [angularZ_positive_half]
  ring

private theorem angularX_formula :
    (∫ x in (-(Real.pi / 2))..(Real.pi / 2),
      angularX x) =
      2 / 1575 * (105 * Real.pi - 92) := by
  rw [integral_even_continuous angularX angularX_continuous
    (Real.pi / 2) angularX_even]
  rw [angularX_positive_half]
  ring

private theorem angularY_formula :
    (∫ x in (-(Real.pi / 2))..(Real.pi / 2),
      angularY x) =
      2 / 1575 * (105 * Real.pi - 272) := by
  rw [integral_even_continuous angularY angularY_continuous
    (Real.pi / 2) angularY_even]
  rw [angularY_positive_half]
  ring

private theorem unit_z_sq_formula :
    (∫ p in unitSolid, p.2.2 ^ 2) =
      2 / 225 * (15 * Real.pi - 16) := by
  rw [unit_z_sq_as_iterated]
  calc
    _ = ∫ theta in (-(Real.pi / 2))..(Real.pi / 2),
        angularZ theta := by
      apply intervalIntegral.integral_congr
      intro theta htheta
      rw [uIcc_of_le (by linarith [Real.pi_pos] :
        -(Real.pi / 2) ≤ Real.pi / 2)] at htheta
      simpa [angularZ] using
        radial_z_formula (Real.cos theta)
          (Real.cos_nonneg_of_mem_Icc htheta)
          (Real.cos_le_one theta)
    _ = _ := angularZ_formula

private theorem unit_x_sq_formula :
    (∫ p in unitSolid, p.1 ^ 2) =
      2 / 1575 * (105 * Real.pi - 92) := by
  rw [unit_x_sq_as_iterated]
  calc
    _ = ∫ theta in (-(Real.pi / 2))..(Real.pi / 2),
        angularX theta := by
      apply intervalIntegral.integral_congr
      intro theta htheta
      rw [uIcc_of_le (by linarith [Real.pi_pos] :
        -(Real.pi / 2) ≤ Real.pi / 2)] at htheta
      calc
        (∫ r in (0 : ℝ)..Real.cos theta,
            2 * r ^ 3 * Real.cos theta ^ 2 *
              Real.sqrt (1 - r ^ 2)) =
            ∫ r in (0 : ℝ)..Real.cos theta,
              Real.cos theta ^ 2 *
                (2 * r ^ 3 * Real.sqrt (1 - r ^ 2)) := by
          apply intervalIntegral.integral_congr
          intro r hr
          ring
        _ = Real.cos theta ^ 2 *
            ∫ r in (0 : ℝ)..Real.cos theta,
              2 * r ^ 3 * Real.sqrt (1 - r ^ 2) := by
          rw [intervalIntegral.integral_const_mul]
        _ = angularX theta := by
          rw [radial_xy_formula (Real.cos theta)
            (Real.cos_nonneg_of_mem_Icc htheta)
            (Real.cos_le_one theta)]
          rfl
    _ = _ := angularX_formula

private theorem unit_y_sq_formula :
    (∫ p in unitSolid, p.2.1 ^ 2) =
      2 / 1575 * (105 * Real.pi - 272) := by
  rw [unit_y_sq_as_iterated]
  calc
    _ = ∫ theta in (-(Real.pi / 2))..(Real.pi / 2),
        angularY theta := by
      apply intervalIntegral.integral_congr
      intro theta htheta
      rw [uIcc_of_le (by linarith [Real.pi_pos] :
        -(Real.pi / 2) ≤ Real.pi / 2)] at htheta
      calc
        (∫ r in (0 : ℝ)..Real.cos theta,
            2 * r ^ 3 * Real.sin theta ^ 2 *
              Real.sqrt (1 - r ^ 2)) =
            ∫ r in (0 : ℝ)..Real.cos theta,
              Real.sin theta ^ 2 *
                (2 * r ^ 3 * Real.sqrt (1 - r ^ 2)) := by
          apply intervalIntegral.integral_congr
          intro r hr
          ring
        _ = Real.sin theta ^ 2 *
            ∫ r in (0 : ℝ)..Real.cos theta,
              2 * r ^ 3 * Real.sqrt (1 - r ^ 2) := by
          rw [intervalIntegral.integral_const_mul]
        _ = angularY theta := by
          rw [radial_xy_formula (Real.cos theta)
            (Real.cos_nonneg_of_mem_Icc htheta)
            (Real.cos_le_one theta)]
          rfl
    _ = _ := angularY_formula

private theorem inertiaXY_formula
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    inertiaXY a b c =
      2 * a * b * c ^ 3 / 225 *
        (15 * Real.pi - 16) := by
  unfold inertiaXY
  rw [scale_set_integral a b c ha hb hc
    (fun p : Point3 => p.2.2 ^ 2)]
  simp only [scale3_apply]
  calc
    (∫ p in unitSolid,
        a * b * c * (c * p.2.2) ^ 2) =
        ∫ p in unitSolid,
          (a * b * c ^ 3) * p.2.2 ^ 2 := by
      apply MeasureTheory.setIntegral_congr_fun
        unitSolid_closed.measurableSet
      intro p hp
      ring
    _ = (a * b * c ^ 3) *
        ∫ p in unitSolid, p.2.2 ^ 2 := by
      rw [MeasureTheory.integral_const_mul]
    _ = _ := by
      rw [unit_z_sq_formula]
      ring

private theorem inertiaYZ_formula
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    inertiaYZ a b c =
      2 * a ^ 3 * b * c / 1575 *
        (105 * Real.pi - 92) := by
  unfold inertiaYZ
  rw [scale_set_integral a b c ha hb hc
    (fun p : Point3 => p.1 ^ 2)]
  simp only [scale3_apply]
  calc
    (∫ p in unitSolid,
        a * b * c * (a * p.1) ^ 2) =
        ∫ p in unitSolid,
          (a ^ 3 * b * c) * p.1 ^ 2 := by
      apply MeasureTheory.setIntegral_congr_fun
        unitSolid_closed.measurableSet
      intro p hp
      ring
    _ = (a ^ 3 * b * c) *
        ∫ p in unitSolid, p.1 ^ 2 := by
      rw [MeasureTheory.integral_const_mul]
    _ = _ := by
      rw [unit_x_sq_formula]
      ring

private theorem inertiaZX_formula
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    inertiaZX a b c =
      2 * a * b ^ 3 * c / 1575 *
        (105 * Real.pi - 272) := by
  unfold inertiaZX
  rw [scale_set_integral a b c ha hb hc
    (fun p : Point3 => p.2.1 ^ 2)]
  simp only [scale3_apply]
  calc
    (∫ p in unitSolid,
        a * b * c * (b * p.2.1) ^ 2) =
        ∫ p in unitSolid,
          (a * b ^ 3 * c) * p.2.1 ^ 2 := by
      apply MeasureTheory.setIntegral_congr_fun
        unitSolid_closed.measurableSet
      intro p hp
      ring
    _ = (a * b ^ 3 * c) *
        ∫ p in unitSolid, p.2.1 ^ 2 := by
      rw [MeasureTheory.integral_const_mul]
    _ = _ := by
      rw [unit_y_sq_formula]
      ring

private theorem tripleXY_formula (a b c : ℝ) :
    (∫ φ in -Real.pi / 2..Real.pi / 2,
        ∫ r in (0 : ℝ)..Real.cos φ,
          ∫ z in -c * Real.sqrt (1 - r ^ 2)..
              c * Real.sqrt (1 - r ^ 2),
            a * b * r * z ^ 2) =
      2 * a * b * c ^ 3 / 225 * (15 * Real.pi - 16) := by
  calc
    (∫ φ in -Real.pi / 2..Real.pi / 2,
        ∫ r in (0 : ℝ)..Real.cos φ,
          ∫ z in -c * Real.sqrt (1 - r ^ 2)..
              c * Real.sqrt (1 - r ^ 2),
            a * b * r * z ^ 2) =
        ∫ φ in -Real.pi / 2..Real.pi / 2,
          ∫ r in (0 : ℝ)..Real.cos φ,
            (a * b * c ^ 3) *
              ((2 / 3 : ℝ) * r *
                Real.sqrt (1 - r ^ 2) ^ 3) := by
      apply intervalIntegral.integral_congr
      intro φ _
      apply intervalIntegral.integral_congr
      intro r _
      dsimp only
      rw [intervalIntegral.integral_const_mul, integral_pow]
      norm_num
      ring
    _ = ∫ φ in -Real.pi / 2..Real.pi / 2,
          (a * b * c ^ 3) *
            ∫ r in (0 : ℝ)..Real.cos φ,
              (2 / 3 : ℝ) * r *
                Real.sqrt (1 - r ^ 2) ^ 3 := by
      apply intervalIntegral.integral_congr
      intro φ _
      dsimp only
      rw [intervalIntegral.integral_const_mul]
    _ = (a * b * c ^ 3) *
        ∫ φ in -Real.pi / 2..Real.pi / 2,
          ∫ r in (0 : ℝ)..Real.cos φ,
            (2 / 3 : ℝ) * r *
              Real.sqrt (1 - r ^ 2) ^ 3 := by
      rw [intervalIntegral.integral_const_mul]
    _ = (a * b * c ^ 3) *
        ∫ p in unitSolid, p.2.2 ^ 2 := by
      convert congrArg (fun t : ℝ => (a * b * c ^ 3) * t)
        unit_z_sq_as_iterated.symm using 1 <;> ring
    _ = _ := by
      rw [unit_z_sq_formula]
      ring

private theorem tripleYZ_formula (a b c : ℝ) :
    (∫ φ in -Real.pi / 2..Real.pi / 2,
        ∫ r in (0 : ℝ)..Real.cos φ,
          ∫ z in -c * Real.sqrt (1 - r ^ 2)..
              c * Real.sqrt (1 - r ^ 2),
            a * b * r * (a * r * Real.cos φ) ^ 2) =
      2 * a ^ 3 * b * c / 1575 *
        (105 * Real.pi - 92) := by
  calc
    (∫ φ in -Real.pi / 2..Real.pi / 2,
        ∫ r in (0 : ℝ)..Real.cos φ,
          ∫ z in -c * Real.sqrt (1 - r ^ 2)..
              c * Real.sqrt (1 - r ^ 2),
            a * b * r * (a * r * Real.cos φ) ^ 2) =
        ∫ φ in -Real.pi / 2..Real.pi / 2,
          ∫ r in (0 : ℝ)..Real.cos φ,
            (a ^ 3 * b * c) *
              (2 * r ^ 3 * Real.cos φ ^ 2 *
                Real.sqrt (1 - r ^ 2)) := by
      apply intervalIntegral.integral_congr
      intro φ _
      apply intervalIntegral.integral_congr
      intro r _
      dsimp only
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    _ = ∫ φ in -Real.pi / 2..Real.pi / 2,
          (a ^ 3 * b * c) *
            ∫ r in (0 : ℝ)..Real.cos φ,
              2 * r ^ 3 * Real.cos φ ^ 2 *
                Real.sqrt (1 - r ^ 2) := by
      apply intervalIntegral.integral_congr
      intro φ _
      dsimp only
      rw [intervalIntegral.integral_const_mul]
    _ = (a ^ 3 * b * c) *
        ∫ φ in -Real.pi / 2..Real.pi / 2,
          ∫ r in (0 : ℝ)..Real.cos φ,
            2 * r ^ 3 * Real.cos φ ^ 2 *
              Real.sqrt (1 - r ^ 2) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (a ^ 3 * b * c) *
        ∫ p in unitSolid, p.1 ^ 2 := by
      convert congrArg (fun t : ℝ => (a ^ 3 * b * c) * t)
        unit_x_sq_as_iterated.symm using 1 <;> ring
    _ = _ := by
      rw [unit_x_sq_formula]
      ring

private theorem tripleZX_formula (a b c : ℝ) :
    (∫ φ in -Real.pi / 2..Real.pi / 2,
        ∫ r in (0 : ℝ)..Real.cos φ,
          ∫ z in -c * Real.sqrt (1 - r ^ 2)..
              c * Real.sqrt (1 - r ^ 2),
            a * b * r * (b * r * Real.sin φ) ^ 2) =
      2 * a * b ^ 3 * c / 1575 *
        (105 * Real.pi - 272) := by
  calc
    (∫ φ in -Real.pi / 2..Real.pi / 2,
        ∫ r in (0 : ℝ)..Real.cos φ,
          ∫ z in -c * Real.sqrt (1 - r ^ 2)..
              c * Real.sqrt (1 - r ^ 2),
            a * b * r * (b * r * Real.sin φ) ^ 2) =
        ∫ φ in -Real.pi / 2..Real.pi / 2,
          ∫ r in (0 : ℝ)..Real.cos φ,
            (a * b ^ 3 * c) *
              (2 * r ^ 3 * Real.sin φ ^ 2 *
                Real.sqrt (1 - r ^ 2)) := by
      apply intervalIntegral.integral_congr
      intro φ _
      apply intervalIntegral.integral_congr
      intro r _
      dsimp only
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    _ = ∫ φ in -Real.pi / 2..Real.pi / 2,
          (a * b ^ 3 * c) *
            ∫ r in (0 : ℝ)..Real.cos φ,
              2 * r ^ 3 * Real.sin φ ^ 2 *
                Real.sqrt (1 - r ^ 2) := by
      apply intervalIntegral.integral_congr
      intro φ _
      dsimp only
      rw [intervalIntegral.integral_const_mul]
    _ = (a * b ^ 3 * c) *
        ∫ φ in -Real.pi / 2..Real.pi / 2,
          ∫ r in (0 : ℝ)..Real.cos φ,
            2 * r ^ 3 * Real.sin φ ^ 2 *
              Real.sqrt (1 - r ^ 2) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (a * b ^ 3 * c) *
        ∫ p in unitSolid, p.2.1 ^ 2 := by
      convert congrArg (fun t : ℝ => (a * b ^ 3 * c) * t)
        unit_y_sq_as_iterated.symm using 1 <;> ring
    _ = _ := by
      rw [unit_y_sq_formula]
      ring

theorem gap1 (c φ r z : ℝ) (hmem : (φ, r, z) ∈ parameterDomain c) :
    -Real.pi / 2 ≤ φ := by
  exact hmem.1

theorem gap2 (c φ r z : ℝ) (hmem : (φ, r, z) ∈ parameterDomain c) :
    φ ≤ Real.pi / 2 := by
  exact hmem.2.1

theorem gap3 (c φ r z : ℝ) (hmem : (φ, r, z) ∈ parameterDomain c) :
    0 ≤ r := by
  exact hmem.2.2.1

theorem gap4 (c φ r z : ℝ) (hmem : (φ, r, z) ∈ parameterDomain c) :
    r ≤ Real.cos φ := by
  exact hmem.2.2.2.1

theorem gap5 (c φ r z : ℝ) (hmem : (φ, r, z) ∈ parameterDomain c) :
    -c * Real.sqrt (1 - r ^ 2) ≤ z := by
  exact hmem.2.2.2.2.1

theorem gap6 (c φ r z : ℝ) (hmem : (φ, r, z) ∈ parameterDomain c) :
    z ≤ c * Real.sqrt (1 - r ^ 2) := by
  exact hmem.2.2.2.2.2

theorem gap7 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    inertiaXY a b c =
      ∫ φ in -Real.pi / 2..Real.pi / 2,
        ∫ r in (0 : ℝ)..Real.cos φ,
          ∫ z in -c * Real.sqrt (1 - r ^ 2)..c * Real.sqrt (1 - r ^ 2),
            a * b * r * z ^ 2 := by
  exact (inertiaXY_formula a b c ha hb hc).trans
    (tripleXY_formula a b c).symm

theorem gap8 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (∫ φ in -Real.pi / 2..Real.pi / 2,
        ∫ r in (0 : ℝ)..Real.cos φ,
          ∫ z in -c * Real.sqrt (1 - r ^ 2)..c * Real.sqrt (1 - r ^ 2),
            a * b * r * z ^ 2) =
      2 * a * b * c ^ 3 / 225 * (15 * Real.pi - 16) := by
  exact tripleXY_formula a b c

theorem gap9 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    inertiaXY a b c =
      2 * a * b * c ^ 3 / 225 * (15 * Real.pi - 16) := by
  exact inertiaXY_formula a b c ha hb hc

theorem gap10 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    inertiaYZ a b c =
      ∫ φ in -Real.pi / 2..Real.pi / 2,
        ∫ r in (0 : ℝ)..Real.cos φ,
          ∫ z in -c * Real.sqrt (1 - r ^ 2)..c * Real.sqrt (1 - r ^ 2),
            a * b * r * (a * r * Real.cos φ) ^ 2 := by
  exact (inertiaYZ_formula a b c ha hb hc).trans
    (tripleYZ_formula a b c).symm

theorem gap11 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (∫ φ in -Real.pi / 2..Real.pi / 2,
        ∫ r in (0 : ℝ)..Real.cos φ,
          ∫ z in -c * Real.sqrt (1 - r ^ 2)..c * Real.sqrt (1 - r ^ 2),
            a * b * r * (a * r * Real.cos φ) ^ 2) =
      2 * a ^ 3 * b * c / 1575 * (105 * Real.pi - 92) := by
  exact tripleYZ_formula a b c

theorem gap12 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    inertiaYZ a b c =
      2 * a ^ 3 * b * c / 1575 * (105 * Real.pi - 92) := by
  exact inertiaYZ_formula a b c ha hb hc

theorem gap13 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    inertiaZX a b c =
      ∫ φ in -Real.pi / 2..Real.pi / 2,
        ∫ r in (0 : ℝ)..Real.cos φ,
          ∫ z in -c * Real.sqrt (1 - r ^ 2)..c * Real.sqrt (1 - r ^ 2),
            a * b * r * (b * r * Real.sin φ) ^ 2 := by
  exact (inertiaZX_formula a b c ha hb hc).trans
    (tripleZX_formula a b c).symm

theorem gap14 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (∫ φ in -Real.pi / 2..Real.pi / 2,
        ∫ r in (0 : ℝ)..Real.cos φ,
          ∫ z in -c * Real.sqrt (1 - r ^ 2)..c * Real.sqrt (1 - r ^ 2),
            a * b * r * (b * r * Real.sin φ) ^ 2) =
      2 * a * b ^ 3 * c / 1575 * (105 * Real.pi - 272) := by
  exact tripleZX_formula a b c

theorem gap15 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    inertiaZX a b c =
      2 * a * b ^ 3 * c / 1575 * (105 * Real.pi - 272) := by
  exact inertiaZX_formula a b c ha hb hc

end

end ProofGap.Exercise4146
