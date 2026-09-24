import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4138

noncomputable section

open MeasureTheory Set
open scoped Interval

abbrev Point3 := ℝ × ℝ × ℝ

def lowerHeight (x y : ℝ) : ℝ :=
  3 - x - y + ((x - 1) ^ 2 + (y - 1) ^ 2) / 2

def upperHeight (x y : ℝ) : ℝ :=
  4 - x - y

def solid : Set Point3 :=
  {p |
    (p.1 - 1) ^ 2 + (p.2.1 - 1) ^ 2 ≤ 2 ∧
      lowerHeight p.1 p.2.1 ≤ p.2.2 ∧
        p.2.2 ≤ upperHeight p.1 p.2.1}

def mass : ℝ :=
  ∫ _p in solid, (1 : ℝ)

def xCentroid : ℝ :=
  1 / mass * ∫ p in solid, p.1

def yCentroid : ℝ :=
  1 / mass * ∫ p in solid, p.2.1

def zCentroid : ℝ :=
  1 / mass * ∫ p in solid, p.2.2

private def baseDisk : Set (ℝ × ℝ) :=
  {q | q.1 ^ 2 + q.2 ^ 2 ≤ 2}

private def shiftedLower (u v : ℝ) : ℝ :=
  1 - u - v + (u ^ 2 + v ^ 2) / 2

private def shiftedUpper (u v : ℝ) : ℝ :=
  2 - u - v

private def shiftedSolid : Set Point3 :=
  {p |
    p.1 ^ 2 + p.2.1 ^ 2 ≤ 2 ∧
      shiftedLower p.1 p.2.1 ≤ p.2.2 ∧
        p.2.2 ≤ shiftedUpper p.1 p.2.1}

private def shift (p : Point3) : Point3 :=
  (p.1 + 1, p.2.1 + 1, p.2.2)

private theorem shiftedSolid_closed : IsClosed shiftedSolid := by
  have hu : Continuous (fun p : Point3 => p.1) := continuous_fst
  have hv : Continuous (fun p : Point3 => p.2.1) :=
    continuous_fst.comp continuous_snd
  have hz : Continuous (fun p : Point3 => p.2.2) :=
    continuous_snd.comp continuous_snd
  have hr : Continuous (fun p : Point3 => p.1 ^ 2 + p.2.1 ^ 2) :=
    (hu.pow 2).add (hv.pow 2)
  have hlo : Continuous (fun p : Point3 =>
      shiftedLower p.1 p.2.1) := by
    unfold shiftedLower
    fun_prop
  have hhi : Continuous (fun p : Point3 =>
      shiftedUpper p.1 p.2.1) := by
    unfold shiftedUpper
    fun_prop
  unfold shiftedSolid
  simpa only [Set.setOf_and] using
    (isClosed_le hr continuous_const).inter
      ((isClosed_le hlo hz).inter (isClosed_le hz hhi))

private theorem shiftedSolid_compact : IsCompact shiftedSolid := by
  apply (isCompact_Icc :
    IsCompact
      (Set.Icc ((-2 : ℝ), ((-2 : ℝ), (-3 : ℝ)))
        (2, (2, 6)))).of_isClosed_subset shiftedSolid_closed
  rintro ⟨u, v, z⟩ h
  change
    u ^ 2 + v ^ 2 ≤ 2 ∧
      1 - u - v + (u ^ 2 + v ^ 2) / 2 ≤ z ∧
        z ≤ 2 - u - v at h
  have hu2 : u ^ 2 ≤ 2 := by nlinarith [sq_nonneg v]
  have hv2 : v ^ 2 ≤ 2 := by nlinarith [sq_nonneg u]
  have hu : -2 ≤ u ∧ u ≤ 2 := by
    constructor <;> nlinarith [sq_nonneg (u + 2), sq_nonneg (u - 2)]
  have hv : -2 ≤ v ∧ v ≤ 2 := by
    constructor <;> nlinarith [sq_nonneg (v + 2), sq_nonneg (v - 2)]
  exact
    ⟨⟨hu.1, hv.1, by nlinarith [h.2.1, sq_nonneg u, sq_nonneg v]⟩,
      ⟨hu.2, hv.2, by linarith [h.2.2]⟩⟩

private theorem shift_image_shiftedSolid :
    shift '' shiftedSolid = solid := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases q with ⟨u, v, z⟩
    change
      u ^ 2 + v ^ 2 ≤ 2 ∧
        shiftedLower u v ≤ z ∧ z ≤ shiftedUpper u v at hq
    change
      ((u + 1 - 1) ^ 2 + (v + 1 - 1) ^ 2 ≤ 2 ∧
        lowerHeight (u + 1) (v + 1) ≤ z ∧
          z ≤ upperHeight (u + 1) (v + 1))
    simp only [shiftedLower, shiftedUpper, lowerHeight, upperHeight] at hq ⊢
    convert hq using 1 <;> ring
  · intro hp
    let q : Point3 := (p.1 - 1, p.2.1 - 1, p.2.2)
    have hshift : shift q = p := by
      rcases p with ⟨x, y, z⟩
      ext <;> simp [shift, q]
    refine ⟨q, ?_, hshift⟩
    change
      (p.1 - 1) ^ 2 + (p.2.1 - 1) ^ 2 ≤ 2 ∧
        shiftedLower (p.1 - 1) (p.2.1 - 1) ≤ p.2.2 ∧
          p.2.2 ≤ shiftedUpper (p.1 - 1) (p.2.1 - 1)
    change
      (p.1 - 1) ^ 2 + (p.2.1 - 1) ^ 2 ≤ 2 ∧
        lowerHeight p.1 p.2.1 ≤ p.2.2 ∧
          p.2.2 ≤ upperHeight p.1 p.2.1 at hp
    simp only [shiftedLower, shiftedUpper, lowerHeight, upperHeight] at hp ⊢
    convert hp using 1 <;> ring

private theorem shift_injOn : Set.InjOn shift shiftedSolid := by
  intro p hp q hq h
  rcases p with ⟨x, y, z⟩
  rcases q with ⟨x', y', z'⟩
  simp only [shift, Prod.mk.injEq] at h
  rcases h with ⟨hx, hy, hz⟩
  simp only [Prod.mk.injEq]
  exact ⟨by linarith, by linarith, hz⟩

private theorem shifted_change_of_variables
    (g : Point3 → ℝ) :
    (∫ p in solid, g p) =
      ∫ q in shiftedSolid, g (shift q) := by
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
  let I : Point3 →L[ℝ] Point3 := ContinuousLinearMap.id ℝ Point3
  have hderiv (p : Point3) :
      HasFDerivAt shift I p := by
    let c : Point3 := ((1 : ℝ), ((1 : ℝ), (0 : ℝ)))
    have hshift : shift = fun q : Point3 => q + c := by
      funext q
      rcases q with ⟨x, y, z⟩
      ext <;> simp [shift, c]
    rw [hshift]
    exact (hasFDerivAt_id (𝕜 := ℝ) p).add_const c
  have hchange :=
    integral_image_eq_integral_abs_det_fderiv_smul
      (μ := MeasureTheory.volume) shiftedSolid_closed.measurableSet
      (f := shift) (f' := fun _ => I)
      (fun p hp => (hderiv p).hasFDerivWithinAt)
      shift_injOn g
  rw [shift_image_shiftedSolid] at hchange
  have hdet : I.det = 1 := by
    rw [ContinuousLinearMap.det]
    exact LinearMap.det_id
  rw [hdet] at hchange
  simpa [smul_eq_mul] using hchange

private theorem baseDisk_closed : IsClosed baseDisk := by
  unfold baseDisk
  exact isClosed_le
    ((continuous_fst.pow 2).add (continuous_snd.pow 2))
    continuous_const

private theorem baseDisk_compact : IsCompact baseDisk := by
  apply (isCompact_Icc :
    IsCompact (Set.Icc ((-2, -2) : ℝ × ℝ) (2, 2))).of_isClosed_subset
      baseDisk_closed
  intro q hq
  change q.1 ^ 2 + q.2 ^ 2 ≤ 2 at hq
  have hx : q.1 ^ 2 ≤ 2 := by nlinarith [sq_nonneg q.2]
  have hy : q.2 ^ 2 ≤ 2 := by nlinarith [sq_nonneg q.1]
  exact
    ⟨⟨by nlinarith [sq_nonneg (q.1 + 2)],
        by nlinarith [sq_nonneg (q.2 + 2)]⟩,
      ⟨by nlinarith [sq_nonneg (q.1 - 2)],
        by nlinarith [sq_nonneg (q.2 - 2)]⟩⟩

private theorem shifted_integral_as_base
    (f : Point3 → ℝ) (hf : Continuous f) :
    (∫ p in shiftedSolid, f p) =
      ∫ q in baseDisk,
        ∫ z in shiftedLower q.1 q.2..shiftedUpper q.1 q.2,
          f (q.1, q.2, z) := by
  classical
  have hs : MeasurableSet shiftedSolid := shiftedSolid_closed.measurableSet
  have hi : Integrable (shiftedSolid.indicator f) volume := by
    rw [integrable_indicator_iff hs]
    exact hf.continuousOn.integrableOn_compact shiftedSolid_compact
  let e :=
    (MeasurableEquiv.prodAssoc :
      ((ℝ × ℝ) × ℝ) ≃ᵐ (ℝ × (ℝ × ℝ)))
  have hi' : Integrable
      (fun q : (ℝ × ℝ) × ℝ => shiftedSolid.indicator f (e q)) := by
    simpa only [Function.comp_apply] using
      (volume_preserving_prodAssoc.integrable_comp_emb
        e.measurableEmbedding).2 hi
  have hreassoc :
      (∫ q : (ℝ × ℝ) × ℝ, shiftedSolid.indicator f (e q)) =
        ∫ p : Point3, shiftedSolid.indicator f p :=
    volume_preserving_prodAssoc.integral_comp' (shiftedSolid.indicator f)
  have hfubini :
      (∫ q : (ℝ × ℝ) × ℝ, shiftedSolid.indicator f (e q)) =
        ∫ q : ℝ × ℝ, ∫ z : ℝ,
          shiftedSolid.indicator f (q.1, q.2, z) := by
    simpa [e] using
      (MeasureTheory.integral_prod
        (fun q : (ℝ × ℝ) × ℝ => shiftedSolid.indicator f (e q)) hi')
  have hsection (q : ℝ × ℝ) :
      (∫ z : ℝ, shiftedSolid.indicator f (q.1, q.2, z)) =
        baseDisk.indicator
          (fun q =>
            ∫ z in shiftedLower q.1 q.2..shiftedUpper q.1 q.2,
              f (q.1, q.2, z)) q := by
    by_cases hq : q ∈ baseDisk
    · rw [Set.indicator_of_mem hq]
      have horder :
          shiftedLower q.1 q.2 ≤ shiftedUpper q.1 q.2 := by
        change q.1 ^ 2 + q.2 ^ 2 ≤ 2 at hq
        unfold shiftedLower shiftedUpper
        linarith
      have hmem (z : ℝ) :
          (q.1, q.2, z) ∈ shiftedSolid ↔
            z ∈ Set.Icc (shiftedLower q.1 q.2) (shiftedUpper q.1 q.2) := by
        change
          (q.1 ^ 2 + q.2 ^ 2 ≤ 2 ∧
            shiftedLower q.1 q.2 ≤ z ∧
              z ≤ shiftedUpper q.1 q.2) ↔
            shiftedLower q.1 q.2 ≤ z ∧ z ≤ shiftedUpper q.1 q.2
        tauto
      calc
        (∫ z : ℝ, shiftedSolid.indicator f (q.1, q.2, z)) =
            ∫ z in Set.Icc (shiftedLower q.1 q.2)
                (shiftedUpper q.1 q.2),
              f (q.1, q.2, z) := by
          rw [← MeasureTheory.integral_indicator measurableSet_Icc]
          apply integral_congr_ae
          filter_upwards with z
          by_cases hz :
              z ∈ Set.Icc (shiftedLower q.1 q.2) (shiftedUpper q.1 q.2)
          · have hp := (hmem z).2 hz
            simp [Set.indicator, hz, hp]
          · have hp : (q.1, q.2, z) ∉ shiftedSolid := by
              intro hp
              exact hz ((hmem z).1 hp)
            simp [Set.indicator, hz, hp]
        _ = ∫ z in shiftedLower q.1 q.2..shiftedUpper q.1 q.2,
              f (q.1, q.2, z) := by
          rw [intervalIntegral.integral_of_le horder]
          rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    · rw [Set.indicator_of_notMem hq, ← integral_zero]
      apply integral_congr_ae
      filter_upwards with z
      have hp : (q.1, q.2, z) ∉ shiftedSolid := by
        intro hp
        exact hq hp.1
      simp [Set.indicator, hp]
  calc
    (∫ p in shiftedSolid, f p) =
        ∫ p : Point3, shiftedSolid.indicator f p := by
      rw [MeasureTheory.integral_indicator hs]
    _ = ∫ q : (ℝ × ℝ) × ℝ, shiftedSolid.indicator f (e q) :=
      hreassoc.symm
    _ = ∫ q : ℝ × ℝ, ∫ z : ℝ,
          shiftedSolid.indicator f (q.1, q.2, z) := hfubini
    _ = ∫ q : ℝ × ℝ,
          baseDisk.indicator
            (fun q =>
              ∫ z in shiftedLower q.1 q.2..shiftedUpper q.1 q.2,
                f (q.1, q.2, z)) q := by
      apply integral_congr_ae
      filter_upwards with q
      exact hsection q
    _ = ∫ q in baseDisk,
          ∫ z in shiftedLower q.1 q.2..shiftedUpper q.1 q.2,
            f (q.1, q.2, z) := by
      rw [MeasureTheory.integral_indicator baseDisk_closed.measurableSet]

private def diskRadius : ℝ := Real.sqrt 2

private theorem diskRadius_pos : 0 < diskRadius := by
  exact Real.sqrt_pos.2 (by norm_num)

private theorem diskRadius_sq : diskRadius ^ 2 = 2 := by
  exact Real.sq_sqrt (by norm_num)

private theorem angular_full :
    (∫ θ in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ)) =
      2 * Real.pi := by
  calc
    _ = ∫ θ in Set.Ioc (-Real.pi) Real.pi, (1 : ℝ) :=
      (integral_Ioc_eq_integral_Ioo
        (f := fun _ : ℝ => (1 : ℝ))).symm
    _ = ∫ θ in -Real.pi..Real.pi, (1 : ℝ) := by
      rw [intervalIntegral.integral_of_le]
      exact neg_le_self Real.pi_nonneg
    _ = 2 * Real.pi := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      ring

private theorem radial_polar_pointwise
    (F : ℝ → ℝ) (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
    p.1 • baseDisk.indicator
        (fun q : ℝ × ℝ =>
          F (Real.sqrt (q.1 ^ 2 + q.2 ^ 2)))
        (polarCoord.symm p) =
      (Set.Iic diskRadius).indicator (fun r => r * F r) p.1 *
        (1 : ℝ) := by
  rcases p with ⟨r, θ⟩
  have hr : 0 < r := hp.1
  have hR : 0 < diskRadius := diskRadius_pos
  have htrig :
      (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    calc
      _ = r ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
      _ = r ^ 2 := by rw [Real.cos_sq_add_sin_sq]; ring
  have hmem :
      polarCoord.symm (r, θ) ∈ baseDisk ↔ r ≤ diskRadius := by
    rw [polarCoord_symm_apply]
    simp only [baseDisk, Set.mem_setOf_eq, htrig, ← diskRadius_sq]
    exact sq_le_sq₀ hr.le hR.le
  simp only [Set.indicator, hmem, Set.mem_Iic, smul_eq_mul]
  by_cases h : r ≤ diskRadius
  · simp only [h, if_true]
    rw [polarCoord_symm_apply, htrig, Real.sqrt_sq_eq_abs,
      abs_of_pos hr]
    ring
  · simp [h]

private theorem radial_set_to_interval (F : ℝ → ℝ) :
    (∫ r in Set.Ioi (0 : ℝ),
        (Set.Iic diskRadius).indicator (fun r => r * F r) r) =
      ∫ r in (0 : ℝ)..diskRadius, r * F r := by
  rw [setIntegral_indicator measurableSet_Iic]
  have hinter :
      Set.Ioi (0 : ℝ) ∩ Set.Iic diskRadius =
        Set.Ioc (0 : ℝ) diskRadius := by
    ext r
    simp
  rw [hinter, intervalIntegral.integral_of_le diskRadius_pos.le]

private theorem radial_disk_integral (F : ℝ → ℝ) :
    (∫ q in baseDisk,
        F (Real.sqrt (q.1 ^ 2 + q.2 ^ 2))) =
      2 * Real.pi *
        ∫ r in (0 : ℝ)..diskRadius, r * F r := by
  have hp := integral_comp_polarCoord_symm
    (baseDisk.indicator
      (fun q : ℝ × ℝ =>
        F (Real.sqrt (q.1 ^ 2 + q.2 ^ 2))))
  rw [integral_indicator baseDisk_closed.measurableSet] at hp
  have hprod :
      (∫ p in polarCoord.target,
          p.1 • baseDisk.indicator
            (fun q : ℝ × ℝ =>
              F (Real.sqrt (q.1 ^ 2 + q.2 ^ 2)))
            (polarCoord.symm p)) =
        (∫ r in Set.Ioi (0 : ℝ),
            (Set.Iic diskRadius).indicator (fun r => r * F r) r) *
          ∫ θ in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
    rw [polarCoord_target]
    calc
      _ = ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          (Set.Iic diskRadius).indicator
              (fun r => r * F r) p.1 * (1 : ℝ) := by
        apply setIntegral_congr_fun
          (measurableSet_Ioi.prod measurableSet_Ioo)
        intro p hp'
        exact radial_polar_pointwise F p hp'
      _ = _ := by
        exact setIntegral_prod_mul
          (fun r : ℝ =>
            (Set.Iic diskRadius).indicator (fun r => r * F r) r)
          (fun _ : ℝ => (1 : ℝ))
          (Set.Ioi (0 : ℝ)) (Set.Ioo (-Real.pi) Real.pi)
  rw [hprod, radial_set_to_interval, angular_full] at hp
  rw [← hp]
  ring

private def negX : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  MeasurableEquiv.prodCongr
    (MeasurableEquiv.neg ℝ)
    (MeasurableEquiv.refl ℝ)

private def negY : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  MeasurableEquiv.prodCongr
    (MeasurableEquiv.refl ℝ)
    (MeasurableEquiv.neg ℝ)

@[simp] private theorem negX_apply (q : ℝ × ℝ) :
    negX q = (-q.1, q.2) := rfl

@[simp] private theorem negY_apply (q : ℝ × ℝ) :
    negY q = (q.1, -q.2) := rfl

private theorem real_neg_measurePreserving :
    MeasurePreserving (fun x : ℝ => -x) volume volume := by
  exact
    ⟨measurable_neg, Measure.map_neg_eq_self (volume : Measure ℝ)⟩

private theorem negX_measurePreserving :
    MeasurePreserving negX volume volume := by
  exact
    real_neg_measurePreserving.prod
      (MeasurePreserving.id (volume : Measure ℝ))

private theorem negY_measurePreserving :
    MeasurePreserving negY volume volume := by
  exact
    (MeasurePreserving.id (volume : Measure ℝ)).prod
      real_neg_measurePreserving

private theorem negX_preimage_baseDisk :
    negX ⁻¹' baseDisk = baseDisk := by
  ext q
  simp only [Set.mem_preimage, baseDisk, Set.mem_setOf_eq]
  rw [negX_apply]
  change (-q.1) ^ 2 + q.2 ^ 2 ≤ 2 ↔ q.1 ^ 2 + q.2 ^ 2 ≤ 2
  ring_nf

private theorem negY_preimage_baseDisk :
    negY ⁻¹' baseDisk = baseDisk := by
  ext q
  simp only [Set.mem_preimage, baseDisk, Set.mem_setOf_eq]
  rw [negY_apply]
  change q.1 ^ 2 + (-q.2) ^ 2 ≤ 2 ↔ q.1 ^ 2 + q.2 ^ 2 ≤ 2
  ring_nf

private theorem baseDisk_x_odd (F : ℝ → ℝ) :
    (∫ q in baseDisk,
        q.1 * F (Real.sqrt (q.1 ^ 2 + q.2 ^ 2))) = 0 := by
  have h := negX_measurePreserving.setIntegral_preimage_emb
    negX.measurableEmbedding
    (fun q : ℝ × ℝ =>
      q.1 * F (Real.sqrt (q.1 ^ 2 + q.2 ^ 2))) baseDisk
  rw [negX_preimage_baseDisk] at h
  have hneg :
      (∫ q in baseDisk,
          -(q.1 * F (Real.sqrt (q.1 ^ 2 + q.2 ^ 2)))) =
        ∫ q in baseDisk,
          q.1 * F (Real.sqrt (q.1 ^ 2 + q.2 ^ 2)) := by
    simpa only [negX_apply, Prod.fst, Prod.snd, neg_sq,
      neg_mul, neg_neg] using h
  rw [MeasureTheory.integral_neg] at hneg
  linarith

private theorem baseDisk_y_odd (F : ℝ → ℝ) :
    (∫ q in baseDisk,
        q.2 * F (Real.sqrt (q.1 ^ 2 + q.2 ^ 2))) = 0 := by
  have h := negY_measurePreserving.setIntegral_preimage_emb
    negY.measurableEmbedding
    (fun q : ℝ × ℝ =>
      q.2 * F (Real.sqrt (q.1 ^ 2 + q.2 ^ 2))) baseDisk
  rw [negY_preimage_baseDisk] at h
  have hneg :
      (∫ q in baseDisk,
          -(q.2 * F (Real.sqrt (q.1 ^ 2 + q.2 ^ 2)))) =
        ∫ q in baseDisk,
          q.2 * F (Real.sqrt (q.1 ^ 2 + q.2 ^ 2)) := by
    simpa only [negY_apply, Prod.fst, Prod.snd, neg_sq,
      neg_mul, neg_neg] using h
  rw [MeasureTheory.integral_neg] at hneg
  linarith

private theorem intervalIntegral_eq_sub_of_hasDerivAt
    {f F : ℝ → ℝ} (hF : ∀ x, HasDerivAt F (f x) x)
    (hf : Continuous f) (l u : ℝ) :
    intervalIntegral f l u volume = F u - F l := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _hx => hF x) (hf.intervalIntegrable (μ := volume) l u)

private def radialWeight (r : ℝ) : ℝ :=
  1 - r ^ 2 / 2

private theorem radialWeight_integral :
    (∫ r in (0 : ℝ)..diskRadius, r * radialWeight r) = 1 / 2 := by
  let F := fun r : ℝ => r ^ 2 / 2 - r ^ 4 / 8
  have hF (r : ℝ) :
      HasDerivAt F (r * radialWeight r) r := by
    dsimp only [F, radialWeight]
    convert
      (((hasDerivAt_id r).pow 2).const_mul (1 / 2)).sub
        (((hasDerivAt_id r).pow 4).const_mul (1 / 8))
      using 1 <;> norm_num <;> try ring
    exact funext (fun x => by
      simp [sub_eq_add_neg, div_eq_mul_inv, add_assoc])
  have hcont : Continuous (fun r : ℝ => r * radialWeight r) := by
    unfold radialWeight
    fun_prop
  rw [intervalIntegral_eq_sub_of_hasDerivAt hF hcont]
  dsimp only [F]
  rw [show diskRadius ^ 4 = (diskRadius ^ 2) ^ 2 by ring,
    diskRadius_sq]
  norm_num

private theorem base_weight_value :
    (∫ q in baseDisk,
        1 - (q.1 ^ 2 + q.2 ^ 2) / 2) = Real.pi := by
  calc
    _ = ∫ q in baseDisk,
          radialWeight (Real.sqrt (q.1 ^ 2 + q.2 ^ 2)) := by
      apply MeasureTheory.setIntegral_congr_fun
        baseDisk_closed.measurableSet
      intro q hq
      have hnonneg : 0 ≤ q.1 ^ 2 + q.2 ^ 2 :=
        add_nonneg (sq_nonneg _) (sq_nonneg _)
      simp only [radialWeight, Real.sq_sqrt hnonneg]
    _ = 2 * Real.pi *
          ∫ r in (0 : ℝ)..diskRadius, r * radialWeight r :=
      radial_disk_integral radialWeight
    _ = Real.pi := by rw [radialWeight_integral]; ring

private def radialZEven (r : ℝ) : ℝ :=
  radialWeight r / 2 * (3 + r ^ 2 / 2)

private theorem radialZEven_integral :
    (∫ r in (0 : ℝ)..diskRadius, r * radialZEven r) = 5 / 6 := by
  let F := fun r : ℝ =>
    3 * r ^ 2 / 4 - r ^ 4 / 8 - r ^ 6 / 48
  have hF (r : ℝ) :
      HasDerivAt F (r * radialZEven r) r := by
    dsimp only [F, radialZEven, radialWeight]
    convert
      ((((hasDerivAt_id r).pow 2).const_mul (3 / 4)).sub
        (((hasDerivAt_id r).pow 4).const_mul (1 / 8))).sub
        (((hasDerivAt_id r).pow 6).const_mul (1 / 48))
      using 1 <;> norm_num <;> try ring
    exact funext (fun x => by
      simp [sub_eq_add_neg, div_eq_mul_inv, add_assoc])
  have hcont : Continuous (fun r : ℝ => r * radialZEven r) := by
    unfold radialZEven radialWeight
    fun_prop
  rw [intervalIntegral_eq_sub_of_hasDerivAt hF hcont]
  dsimp only [F]
  rw [show diskRadius ^ 4 = (diskRadius ^ 2) ^ 2 by ring,
    show diskRadius ^ 6 = (diskRadius ^ 2) ^ 3 by ring,
    diskRadius_sq]
  norm_num

private theorem base_zEven_value :
    (∫ q in baseDisk,
        (1 - (q.1 ^ 2 + q.2 ^ 2) / 2) / 2 *
          (3 + (q.1 ^ 2 + q.2 ^ 2) / 2)) =
      5 * Real.pi / 3 := by
  calc
    _ = ∫ q in baseDisk,
          radialZEven (Real.sqrt (q.1 ^ 2 + q.2 ^ 2)) := by
      apply MeasureTheory.setIntegral_congr_fun
        baseDisk_closed.measurableSet
      intro q hq
      have hnonneg : 0 ≤ q.1 ^ 2 + q.2 ^ 2 :=
        add_nonneg (sq_nonneg _) (sq_nonneg _)
      simp only [radialZEven, radialWeight, Real.sq_sqrt hnonneg]
    _ = 2 * Real.pi *
          ∫ r in (0 : ℝ)..diskRadius, r * radialZEven r :=
      radial_disk_integral radialZEven
    _ = 5 * Real.pi / 3 := by
      rw [radialZEven_integral]
      ring

private theorem base_xWeight_odd :
    (∫ q in baseDisk,
        q.1 * (1 - (q.1 ^ 2 + q.2 ^ 2) / 2)) = 0 := by
  calc
    _ = ∫ q in baseDisk,
          q.1 * radialWeight
            (Real.sqrt (q.1 ^ 2 + q.2 ^ 2)) := by
      apply MeasureTheory.setIntegral_congr_fun
        baseDisk_closed.measurableSet
      intro q hq
      have hnonneg : 0 ≤ q.1 ^ 2 + q.2 ^ 2 :=
        add_nonneg (sq_nonneg _) (sq_nonneg _)
      simp only [radialWeight, Real.sq_sqrt hnonneg]
    _ = 0 := baseDisk_x_odd radialWeight

private theorem base_yWeight_odd :
    (∫ q in baseDisk,
        q.2 * (1 - (q.1 ^ 2 + q.2 ^ 2) / 2)) = 0 := by
  calc
    _ = ∫ q in baseDisk,
          q.2 * radialWeight
            (Real.sqrt (q.1 ^ 2 + q.2 ^ 2)) := by
      apply MeasureTheory.setIntegral_congr_fun
        baseDisk_closed.measurableSet
      intro q hq
      have hnonneg : 0 ≤ q.1 ^ 2 + q.2 ^ 2 :=
        add_nonneg (sq_nonneg _) (sq_nonneg _)
      simp only [radialWeight, Real.sq_sqrt hnonneg]
    _ = 0 := baseDisk_y_odd radialWeight

private theorem base_xMoment_value :
    (∫ q in baseDisk,
        (1 + q.1) * (1 - (q.1 ^ 2 + q.2 ^ 2) / 2)) =
      Real.pi := by
  have hw : IntegrableOn
      (fun q : ℝ × ℝ => 1 - (q.1 ^ 2 + q.2 ^ 2) / 2)
      baseDisk volume :=
    (by fun_prop : Continuous
      (fun q : ℝ × ℝ => 1 - (q.1 ^ 2 + q.2 ^ 2) / 2)).continuousOn
      |>.integrableOn_compact baseDisk_compact
  have hodd : IntegrableOn
      (fun q : ℝ × ℝ =>
        q.1 * (1 - (q.1 ^ 2 + q.2 ^ 2) / 2))
      baseDisk volume :=
    (by fun_prop : Continuous
      (fun q : ℝ × ℝ =>
        q.1 * (1 - (q.1 ^ 2 + q.2 ^ 2) / 2))).continuousOn
      |>.integrableOn_compact baseDisk_compact
  calc
    _ = ∫ q in baseDisk,
          (1 - (q.1 ^ 2 + q.2 ^ 2) / 2) +
            q.1 * (1 - (q.1 ^ 2 + q.2 ^ 2) / 2) := by
      apply MeasureTheory.setIntegral_congr_fun
        baseDisk_closed.measurableSet
      intro q hq
      ring
    _ = (∫ q in baseDisk, 1 - (q.1 ^ 2 + q.2 ^ 2) / 2) +
          ∫ q in baseDisk,
            q.1 * (1 - (q.1 ^ 2 + q.2 ^ 2) / 2) := by
      rw [MeasureTheory.integral_add hw hodd]
    _ = Real.pi := by rw [base_weight_value, base_xWeight_odd]; ring

private theorem base_yMoment_value :
    (∫ q in baseDisk,
        (1 + q.2) * (1 - (q.1 ^ 2 + q.2 ^ 2) / 2)) =
      Real.pi := by
  have hw : IntegrableOn
      (fun q : ℝ × ℝ => 1 - (q.1 ^ 2 + q.2 ^ 2) / 2)
      baseDisk volume :=
    (by fun_prop : Continuous
      (fun q : ℝ × ℝ => 1 - (q.1 ^ 2 + q.2 ^ 2) / 2)).continuousOn
      |>.integrableOn_compact baseDisk_compact
  have hodd : IntegrableOn
      (fun q : ℝ × ℝ =>
        q.2 * (1 - (q.1 ^ 2 + q.2 ^ 2) / 2))
      baseDisk volume :=
    (by fun_prop : Continuous
      (fun q : ℝ × ℝ =>
        q.2 * (1 - (q.1 ^ 2 + q.2 ^ 2) / 2))).continuousOn
      |>.integrableOn_compact baseDisk_compact
  calc
    _ = ∫ q in baseDisk,
          (1 - (q.1 ^ 2 + q.2 ^ 2) / 2) +
            q.2 * (1 - (q.1 ^ 2 + q.2 ^ 2) / 2) := by
      apply MeasureTheory.setIntegral_congr_fun
        baseDisk_closed.measurableSet
      intro q hq
      ring
    _ = (∫ q in baseDisk, 1 - (q.1 ^ 2 + q.2 ^ 2) / 2) +
          ∫ q in baseDisk,
            q.2 * (1 - (q.1 ^ 2 + q.2 ^ 2) / 2) := by
      rw [MeasureTheory.integral_add hw hodd]
    _ = Real.pi := by rw [base_weight_value, base_yWeight_odd]; ring

private theorem shifted_z_inner (q : ℝ × ℝ) :
    (∫ z in shiftedLower q.1 q.2..shiftedUpper q.1 q.2, z) =
      (1 - (q.1 ^ 2 + q.2 ^ 2) / 2) / 2 *
          (3 + (q.1 ^ 2 + q.2 ^ 2) / 2) -
        q.1 * (1 - (q.1 ^ 2 + q.2 ^ 2) / 2) -
        q.2 * (1 - (q.1 ^ 2 + q.2 ^ 2) / 2) := by
  rw [integral_id]
  unfold shiftedLower shiftedUpper
  ring

private theorem base_zMoment_value :
    (∫ q in baseDisk,
        ∫ z in shiftedLower q.1 q.2..shiftedUpper q.1 q.2, z) =
      5 * Real.pi / 3 := by
  let evenPart := fun q : ℝ × ℝ =>
    (1 - (q.1 ^ 2 + q.2 ^ 2) / 2) / 2 *
      (3 + (q.1 ^ 2 + q.2 ^ 2) / 2)
  let xPart := fun q : ℝ × ℝ =>
    q.1 * (1 - (q.1 ^ 2 + q.2 ^ 2) / 2)
  let yPart := fun q : ℝ × ℝ =>
    q.2 * (1 - (q.1 ^ 2 + q.2 ^ 2) / 2)
  have heven : IntegrableOn evenPart baseDisk volume :=
    (by
      dsimp only [evenPart]
      fun_prop : Continuous evenPart).continuousOn
      |>.integrableOn_compact baseDisk_compact
  have hx : IntegrableOn xPart baseDisk volume :=
    (by
      dsimp only [xPart]
      fun_prop : Continuous xPart).continuousOn
      |>.integrableOn_compact baseDisk_compact
  have hy : IntegrableOn yPart baseDisk volume :=
    (by
      dsimp only [yPart]
      fun_prop : Continuous yPart).continuousOn
      |>.integrableOn_compact baseDisk_compact
  calc
    _ = ∫ q in baseDisk, evenPart q - xPart q - yPart q := by
      apply MeasureTheory.setIntegral_congr_fun
        baseDisk_closed.measurableSet
      intro q hq
      exact shifted_z_inner q
    _ = (∫ q in baseDisk, evenPart q) -
          (∫ q in baseDisk, xPart q) -
          (∫ q in baseDisk, yPart q) := by
      rw [MeasureTheory.integral_sub
        (f := fun q => evenPart q - xPart q) (g := yPart)
        (heven.sub hx) hy,
        MeasureTheory.integral_sub
          (f := evenPart) (g := xPart) heven hx]
    _ = 5 * Real.pi / 3 := by
      dsimp only [evenPart, xPart, yPart]
      rw [base_zEven_value, base_xWeight_odd, base_yWeight_odd]
      ring

private theorem mass_value : mass = Real.pi := by
  unfold mass
  rw [shifted_change_of_variables]
  change (∫ q in shiftedSolid, (1 : ℝ)) = Real.pi
  rw [shifted_integral_as_base
    (fun _q : Point3 => (1 : ℝ)) continuous_const]
  calc
    (∫ q in baseDisk,
        ∫ z in shiftedLower q.1 q.2..shiftedUpper q.1 q.2,
          (1 : ℝ)) =
        ∫ q in baseDisk, 1 - (q.1 ^ 2 + q.2 ^ 2) / 2 := by
      apply MeasureTheory.setIntegral_congr_fun
        baseDisk_closed.measurableSet
      intro q hq
      change
        (∫ z in shiftedLower q.1 q.2..shiftedUpper q.1 q.2,
          (1 : ℝ)) =
          1 - (q.1 ^ 2 + q.2 ^ 2) / 2
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      unfold shiftedLower shiftedUpper
      ring
    _ = Real.pi := base_weight_value

private theorem xMoment_value :
    (∫ p in solid, p.1) = Real.pi := by
  rw [shifted_change_of_variables]
  change (∫ q in shiftedSolid, q.1 + 1) = Real.pi
  rw [shifted_integral_as_base
    (fun q : Point3 => q.1 + 1) (by fun_prop)]
  calc
    (∫ q in baseDisk,
        ∫ z in shiftedLower q.1 q.2..shiftedUpper q.1 q.2,
          q.1 + 1) =
        ∫ q in baseDisk,
          (1 + q.1) * (1 - (q.1 ^ 2 + q.2 ^ 2) / 2) := by
      apply MeasureTheory.setIntegral_congr_fun
        baseDisk_closed.measurableSet
      intro q hq
      change
        (∫ z in shiftedLower q.1 q.2..shiftedUpper q.1 q.2,
          q.1 + 1) =
          (1 + q.1) * (1 - (q.1 ^ 2 + q.2 ^ 2) / 2)
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      unfold shiftedLower shiftedUpper
      ring
    _ = Real.pi := base_xMoment_value

private theorem yMoment_value :
    (∫ p in solid, p.2.1) = Real.pi := by
  rw [shifted_change_of_variables]
  change (∫ q in shiftedSolid, q.2.1 + 1) = Real.pi
  rw [shifted_integral_as_base
    (fun q : Point3 => q.2.1 + 1) (by fun_prop)]
  calc
    (∫ q in baseDisk,
        ∫ z in shiftedLower q.1 q.2..shiftedUpper q.1 q.2,
          q.2 + 1) =
        ∫ q in baseDisk,
          (1 + q.2) * (1 - (q.1 ^ 2 + q.2 ^ 2) / 2) := by
      apply MeasureTheory.setIntegral_congr_fun
        baseDisk_closed.measurableSet
      intro q hq
      change
        (∫ z in shiftedLower q.1 q.2..shiftedUpper q.1 q.2,
          q.2 + 1) =
          (1 + q.2) * (1 - (q.1 ^ 2 + q.2 ^ 2) / 2)
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      unfold shiftedLower shiftedUpper
      ring
    _ = Real.pi := base_yMoment_value

private theorem zMoment_value :
    (∫ p in solid, p.2.2) = 5 * Real.pi / 3 := by
  rw [shifted_change_of_variables]
  change (∫ q in shiftedSolid, q.2.2) = 5 * Real.pi / 3
  rw [shifted_integral_as_base
    (fun q : Point3 => q.2.2) (by fun_prop)]
  exact base_zMoment_value

private theorem xCentroid_value : xCentroid = 1 := by
  unfold xCentroid
  rw [mass_value, xMoment_value]
  field_simp [Real.pi_ne_zero]

private theorem yCentroid_value : yCentroid = 1 := by
  unfold yCentroid
  rw [mass_value, yMoment_value]
  field_simp [Real.pi_ne_zero]

private theorem zCentroid_value : zCentroid = (5 : ℝ) / 3 := by
  unfold zCentroid
  rw [mass_value, zMoment_value]
  field_simp [Real.pi_ne_zero]
  <;> ring

private def polarLower (θ r : ℝ) : ℝ :=
  1 - r * (Real.cos θ + Real.sin θ) + r ^ 2 / 2

private def polarUpper (θ r : ℝ) : ℝ :=
  2 - r * (Real.cos θ + Real.sin θ)

private theorem angular_cos_zero :
    (∫ θ in (0 : ℝ)..2 * Real.pi, Real.cos θ) = 0 := by
  rw [integral_cos]
  simp

private theorem angular_sin_zero :
    (∫ θ in (0 : ℝ)..2 * Real.pi, Real.sin θ) = 0 := by
  rw [integral_sin]
  simp

private theorem polar_mass_inner (θ r : ℝ) :
    (∫ z in polarLower θ r..polarUpper θ r, r) =
      r * radialWeight r := by
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  unfold polarLower polarUpper radialWeight
  ring

private theorem polar_mass_value :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..diskRadius,
          ∫ z in polarLower θ r..polarUpper θ r, r) =
      Real.pi := by
  simp_rw [polar_mass_inner, radialWeight_integral]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

private def radialOdd : ℝ :=
  ∫ r in (0 : ℝ)..diskRadius, r ^ 2 * radialWeight r

private theorem polar_x_inner (θ r : ℝ) :
    (∫ z in polarLower θ r..polarUpper θ r,
        (1 + r * Real.cos θ) * r) =
      (1 + r * Real.cos θ) * r * radialWeight r := by
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  unfold polarLower polarUpper radialWeight
  ring

private theorem polar_x_radial (θ : ℝ) :
    (∫ r in (0 : ℝ)..diskRadius,
        (1 + r * Real.cos θ) * r * radialWeight r) =
      1 / 2 + Real.cos θ * radialOdd := by
  have hbase : IntervalIntegrable
      (fun r : ℝ => r * radialWeight r) volume 0 diskRadius :=
    (by
      unfold radialWeight
      fun_prop : Continuous (fun r : ℝ => r * radialWeight r))
      |>.intervalIntegrable _ _
  have hodd : IntervalIntegrable
      (fun r : ℝ => Real.cos θ * (r ^ 2 * radialWeight r))
      volume 0 diskRadius :=
    (by
      unfold radialWeight
      fun_prop : Continuous
        (fun r : ℝ => Real.cos θ * (r ^ 2 * radialWeight r)))
      |>.intervalIntegrable _ _
  calc
    _ = ∫ r in (0 : ℝ)..diskRadius,
          r * radialWeight r +
            Real.cos θ * (r ^ 2 * radialWeight r) := by
      apply intervalIntegral.integral_congr
      intro r hr
      ring
    _ = (∫ r in (0 : ℝ)..diskRadius, r * radialWeight r) +
          ∫ r in (0 : ℝ)..diskRadius,
            Real.cos θ * (r ^ 2 * radialWeight r) := by
      rw [intervalIntegral.integral_add hbase hodd]
    _ = 1 / 2 + Real.cos θ * radialOdd := by
      rw [radialWeight_integral,
        intervalIntegral.integral_const_mul]
      rfl

private theorem polar_x_angular :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
        (1 / 2 + Real.cos θ * radialOdd)) =
      Real.pi := by
  have hconst : IntervalIntegrable
      (fun _θ : ℝ => (1 / 2 : ℝ)) volume 0 (2 * Real.pi) :=
    continuous_const.intervalIntegrable _ _
  have hcos : IntervalIntegrable
      (fun θ : ℝ => Real.cos θ * radialOdd)
      volume 0 (2 * Real.pi) :=
    (Real.continuous_cos.mul continuous_const).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hconst hcos]
  rw [show
    (fun θ : ℝ => Real.cos θ * radialOdd) =
      fun θ => radialOdd * Real.cos θ by
        funext θ
        ring]
  rw [intervalIntegral.integral_const_mul, angular_cos_zero,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

private theorem polar_x_value :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..diskRadius,
          ∫ z in polarLower θ r..polarUpper θ r,
            (1 + r * Real.cos θ) * r) =
      Real.pi := by
  simp_rw [polar_x_inner, polar_x_radial]
  exact polar_x_angular

private theorem polar_z_inner (θ r : ℝ) :
    (∫ z in polarLower θ r..polarUpper θ r, z * r) =
      r * radialZEven r -
        (Real.cos θ + Real.sin θ) * (r ^ 2 * radialWeight r) := by
  rw [show (fun z : ℝ => z * r) = fun z => r * z by
    funext z
    ring]
  rw [intervalIntegral.integral_const_mul, integral_id]
  unfold polarLower polarUpper radialZEven radialWeight
  ring

private theorem polar_z_radial (θ : ℝ) :
    (∫ r in (0 : ℝ)..diskRadius,
        r * radialZEven r -
          (Real.cos θ + Real.sin θ) * (r ^ 2 * radialWeight r)) =
      5 / 6 - (Real.cos θ + Real.sin θ) * radialOdd := by
  have heven : IntervalIntegrable
      (fun r : ℝ => r * radialZEven r) volume 0 diskRadius :=
    (by
      unfold radialZEven radialWeight
      fun_prop : Continuous (fun r : ℝ => r * radialZEven r))
      |>.intervalIntegrable _ _
  have hodd : IntervalIntegrable
      (fun r : ℝ =>
        (Real.cos θ + Real.sin θ) * (r ^ 2 * radialWeight r))
      volume 0 diskRadius :=
    (by
      unfold radialWeight
      fun_prop : Continuous
        (fun r : ℝ =>
          (Real.cos θ + Real.sin θ) * (r ^ 2 * radialWeight r)))
      |>.intervalIntegrable _ _
  rw [intervalIntegral.integral_sub heven hodd,
    radialZEven_integral, intervalIntegral.integral_const_mul]
  rfl

private theorem polar_z_angular :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
        (5 / 6 - (Real.cos θ + Real.sin θ) * radialOdd)) =
      5 * Real.pi / 3 := by
  have hconst : IntervalIntegrable
      (fun _θ : ℝ => (5 / 6 : ℝ)) volume 0 (2 * Real.pi) :=
    continuous_const.intervalIntegrable _ _
  have htrig : IntervalIntegrable
      (fun θ : ℝ =>
        (Real.cos θ + Real.sin θ) * radialOdd)
      volume 0 (2 * Real.pi) :=
    ((Real.continuous_cos.add Real.continuous_sin).mul continuous_const)
      |>.intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hconst htrig]
  rw [show
    (fun θ : ℝ => (Real.cos θ + Real.sin θ) * radialOdd) =
      fun θ => radialOdd * Real.cos θ + radialOdd * Real.sin θ by
        funext θ
        ring]
  have hcos : IntervalIntegrable
      (fun θ : ℝ => radialOdd * Real.cos θ)
      volume 0 (2 * Real.pi) :=
    (continuous_const.mul Real.continuous_cos).intervalIntegrable _ _
  have hsin : IntervalIntegrable
      (fun θ : ℝ => radialOdd * Real.sin θ)
      volume 0 (2 * Real.pi) :=
    (continuous_const.mul Real.continuous_sin).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hcos hsin,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    angular_cos_zero, angular_sin_zero,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

private theorem polar_z_value :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..diskRadius,
          ∫ z in polarLower θ r..polarUpper θ r, z * r) =
      5 * Real.pi / 3 := by
  simp_rw [polar_z_inner, polar_z_radial]
  exact polar_z_angular

theorem gap1 :
    mass =
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..Real.sqrt 2,
          ∫ z in
              1 - r * (Real.cos θ + Real.sin θ) + r ^ 2 / 2..
              2 - r * (Real.cos θ + Real.sin θ),
            r := by
  calc
    mass = Real.pi := mass_value
    _ = ∫ θ in (0 : ℝ)..2 * Real.pi,
          ∫ r in (0 : ℝ)..Real.sqrt 2,
            ∫ z in
                1 - r * (Real.cos θ + Real.sin θ) + r ^ 2 / 2..
                2 - r * (Real.cos θ + Real.sin θ),
              r := by
      simpa only [diskRadius, polarLower, polarUpper] using
        polar_mass_value.symm

theorem gap2 :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..Real.sqrt 2,
          ∫ z in
              1 - r * (Real.cos θ + Real.sin θ) + r ^ 2 / 2..
              2 - r * (Real.cos θ + Real.sin θ),
            r) =
      2 * Real.pi *
        ∫ r in (0 : ℝ)..Real.sqrt 2, (1 - r ^ 2 / 2) * r := by
  have hleft :
      (∫ θ in (0 : ℝ)..2 * Real.pi,
          ∫ r in (0 : ℝ)..Real.sqrt 2,
            ∫ z in
                1 - r * (Real.cos θ + Real.sin θ) + r ^ 2 / 2..
                2 - r * (Real.cos θ + Real.sin θ),
              r) = Real.pi := by
    simpa only [diskRadius, polarLower, polarUpper] using
      polar_mass_value
  have hrad :
      (∫ r in (0 : ℝ)..Real.sqrt 2, (1 - r ^ 2 / 2) * r) =
        (1 / 2 : ℝ) := by
    rw [show
      (fun r : ℝ => (1 - r ^ 2 / 2) * r) =
        fun r => r * radialWeight r by
          funext r
          unfold radialWeight
          ring]
    simpa only [diskRadius] using radialWeight_integral
  rw [hleft, hrad]
  ring

theorem gap3 :
    2 * Real.pi *
        (∫ r in (0 : ℝ)..Real.sqrt 2, (1 - r ^ 2 / 2) * r) =
      Real.pi := by
  have hrad :
      (∫ r in (0 : ℝ)..Real.sqrt 2, (1 - r ^ 2 / 2) * r) =
        (1 / 2 : ℝ) := by
    rw [show
      (fun r : ℝ => (1 - r ^ 2 / 2) * r) =
        fun r => r * radialWeight r by
          funext r
          unfold radialWeight
          ring]
    simpa only [diskRadius] using radialWeight_integral
  rw [hrad]
  ring

theorem gap4 :
    mass = Real.pi := by
  exact mass_value

theorem gap5 :
    xCentroid =
      1 / mass *
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          ∫ r in (0 : ℝ)..Real.sqrt 2,
            ∫ z in
                1 - r * (Real.cos θ + Real.sin θ) + r ^ 2 / 2..
                2 - r * (Real.cos θ + Real.sin θ),
              (1 + r * Real.cos θ) * r := by
  have hp :
      (∫ θ in (0 : ℝ)..2 * Real.pi,
          ∫ r in (0 : ℝ)..Real.sqrt 2,
            ∫ z in
                1 - r * (Real.cos θ + Real.sin θ) + r ^ 2 / 2..
                2 - r * (Real.cos θ + Real.sin θ),
              (1 + r * Real.cos θ) * r) = Real.pi := by
    simpa only [diskRadius, polarLower, polarUpper] using polar_x_value
  rw [xCentroid_value, mass_value, hp]
  field_simp [Real.pi_ne_zero]

theorem gap6 :
    1 / mass *
        (∫ θ in (0 : ℝ)..2 * Real.pi,
          ∫ r in (0 : ℝ)..Real.sqrt 2,
            ∫ z in
                1 - r * (Real.cos θ + Real.sin θ) + r ^ 2 / 2..
                2 - r * (Real.cos θ + Real.sin θ),
              (1 + r * Real.cos θ) * r) =
      1 := by
  have hp :
      (∫ θ in (0 : ℝ)..2 * Real.pi,
          ∫ r in (0 : ℝ)..Real.sqrt 2,
            ∫ z in
                1 - r * (Real.cos θ + Real.sin θ) + r ^ 2 / 2..
                2 - r * (Real.cos θ + Real.sin θ),
              (1 + r * Real.cos θ) * r) = Real.pi := by
    simpa only [diskRadius, polarLower, polarUpper] using polar_x_value
  rw [mass_value, hp]
  field_simp [Real.pi_ne_zero]

theorem gap7 :
    xCentroid = 1 := by
  exact xCentroid_value

theorem gap8 :
    yCentroid = 1 := by
  exact yCentroid_value

theorem gap9 :
    zCentroid =
      1 / mass *
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          ∫ r in (0 : ℝ)..Real.sqrt 2,
            ∫ z in
                1 - r * (Real.cos θ + Real.sin θ) + r ^ 2 / 2..
                2 - r * (Real.cos θ + Real.sin θ),
              z * r := by
  have hp :
      (∫ θ in (0 : ℝ)..2 * Real.pi,
          ∫ r in (0 : ℝ)..Real.sqrt 2,
            ∫ z in
                1 - r * (Real.cos θ + Real.sin θ) + r ^ 2 / 2..
                2 - r * (Real.cos θ + Real.sin θ),
              z * r) = 5 * Real.pi / 3 := by
    simpa only [diskRadius, polarLower, polarUpper] using polar_z_value
  rw [zCentroid_value, mass_value, hp]
  field_simp [Real.pi_ne_zero]
  <;> ring

theorem gap10 :
    1 / mass *
        (∫ θ in (0 : ℝ)..2 * Real.pi,
          ∫ r in (0 : ℝ)..Real.sqrt 2,
            ∫ z in
                1 - r * (Real.cos θ + Real.sin θ) + r ^ 2 / 2..
                2 - r * (Real.cos θ + Real.sin θ),
              z * r) =
      1 / (2 * Real.pi) * (10 * Real.pi / 3) := by
  have hp :
      (∫ θ in (0 : ℝ)..2 * Real.pi,
          ∫ r in (0 : ℝ)..Real.sqrt 2,
            ∫ z in
                1 - r * (Real.cos θ + Real.sin θ) + r ^ 2 / 2..
                2 - r * (Real.cos θ + Real.sin θ),
              z * r) = 5 * Real.pi / 3 := by
    simpa only [diskRadius, polarLower, polarUpper] using polar_z_value
  rw [mass_value, hp]
  field_simp [Real.pi_ne_zero]
  <;> ring

theorem gap11 :
    1 / (2 * Real.pi) * (10 * Real.pi / 3) = (5 : ℝ) / 3 := by
  field_simp [Real.pi_ne_zero]
  <;> ring

theorem gap12 :
    zCentroid = (5 : ℝ) / 3 := by
  exact zCentroid_value

theorem gap13 :
    (xCentroid, yCentroid, zCentroid) =
      ((1 : ℝ), 1, (5 : ℝ) / 3) := by
  rw [xCentroid_value, yCentroid_value, zCentroid_value]

end

end ProofGap.Exercise4138
