import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FinCases

namespace ProofGap.Exercise4092

noncomputable section

open MeasureTheory
open scoped Interval

def correctedRegion (a b alpha beta h : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | a * p.2.1 ^ 2 ≤ p.2.2 ∧ p.2.2 ≤ b * p.2.1 ^ 2 ∧
    0 < p.2.1 ∧ alpha * p.1 ≤ p.2.2 ∧
    p.2.2 ≤ beta * p.1 ∧ p.2.2 ≤ h}

def parameterDomain (a b alpha beta h : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | a ≤ p.1 ∧ p.1 ≤ b ∧
    alpha ≤ p.2.1 ∧ p.2.1 ≤ beta ∧
    0 < p.2.2 ∧ p.2.2 ≤ h}

def inverseMap (u v w : ℝ) : ℝ × ℝ × ℝ :=
  (w / v, Real.sqrt (w / u), w)

def jacobianDet (u v w : ℝ) : ℝ :=
  -(w * Real.sqrt w / (2 * u * Real.sqrt u * v ^ 2))

def jacobianAbs (u v w : ℝ) : ℝ :=
  |jacobianDet u v w|

def xSquaredIntegral (a b alpha beta h : ℝ) : ℝ :=
  ∫ p in correctedRegion a b alpha beta h, p.1 ^ 2

theorem gap1 (u v w : ℝ) (hv : 0 < v) :
    (inverseMap u v w).1 = w / v := by
  rfl

theorem gap2 (u v w : ℝ) (hu : 0 < u) (hw : 0 ≤ w) :
    (inverseMap u v w).2.1 = Real.sqrt (w / u) := by
  rfl

theorem gap3 (u v w : ℝ) :
    (inverseMap u v w).2.2 = w := by
  rfl

theorem gap4 (a b alpha beta h : ℝ)
    (ha : 0 < a) (hab : a < b)
    (halpha : 0 < alpha) (halphabeta : alpha < beta)
    (hh : 0 < h) :
    (fun p => inverseMap p.1 p.2.1 p.2.2) ''
        parameterDomain a b alpha beta h =
      correctedRegion a b alpha beta h := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases q with ⟨u, v, w⟩
    change
      a ≤ u ∧ u ≤ b ∧ alpha ≤ v ∧ v ≤ beta ∧
        0 < w ∧ w ≤ h at hq
    rcases hq with ⟨hau, hub, hav, hvb, hw, hwh⟩
    have hu : 0 < u := lt_of_lt_of_le ha hau
    have hv : 0 < v := lt_of_lt_of_le halpha hav
    have hwu : 0 ≤ w / u := div_nonneg hw.le hu.le
    have hsqrt : Real.sqrt (w / u) ^ 2 = w / u :=
      Real.sq_sqrt hwu
    have hys : 0 < Real.sqrt (w / u) :=
      Real.sqrt_pos.2 (div_pos hw hu)
    change
      a * Real.sqrt (w / u) ^ 2 ≤ w ∧
        w ≤ b * Real.sqrt (w / u) ^ 2 ∧
        0 < Real.sqrt (w / u) ∧
        alpha * (w / v) ≤ w ∧
        w ≤ beta * (w / v) ∧ w ≤ h
    rw [hsqrt]
    constructor
    · calc
        a * (w / u) = (a * w) / u := by ring
        _ ≤ w := (div_le_iff₀ hu).2 (by nlinarith)
    constructor
    · calc
        w ≤ (b * w) / u := (le_div_iff₀ hu).2 (by nlinarith)
        _ = b * (w / u) := by ring
    refine ⟨hys, ?_, ?_, hwh⟩
    · calc
        alpha * (w / v) = (alpha * w) / v := by ring
        _ ≤ w := (div_le_iff₀ hv).2 (by nlinarith)
    · calc
        w ≤ (beta * w) / v := (le_div_iff₀ hv).2 (by nlinarith)
        _ = beta * (w / v) := by ring
  · intro hp
    rcases p with ⟨x, y, z⟩
    change
      a * y ^ 2 ≤ z ∧ z ≤ b * y ^ 2 ∧ 0 < y ∧
        alpha * x ≤ z ∧ z ≤ beta * x ∧ z ≤ h at hp
    rcases hp with ⟨hay, hby, hy, hax, hbx, hzh⟩
    have hy2 : 0 < y ^ 2 := sq_pos_of_pos hy
    have hz : 0 < z := lt_of_lt_of_le
      (mul_pos ha hy2) hay
    have hbeta : 0 < beta := lt_trans halpha halphabeta
    have hx : 0 < x := by
      exact (mul_pos_iff_of_pos_left hbeta).mp
        (lt_of_lt_of_le hz hbx)
    refine ⟨(z / y ^ 2, z / x, z), ?_, ?_⟩
    · change
        a ≤ z / y ^ 2 ∧ z / y ^ 2 ≤ b ∧
          alpha ≤ z / x ∧ z / x ≤ beta ∧
          0 < z ∧ z ≤ h
      refine ⟨(le_div_iff₀ hy2).2 ?_,
        (div_le_iff₀ hy2).2 ?_,
        (le_div_iff₀ hx).2 ?_,
        (div_le_iff₀ hx).2 ?_, hz, hzh⟩
      · simpa [mul_comm] using hay
      · simpa [mul_comm] using hby
      · simpa [mul_comm] using hax
      · simpa [mul_comm] using hbx
    · change
        inverseMap (z / y ^ 2) (z / x) z = (x, y, z)
      apply Prod.ext
      · simp only [inverseMap]
        field_simp [hz.ne', hx.ne']
      · apply Prod.ext
        · simp only [inverseMap]
          have hratio : z / (z / y ^ 2) = y ^ 2 := by
            field_simp [hz.ne', hy.ne']
          rw [hratio, Real.sqrt_sq_eq_abs, abs_of_pos hy]
        · rfl

theorem gap5 (u v w : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 ≤ w) :
    jacobianAbs u v w =
      w * Real.sqrt w / (2 * u * Real.sqrt u * v ^ 2) := by
  unfold jacobianAbs jacobianDet
  rw [abs_neg, abs_of_nonneg]
  exact div_nonneg
    (mul_nonneg hw (Real.sqrt_nonneg _))
    (by positivity)

private abbrev Point3 := ℝ × ℝ × ℝ

private def coordEquiv :
    Point3 ≃ₗ[ℝ] (Fin 3 → ℝ) :=
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

private def coordU : Point3 →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)

private def coordV : Point3 →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

private def coordW : Point3 →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
    (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

private def inverseMapDeriv (u v w : ℝ) :
    Point3 →L[ℝ] Point3 :=
  let k := 1 / (2 * Real.sqrt (w / u))
  let A : Matrix (Fin 3) (Fin 3) ℝ :=
    ![![0, -w / v ^ 2, 1 / v],
      ![-k * w / u ^ 2, 0, k / u],
      ![0, 0, 1] ]
  ((coordEquiv.symm : (Fin 3 → ℝ) →ₗ[ℝ] Point3) ∘ₗ
    Matrix.toLin' A ∘ₗ
      (coordEquiv : Point3 →ₗ[ℝ] (Fin 3 → ℝ))).toContinuousLinearMap

private theorem inverseMapDeriv_apply (u v w : ℝ) (p : Point3) :
    inverseMapDeriv u v w p =
      ((-w / v ^ 2) * p.2.1 + (1 / v) * p.2.2,
        (-(1 / (2 * Real.sqrt (w / u))) * w / u ^ 2) * p.1 +
          ((1 / (2 * Real.sqrt (w / u))) / u) * p.2.2,
        p.2.2) := by
  ext <;>
    simp [inverseMapDeriv, coordEquiv, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring

private theorem hasFDerivAt_inverseMap
    (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) :
    HasFDerivAt
      (fun p : Point3 => inverseMap p.1 p.2.1 p.2.2)
      (inverseMapDeriv u v w) (u, v, w) := by
  have huF :
      HasFDerivAt (fun p : Point3 => p.1) coordU (u, v, w) :=
    coordU.hasFDerivAt
  have hvF :
      HasFDerivAt (fun p : Point3 => p.2.1) coordV (u, v, w) :=
    coordV.hasFDerivAt
  have hwF :
      HasFDerivAt (fun p : Point3 => p.2.2) coordW (u, v, w) :=
    coordW.hasFDerivAt
  have hvInv := (hasFDerivAt_inv hv.ne').comp (u, v, w) hvF
  have hxRaw := hwF.mul hvInv
  have hx :
      HasFDerivAt (fun p : Point3 => p.2.2 / p.2.1)
        (v⁻¹ • coordW - (w / v ^ 2) • coordV) (u, v, w) := by
    convert hxRaw using 1
    · apply ContinuousLinearMap.ext
      rintro ⟨du, dv, dw⟩
      simp [coordV, coordW, Function.comp_def]
      field_simp [hv.ne']
      ring
  have huInv := (hasFDerivAt_inv hu.ne').comp (u, v, w) huF
  have hratioRaw := hwF.mul huInv
  have hratio :
      HasFDerivAt (fun p : Point3 => p.2.2 / p.1)
        (u⁻¹ • coordW - (w / u ^ 2) • coordU) (u, v, w) := by
    convert hratioRaw using 1
    · apply ContinuousLinearMap.ext
      rintro ⟨du, dv, dw⟩
      simp [coordU, coordW, Function.comp_def]
      field_simp [hu.ne']
      ring
  have hy :=
    (Real.hasDerivAt_sqrt (div_ne_zero hw.ne' hu.ne')).comp_hasFDerivAt
      (u, v, w) hratio
  have hall := hx.prodMk (hy.prodMk hwF)
  convert hall using 1
  · apply ContinuousLinearMap.ext
    rintro ⟨du, dv, dw⟩
    ext <;>
      simp [inverseMapDeriv_apply, coordU, coordV, coordW,
        Function.comp_def] <;>
      ring

private theorem inverseMapDeriv_det_raw (u v w : ℝ) :
    (inverseMapDeriv u v w).det =
      -w ^ 2 / (2 * Real.sqrt (w / u) * u ^ 2 * v ^ 2) := by
  let k := 1 / (2 * Real.sqrt (w / u))
  let A : Matrix (Fin 3) (Fin 3) ℝ :=
    ![![0, -w / v ^ 2, 1 / v],
      ![-k * w / u ^ 2, 0, k / u],
      ![0, 0, 1] ]
  change
    LinearMap.det
      ((coordEquiv.symm : (Fin 3 → ℝ) →ₗ[ℝ] Point3) ∘ₗ
        Matrix.toLin' A ∘ₗ
          (coordEquiv : Point3 →ₗ[ℝ] (Fin 3 → ℝ))) = _
  have hconj :
      LinearMap.det
        ((coordEquiv.symm : (Fin 3 → ℝ) →ₗ[ℝ] Point3) ∘ₗ
          Matrix.toLin' A ∘ₗ
            (coordEquiv : Point3 →ₗ[ℝ] (Fin 3 → ℝ))) =
        LinearMap.det (Matrix.toLin' A) := by
    simpa only [LinearEquiv.symm_symm] using
      (LinearMap.det_conj (Matrix.toLin' A) coordEquiv.symm)
  rw [hconj]
  simp only [LinearMap.det_toLin']
  rw [Matrix.det_fin_three]
  simp [A, k]
  ring

private theorem inverseMapDeriv_det
    (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) :
    (inverseMapDeriv u v w).det = jacobianDet u v w := by
  rw [inverseMapDeriv_det_raw]
  have hsu : Real.sqrt u ≠ 0 := Real.sqrt_ne_zero'.mpr hu
  have hsr : Real.sqrt (w / u) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (div_pos hw hu)
  have hsqw : Real.sqrt w ^ 2 = w := Real.sq_sqrt hw.le
  have hsqu : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu.le
  rw [Real.sqrt_div hw.le]
  unfold jacobianDet
  field_simp [hu.ne', hv.ne', hsu, hsr]
  nlinarith

private theorem inverseMap_injOn
    (a b alpha beta h : ℝ) (ha : 0 < a) (halpha : 0 < alpha) :
    Set.InjOn (fun p : Point3 => inverseMap p.1 p.2.1 p.2.2)
      (parameterDomain a b alpha beta h) := by
  intro p hp q hq heq
  have hpu : 0 < p.1 := lt_of_lt_of_le ha hp.1
  have hqu : 0 < q.1 := lt_of_lt_of_le ha hq.1
  have hpv : 0 < p.2.1 := lt_of_lt_of_le halpha hp.2.2.1
  have hqv : 0 < q.2.1 := lt_of_lt_of_le halpha hq.2.2.1
  have hpw : 0 < p.2.2 := hp.2.2.2.2.1
  have hqw : 0 < q.2.2 := hq.2.2.2.2.1
  have hw' := congrArg (fun r : Point3 => r.2.2) heq
  change p.2.2 = q.2.2 at hw'
  have hw : p.2.2 = q.2.2 := hw'
  have hx' := congrArg (fun r : Point3 => r.1) heq
  change p.2.2 / p.2.1 = q.2.2 / q.2.1 at hx'
  have hx : p.2.2 / p.2.1 = q.2.2 / q.2.1 := hx'
  have hv : p.2.1 = q.2.1 := by
    rw [hw] at hx
    field_simp [hpv.ne', hqv.ne'] at hx
    nlinarith
  have hy' := congrArg (fun r : Point3 => r.2.1) heq
  change
    Real.sqrt (p.2.2 / p.1) =
      Real.sqrt (q.2.2 / q.1) at hy'
  have hy :
      Real.sqrt (p.2.2 / p.1) =
        Real.sqrt (q.2.2 / q.1) := hy'
  have hy2 := congrArg (fun r : ℝ => r ^ 2) hy
  change
    Real.sqrt (p.2.2 / p.1) ^ 2 =
      Real.sqrt (q.2.2 / q.1) ^ 2 at hy2
  rw [Real.sq_sqrt (div_nonneg hpw.le hpu.le),
    Real.sq_sqrt (div_nonneg hqw.le hqu.le), hw] at hy2
  have hu : p.1 = q.1 := by
    field_simp [hpu.ne', hqu.ne'] at hy2
    nlinarith
  exact Prod.ext hu (Prod.ext hv hw)

private theorem parameterDomain_product
    (a b alpha beta h : ℝ) :
    parameterDomain a b alpha beta h =
      Set.Icc a b ×ˢ (Set.Icc alpha beta ×ˢ Set.Ioc 0 h) := by
  ext p
  simp only [parameterDomain, Set.mem_setOf_eq, Set.mem_prod,
    Set.mem_Icc, Set.mem_Ioc]
  aesop

private theorem w_factor_integral (h : ℝ) (hh : 0 < h) :
    (∫ w in (0 : ℝ)..h, w ^ 3 * Real.sqrt w) =
      2 / 9 * h ^ 4 * Real.sqrt h := by
  calc
    (∫ w in (0 : ℝ)..h, w ^ 3 * Real.sqrt w) =
        ∫ w in (0 : ℝ)..h, w ^ (7 / 2 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro w hw
      have hw0 : 0 ≤ w := by
        rw [Set.uIcc_of_le hh.le] at hw
        exact hw.1
      change w ^ 3 * Real.sqrt w = w ^ (7 / 2 : ℝ)
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast]
      rw [← Real.rpow_add_of_nonneg hw0 (by norm_num) (by norm_num)]
      norm_num
    _ = (h ^ ((7 / 2 : ℝ) + 1) -
          (0 : ℝ) ^ ((7 / 2 : ℝ) + 1)) /
        ((7 / 2 : ℝ) + 1) :=
      integral_rpow (by norm_num)
    _ = 2 / 9 * h ^ 4 * Real.sqrt h := by
      have hpow :
          h ^ (9 / 2 : ℝ) = h ^ 4 * Real.sqrt h := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast]
        rw [← Real.rpow_add hh]
        norm_num
      rw [show (7 / 2 : ℝ) + 1 = 9 / 2 by norm_num,
        hpow]
      norm_num
      ring

private theorem v_factor_integral (alpha beta : ℝ)
    (halpha : 0 < alpha) (halphabeta : alpha < beta) :
    (∫ v in alpha..beta, 1 / v ^ 4) =
      1 / 3 * (1 / alpha ^ 3 - 1 / beta ^ 3) := by
  have hbeta : 0 < beta := lt_trans halpha halphabeta
  calc
    (∫ v in alpha..beta, 1 / v ^ 4) =
        ∫ v in alpha..beta, v ^ (-4 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [Set.uIcc_of_le halphabeta.le] at hv
      have hvpos : 0 < v := lt_of_lt_of_le halpha hv.1
      change 1 / v ^ 4 = v ^ (-4 : ℝ)
      rw [Real.rpow_neg hvpos.le, one_div]
      congr 1
      exact (Real.rpow_natCast v 4).symm
    _ = (beta ^ ((-4 : ℝ) + 1) -
          alpha ^ ((-4 : ℝ) + 1)) / ((-4 : ℝ) + 1) := by
      apply integral_rpow
      right
      constructor
      · norm_num
      · rw [Set.uIcc_of_le halphabeta.le]
        intro hv
        exact (not_le_of_gt halpha) hv.1
    _ = 1 / 3 * (1 / alpha ^ 3 - 1 / beta ^ 3) := by
      rw [show (-4 : ℝ) + 1 = -3 by norm_num,
        Real.rpow_neg hbeta.le, Real.rpow_neg halpha.le]
      norm_num [Real.rpow_natCast]
      ring

private theorem u_factor_integral (a b : ℝ)
    (ha : 0 < a) (hab : a < b) :
    (∫ u in a..b, 1 / (2 * u * Real.sqrt u)) =
      1 / Real.sqrt a - 1 / Real.sqrt b := by
  have hb : 0 < b := lt_trans ha hab
  calc
    (∫ u in a..b, 1 / (2 * u * Real.sqrt u)) =
        ∫ u in a..b, (1 / 2 : ℝ) * u ^ (-3 / 2 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le hab.le] at hu
      have hupos : 0 < u := lt_of_lt_of_le ha hu.1
      change
        1 / (2 * u * Real.sqrt u) =
          (1 / 2 : ℝ) * u ^ (-3 / 2 : ℝ)
      rw [show (-3 / 2 : ℝ) = -(3 / 2) by norm_num,
        Real.rpow_neg hupos.le]
      have hthree :
          u ^ (3 / 2 : ℝ) = u * Real.sqrt u := by
        rw [Real.sqrt_eq_rpow]
        calc
          u ^ (3 / 2 : ℝ) = u ^ ((1 : ℝ) + 1 / 2) := by
            norm_num
          _ = u ^ (1 : ℝ) * u ^ (1 / 2 : ℝ) :=
            Real.rpow_add hupos 1 (1 / 2)
          _ = u * u ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
      rw [hthree]
      ring
    _ = (1 / 2 : ℝ) *
        ∫ u in a..b, u ^ (-3 / 2 : ℝ) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (1 / 2 : ℝ) *
        ((b ^ ((-3 / 2 : ℝ) + 1) -
          a ^ ((-3 / 2 : ℝ) + 1)) /
            ((-3 / 2 : ℝ) + 1)) := by
      rw [integral_rpow]
      right
      constructor
      · norm_num
      · rw [Set.uIcc_of_le hab.le]
        intro hu
        exact (not_le_of_gt ha) hu.1
    _ = 1 / Real.sqrt a - 1 / Real.sqrt b := by
      rw [show (-3 / 2 : ℝ) + 1 = -(1 / 2) by norm_num,
        Real.rpow_neg hb.le, Real.rpow_neg ha.le,
        ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
      ring

theorem gap6 (a b alpha beta h : ℝ)
    (ha : 0 < a) (hab : a < b)
    (halpha : 0 < alpha) (halphabeta : alpha < beta)
    (hh : 0 < h) :
    xSquaredIntegral a b alpha beta h =
      (∫ w in (0 : ℝ)..h, w ^ 3 * Real.sqrt w) *
      (∫ v in alpha..beta, 1 / v ^ 4) *
      ∫ u in a..b, 1 / (2 * u * Real.sqrt u) := by
  letI : Measure.IsAddHaarMeasure
      (MeasureTheory.volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  letI : Measure.IsAddHaarMeasure
      (MeasureTheory.volume : Measure Point3) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hparam : MeasurableSet (parameterDomain a b alpha beta h) := by
    unfold parameterDomain
    measurability
  have hchange :=
    MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
      (μ := (MeasureTheory.volume : Measure Point3))
      hparam
      (f := fun p : Point3 => inverseMap p.1 p.2.1 p.2.2)
      (f' := fun p => inverseMapDeriv p.1 p.2.1 p.2.2)
      (fun p hp => by
        have hu : 0 < p.1 := lt_of_lt_of_le ha hp.1
        have hv : 0 < p.2.1 :=
          lt_of_lt_of_le halpha hp.2.2.1
        have hw : 0 < p.2.2 := hp.2.2.2.2.1
        exact
          (hasFDerivAt_inverseMap p.1 p.2.1 p.2.2 hu hv hw).hasFDerivWithinAt)
      (inverseMap_injOn a b alpha beta h ha halpha)
      (fun p : Point3 => p.1 ^ 2)
  rw [gap4 a b alpha beta h ha hab halpha halphabeta hh] at hchange
  have hpoint : ∀ p ∈ parameterDomain a b alpha beta h,
      |(inverseMapDeriv p.1 p.2.1 p.2.2).det| •
          (inverseMap p.1 p.2.1 p.2.2).1 ^ 2 =
        (1 / (2 * p.1 * Real.sqrt p.1)) *
          ((1 / p.2.1 ^ 4) *
            (p.2.2 ^ 3 * Real.sqrt p.2.2)) := by
    intro p hp
    have hu : 0 < p.1 := lt_of_lt_of_le ha hp.1
    have hv : 0 < p.2.1 :=
      lt_of_lt_of_le halpha hp.2.2.1
    have hw : 0 < p.2.2 := hp.2.2.2.2.1
    rw [inverseMapDeriv_det p.1 p.2.1 p.2.2 hu hv hw]
    change
      jacobianAbs p.1 p.2.1 p.2.2 *
          (p.2.2 / p.2.1) ^ 2 =
        (1 / (2 * p.1 * Real.sqrt p.1)) *
          ((1 / p.2.1 ^ 4) *
            (p.2.2 ^ 3 * Real.sqrt p.2.2))
    rw [gap5 p.1 p.2.1 p.2.2 hu hv hw.le]
    ring
  have hrect :
      (∫ p in parameterDomain a b alpha beta h,
          (1 / (2 * p.1 * Real.sqrt p.1)) *
            ((1 / p.2.1 ^ 4) *
              (p.2.2 ^ 3 * Real.sqrt p.2.2))) =
        (∫ u in Set.Icc a b,
          1 / (2 * u * Real.sqrt u)) *
        ((∫ v in Set.Icc alpha beta, 1 / v ^ 4) *
          ∫ w in Set.Ioc (0 : ℝ) h,
            w ^ 3 * Real.sqrt w) := by
    rw [parameterDomain_product]
    calc
      (∫ p in Set.Icc a b ×ˢ
          (Set.Icc alpha beta ×ˢ Set.Ioc (0 : ℝ) h),
          (1 / (2 * p.1 * Real.sqrt p.1)) *
            ((1 / p.2.1 ^ 4) *
              (p.2.2 ^ 3 * Real.sqrt p.2.2))) =
          (∫ u in Set.Icc a b,
            1 / (2 * u * Real.sqrt u)) *
            ∫ q in Set.Icc alpha beta ×ˢ Set.Ioc (0 : ℝ) h,
              (1 / q.1 ^ 4) *
                (q.2 ^ 3 * Real.sqrt q.2) := by
        exact MeasureTheory.setIntegral_prod_mul
          (fun u : ℝ => 1 / (2 * u * Real.sqrt u))
          (fun q : ℝ × ℝ =>
            (1 / q.1 ^ 4) * (q.2 ^ 3 * Real.sqrt q.2))
          (Set.Icc a b) (Set.Icc alpha beta ×ˢ Set.Ioc (0 : ℝ) h)
      _ = _ := by
        congr 1
        exact MeasureTheory.setIntegral_prod_mul
          (fun v : ℝ => 1 / v ^ 4)
          (fun w : ℝ => w ^ 3 * Real.sqrt w)
          (Set.Icc alpha beta) (Set.Ioc (0 : ℝ) h)
  have huInterval :
      (∫ u in Set.Icc a b, 1 / (2 * u * Real.sqrt u)) =
        ∫ u in a..b, 1 / (2 * u * Real.sqrt u) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le hab.le]
  have hvInterval :
      (∫ v in Set.Icc alpha beta, 1 / v ^ 4) =
        ∫ v in alpha..beta, 1 / v ^ 4 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le halphabeta.le]
  have hwInterval :
      (∫ w in Set.Ioc (0 : ℝ) h, w ^ 3 * Real.sqrt w) =
        ∫ w in (0 : ℝ)..h, w ^ 3 * Real.sqrt w := by
    rw [intervalIntegral.integral_of_le hh.le]
  calc
    xSquaredIntegral a b alpha beta h =
        ∫ p in parameterDomain a b alpha beta h,
          |(inverseMapDeriv p.1 p.2.1 p.2.2).det| •
            (inverseMap p.1 p.2.1 p.2.2).1 ^ 2 := by
      unfold xSquaredIntegral
      exact hchange
    _ = ∫ p in parameterDomain a b alpha beta h,
          (1 / (2 * p.1 * Real.sqrt p.1)) *
            ((1 / p.2.1 ^ 4) *
              (p.2.2 ^ 3 * Real.sqrt p.2.2)) := by
      exact MeasureTheory.setIntegral_congr_fun hparam hpoint
    _ = (∫ u in Set.Icc a b,
          1 / (2 * u * Real.sqrt u)) *
        ((∫ v in Set.Icc alpha beta, 1 / v ^ 4) *
          ∫ w in Set.Ioc (0 : ℝ) h,
            w ^ 3 * Real.sqrt w) := hrect
    _ = (∫ w in (0 : ℝ)..h, w ^ 3 * Real.sqrt w) *
        (∫ v in alpha..beta, 1 / v ^ 4) *
        ∫ u in a..b, 1 / (2 * u * Real.sqrt u) := by
      rw [huInterval, hvInterval, hwInterval]
      ring

theorem gap7 (a b alpha beta h : ℝ)
    (ha : 0 < a) (hab : a < b)
    (halpha : 0 < alpha) (halphabeta : alpha < beta)
    (hh : 0 < h) :
    (∫ w in (0 : ℝ)..h, w ^ 3 * Real.sqrt w) *
        (∫ v in alpha..beta, 1 / v ^ 4) *
        (∫ u in a..b, 1 / (2 * u * Real.sqrt u)) =
      2 / 27 *
        (1 / alpha ^ 3 - 1 / beta ^ 3) *
        (1 / Real.sqrt a - 1 / Real.sqrt b) *
        h ^ 4 * Real.sqrt h := by
  rw [w_factor_integral h hh,
    v_factor_integral alpha beta halpha halphabeta,
    u_factor_integral a b ha hab]
  ring

theorem gap8 (a b alpha beta h : ℝ)
    (ha : 0 < a) (hab : a < b)
    (halpha : 0 < alpha) (halphabeta : alpha < beta)
    (hh : 0 < h) :
    xSquaredIntegral a b alpha beta h =
      2 / 27 *
        (1 / alpha ^ 3 - 1 / beta ^ 3) *
        (1 / Real.sqrt a - 1 / Real.sqrt b) *
        h ^ 4 * Real.sqrt h := by
  rw [gap6 a b alpha beta h ha hab halpha halphabeta hh]
  exact gap7 a b alpha beta h ha hab halpha halphabeta hh

end

end ProofGap.Exercise4092
