import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FinCases

namespace ProofGap.Exercise4093

noncomputable section

open MeasureTheory
open scoped Interval

def originalRegion (a b alpha beta m n : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | 0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2 ∧
    (p.1 ^ 2 + p.2.1 ^ 2) / n ≤ p.2.2 ∧
    p.2.2 ≤ (p.1 ^ 2 + p.2.1 ^ 2) / m ∧
    a ^ 2 ≤ p.1 * p.2.1 ∧ p.1 * p.2.1 ≤ b ^ 2 ∧
    alpha * p.1 ≤ p.2.1 ∧ p.2.1 ≤ beta * p.1}

def parameterDomain (a b alpha beta m n : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | 1 / n ≤ p.1 ∧ p.1 ≤ 1 / m ∧
    a ^ 2 ≤ p.2.1 ∧ p.2.1 ≤ b ^ 2 ∧
    alpha ≤ p.2.2 ∧ p.2.2 ≤ beta}

def inverseMap (u v w : ℝ) : ℝ × ℝ × ℝ :=
  (Real.sqrt (v / w), Real.sqrt (v * w),
    u * v * (w + 1 / w))

def jacobianDet (v w : ℝ) : ℝ :=
  v / (2 * w) * (w + 1 / w)

def jacobianAbs (v w : ℝ) : ℝ :=
  |jacobianDet v w|

def xyzIntegral (a b alpha beta m n : ℝ) : ℝ :=
  ∫ p in originalRegion a b alpha beta m n,
    p.1 * p.2.1 * p.2.2

theorem gap1 (u v w : ℝ) (hv : 0 ≤ v) (hw : 0 < w) :
    (inverseMap u v w).1 = Real.sqrt (v / w) := by
  rfl

theorem gap2 (u v w : ℝ) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    (inverseMap u v w).2.1 = Real.sqrt (v * w) := by
  rfl

theorem gap3 (u v w : ℝ) :
    (inverseMap u v w).2.2 = u * v * (w + 1 / w) := by
  rfl

theorem gap4 (v w : ℝ) (hv : 0 ≤ v) (hw : 0 < w) :
    jacobianAbs v w = v / (2 * w) * (w + 1 / w) := by
  unfold jacobianAbs jacobianDet
  exact abs_of_nonneg (mul_nonneg
    (div_nonneg hv (by positivity))
    (add_nonneg hw.le (by positivity)))

theorem gap5 (a b alpha beta m n : ℝ)
    (ha : 0 < a) (hab : a < b)
    (halpha : 0 < alpha) (halphabeta : alpha < beta)
    (hm : 0 < m) (hmn : m < n) :
    (fun p => inverseMap p.1 p.2.1 p.2.2) ''
        parameterDomain a b alpha beta m n =
      originalRegion a b alpha beta m n := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases q with ⟨u, v, w⟩
    change
      1 / n ≤ u ∧ u ≤ 1 / m ∧
        a ^ 2 ≤ v ∧ v ≤ b ^ 2 ∧
        alpha ≤ w ∧ w ≤ beta at hq
    rcases hq with ⟨hnu, hum, hav, hvb, haw, hwb⟩
    have hn : 0 < n := lt_trans hm hmn
    have hu : 0 < u := lt_of_lt_of_le (by positivity : 0 < 1 / n) hnu
    have hv : 0 < v := lt_of_lt_of_le (sq_pos_of_pos ha) hav
    have hw : 0 < w := lt_of_lt_of_le halpha haw
    have hvw : 0 ≤ v / w := (div_pos hv hw).le
    have hv_mul_w : 0 ≤ v * w := (mul_pos hv hw).le
    have hx2 : Real.sqrt (v / w) ^ 2 = v / w :=
      Real.sq_sqrt hvw
    have hy2 : Real.sqrt (v * w) ^ 2 = v * w :=
      Real.sq_sqrt hv_mul_w
    have hx : 0 < Real.sqrt (v / w) :=
      Real.sqrt_pos.2 (div_pos hv hw)
    have hy : 0 < Real.sqrt (v * w) :=
      Real.sqrt_pos.2 (mul_pos hv hw)
    have hxy : Real.sqrt (v / w) * Real.sqrt (v * w) = v := by
      have hsquare :
          (Real.sqrt (v / w) * Real.sqrt (v * w)) ^ 2 = v ^ 2 := by
        rw [mul_pow, hx2, hy2]
        field_simp [hw.ne']
      have hprod : 0 ≤ Real.sqrt (v / w) * Real.sqrt (v * w) :=
        mul_nonneg hx.le hy.le
      nlinarith
    have hywx : Real.sqrt (v * w) = w * Real.sqrt (v / w) := by
      have hsquare :
          Real.sqrt (v * w) ^ 2 =
            (w * Real.sqrt (v / w)) ^ 2 := by
        rw [hy2, mul_pow, hx2]
        field_simp [hw.ne']
      have hright : 0 < w * Real.sqrt (v / w) := mul_pos hw hx
      nlinarith
    have hsum :
        Real.sqrt (v / w) ^ 2 + Real.sqrt (v * w) ^ 2 =
          v * (w + 1 / w) := by
      rw [hx2, hy2]
      field_simp [hw.ne']
      ring
    change
      0 < Real.sqrt (v / w) ∧
        0 < Real.sqrt (v * w) ∧
        0 < u * v * (w + 1 / w) ∧
        (Real.sqrt (v / w) ^ 2 + Real.sqrt (v * w) ^ 2) / n ≤
          u * v * (w + 1 / w) ∧
        u * v * (w + 1 / w) ≤
          (Real.sqrt (v / w) ^ 2 + Real.sqrt (v * w) ^ 2) / m ∧
        a ^ 2 ≤ Real.sqrt (v / w) * Real.sqrt (v * w) ∧
        Real.sqrt (v / w) * Real.sqrt (v * w) ≤ b ^ 2 ∧
        alpha * Real.sqrt (v / w) ≤ Real.sqrt (v * w) ∧
        Real.sqrt (v * w) ≤ beta * Real.sqrt (v / w)
    refine ⟨hx, hy, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact mul_pos (mul_pos hu hv) (add_pos hw (by positivity))
    · rw [hsum]
      have hfactor : 0 ≤ v * (w + 1 / w) := by positivity
      have := mul_le_mul_of_nonneg_right hnu hfactor
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
    · rw [hsum]
      have hfactor : 0 ≤ v * (w + 1 / w) := by positivity
      have := mul_le_mul_of_nonneg_right hum hfactor
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
    · simpa [hxy] using hav
    · simpa [hxy] using hvb
    · rw [hywx]
      exact mul_le_mul_of_nonneg_right haw hx.le
    · rw [hywx]
      exact mul_le_mul_of_nonneg_right hwb hx.le
  · intro hp
    rcases p with ⟨x, y, z⟩
    change
      0 < x ∧ 0 < y ∧ 0 < z ∧
        (x ^ 2 + y ^ 2) / n ≤ z ∧
        z ≤ (x ^ 2 + y ^ 2) / m ∧
        a ^ 2 ≤ x * y ∧ x * y ≤ b ^ 2 ∧
        alpha * x ≤ y ∧ y ≤ beta * x at hp
    rcases hp with
      ⟨hx, hy, hz, hlower, hupper, hav, hvb, haw, hwb⟩
    have hsum : 0 < x ^ 2 + y ^ 2 := by positivity
    refine ⟨(z / (x ^ 2 + y ^ 2), x * y, y / x), ?_, ?_⟩
    · change
        1 / n ≤ z / (x ^ 2 + y ^ 2) ∧
          z / (x ^ 2 + y ^ 2) ≤ 1 / m ∧
          a ^ 2 ≤ x * y ∧ x * y ≤ b ^ 2 ∧
          alpha ≤ y / x ∧ y / x ≤ beta
      refine ⟨?_, ?_, hav, hvb, ?_, ?_⟩
      · apply (le_div_iff₀ hsum).2
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hlower
      · apply (div_le_iff₀ hsum).2
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hupper
      · exact (le_div_iff₀ hx).2 (by simpa [mul_comm] using haw)
      · exact (div_le_iff₀ hx).2 (by simpa [mul_comm] using hwb)
    · change
        inverseMap (z / (x ^ 2 + y ^ 2)) (x * y) (y / x) =
          (x, y, z)
      have hfirst : (x * y) / (y / x) = x ^ 2 := by
        field_simp [hx.ne', hy.ne']
      have hsecond : (x * y) * (y / x) = y ^ 2 := by
        field_simp [hx.ne']
      have hfactor :
          (x * y) * (y / x + 1 / (y / x)) = x ^ 2 + y ^ 2 := by
        field_simp [hx.ne', hy.ne']
        ring
      apply Prod.ext
      · simp only [inverseMap]
        rw [hfirst, Real.sqrt_sq_eq_abs, abs_of_pos hx]
      · apply Prod.ext
        · simp only [inverseMap]
          rw [hsecond, Real.sqrt_sq_eq_abs, abs_of_pos hy]
        · simp only [inverseMap]
          calc
            z / (x ^ 2 + y ^ 2) * (x * y) *
                (y / x + 1 / (y / x)) =
              z / (x ^ 2 + y ^ 2) *
                ((x * y) * (y / x + 1 / (y / x))) := by ring
            _ = z / (x ^ 2 + y ^ 2) * (x ^ 2 + y ^ 2) := by
              rw [hfactor]
            _ = z := div_mul_cancel₀ z hsum.ne'

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

private theorem sqrtCoords_product
    (v w : ℝ) (hv : 0 < v) (hw : 0 < w) :
    Real.sqrt (v / w) * Real.sqrt (v * w) = v := by
  have hx2 : Real.sqrt (v / w) ^ 2 = v / w :=
    Real.sq_sqrt (div_pos hv hw).le
  have hy2 : Real.sqrt (v * w) ^ 2 = v * w :=
    Real.sq_sqrt (mul_pos hv hw).le
  have hx : 0 < Real.sqrt (v / w) :=
    Real.sqrt_pos.2 (div_pos hv hw)
  have hy : 0 < Real.sqrt (v * w) :=
    Real.sqrt_pos.2 (mul_pos hv hw)
  have hsquare :
      (Real.sqrt (v / w) * Real.sqrt (v * w)) ^ 2 = v ^ 2 := by
    rw [mul_pow, hx2, hy2]
    field_simp [hw.ne']
  have hprod : 0 ≤ Real.sqrt (v / w) * Real.sqrt (v * w) :=
    mul_nonneg hx.le hy.le
  nlinarith

private theorem sqrtCoords_second
    (v w : ℝ) (hv : 0 < v) (hw : 0 < w) :
    Real.sqrt (v * w) = w * Real.sqrt (v / w) := by
  have hx2 : Real.sqrt (v / w) ^ 2 = v / w :=
    Real.sq_sqrt (div_pos hv hw).le
  have hy2 : Real.sqrt (v * w) ^ 2 = v * w :=
    Real.sq_sqrt (mul_pos hv hw).le
  have hx : 0 < Real.sqrt (v / w) :=
    Real.sqrt_pos.2 (div_pos hv hw)
  have hy : 0 < Real.sqrt (v * w) :=
    Real.sqrt_pos.2 (mul_pos hv hw)
  have hsquare :
      Real.sqrt (v * w) ^ 2 =
        (w * Real.sqrt (v / w)) ^ 2 := by
    rw [hy2, mul_pow, hx2]
    field_simp [hw.ne']
  have hright : 0 < w * Real.sqrt (v / w) := mul_pos hw hx
  nlinarith

private def inverseMapDeriv (u v w : ℝ) :
    Point3 →L[ℝ] Point3 :=
  let kx := 1 / (2 * Real.sqrt (v / w))
  let ky := 1 / (2 * Real.sqrt (v * w))
  let s := w + 1 / w
  let A : Matrix (Fin 3) (Fin 3) ℝ :=
    ![![0, kx / w, -kx * v / w ^ 2],
      ![0, ky * w, ky * v],
      ![v * s, u * s, u * v * (1 - 1 / w ^ 2)] ]
  ((coordEquiv.symm : (Fin 3 → ℝ) →ₗ[ℝ] Point3) ∘ₗ
    Matrix.toLin' A ∘ₗ
      (coordEquiv : Point3 →ₗ[ℝ] (Fin 3 → ℝ))).toContinuousLinearMap

private theorem inverseMapDeriv_apply (u v w : ℝ) (p : Point3) :
    inverseMapDeriv u v w p =
      ((1 / (2 * Real.sqrt (v / w)) / w) * p.2.1 +
          (-(1 / (2 * Real.sqrt (v / w))) * v / w ^ 2) * p.2.2,
        ((1 / (2 * Real.sqrt (v * w))) * w) * p.2.1 +
          ((1 / (2 * Real.sqrt (v * w))) * v) * p.2.2,
        (v * (w + 1 / w)) * p.1 +
          (u * (w + 1 / w)) * p.2.1 +
          (u * v * (1 - 1 / w ^ 2)) * p.2.2) := by
  ext <;>
    simp [inverseMapDeriv, coordEquiv, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring

private theorem hasFDerivAt_inverseMap
    (u v w : ℝ) (hv : 0 < v) (hw : 0 < w) :
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
  have hwInv := (hasFDerivAt_inv hw.ne').comp (u, v, w) hwF
  have hratioRaw := hvF.mul hwInv
  have hratio :
      HasFDerivAt (fun p : Point3 => p.2.1 / p.2.2)
        (w⁻¹ • coordV - (v / w ^ 2) • coordW) (u, v, w) := by
    convert hratioRaw using 1
    · apply ContinuousLinearMap.ext
      rintro ⟨du, dv, dw⟩
      simp [coordV, coordW, Function.comp_def]
      field_simp [hw.ne']
      ring
  have hx :=
    (Real.hasDerivAt_sqrt (div_ne_zero hv.ne' hw.ne')).comp_hasFDerivAt
      (u, v, w) hratio
  have hmul := hvF.mul hwF
  have hy :=
    (Real.hasDerivAt_sqrt (mul_ne_zero hv.ne' hw.ne')).comp_hasFDerivAt
      (u, v, w) hmul
  have hsum := hwF.add hwInv
  have hz := (huF.mul hvF).mul hsum
  have hall := hx.prodMk (hy.prodMk hz)
  convert hall using 1
  · funext p
    simp [inverseMap, Function.comp_def, div_eq_mul_inv]
  · apply ContinuousLinearMap.ext
    rintro ⟨du, dv, dw⟩
    ext <;>
      simp [inverseMapDeriv_apply, coordU, coordV, coordW,
        Function.comp_def] <;>
      field_simp [hw.ne'] <;>
      ring

private theorem inverseMapDeriv_det_raw
    (u v w : ℝ) (hv : 0 < v) (hw : 0 < w) :
    (inverseMapDeriv u v w).det =
      v ^ 2 * (w + 1 / w) /
        (2 * Real.sqrt (v / w) * Real.sqrt (v * w) * w) := by
  let kx := 1 / (2 * Real.sqrt (v / w))
  let ky := 1 / (2 * Real.sqrt (v * w))
  let s := w + 1 / w
  let A : Matrix (Fin 3) (Fin 3) ℝ :=
    ![![0, kx / w, -kx * v / w ^ 2],
      ![0, ky * w, ky * v],
      ![v * s, u * s, u * v * (1 - 1 / w ^ 2)] ]
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
  simp [A, kx, ky, s]
  have hsx : Real.sqrt (v / w) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (div_pos hv hw)
  have hsy : Real.sqrt (v * w) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (mul_pos hv hw)
  field_simp [hw.ne', hsx, hsy] <;> ring

private theorem inverseMapDeriv_det
    (u v w : ℝ) (hv : 0 < v) (hw : 0 < w) :
    (inverseMapDeriv u v w).det = jacobianDet v w := by
  rw [inverseMapDeriv_det_raw u v w hv hw]
  have hxy := sqrtCoords_product v w hv hw
  have hsx : Real.sqrt (v / w) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (div_pos hv hw)
  have hsy : Real.sqrt (v * w) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (mul_pos hv hw)
  unfold jacobianDet
  field_simp [hw.ne', hv.ne', hsx, hsy]
  nlinarith

private theorem inverseMap_injOn
    (a b alpha beta m n : ℝ) (ha : 0 < a) (halpha : 0 < alpha) :
    Set.InjOn (fun p : Point3 => inverseMap p.1 p.2.1 p.2.2)
      (parameterDomain a b alpha beta m n) := by
  intro p hp q hq heq
  have hpv : 0 < p.2.1 :=
    lt_of_lt_of_le (sq_pos_of_pos ha) hp.2.2.1
  have hqv : 0 < q.2.1 :=
    lt_of_lt_of_le (sq_pos_of_pos ha) hq.2.2.1
  have hpw : 0 < p.2.2 := lt_of_lt_of_le halpha hp.2.2.2.2.1
  have hqw : 0 < q.2.2 := lt_of_lt_of_le halpha hq.2.2.2.2.1
  have hprod' := congrArg (fun r : Point3 => r.1 * r.2.1) heq
  change
    Real.sqrt (p.2.1 / p.2.2) * Real.sqrt (p.2.1 * p.2.2) =
      Real.sqrt (q.2.1 / q.2.2) * Real.sqrt (q.2.1 * q.2.2) at hprod'
  rw [sqrtCoords_product p.2.1 p.2.2 hpv hpw,
    sqrtCoords_product q.2.1 q.2.2 hqv hqw] at hprod'
  have hv : p.2.1 = q.2.1 := hprod'
  have hx' := congrArg (fun r : Point3 => r.1) heq
  change
    Real.sqrt (p.2.1 / p.2.2) =
      Real.sqrt (q.2.1 / q.2.2) at hx'
  have hx2 := congrArg (fun r : ℝ => r ^ 2) hx'
  change
    Real.sqrt (p.2.1 / p.2.2) ^ 2 =
      Real.sqrt (q.2.1 / q.2.2) ^ 2 at hx2
  rw [Real.sq_sqrt (div_pos hpv hpw).le,
    Real.sq_sqrt (div_pos hqv hqw).le, hv] at hx2
  have hw : p.2.2 = q.2.2 := by
    field_simp [hpv.ne', hqv.ne', hpw.ne', hqw.ne'] at hx2
    nlinarith
  have hz' := congrArg (fun r : Point3 => r.2.2) heq
  change
    p.1 * p.2.1 * (p.2.2 + 1 / p.2.2) =
      q.1 * q.2.1 * (q.2.2 + 1 / q.2.2) at hz'
  rw [hv, hw] at hz'
  have hfactor : 0 < q.2.1 * (q.2.2 + 1 / q.2.2) := by positivity
  have hu : p.1 = q.1 := by
    nlinarith
  exact Prod.ext hu (Prod.ext hv hw)

private theorem parameterDomain_product
    (a b alpha beta m n : ℝ) :
    parameterDomain a b alpha beta m n =
      Set.Icc (1 / n) (1 / m) ×ˢ
        (Set.Icc (a ^ 2) (b ^ 2) ×ˢ Set.Icc alpha beta) := by
  ext p
  simp only [parameterDomain, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Icc]
  aesop

theorem gap6 (a b alpha beta m n : ℝ)
    (ha : 0 < a) (hab : a < b)
    (halpha : 0 < alpha) (halphabeta : alpha < beta)
    (hm : 0 < m) (hmn : m < n) :
    xyzIntegral a b alpha beta m n =
      (∫ u in 1 / n..1 / m, u / 2) *
      (∫ v in a ^ 2..b ^ 2, v ^ 3) *
      ∫ w in alpha..beta, w + 1 / w ^ 3 + 2 / w := by
  letI : Measure.IsAddHaarMeasure
      (MeasureTheory.volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  letI : Measure.IsAddHaarMeasure
      (MeasureTheory.volume : Measure Point3) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hparam :
      MeasurableSet (parameterDomain a b alpha beta m n) := by
    unfold parameterDomain
    measurability
  have hchange :=
    MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
      (μ := (MeasureTheory.volume : Measure Point3))
      hparam
      (f := fun p : Point3 => inverseMap p.1 p.2.1 p.2.2)
      (f' := fun p => inverseMapDeriv p.1 p.2.1 p.2.2)
      (fun p hp => by
        have hv : 0 < p.2.1 :=
          lt_of_lt_of_le (sq_pos_of_pos ha) hp.2.2.1
        have hw : 0 < p.2.2 :=
          lt_of_lt_of_le halpha hp.2.2.2.2.1
        exact
          (hasFDerivAt_inverseMap p.1 p.2.1 p.2.2 hv hw).hasFDerivWithinAt)
      (inverseMap_injOn a b alpha beta m n ha halpha)
      (fun p : Point3 => p.1 * p.2.1 * p.2.2)
  rw [gap5 a b alpha beta m n ha hab halpha halphabeta hm hmn] at hchange
  have hpoint : ∀ p ∈ parameterDomain a b alpha beta m n,
      |(inverseMapDeriv p.1 p.2.1 p.2.2).det| •
          ((inverseMap p.1 p.2.1 p.2.2).1 *
            (inverseMap p.1 p.2.1 p.2.2).2.1 *
            (inverseMap p.1 p.2.1 p.2.2).2.2) =
        (p.1 / 2) *
          (p.2.1 ^ 3 *
            (p.2.2 + 1 / p.2.2 ^ 3 + 2 / p.2.2)) := by
    intro p hp
    have hv : 0 < p.2.1 :=
      lt_of_lt_of_le (sq_pos_of_pos ha) hp.2.2.1
    have hw : 0 < p.2.2 :=
      lt_of_lt_of_le halpha hp.2.2.2.2.1
    rw [inverseMapDeriv_det p.1 p.2.1 p.2.2 hv hw]
    change
      jacobianAbs p.2.1 p.2.2 *
          (Real.sqrt (p.2.1 / p.2.2) *
            Real.sqrt (p.2.1 * p.2.2) *
            (p.1 * p.2.1 * (p.2.2 + 1 / p.2.2))) =
        (p.1 / 2) *
          (p.2.1 ^ 3 *
            (p.2.2 + 1 / p.2.2 ^ 3 + 2 / p.2.2))
    rw [gap4 p.2.1 p.2.2 hv.le hw,
      sqrtCoords_product p.2.1 p.2.2 hv hw]
    field_simp [hw.ne']
    ring
  have hrect :
      (∫ p in parameterDomain a b alpha beta m n,
          (p.1 / 2) *
            (p.2.1 ^ 3 *
              (p.2.2 + 1 / p.2.2 ^ 3 + 2 / p.2.2))) =
        (∫ u in Set.Icc (1 / n) (1 / m), u / 2) *
          ((∫ v in Set.Icc (a ^ 2) (b ^ 2), v ^ 3) *
            ∫ w in Set.Icc alpha beta,
              w + 1 / w ^ 3 + 2 / w) := by
    rw [parameterDomain_product]
    calc
      (∫ p in Set.Icc (1 / n) (1 / m) ×ˢ
          (Set.Icc (a ^ 2) (b ^ 2) ×ˢ Set.Icc alpha beta),
          (p.1 / 2) *
            (p.2.1 ^ 3 *
              (p.2.2 + 1 / p.2.2 ^ 3 + 2 / p.2.2))) =
          (∫ u in Set.Icc (1 / n) (1 / m), u / 2) *
            ∫ q in Set.Icc (a ^ 2) (b ^ 2) ×ˢ Set.Icc alpha beta,
              q.1 ^ 3 * (q.2 + 1 / q.2 ^ 3 + 2 / q.2) := by
        exact MeasureTheory.setIntegral_prod_mul
          (fun u : ℝ => u / 2)
          (fun q : ℝ × ℝ =>
            q.1 ^ 3 * (q.2 + 1 / q.2 ^ 3 + 2 / q.2))
          (Set.Icc (1 / n) (1 / m))
          (Set.Icc (a ^ 2) (b ^ 2) ×ˢ Set.Icc alpha beta)
      _ = _ := by
        congr 1
        exact MeasureTheory.setIntegral_prod_mul
          (fun v : ℝ => v ^ 3)
          (fun w : ℝ => w + 1 / w ^ 3 + 2 / w)
          (Set.Icc (a ^ 2) (b ^ 2)) (Set.Icc alpha beta)
  have hn : 0 < n := lt_trans hm hmn
  have huorder : 1 / n ≤ 1 / m :=
    (one_div_lt_one_div_of_lt hm hmn).le
  have hvorder : a ^ 2 ≤ b ^ 2 := by nlinarith
  have huInterval :
      (∫ u in Set.Icc (1 / n) (1 / m), u / 2) =
        ∫ u in 1 / n..1 / m, u / 2 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le huorder]
  have hvInterval :
      (∫ v in Set.Icc (a ^ 2) (b ^ 2), v ^ 3) =
        ∫ v in a ^ 2..b ^ 2, v ^ 3 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le hvorder]
  have hwInterval :
      (∫ w in Set.Icc alpha beta,
          w + 1 / w ^ 3 + 2 / w) =
        ∫ w in alpha..beta, w + 1 / w ^ 3 + 2 / w := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le halphabeta.le]
  calc
    xyzIntegral a b alpha beta m n =
        ∫ p in parameterDomain a b alpha beta m n,
          |(inverseMapDeriv p.1 p.2.1 p.2.2).det| •
            ((inverseMap p.1 p.2.1 p.2.2).1 *
              (inverseMap p.1 p.2.1 p.2.2).2.1 *
              (inverseMap p.1 p.2.1 p.2.2).2.2) := by
      unfold xyzIntegral
      exact hchange
    _ = ∫ p in parameterDomain a b alpha beta m n,
          (p.1 / 2) *
            (p.2.1 ^ 3 *
              (p.2.2 + 1 / p.2.2 ^ 3 + 2 / p.2.2)) := by
      exact MeasureTheory.setIntegral_congr_fun hparam hpoint
    _ = (∫ u in Set.Icc (1 / n) (1 / m), u / 2) *
          ((∫ v in Set.Icc (a ^ 2) (b ^ 2), v ^ 3) *
            ∫ w in Set.Icc alpha beta,
              w + 1 / w ^ 3 + 2 / w) := hrect
    _ = (∫ u in 1 / n..1 / m, u / 2) *
        (∫ v in a ^ 2..b ^ 2, v ^ 3) *
        ∫ w in alpha..beta, w + 1 / w ^ 3 + 2 / w := by
      rw [huInterval, hvInterval, hwInterval]
      ring

private theorem u_factor_integral (m n : ℝ)
    (hm : 0 < m) (hmn : m < n) :
    (∫ u in 1 / n..1 / m, u / 2) =
      1 / 4 * (1 / m ^ 2 - 1 / n ^ 2) := by
  rw [show (fun u : ℝ => u / 2) = fun u => (1 / 2 : ℝ) * u by
    funext u
    ring]
  rw [intervalIntegral.integral_const_mul, integral_id]
  ring

private theorem v_factor_integral (a b : ℝ) :
    (∫ v in a ^ 2..b ^ 2, v ^ 3) =
      1 / 4 * (b ^ 8 - a ^ 8) := by
  rw [integral_pow]
  norm_num
  ring

private theorem w_factor_integral (alpha beta : ℝ)
    (halpha : 0 < alpha) (halphabeta : alpha < beta) :
    (∫ w in alpha..beta, w + 1 / w ^ 3 + 2 / w) =
      1 / 2 *
        ((beta ^ 2 - alpha ^ 2) *
            (1 + 1 / (alpha ^ 2 * beta ^ 2)) +
          4 * Real.log (beta / alpha)) := by
  have hbeta : 0 < beta := lt_trans halpha halphabeta
  let F : ℝ → ℝ := fun w =>
    w ^ 2 / 2 + (-1 / 2 : ℝ) * (w ^ 2)⁻¹ + 2 * Real.log w
  have hderiv (w : ℝ) (hw : w ∈ Set.uIcc alpha beta) :
      HasDerivAt F (w + 1 / w ^ 3 + 2 / w) w := by
    rw [Set.uIcc_of_le halphabeta.le] at hw
    have hwpos : 0 < w := lt_of_lt_of_le halpha hw.1
    have hsq :
        HasDerivAt (fun t : ℝ => t ^ 2) (2 * w) w := by
      convert (hasDerivAt_id w).pow 2 using 1 <;> norm_num <;> ring
    have hfirst :
        HasDerivAt (fun t : ℝ => t ^ 2 / 2) w w := by
      convert hsq.div_const 2 using 1 <;> ring
    have hsecond :
        HasDerivAt (fun t : ℝ => (-1 / 2 : ℝ) * (t ^ 2)⁻¹)
          (1 / w ^ 3) w := by
      convert
        (hsq.inv (pow_ne_zero 2 hwpos.ne')).const_mul (-1 / 2 : ℝ)
          using 1 <;>
        field_simp [hwpos.ne'] <;>
        ring
    have hlog :
        HasDerivAt (fun t : ℝ => 2 * Real.log t) (2 / w) w := by
      convert (Real.hasDerivAt_log hwpos.ne').const_mul 2 using 1 <;>
        ring
    simpa only [F] using (hfirst.add hsecond).add hlog
  have hint :
      IntervalIntegrable (fun w : ℝ => w + 1 / w ^ 3 + 2 / w)
        MeasureTheory.volume alpha beta := by
    apply ContinuousOn.intervalIntegrable
    intro w hw
    rw [Set.uIcc_of_le halphabeta.le] at hw
    have hwpos : 0 < w := lt_of_lt_of_le halpha hw.1
    have hrecipCube : ContinuousAt (fun t : ℝ => 1 / t ^ 3) w := by
      simpa [one_div] using
        (continuousAt_id.pow 3).inv₀ (pow_ne_zero 3 hwpos.ne')
    have htwiceRecip : ContinuousAt (fun t : ℝ => 2 / t) w :=
      continuousAt_const.div continuousAt_id hwpos.ne'
    exact
      ((continuousAt_id.add hrecipCube).add htwiceRecip).continuousWithinAt
  have hfund :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := F) hderiv hint
  rw [hfund]
  dsimp [F]
  rw [Real.log_div hbeta.ne' halpha.ne']
  field_simp [halpha.ne', hbeta.ne']
  ring

theorem gap7 (a b alpha beta m n : ℝ)
    (ha : 0 < a) (hab : a < b)
    (halpha : 0 < alpha) (halphabeta : alpha < beta)
    (hm : 0 < m) (hmn : m < n) :
    xyzIntegral a b alpha beta m n =
      1 / 32 * (1 / m ^ 2 - 1 / n ^ 2) *
        (b ^ 8 - a ^ 8) *
        ((beta ^ 2 - alpha ^ 2) *
            (1 + 1 / (alpha ^ 2 * beta ^ 2)) +
          4 * Real.log (beta / alpha)) := by
  rw [gap6 a b alpha beta m n ha hab halpha halphabeta hm hmn,
    u_factor_integral m n hm hmn,
    v_factor_integral a b,
    w_factor_integral alpha beta halpha halphabeta]
  ring

end

end ProofGap.Exercise4093
