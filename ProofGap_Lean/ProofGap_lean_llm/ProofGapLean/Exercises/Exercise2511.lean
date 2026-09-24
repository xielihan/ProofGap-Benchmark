import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise2511

noncomputable section

def radius (a m φ : ℝ) : ℝ := a * Real.exp (m * φ)
def speedWeight (a m t : ℝ) : ℝ :=
  Real.sqrt (a ^ 2 * (1 + m ^ 2)) * Real.exp (m * t)
def mass (a m φ : ℝ) : ℝ :=
  ∫ t in Set.Iic φ, speedWeight a m t
def xFirstMoment (a m φ : ℝ) : ℝ :=
  ∫ t in Set.Iic φ,
    radius a m t * Real.cos t * speedWeight a m t
def yFirstMoment (a m φ : ℝ) : ℝ :=
  ∫ t in Set.Iic φ,
    radius a m t * Real.sin t * speedWeight a m t
def centroidX (a m φ : ℝ) : ℝ := xFirstMoment a m φ / mass a m φ
def centroidY (a m φ : ℝ) : ℝ := yFirstMoment a m φ / mass a m φ
def reducedX (a m φ : ℝ) : ℝ :=
  a * (∫ t in Set.Iic φ, Real.exp (2 * m * t) * Real.cos t) /
    (∫ t in Set.Iic φ, Real.exp (m * t))
def reducedY (a m φ : ℝ) : ℝ :=
  a * (∫ t in Set.Iic φ, Real.exp (2 * m * t) * Real.sin t) /
    (∫ t in Set.Iic φ, Real.exp (m * t))

private theorem integral_exp_mul_cos_Iic (k φ : ℝ) (hk : 0 < k) :
    (∫ t in Set.Iic φ, Real.exp (k * t) * Real.cos t) =
      Real.exp (k * φ) * (k * Real.cos φ + Real.sin φ) / (k ^ 2 + 1) := by
  let z : ℂ := (k : ℂ) + Complex.I
  have hz : 0 < z.re := by simpa [z] using hk
  have hint := integrableOn_exp_mul_complex_Iic (a := z) hz φ
  have hi := integral_exp_mul_complex_Iic (a := z) hz φ
  have h := (integral_re (μ := MeasureTheory.volume.restrict (Set.Iic φ)) hint).trans
    (congrArg Complex.re hi)
  convert h using 1 <;>
    simp [z, Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.normSq] <;> ring

private theorem integral_exp_mul_sin_Iic (k φ : ℝ) (hk : 0 < k) :
    (∫ t in Set.Iic φ, Real.exp (k * t) * Real.sin t) =
      Real.exp (k * φ) * (k * Real.sin φ - Real.cos φ) / (k ^ 2 + 1) := by
  let z : ℂ := (k : ℂ) + Complex.I
  have hz : 0 < z.re := by simpa [z] using hk
  have hint := integrableOn_exp_mul_complex_Iic (a := z) hz φ
  have hi := integral_exp_mul_complex_Iic (a := z) hz φ
  have h := (integral_im (μ := MeasureTheory.volume.restrict (Set.Iic φ)) hint).trans
    (congrArg Complex.im hi)
  convert h using 1 <;>
    simp [z, Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im,
      Complex.div_im, Complex.normSq] <;> ring

private theorem cancel_common_factor (a s x y : ℝ) (hs : s ≠ 0) :
    a * s * x / (s * y) = a * x / y := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
  calc
    a * s * x * (y⁻¹ * s⁻¹) = a * (s * s⁻¹) * x * y⁻¹ := by ring
    _ = a * x * y⁻¹ := by simp [hs]

private theorem centroidX_eq_reduced (a m φ : ℝ) (ha : 0 < a) :
    centroidX a m φ = reducedX a m φ := by
  let s := Real.sqrt (a ^ 2 * (1 + m ^ 2))
  have hs : s ≠ 0 := (Real.sqrt_pos.2 (mul_pos (sq_pos_of_pos ha) (by nlinarith [sq_nonneg m]))).ne'
  have hx :
      (∫ t in Set.Iic φ, radius a m t * Real.cos t * speedWeight a m t) =
        a * s * (∫ t in Set.Iic φ, Real.exp (2 * m * t) * Real.cos t) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [show Real.exp (2 * m * t) = Real.exp (m * t) * Real.exp (m * t) by
      rw [← Real.exp_add]; congr 1 <;> ring]
    simp only [radius, speedWeight, s]
    ring
  have hmass :
      (∫ t in Set.Iic φ, speedWeight a m t) =
        s * (∫ t in Set.Iic φ, Real.exp (m * t)) := by
    rw [← MeasureTheory.integral_const_mul]
    rfl
  rw [centroidX, xFirstMoment, mass, reducedX, hx, hmass]
  exact cancel_common_factor a s _ _ hs

private theorem centroidY_eq_reduced (a m φ : ℝ) (ha : 0 < a) :
    centroidY a m φ = reducedY a m φ := by
  let s := Real.sqrt (a ^ 2 * (1 + m ^ 2))
  have hs : s ≠ 0 := (Real.sqrt_pos.2 (mul_pos (sq_pos_of_pos ha) (by nlinarith [sq_nonneg m]))).ne'
  have hy :
      (∫ t in Set.Iic φ, radius a m t * Real.sin t * speedWeight a m t) =
        a * s * (∫ t in Set.Iic φ, Real.exp (2 * m * t) * Real.sin t) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [show Real.exp (2 * m * t) = Real.exp (m * t) * Real.exp (m * t) by
      rw [← Real.exp_add]; congr 1 <;> ring]
    simp only [radius, speedWeight, s]
    ring
  have hmass :
      (∫ t in Set.Iic φ, speedWeight a m t) =
        s * (∫ t in Set.Iic φ, Real.exp (m * t)) := by
    rw [← MeasureTheory.integral_const_mul]
    rfl
  rw [centroidY, yFirstMoment, mass, reducedY, hy, hmass]
  exact cancel_common_factor a s _ _ hs

theorem gap1 (a m φ ξ : ℝ) (hξ : ξ = centroidX a m φ) :
    ξ = xFirstMoment a m φ / mass a m φ := by
  simpa [centroidX] using hξ

theorem gap2 (a m φ : ℝ) (ha : 0 < a) (hm : 0 < m) :
    centroidX a m φ = reducedX a m φ := centroidX_eq_reduced a m φ ha

theorem gap3 (a m φ : ℝ) (ha : 0 < a) (hm : 0 < m) :
    reducedX a m φ =
      m * a * Real.exp (m * φ) *
        (Real.sin φ + 2 * m * Real.cos φ) / (4 * m ^ 2 + 1) := by
  rw [reducedX, integral_exp_mul_cos_Iic (2 * m) φ (by positivity),
    integral_exp_mul_Iic hm φ]
  rw [show Real.exp (2 * m * φ) = Real.exp (m * φ) ^ 2 by
    rw [pow_two, ← Real.exp_add]; congr 1 <;> ring]
  field_simp [hm.ne', Real.exp_ne_zero]
  ring

theorem gap4 (a m φ ξ : ℝ) (ha : 0 < a) (hm : 0 < m)
    (hξ : ξ = centroidX a m φ) :
    ξ = m * a * Real.exp (m * φ) *
      (Real.sin φ + 2 * m * Real.cos φ) / (4 * m ^ 2 + 1) := by
  rw [hξ, gap2 a m φ ha hm, gap3 a m φ ha hm]

theorem gap5 (a m φ η : ℝ) (hη : η = centroidY a m φ) :
    η = yFirstMoment a m φ / mass a m φ := by
  simpa [centroidY] using hη

theorem gap6 (a m φ : ℝ) (ha : 0 < a) (hm : 0 < m) :
    reducedY a m φ =
      m * a * Real.exp (m * φ) *
        (2 * m * Real.sin φ - Real.cos φ) / (4 * m ^ 2 + 1) := by
  rw [reducedY, integral_exp_mul_sin_Iic (2 * m) φ (by positivity),
    integral_exp_mul_Iic hm φ]
  rw [show Real.exp (2 * m * φ) = Real.exp (m * φ) ^ 2 by
    rw [pow_two, ← Real.exp_add]; congr 1 <;> ring]
  field_simp [hm.ne', Real.exp_ne_zero]
  ring

theorem gap7 (a m φ η : ℝ) (ha : 0 < a) (hm : 0 < m)
    (hη : η = centroidY a m φ) :
    η = m * a * Real.exp (m * φ) *
      (2 * m * Real.sin φ - Real.cos φ) / (4 * m ^ 2 + 1) := by
  rw [hη, centroidY_eq_reduced a m φ ha, gap6 a m φ ha hm]

theorem gap8 (ξ η r₀ : ℝ)
    (hr : r₀ = Real.sqrt (ξ ^ 2 + η ^ 2)) :
    r₀ = Real.sqrt (ξ ^ 2 + η ^ 2) := hr

theorem gap9 (a m φ ξ η : ℝ) (ha : 0 < a) (hm : 0 < m)
    (hξ : ξ = centroidX a m φ) (hη : η = centroidY a m φ) :
    Real.sqrt (ξ ^ 2 + η ^ 2) =
      (m * a / (4 * m ^ 2 + 1)) *
        Real.sqrt (4 * m ^ 2 + 1) * Real.exp (m * φ) := by
  rw [hξ, hη, centroidX_eq_reduced a m φ ha, gap3 a m φ ha hm,
    centroidY_eq_reduced a m φ ha, gap6 a m φ ha hm]
  have hD : 0 < 4 * m ^ 2 + 1 := by positivity
  have hrad :
      (m * a * Real.exp (m * φ) *
          (Real.sin φ + 2 * m * Real.cos φ) / (4 * m ^ 2 + 1)) ^ 2 +
        (m * a * Real.exp (m * φ) *
          (2 * m * Real.sin φ - Real.cos φ) / (4 * m ^ 2 + 1)) ^ 2 =
        ((m * a / (4 * m ^ 2 + 1)) *
          Real.sqrt (4 * m ^ 2 + 1) * Real.exp (m * φ)) ^ 2 := by
    have hsquare := Real.sq_sqrt
      (show 0 ≤ m ^ 2 * 4 + 1 by positivity)
    field_simp [hD.ne']
    nlinarith [hsquare, Real.sin_sq_add_cos_sq φ]
  have hnonneg :
      0 ≤ (m * a * Real.exp (m * φ) *
          (Real.sin φ + 2 * m * Real.cos φ) / (4 * m ^ 2 + 1)) ^ 2 +
        (m * a * Real.exp (m * φ) *
          (2 * m * Real.sin φ - Real.cos φ) / (4 * m ^ 2 + 1)) ^ 2 := by
    positivity
  have hsqrt := Real.sq_sqrt hnonneg
  have hsqrt_nonneg :
      0 ≤ Real.sqrt
        ((m * a * Real.exp (m * φ) *
            (Real.sin φ + 2 * m * Real.cos φ) / (4 * m ^ 2 + 1)) ^ 2 +
          (m * a * Real.exp (m * φ) *
            (2 * m * Real.sin φ - Real.cos φ) / (4 * m ^ 2 + 1)) ^ 2) :=
    Real.sqrt_nonneg _
  have hright :
      0 ≤ (m * a / (4 * m ^ 2 + 1)) *
        Real.sqrt (4 * m ^ 2 + 1) * Real.exp (m * φ) := by positivity
  nlinarith

theorem gap10 (a m φ : ℝ) (ha : 0 < a) (hm : 0 < m) :
    (m * a / (4 * m ^ 2 + 1)) *
        Real.sqrt (4 * m ^ 2 + 1) * Real.exp (m * φ) =
      m * radius a m φ / Real.sqrt (4 * m ^ 2 + 1) := by
  have hD : 0 < 4 * m ^ 2 + 1 := by positivity
  have hs : Real.sqrt (4 * m ^ 2 + 1) ≠ 0 := (Real.sqrt_pos.2 hD).ne'
  have hsquare := Real.sq_sqrt hD.le
  rw [radius]
  calc
    m * a / (4 * m ^ 2 + 1) * Real.sqrt (4 * m ^ 2 + 1) * Real.exp (m * φ) =
        m * a * Real.exp (m * φ) *
          (Real.sqrt (4 * m ^ 2 + 1) / (4 * m ^ 2 + 1)) := by ring
    _ = m * a * Real.exp (m * φ) *
          (Real.sqrt (4 * m ^ 2 + 1) / Real.sqrt (4 * m ^ 2 + 1) ^ 2) := by
      rw [hsquare]
    _ = m * (a * Real.exp (m * φ)) / Real.sqrt (4 * m ^ 2 + 1) := by
      field_simp [hs]

theorem gap11 (a m φ r₀ : ℝ) (ha : 0 < a) (hm : 0 < m)
    (hr : r₀ = Real.sqrt ((centroidX a m φ) ^ 2 +
      (centroidY a m φ) ^ 2)) :
    r₀ = m * radius a m φ / Real.sqrt (4 * m ^ 2 + 1) := by
  rw [hr, gap9 a m φ (centroidX a m φ) (centroidY a m φ) ha hm rfl rfl,
    gap10 a m φ ha hm]

theorem gap12 (ξ η φ₀ : ℝ) (hξ : ξ ≠ 0)
    (hφ : Real.tan φ₀ = η / ξ) :
    Real.tan φ₀ = η / ξ := hφ

theorem gap13 (a m φ : ℝ) (ha : 0 < a) (hm : 0 < m)
    (hcos : Real.cos φ ≠ 0)
    (hden : Real.tan φ + 2 * m ≠ 0) :
    centroidY a m φ / centroidX a m φ =
      (2 * m * Real.tan φ - 1) / (Real.tan φ + 2 * m) := by
  have hD : 4 * m ^ 2 + 1 ≠ 0 := by positivity
  have hsum : Real.sin φ + 2 * m * Real.cos φ ≠ 0 := by
    intro h
    apply hden
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcos]
    linarith
  rw [centroidY_eq_reduced a m φ ha, gap6 a m φ ha hm,
    centroidX_eq_reduced a m φ ha, gap3 a m φ ha hm,
    Real.tan_eq_sin_div_cos]
  field_simp [hm.ne', ha.ne', Real.exp_ne_zero, hD, hcos, hsum]

theorem gap14 (m φ : ℝ) (hm : m ≠ 0)
    (h₁ : Real.tan φ + 2 * m ≠ 0)
    (h₂ : 1 + (1 / (2 * m)) * Real.tan φ ≠ 0) :
    (2 * m * Real.tan φ - 1) / (Real.tan φ + 2 * m) =
      (Real.tan φ - 1 / (2 * m)) /
        (1 + (1 / (2 * m)) * Real.tan φ) := by
  have h₁' : 2 * m + Real.tan φ ≠ 0 := by
    intro h
    apply h₁
    linarith
  field_simp [hm, h₁, h₁', h₂]
  ring

theorem gap15 (m φ φ₀ : ℝ) (hm : m ≠ 0)
    (h₁ : Real.tan φ + 2 * m ≠ 0)
    (h₂ : 1 + (1 / (2 * m)) * Real.tan φ ≠ 0)
    (hφ₀ :
      Real.tan φ₀ =
        (2 * m * Real.tan φ - 1) / (Real.tan φ + 2 * m)) :
    Real.tan φ₀ =
      (Real.tan φ - 1 / (2 * m)) /
        (1 + (1 / (2 * m)) * Real.tan φ) := by
  rw [hφ₀, gap14 m φ hm h₁ h₂]

theorem gap16 (φ φ₀ α : ℝ)
    (hφ₀ : φ₀ ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2))
    (hφa : φ - α ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2))
    (htan : Real.tan φ₀ = Real.tan (φ - α)) :
    φ₀ = φ - α := by
  apply Real.strictMonoOn_tan.injOn
  · simpa only [neg_div] using hφ₀
  · simpa only [neg_div] using hφa
  · exact htan

theorem gap17 (m α : ℝ) (hm : 0 < m)
    (hα : α = Real.arctan (1 / (2 * m))) :
    α = Real.arctan (1 / (2 * m)) := hα

theorem gap18 (a m φ r₀ : ℝ) (ha : 0 < a) (hm : 0 < m)
    (hr : r₀ = m * radius a m φ / Real.sqrt (4 * m ^ 2 + 1)) :
    r₀ = m * a / Real.sqrt (4 * m ^ 2 + 1) *
      Real.exp (m * φ) := by
  rw [hr, radius]
  ring

theorem gap19 (a m φ φ₀ α : ℝ) (hangle : φ₀ = φ - α) :
    m * a / Real.sqrt (4 * m ^ 2 + 1) * Real.exp (m * φ) =
      m * a / Real.sqrt (4 * m ^ 2 + 1) *
        Real.exp (m * (φ₀ + α)) := by
  rw [show φ = φ₀ + α by linarith]

theorem gap20 (a m φ₀ α r₀ : ℝ)
    (hr : r₀ = m * a / Real.sqrt (4 * m ^ 2 + 1) *
      Real.exp (m * (φ₀ + α))) :
    r₀ = m * a / Real.sqrt (4 * m ^ 2 + 1) *
      Real.exp (m * (φ₀ + α)) := hr

end

end ProofGap.Exercise2511
