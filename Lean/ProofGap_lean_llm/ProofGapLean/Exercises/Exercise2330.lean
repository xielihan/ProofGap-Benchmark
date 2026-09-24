import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue

open scoped Interval

namespace ProofGap.Exercise2330

noncomputable section

def targetIntegral (a b : ℝ) : ℝ :=
  ∫ x in a..b, Real.sin (x ^ 2)

def transformedIntegral (a b : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ t in a ^ 2..b ^ 2, Real.sin t / Real.sqrt t

def φ (t : ℝ) : ℝ := 1 / Real.sqrt t

def correctedMeanValue (a b ξ : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ((1 / a - 1 / b) * (Real.cos (a ^ 2) - Real.cos ξ) +
      1 / b * (Real.cos (a ^ 2) - Real.cos (b ^ 2)))

def θValue (a b ξ : ℝ) : ℝ := a * correctedMeanValue a b ξ

private theorem sq_lt_sq (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    a ^ 2 < b ^ 2 := by nlinarith

private theorem target_eq_transformed (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    targetIntegral a b = transformedIntegral a b := by
  have hle : a ≤ b := hab.le
  let g : ℝ → ℝ := fun t => Real.sin t / Real.sqrt t
  have hsquare : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    intro x hx
    convert (hasDerivAt_id x).pow 2 using 1 <;> norm_num <;> ring
  have hderivCont : ContinuousOn (fun x : ℝ => 2 * x) (Set.uIcc a b) := by
    fun_prop
  have hg : ContinuousOn g ((fun x : ℝ => x ^ 2) '' Set.uIcc a b) := by
    unfold g
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro t ht
      rcases ht with ⟨x, hx, rfl⟩
      rw [Set.uIcc_of_le hle] at hx
      exact (Real.sqrt_pos.2 (sq_pos_of_pos (ha.trans_le hx.1))).ne'
  have H := intervalIntegral.integral_comp_mul_deriv' hsquare hderivCont hg
  have htwo : 2 * targetIntegral a b =
      ∫ t in a ^ 2..b ^ 2, Real.sin t / Real.sqrt t := by
    unfold targetIntegral
    calc
      2 * (∫ x in a..b, Real.sin (x ^ 2)) =
          ∫ x in a..b, 2 * Real.sin (x ^ 2) := by
            rw [intervalIntegral.integral_const_mul]
      _ = ∫ x in a..b, (g ∘ fun y : ℝ => y ^ 2) x * (2 * x) := by
            apply intervalIntegral.integral_congr
            intro x hx
            rw [Set.uIcc_of_le hle] at hx
            dsimp [g]
            rw [Real.sqrt_sq (ha.trans_le hx.1).le]
            field_simp [(ha.trans_le hx.1).ne']
      _ = ∫ t in a ^ 2..b ^ 2, g t := H
  unfold transformedIntegral
  linarith

private def primitive (a t : ℝ) : ℝ := Real.cos (a ^ 2) - Real.cos t

private def weight (t : ℝ) : ℝ := 1 / (2 * Real.sqrt t ^ 3)

private theorem hasDerivAt_phi (t : ℝ) (ht : 0 < t) :
    HasDerivAt φ (-weight t) t := by
  have hs := Real.hasDerivAt_sqrt ht.ne'
  have hi := hs.inv (Real.sqrt_pos.2 ht).ne'
  have hval : -(1 / (2 * Real.sqrt t)) / Real.sqrt t ^ 2 =
      -(1 / (2 * Real.sqrt t ^ 3)) := by
    field_simp [(Real.sqrt_pos.2 ht).ne']
  rw [hval] at hi
  have hfun : φ = fun x : ℝ => (Real.sqrt x)⁻¹ := by
    funext x
    simp [φ, one_div]
  rw [hfun]
  simpa [weight, one_div] using hi

private theorem exists_transformedMean (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ ξ ∈ Set.Icc (a ^ 2) (b ^ 2),
      transformedIntegral a b = correctedMeanValue a b ξ := by
  have hsq : a ^ 2 < b ^ 2 := sq_lt_sq a b ha hab
  have hle : a ^ 2 ≤ b ^ 2 := hsq.le
  have hApos : 0 < a ^ 2 := sq_pos_of_pos ha
  have hu : ∀ t ∈ Set.uIcc (a ^ 2) (b ^ 2),
      HasDerivAt φ (-weight t) t := by
    intro t ht
    rw [Set.uIcc_of_le hle] at ht
    exact hasDerivAt_phi t (hApos.trans_le ht.1)
  have hv : ∀ t ∈ Set.uIcc (a ^ 2) (b ^ 2),
      HasDerivAt (primitive a) (Real.sin t) t := by
    intro t ht
    unfold primitive
    convert (hasDerivAt_const t (Real.cos (a ^ 2))).sub
      (Real.hasDerivAt_cos t) using 1 <;> ring
  have hwInt : IntervalIntegrable weight MeasureTheory.volume (a ^ 2) (b ^ 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hle]
    unfold weight
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro t ht
      have htpos : 0 < t := hApos.trans_le ht.1
      positivity
  have hsinInt : IntervalIntegrable Real.sin MeasureTheory.volume (a ^ 2) (b ^ 2) :=
    Real.continuous_sin.intervalIntegrable _ _
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    hwInt.neg hsinInt
  have hprim : ContinuousOn (primitive a) (Set.uIcc (a ^ 2) (b ^ 2)) := by
    unfold primitive
    fun_prop
  have hw0 : ∀ t ∈ Set.uIoc (a ^ 2) (b ^ 2), 0 ≤ weight t := by
    intro t ht
    rw [Set.uIoc_of_le hle] at ht
    unfold weight
    have htpos : 0 < t := hApos.trans_le ht.1.le
    positivity
  rcases exists_eq_const_mul_intervalIntegral_of_nonneg hprim hwInt hw0 with
    ⟨ξ, hξ, hmean⟩
  rw [Set.uIcc_of_le hle] at hξ
  have hweight : (∫ t in a ^ 2..b ^ 2, weight t) = 1 / a - 1 / b := by
    have hderiv := intervalIntegral.integral_eq_sub_of_hasDerivAt hu hwInt.neg
    rw [intervalIntegral.integral_neg] at hderiv
    have hsqrta : Real.sqrt (a ^ 2) = a := Real.sqrt_sq ha.le
    have hsqrtb : Real.sqrt (b ^ 2) = b := Real.sqrt_sq (ha.trans hab).le
    unfold φ at hderiv
    rw [hsqrta, hsqrtb] at hderiv
    linarith
  have hpa : primitive a (a ^ 2) = 0 := by simp [primitive]
  have hrewrite :
      (∫ t in a ^ 2..b ^ 2, weight t * primitive a t) =
        primitive a ξ * (1 / a - 1 / b) := by
    calc
      _ = ∫ t in a ^ 2..b ^ 2, primitive a t * weight t := by
            apply intervalIntegral.integral_congr
            intro t ht
            ring
      _ = _ := by rw [hmean, hweight]
  have htarget :
      (∫ t in a ^ 2..b ^ 2, φ t * Real.sin t) =
        φ (b ^ 2) * primitive a (b ^ 2) +
          ∫ t in a ^ 2..b ^ 2, weight t * primitive a t := by
    rw [hpa] at hparts
    simp only [mul_zero, sub_zero] at hparts
    have hneg :
        -(∫ t in a ^ 2..b ^ 2, -weight t * primitive a t) =
          ∫ t in a ^ 2..b ^ 2, weight t * primitive a t := by
      calc
        _ = ∫ t in a ^ 2..b ^ 2, -(-weight t * primitive a t) :=
          (intervalIntegral.integral_neg).symm
        _ = _ := by
          apply intervalIntegral.integral_congr
          intro t ht
          ring
    linarith [hparts, hneg]
  have hsqrtb : Real.sqrt (b ^ 2) = b := Real.sqrt_sq (ha.trans hab).le
  have hint :
      (∫ t in a ^ 2..b ^ 2, Real.sin t / Real.sqrt t) =
        ∫ t in a ^ 2..b ^ 2, φ t * Real.sin t := by
    apply intervalIntegral.integral_congr
    intro t ht
    unfold φ
    dsimp
    rw [div_eq_mul_inv]
    ring
  refine ⟨ξ, hξ, ?_⟩
  unfold transformedIntegral correctedMeanValue
  rw [hint, htarget, hrewrite]
  unfold primitive φ
  rw [hsqrtb]
  ring

private theorem theta_abs_le_one (a b ξ : ℝ) (ha : 0 < a) (hab : a < b) :
    |θValue a b ξ| ≤ 1 := by
  have hb : 0 < b := ha.trans hab
  have hib : 0 ≤ 1 / b := by positivity
  have hiba : 1 / b ≤ 1 / a := one_div_le_one_div_of_le ha hab.le
  have hd : 0 ≤ 1 / a - 1 / b := sub_nonneg.mpr hiba
  have hp : |Real.cos (a ^ 2) - Real.cos ξ| ≤ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [Real.neg_one_le_cos (a ^ 2), Real.cos_le_one (a ^ 2),
      Real.neg_one_le_cos ξ, Real.cos_le_one ξ]
  have hq : |Real.cos (a ^ 2) - Real.cos (b ^ 2)| ≤ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [Real.neg_one_le_cos (a ^ 2), Real.cos_le_one (a ^ 2),
      Real.neg_one_le_cos (b ^ 2), Real.cos_le_one (b ^ 2)]
  let inner : ℝ :=
    (1 / a - 1 / b) * (Real.cos (a ^ 2) - Real.cos ξ) +
      1 / b * (Real.cos (a ^ 2) - Real.cos (b ^ 2))
  have hinner : |inner| ≤ 2 / a := by
    dsimp [inner]
    calc
      _ ≤ |(1 / a - 1 / b) * (Real.cos (a ^ 2) - Real.cos ξ)| +
          |1 / b * (Real.cos (a ^ 2) - Real.cos (b ^ 2))| := abs_add_le _ _
      _ = (1 / a - 1 / b) * |Real.cos (a ^ 2) - Real.cos ξ| +
          1 / b * |Real.cos (a ^ 2) - Real.cos (b ^ 2)| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hd, abs_of_nonneg hib]
      _ ≤ (1 / a - 1 / b) * 2 + 1 / b * 2 := by
            exact add_le_add (mul_le_mul_of_nonneg_left hp hd)
              (mul_le_mul_of_nonneg_left hq hib)
      _ = 2 / a := by ring
  unfold θValue correctedMeanValue
  change |a * ((1 / 2 : ℝ) * inner)| ≤ 1
  rw [abs_mul, abs_of_pos ha, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc
    a * (1 / 2 * |inner|) ≤ a * (1 / 2 * (2 / a)) := by
      gcongr
    _ = 1 := by field_simp [ha.ne']

theorem gap1 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    targetIntegral a b = transformedIntegral a b := by
  exact target_eq_transformed a b ha hab

theorem gap2 :
    AntitoneOn φ (Set.Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  unfold φ
  exact one_div_le_one_div_of_le (Real.sqrt_pos.2 hx)
    (Real.sqrt_le_sqrt hxy)

theorem gap3 (t : ℝ) (ht : 0 < t) :
    0 < φ t := by
  unfold φ
  positivity

theorem gap4 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ ξ ∈ Set.Icc (a ^ 2) (b ^ 2),
      transformedIntegral a b =
        (1 / 2 : ℝ) *
          ((1 / a - 1 / b) * (∫ t in a ^ 2..ξ, Real.sin t) +
            1 / b * ∫ t in a ^ 2..b ^ 2, Real.sin t) := by
  rcases exists_transformedMean a b ha hab with ⟨ξ, hξ, htarget⟩
  refine ⟨ξ, hξ, ?_⟩
  rw [htarget]
  unfold correctedMeanValue
  rw [integral_sin, integral_sin]

theorem gap5 (a b ξ : ℝ) :
    (1 / 2 : ℝ) *
        ((1 / a - 1 / b) * (∫ t in a ^ 2..ξ, Real.sin t) +
          1 / b * (∫ t in a ^ 2..b ^ 2, Real.sin t)) =
      correctedMeanValue a b ξ := by
  unfold correctedMeanValue
  rw [integral_sin, integral_sin]

theorem gap6 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ ξ ∈ Set.Icc (a ^ 2) (b ^ 2),
      transformedIntegral a b = correctedMeanValue a b ξ := by
  exact exists_transformedMean a b ha hab

theorem gap7 (a b ξ : ℝ) :
    correctedMeanValue a b ξ =
      (1 / 2 : ℝ) *
        ((1 / a - 1 / b) *
            (2 * Real.sin ((ξ + a ^ 2) / 2) *
              Real.sin ((ξ - a ^ 2) / 2)) +
          1 / b *
            (2 * Real.sin ((b ^ 2 + a ^ 2) / 2) *
              Real.sin ((b ^ 2 - a ^ 2) / 2))) := by
  unfold correctedMeanValue
  have h₁ : Real.cos (a ^ 2) - Real.cos ξ =
      2 * Real.sin ((ξ + a ^ 2) / 2) * Real.sin ((ξ - a ^ 2) / 2) := by
    rw [Real.cos_sub_cos]
    have hs : (a ^ 2 - ξ) / 2 = -((ξ - a ^ 2) / 2) := by ring
    rw [hs, Real.sin_neg]
    ring
  have h₂ : Real.cos (a ^ 2) - Real.cos (b ^ 2) =
      2 * Real.sin ((b ^ 2 + a ^ 2) / 2) *
        Real.sin ((b ^ 2 - a ^ 2) / 2) := by
    rw [Real.cos_sub_cos]
    have hs : (a ^ 2 - b ^ 2) / 2 = -((b ^ 2 - a ^ 2) / 2) := by ring
    rw [hs, Real.sin_neg]
    ring
  rw [h₁, h₂]

theorem gap8 (a b ξ : ℝ) (ha : a ≠ 0) :
    ∃ θ : ℝ, θ = θValue a b ξ ∧
      correctedMeanValue a b ξ = θ / a := by
  refine ⟨θValue a b ξ, rfl, ?_⟩
  unfold θValue
  field_simp [ha]

theorem gap9 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ ξ ∈ Set.Icc (a ^ 2) (b ^ 2), ∃ θ : ℝ,
      correctedMeanValue a b ξ = θ / a := by
  rcases gap6 a b ha hab with ⟨ξ, hξ, htarget⟩
  rcases gap8 a b ξ ha.ne' with ⟨θ, hθ, hcorr⟩
  exact ⟨ξ, hξ, θ, hcorr⟩

theorem gap10 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ ξ ∈ Set.Icc (a ^ 2) (b ^ 2), a ^ 2 ≤ ξ := by
  exact ⟨a ^ 2, ⟨le_rfl, (sq_lt_sq a b ha hab).le⟩, le_rfl⟩

theorem gap11 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ ξ ∈ Set.Icc (a ^ 2) (b ^ 2), ξ ≤ b ^ 2 := by
  exact ⟨b ^ 2, ⟨(sq_lt_sq a b ha hab).le, le_rfl⟩, le_rfl⟩

theorem gap12 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ ξ ∈ Set.Icc (a ^ 2) (b ^ 2), ∃ θ : ℝ,
      θ = θValue a b ξ ∧ |θ| ≤ 1 := by
  rcases gap6 a b ha hab with ⟨ξ, hξ, htarget⟩
  exact ⟨ξ, hξ, θValue a b ξ, rfl, theta_abs_le_one a b ξ ha hab⟩

theorem gap13 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ θ : ℝ, |θ| ≤ 1 ∧ targetIntegral a b = θ / a := by
  rcases gap6 a b ha hab with ⟨ξ, hξ, hmean⟩
  rcases gap8 a b ξ ha.ne' with ⟨θ, hθ, hcorr⟩
  refine ⟨θ, ?_, ?_⟩
  · rw [hθ]
    exact theta_abs_le_one a b ξ ha hab
  calc
    targetIntegral a b = transformedIntegral a b := gap1 a b ha hab
    _ = correctedMeanValue a b ξ := hmean
    _ = θ / a := hcorr

end

end ProofGap.Exercise2330
