import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open scoped Interval

namespace ProofGap.Exercise2449

noncomputable section

def radius (p φ : ℝ) : ℝ := p / (1 + Real.cos φ)

def radiusDeriv (p φ : ℝ) : ℝ :=
  p * Real.sin φ / (1 + Real.cos φ) ^ 2

def polarSpeed (p φ : ℝ) : ℝ :=
  Real.sqrt (radius p φ ^ 2 + radiusDeriv p φ ^ 2)

def sec (x : ℝ) : ℝ := 1 / Real.cos x

def arcLength (p : ℝ) : ℝ :=
  ∫ φ in -(Real.pi / 2)..(Real.pi / 2), polarSpeed p φ

private def secHalfPrimitive (x : ℝ) : ℝ :=
  sec (x / 2) * Real.tan (x / 2) +
    Real.log (sec (x / 2) + Real.tan (x / 2))

private theorem hasDerivAt_secHalfPrimitive (x : ℝ)
    (hx₀ : -(Real.pi / 2) ≤ x) (hx₁ : x ≤ Real.pi / 2) :
    HasDerivAt secHalfPrimitive (sec (x / 2) ^ 3) x := by
  let t : ℝ := x / 2
  have ht₀ : -(Real.pi / 2) < t := by
    dsimp [t]
    nlinarith [Real.pi_pos]
  have ht₁ : t < Real.pi / 2 := by
    dsimp [t]
    nlinarith [Real.pi_pos]
  have hc : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨ht₀, ht₁⟩
  have hcne : Real.cos t ≠ 0 := ne_of_gt hc
  have hinner : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) x := by
    convert (hasDerivAt_id x).div_const 2 using 1 <;> norm_num
  have hsec₀ : HasDerivAt sec (Real.sin t / Real.cos t ^ 2) t := by
    unfold sec
    convert (hasDerivAt_const t 1).div (Real.hasDerivAt_cos t) hcne using 1 <;>
      field_simp [hcne] <;> ring
  have htan₀ : HasDerivAt Real.tan (1 / Real.cos t ^ 2) t :=
    Real.hasDerivAt_tan hcne
  have hsec := hsec₀.comp x hinner
  have htan := htan₀.comp x hinner
  have hsplus : 0 < 1 + Real.sin t := by
    nlinarith [Real.sin_sq_add_cos_sq t, sq_pos_of_pos hc]
  have hsumpos : 0 < sec t + Real.tan t := by
    unfold sec
    rw [Real.tan_eq_sin_div_cos, ← add_div]
    exact div_pos hsplus hc
  have hlog :=
    (Real.hasDerivAt_log hsumpos.ne').comp x (hsec.add htan)
  have hall := (hsec.mul htan).add hlog
  have hcoef :
      sec t ^ 3 =
        Real.sin t / Real.cos t ^ 2 * (1 / 2) * Real.tan t +
          sec t * (1 / Real.cos t ^ 2 * (1 / 2)) +
        (sec t + Real.tan t)⁻¹ *
          (Real.sin t / Real.cos t ^ 2 * (1 / 2) +
            1 / Real.cos t ^ 2 * (1 / 2)) := by
    unfold sec
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcne, hsplus.ne'] <;>
      nlinarith [Real.sin_sq_add_cos_sq t]
  convert hall using 1

private theorem integral_secHalfCube :
    (∫ φ in -(Real.pi / 2)..(Real.pi / 2), sec (φ / 2) ^ 3) =
      2 * (Real.sqrt 2 + Real.log (Real.sqrt 2 + 1)) := by
  have hab : -(Real.pi / 2) ≤ Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hderiv : ∀ x ∈ Set.uIcc (-(Real.pi / 2)) (Real.pi / 2),
      HasDerivAt secHalfPrimitive (sec (x / 2) ^ 3) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact hasDerivAt_secHalfPrimitive x hx.1 hx.2
  have hcont : ContinuousOn (fun x : ℝ => sec (x / 2) ^ 3)
      (Set.uIcc (-(Real.pi / 2)) (Real.pi / 2)) := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have ht₀ : -(Real.pi / 2) < x / 2 := by
      have hlow := hx.1
      ring_nf at hlow ⊢
      nlinarith [Real.pi_pos]
    have ht₁ : x / 2 < Real.pi / 2 := by
      have hupp := hx.2
      ring_nf at hupp ⊢
      nlinarith [Real.pi_pos]
    have hc : 0 < Real.cos (x / 2) :=
      Real.cos_pos_of_mem_Ioo ⟨ht₀, ht₁⟩
    have harg : ContinuousAt (fun y : ℝ => y / 2) x :=
      continuousAt_id.div_const (2 : ℝ)
    have hcos : ContinuousAt (fun y : ℝ => Real.cos (y / 2)) x :=
      Real.continuous_cos.continuousAt.comp harg
    have hone : ContinuousAt (fun _ : ℝ => (1 : ℝ)) x :=
      continuousAt_const
    unfold sec
    exact ((hone.div hcos (ne_of_gt hc)).pow 3).continuousWithinAt
  have hFTC :
      (∫ φ in -(Real.pi / 2)..(Real.pi / 2), sec (φ / 2) ^ 3) =
        secHalfPrimitive (Real.pi / 2) -
          secHalfPrimitive (-(Real.pi / 2)) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      hderiv hcont.intervalIntegrable
  rw [hFTC]
  have hb : (Real.pi / 2) / 2 = Real.pi / 4 := by ring
  have ha : (-(Real.pi / 2)) / 2 = -(Real.pi / 4) := by ring
  have hsqrt : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsqrtpos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsecval : 1 / (Real.sqrt 2 / 2) = Real.sqrt 2 := by
    field_simp [ne_of_gt hsqrtpos]
    nlinarith
  have hplus : Real.sqrt 2 + 1 ≠ 0 := by positivity
  have hrecip :
      Real.sqrt 2 - 1 = (Real.sqrt 2 + 1)⁻¹ := by
    field_simp [hplus] <;> nlinarith [hsqrt]
  have hlog :
      Real.log (Real.sqrt 2 - 1) =
        -Real.log (Real.sqrt 2 + 1) := by
    rw [hrecip, Real.log_inv]
  simp only [secHalfPrimitive, hb, ha, sec, Real.cos_neg, Real.tan_neg,
    Real.cos_pi_div_four, Real.tan_pi_div_four, hsecval]
  have hminus : Real.sqrt 2 + -1 = Real.sqrt 2 - 1 := by ring
  rw [hminus, hlog]
  ring

theorem gap1 (p φ : ℝ) (hφ₀ : -(Real.pi / 2) ≤ φ)
    (hφ₁ : φ ≤ Real.pi / 2) :
    deriv (radius p) φ = radiusDeriv p φ := by
  have hcos : 0 ≤ Real.cos φ :=
    Real.cos_nonneg_of_mem_Icc ⟨hφ₀, hφ₁⟩
  have hden : 1 + Real.cos φ ≠ 0 := by
    nlinarith
  unfold radius radiusDeriv
  simpa using
    (((hasDerivAt_const φ p).div
      ((hasDerivAt_const φ 1).add (Real.hasDerivAt_cos φ)) hden).deriv)

theorem gap2 (p φ : ℝ) (hp : 0 ≤ p)
    (hφ₀ : -(Real.pi / 2) ≤ φ) (hφ₁ : φ ≤ Real.pi / 2) :
    polarSpeed p φ =
      2 * p * Real.cos (φ / 2) / (1 + Real.cos φ) ^ 2 := by
  have hcos : 0 ≤ Real.cos φ :=
    Real.cos_nonneg_of_mem_Icc ⟨hφ₀, hφ₁⟩
  have hden : 1 + Real.cos φ ≠ 0 := by
    nlinarith
  have hhalf₀ : -(Real.pi / 2) ≤ φ / 2 := by
    nlinarith [Real.pi_pos]
  have hhalf₁ : φ / 2 ≤ Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hhalfcos : 0 ≤ Real.cos (φ / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨hhalf₀, hhalf₁⟩
  have hdouble :
      Real.cos φ = 2 * Real.cos (φ / 2) ^ 2 - 1 := by
    convert Real.cos_two_mul (φ / 2) using 1 <;> ring
  have htrig :
      (1 + Real.cos φ) ^ 2 + Real.sin φ ^ 2 =
        4 * Real.cos (φ / 2) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq φ]
  have hsquare :
      radius p φ ^ 2 + radiusDeriv p φ ^ 2 =
        (2 * p * Real.cos (φ / 2) / (1 + Real.cos φ) ^ 2) ^ 2 := by
    unfold radius radiusDeriv
    field_simp [hden]
    rw [htrig]
    ring
  unfold polarSpeed
  rw [hsquare, Real.sqrt_sq]
  positivity

theorem gap3 (p s : ℝ) (hs : s = arcLength p) :
    s = ∫ φ in -(Real.pi / 2)..(Real.pi / 2),
      polarSpeed p φ := by
  simpa [arcLength] using hs

theorem gap4 (p s : ℝ) (hp : 0 ≤ p) (hs : s = arcLength p) :
    s = p / 2 * ∫ φ in -(Real.pi / 2)..(Real.pi / 2),
      sec (φ / 2) ^ 3 := by
  rw [hs]
  unfold arcLength
  calc
    (∫ φ in -(Real.pi / 2)..(Real.pi / 2), polarSpeed p φ) =
        ∫ φ in -(Real.pi / 2)..(Real.pi / 2),
          p / 2 * sec (φ / 2) ^ 3 := by
      apply intervalIntegral.integral_congr
      intro φ hφ
      have hab : -(Real.pi / 2) ≤ Real.pi / 2 := by
        nlinarith [Real.pi_pos]
      rw [Set.uIcc_of_le hab] at hφ
      have hspeed := gap2 p φ hp hφ.1 hφ.2
      have hhalf₀ : -(Real.pi / 2) < φ / 2 := by
        have hlow := hφ.1
        ring_nf at hlow ⊢
        nlinarith [Real.pi_pos]
      have hhalf₁ : φ / 2 < Real.pi / 2 := by
        have hupp := hφ.2
        ring_nf at hupp ⊢
        nlinarith [Real.pi_pos]
      have hc : 0 < Real.cos (φ / 2) :=
        Real.cos_pos_of_mem_Ioo ⟨hhalf₀, hhalf₁⟩
      have hdouble :
          Real.cos φ = 2 * Real.cos (φ / 2) ^ 2 - 1 := by
        convert Real.cos_two_mul (φ / 2) using 1 <;> ring
      rw [hspeed]
      unfold sec
      have hidentity :
          1 + Real.cos φ = 2 * Real.cos (φ / 2) ^ 2 := by
        nlinarith
      rw [hidentity]
      field_simp [ne_of_gt hc] <;> ring
    _ = p / 2 * ∫ φ in -(Real.pi / 2)..(Real.pi / 2),
          sec (φ / 2) ^ 3 := by
      rw [intervalIntegral.integral_const_mul]

theorem gap5 (p s : ℝ) (hp : 0 ≤ p) (hs : s = arcLength p) :
    s = p * (Real.sqrt 2 + Real.log (Real.sqrt 2 + 1)) := by
  rw [gap4 p s hp hs, integral_secHalfCube]
  ring

end

end ProofGap.Exercise2449
