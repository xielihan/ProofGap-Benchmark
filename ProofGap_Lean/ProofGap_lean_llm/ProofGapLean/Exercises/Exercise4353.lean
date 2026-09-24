import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise4353

noncomputable section

open scoped Interval

def upperHemisphere : ℝ → Set (ℝ × (ℝ × ℝ)) :=
  fun a =>
    {p |
      p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 = a ^ 2 ∧
        0 ≤ p.2.2}

def polarInertiaIntegral (a : ℝ) : ℝ :=
  ∫ φ in (0 : ℝ)..2 * Real.pi,
    ∫ r in (0 : ℝ)..a,
      a * r ^ 3 / Real.sqrt (a ^ 2 - r ^ 2)

def momentOfInertia (a ρ₀ : ℝ) : ℝ :=
  ρ₀ * polarInertiaIntegral a

private lemma private_sine_cube_integral :
    (∫ θ in (0 : ℝ)..Real.pi / 2, Real.sin θ ^ 3) = (2 / 3 : ℝ) := by
  let F : ℝ → ℝ := fun x => -Real.cos x + Real.cos x ^ 3 / 3
  have hF : ∀ x : ℝ, HasDerivAt F (Real.sin x ^ 3) x := by
    intro x
    have hc := Real.hasDerivAt_cos x
    have h := hc.neg.add ((hc.pow 3).const_mul (1 / 3 : ℝ))
    convert h using 1
    · ext y
      simp [F]
      ring
    · have hmul :
          Real.sin x ^ 3 + Real.sin x * Real.cos x ^ 2 = Real.sin x := by
        calc
          Real.sin x ^ 3 + Real.sin x * Real.cos x ^ 2 =
              Real.sin x * (Real.sin x ^ 2 + Real.cos x ^ 2) := by ring
          _ = Real.sin x := by rw [Real.sin_sq_add_cos_sq]; ring
      norm_num <;> nlinarith [hmul]
  have hint : IntervalIntegrable
      (fun θ : ℝ => Real.sin θ ^ 3) MeasureTheory.volume
      (0 : ℝ) (Real.pi / 2) :=
    (Real.continuous_sin.pow 3).intervalIntegrable
      (0 : ℝ) (Real.pi / 2)
  calc
    (∫ θ in (0 : ℝ)..Real.pi / 2, Real.sin θ ^ 3) = F (Real.pi / 2) - F 0 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x _
        exact hF x
      · exact hint
    _ = (2 / 3 : ℝ) := by
      simp [F, Real.cos_pi_div_two]
      ring

private lemma private_radial_integral (a : ℝ) (ha : 0 < a) :
    (∫ r in (0 : ℝ)..a,
      a * r ^ 3 / Real.sqrt (a ^ 2 - r ^ 2)) =
      (2 / 3 : ℝ) * a ^ 4 := by
  let F : ℝ → ℝ := fun r =>
    -a ^ 3 * Real.sqrt (a ^ 2 - r ^ 2) +
      (a / 3) * Real.sqrt (a ^ 2 - r ^ 2) ^ 3
  have hFcont : Continuous F := by
    dsimp [F]
    continuity
  have hFderiv : ∀ r ∈ Set.Ioo (0 : ℝ) a,
      HasDerivAt F (a * r ^ 3 / Real.sqrt (a ^ 2 - r ^ 2)) r := by
    intro r hr
    have hpos : 0 < a ^ 2 - r ^ 2 := by
      have hm : 0 < (a - r) * (a + r) :=
        mul_pos (sub_pos.mpr hr.2) (add_pos ha hr.1)
      nlinarith
    have hinner : HasDerivAt (fun x : ℝ => a ^ 2 - x ^ 2) (-2 * r) r := by
      convert (hasDerivAt_const r (a ^ 2)).sub ((hasDerivAt_id r).pow 2) using 1 <;>
        simp <;> ring
    have hs := (Real.hasDerivAt_sqrt hpos.ne').comp r hinner
    have hsquare : Real.sqrt (a ^ 2 - r ^ 2) ^ 2 = a ^ 2 - r ^ 2 :=
      Real.sq_sqrt hpos.le
    have h := (hs.const_mul (-a ^ 3)).add ((hs.pow 3).const_mul (a / 3))
    convert h using 1
    · dsimp [F]
      rw [hsquare]
      ring
  have hint : IntervalIntegrable
      (fun r : ℝ => a * r ^ 3 / Real.sqrt (a ^ 2 - r ^ 2))
      MeasureTheory.volume 0 a := by
    refine intervalIntegral.intervalIntegrable_deriv_of_nonneg
      hFcont.continuousOn ?_ ?_
    · intro r hr
      apply hFderiv r
      simpa [min_eq_left ha.le, max_eq_right ha.le] using hr
    · intro r hr
      have hr' : r ∈ Set.Ioo (0 : ℝ) a := by
        simpa [min_eq_left ha.le, max_eq_right ha.le] using hr
      exact div_nonneg
        (mul_nonneg ha.le (pow_nonneg hr'.1.le 3))
        (Real.sqrt_nonneg _)
  calc
    (∫ r in (0 : ℝ)..a,
        a * r ^ 3 / Real.sqrt (a ^ 2 - r ^ 2)) = F a - F 0 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha.le hFcont.continuousOn
      · intro r hr
        exact hFderiv r hr
      · exact hint
    _ = (2 / 3 : ℝ) * a ^ 4 := by
      have hsqa : Real.sqrt (a ^ 2) = a := by
        rw [Real.sqrt_sq_eq_abs, abs_of_pos ha]
      simp [F, hsqa]
      ring

theorem gap1 (a ρ₀ : ℝ) :
    momentOfInertia a ρ₀ =
      ρ₀ * polarInertiaIntegral a := by
  rfl

theorem gap2 (a ρ₀ : ℝ) :
    ρ₀ * polarInertiaIntegral a =
      ρ₀ *
        (∫ φ in (0 : ℝ)..2 * Real.pi,
          ∫ r in (0 : ℝ)..a,
            a * r ^ 3 / Real.sqrt (a ^ 2 - r ^ 2)) := by
  rfl

theorem gap3 (a ρ₀ : ℝ) (ha : 0 < a) :
    ρ₀ *
        (∫ φ in (0 : ℝ)..2 * Real.pi,
          ∫ r in (0 : ℝ)..a,
            a * r ^ 3 / Real.sqrt (a ^ 2 - r ^ 2)) =
      ρ₀ * polarInertiaIntegral a := by
  rfl

theorem gap4 (a ρ₀ : ℝ) (ha : 0 < a) :
    momentOfInertia a ρ₀ = ρ₀ * polarInertiaIntegral a := by
  rfl

theorem gap5 (a ρ₀ : ℝ) (ha : 0 < a) :
    momentOfInertia a ρ₀ =
      2 * Real.pi * a ^ 4 * ρ₀ *
        (∫ θ in (0 : ℝ)..Real.pi / 2, Real.sin θ ^ 3) := by
  rw [gap1, polarInertiaIntegral]
  rw [intervalIntegral.integral_const]
  rw [private_radial_integral a ha, private_sine_cube_integral]
  simp only [smul_eq_mul]
  ring

theorem gap6 (a ρ₀ : ℝ) (ha : 0 < a) :
    momentOfInertia a ρ₀ =
      (4 / 3 : ℝ) * Real.pi * a ^ 4 * ρ₀ := by
  rw [gap5 a ρ₀ ha, private_sine_cube_integral]
  ring

end

end ProofGap.Exercise4353
