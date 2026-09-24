import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise4385

noncomputable section

open scoped Interval

def sliceVolumeIntegral (a : ℝ) : ℝ :=
  ∫ v in -Real.pi / 2..Real.pi / 2,
    ∫ u in (0 : ℝ)..a * Real.cos v,
      (-u + a * Real.cos v) * u

def baseFlux : ℝ :=
  0

def sideFlux (a : ℝ) : ℝ :=
  ∫ v in -Real.pi / 2..Real.pi / 2,
    ∫ u in (0 : ℝ)..a * Real.cos v,
      a * u * Real.cos v

def totalBoundaryFlux (a : ℝ) : ℝ :=
  baseFlux + sideFlux a

def solidVolume (a : ℝ) : ℝ :=
  sliceVolumeIntegral a

private lemma integral_cos_cube :
    (∫ x in -Real.pi / 2..Real.pi / 2, Real.cos x ^ 3) = (4 / 3 : ℝ) := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt
        (fun y : ℝ => Real.sin y - (1 / 3) * Real.sin y ^ 3)
        (Real.cos x ^ 3) x := by
    intro x
    have hs : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
      linarith [Real.sin_sq_add_cos_sq x]
    convert (Real.hasDerivAt_sin x).sub
      (((Real.hasDerivAt_sin x).pow 3).const_mul (1 / 3)) using 1 <;>
      norm_num [hs] <;> ring
  calc
    (∫ x in -Real.pi / 2..Real.pi / 2, Real.cos x ^ 3) =
        (Real.sin (Real.pi / 2) - (1 / 3) * Real.sin (Real.pi / 2) ^ 3) -
          (Real.sin (-Real.pi / 2) - (1 / 3) * Real.sin (-Real.pi / 2) ^ 3) := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun y : ℝ => Real.sin y - (1 / 3) * Real.sin y ^ 3)
        (f' := fun y : ℝ => Real.cos y ^ 3)
        (fun x hx => hderiv x)
        ((Real.continuous_cos.pow 3).intervalIntegrable _ _)
    _ = 4 / 3 := by
      rw [show -Real.pi / 2 = -(Real.pi / 2) by ring,
        Real.sin_neg, Real.sin_pi_div_two]
      norm_num

private lemma sideFlux_formula (a : ℝ) :
    sideFlux a = 2 / 3 * a ^ 3 := by
  unfold sideFlux
  have hinner : ∀ v : ℝ,
      (∫ u in (0 : ℝ)..a * Real.cos v, a * u * Real.cos v) =
        (1 / 2) * a ^ 3 * Real.cos v ^ 3 := by
    intro v
    have hderiv : ∀ u : ℝ,
        HasDerivAt
          (fun t : ℝ => (a * Real.cos v / 2) * t ^ 2)
          (a * u * Real.cos v) u := by
      intro u
      convert (((hasDerivAt_id u).pow 2).const_mul
        (a * Real.cos v / 2)) using 1 <;>
        simp only [id_eq] <;> ring
    have hint : IntervalIntegrable
        (fun u : ℝ => a * u * Real.cos v) MeasureTheory.volume
        0 (a * Real.cos v) :=
      ((continuous_const.mul continuous_id).mul continuous_const).intervalIntegrable _ _
    calc
      (∫ u in (0 : ℝ)..a * Real.cos v, a * u * Real.cos v) =
          (a * Real.cos v / 2) * (a * Real.cos v) ^ 2 -
            (a * Real.cos v / 2) * (0 : ℝ) ^ 2 := by
        exact intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun t : ℝ => (a * Real.cos v / 2) * t ^ 2)
          (f' := fun u : ℝ => a * u * Real.cos v)
          (fun u hu => hderiv u) hint
      _ = (1 / 2) * a ^ 3 * Real.cos v ^ 3 := by ring
  simp_rw [hinner]
  rw [intervalIntegral.integral_const_mul, integral_cos_cube]
  ring

private lemma solidVolume_formula (a : ℝ) :
    solidVolume a = 2 / 9 * a ^ 3 := by
  unfold solidVolume sliceVolumeIntegral
  have hinner : ∀ v : ℝ,
      (∫ u in (0 : ℝ)..a * Real.cos v,
        (-u + a * Real.cos v) * u) =
          (1 / 6) * a ^ 3 * Real.cos v ^ 3 := by
    intro v
    have hderiv : ∀ u : ℝ,
        HasDerivAt
          (fun t : ℝ =>
            -(1 / 3) * t ^ 3 + (a * Real.cos v / 2) * t ^ 2)
          ((-u + a * Real.cos v) * u) u := by
      intro u
      convert ((((hasDerivAt_id u).pow 3).const_mul (-(1 / 3))).add
        (((hasDerivAt_id u).pow 2).const_mul
          (a * Real.cos v / 2))) using 1 <;>
        simp only [id_eq] <;> ring
    have hint : IntervalIntegrable
        (fun u : ℝ => (-u + a * Real.cos v) * u)
        MeasureTheory.volume 0 (a * Real.cos v) :=
      ((continuous_id.neg.add continuous_const).mul continuous_id).intervalIntegrable _ _
    calc
      (∫ u in (0 : ℝ)..a * Real.cos v,
          (-u + a * Real.cos v) * u) =
          (-(1 / 3) * (a * Real.cos v) ^ 3 +
              (a * Real.cos v / 2) * (a * Real.cos v) ^ 2) -
            (-(1 / 3) * (0 : ℝ) ^ 3 +
              (a * Real.cos v / 2) * (0 : ℝ) ^ 2) := by
        exact intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun t : ℝ =>
            -(1 / 3) * t ^ 3 + (a * Real.cos v / 2) * t ^ 2)
          (f' := fun u : ℝ => (-u + a * Real.cos v) * u)
          (fun u hu => hderiv u) hint
      _ = (1 / 6) * a ^ 3 * Real.cos v ^ 3 := by ring
  simp_rw [hinner]
  rw [intervalIntegral.integral_const_mul, integral_cos_cube]
  ring

theorem gap1 (a : ℝ) (ha : 0 < a) :
    solidVolume a = 1 / 3 * totalBoundaryFlux a := by
  unfold totalBoundaryFlux baseFlux
  rw [solidVolume_formula, sideFlux_formula]
  ring

theorem gap2 :
    baseFlux = 0 := by
  rfl

theorem gap3 (a : ℝ) (ha : 0 < a) :
    sideFlux a =
      ∫ v in -Real.pi / 2..Real.pi / 2,
        ∫ u in (0 : ℝ)..a * Real.cos v,
          a * u * Real.cos v := by
  rfl

theorem gap4 (a : ℝ) (ha : 0 < a) :
    sideFlux a = 2 / 3 * a ^ 3 := by
  exact sideFlux_formula a

theorem gap5 (a : ℝ) (ha : 0 < a) :
    solidVolume a = 2 / 9 * a ^ 3 := by
  exact solidVolume_formula a

theorem gap6 (a : ℝ) (ha : 0 < a) :
    0 < solidVolume a := by
  rw [solidVolume_formula]
  have hpow : 0 < a ^ 3 := pow_pos ha 3
  nlinarith

theorem gap7 (a : ℝ) (ha : 0 < a) :
    solidVolume a = 2 / 9 * a ^ 3 := by
  exact gap5 a ha

theorem gap8 (a : ℝ) (ha : 0 < a) :
    solidVolume a =
      ∫ v in -Real.pi / 2..Real.pi / 2,
        ∫ u in (0 : ℝ)..a * Real.cos v,
          (-u + a * Real.cos v) * u := by
  rfl

theorem gap9 (a : ℝ) (ha : 0 < a) :
    (∫ v in -Real.pi / 2..Real.pi / 2,
      ∫ u in (0 : ℝ)..a * Real.cos v,
        (-u + a * Real.cos v) * u) =
      2 / 9 * a ^ 3 := by
  simpa [solidVolume, sliceVolumeIntegral] using solidVolume_formula a

theorem gap10 (a : ℝ) (ha : 0 < a) :
    solidVolume a = 2 / 9 * a ^ 3 := by
  exact gap7 a ha

end

end ProofGap.Exercise4385
