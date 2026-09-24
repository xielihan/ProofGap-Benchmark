import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4365

noncomputable section

open scoped Interval

def unitRadialIntegral : ℝ :=
  ∫ r in (0 : ℝ)..1, r / Real.sqrt (1 - r ^ 2)

def zFlux (a b c : ℝ) : ℝ :=
  2 * a * b / c *
    ∫ φ in (0 : ℝ)..2 * Real.pi, unitRadialIntegral

def xFlux (a b c : ℝ) : ℝ :=
  2 * b * c / a *
    ∫ φ in (0 : ℝ)..2 * Real.pi, unitRadialIntegral

def yFlux (a b c : ℝ) : ℝ :=
  2 * a * c / b *
    ∫ φ in (0 : ℝ)..2 * Real.pi, unitRadialIntegral

def totalFlux (a b c : ℝ) : ℝ :=
  xFlux a b c + yFlux a b c + zFlux a b c

private def radialReal (r : ℝ) : ℝ :=
  r / Real.sqrt (1 - r ^ 2)

private theorem radial_derivative
    (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun x : ℝ => -Real.sqrt (1 - x ^ 2))
      (radialReal r) r := by
  have hpos : 0 < 1 - r ^ 2 := by
    have hrsq : r ^ 2 < (1 : ℝ) ^ 2 :=
      (sq_lt_sq₀ hr.1.le zero_le_one).2 hr.2
    nlinarith
  have hinner :
      HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * r) r := by
    convert (hasDerivAt_const r 1).sub ((hasDerivAt_id r).pow 2)
      using 1 <;> simp only [id_eq] <;> ring
  have hsqrt :
      HasDerivAt (fun x : ℝ => Real.sqrt (1 - x ^ 2))
        (1 / (2 * Real.sqrt (1 - r ^ 2)) * (-2 * r)) r := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_sqrt hpos.ne').comp r hinner
  unfold radialReal
  convert hsqrt.neg using 1
  field_simp [Real.sqrt_ne_zero'.mpr hpos]

private theorem radial_intervalIntegrable :
    IntervalIntegrable radialReal MeasureTheory.volume (0 : ℝ) 1 := by
  let F : ℝ → ℝ := fun x => -Real.sqrt (1 - x ^ 2)
  have hcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
    unfold F
    fun_prop
  have hder : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt F (radialReal r) r := by
    intro r hr
    exact radial_derivative r hr
  have hpos : ∀ r ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ radialReal r := by
    intro r hr
    unfold radialReal
    exact div_nonneg hr.1.le (Real.sqrt_nonneg _)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact intervalIntegral.integrableOn_deriv_of_nonneg hcont hder hpos

private theorem unitRadialIntegral_value :
    unitRadialIntegral = 1 := by
  let F : ℝ → ℝ := fun x => -Real.sqrt (1 - x ^ 2)
  have hcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
    unfold F
    fun_prop
  have hder : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt F (radialReal r) r := by
    intro r hr
    exact radial_derivative r hr
  have hFTC :
      (∫ r in (0 : ℝ)..1, radialReal r) = F 1 - F 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      zero_le_one hcont hder radial_intervalIntegrable
  unfold unitRadialIntegral
  change (∫ r in (0 : ℝ)..1, radialReal r) = 1
  rw [hFTC]
  norm_num [F]

private theorem constantRadialIntegral :
    (∫ _φ in (0 : ℝ)..2 * Real.pi, unitRadialIntegral) =
      2 * Real.pi := by
  rw [unitRadialIntegral_value]
  norm_num [intervalIntegral.integral_const]

theorem gap1 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    zFlux a b c =
      2 * a * b / c *
        ∫ φ in (0 : ℝ)..2 * Real.pi,
          ∫ r in (0 : ℝ)..1, r / Real.sqrt (1 - r ^ 2) := by
  rfl

theorem gap2 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    zFlux a b c = 4 * Real.pi * a * b / c := by
  unfold zFlux
  rw [constantRadialIntegral]
  ring

theorem gap3 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    xFlux a b c = 4 * Real.pi * b * c / a := by
  unfold xFlux
  rw [constantRadialIntegral]
  ring

theorem gap4 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    yFlux a b c = 4 * Real.pi * a * c / b := by
  unfold yFlux
  rw [constantRadialIntegral]
  ring

theorem gap5 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    totalFlux a b c =
      4 * Real.pi *
        (b * c / a + a * c / b + a * b / c) := by
  rw [totalFlux, gap2 a b c ha hb hc, gap3 a b c ha hb hc,
    gap4 a b c ha hb hc]
  ring

end

end ProofGap.Exercise4365
