import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise4357

noncomputable section

open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def observationPoint : Vec3 :=
  (0, 0, 0)

def surfaceAreaBand (r : ℝ) : ℝ :=
  2 * Real.sqrt 2 * Real.pi * r

def coneHeight (r : ℝ) : ℝ :=
  r

def verticalForceDensity (k m ρ₀ r : ℝ) : ℝ :=
  k * Real.pi * m * ρ₀ / r

def forceX : ℝ :=
  0

def forceY : ℝ :=
  0

def forceZ (a b k m ρ₀ : ℝ) : ℝ :=
  ∫ r in b..a, verticalForceDensity k m ρ₀ r

def forceVector (a b k m ρ₀ : ℝ) : Vec3 :=
  (forceX, forceY, forceZ a b k m ρ₀)

theorem gap1 :
    observationPoint = (0, 0, 0) := by
  rfl

theorem gap2 (r : ℝ) :
    surfaceAreaBand r = 2 * Real.sqrt 2 * Real.pi * r := by
  rfl

theorem gap3 :
    forceX = 0 := by
  rfl

theorem gap4 :
    forceY = 0 := by
  rfl

theorem gap5 (a b k m ρ₀ r : ℝ)
    (hb : 0 < b) (hba : b ≤ r) (hra : r ≤ a) :
    k * m * surfaceAreaBand r * ρ₀ /
          (r ^ 2 + coneHeight r ^ 2) *
          (coneHeight r / Real.sqrt (r ^ 2 + coneHeight r ^ 2)) =
      verticalForceDensity k m ρ₀ r := by
  have hr : 0 < r := lt_of_lt_of_le hb hba
  have hroot :
      Real.sqrt (r ^ 2 + r ^ 2) = Real.sqrt 2 * r := by
    have hsquare :
        Real.sqrt (r ^ 2 + r ^ 2) ^ 2 = r ^ 2 + r ^ 2 :=
      Real.sq_sqrt (by nlinarith [sq_nonneg r])
    have hprod :
        (Real.sqrt 2 * r) ^ 2 = r ^ 2 + r ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    have hleft : 0 ≤ Real.sqrt (r ^ 2 + r ^ 2) := Real.sqrt_nonneg _
    have hright : 0 ≤ Real.sqrt 2 * r :=
      mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hr)
    nlinarith
  have hsum : r ^ 2 + r ^ 2 = 2 * r ^ 2 := by
    ring
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  unfold surfaceAreaBand coneHeight verticalForceDensity
  rw [hroot, hsum]
  field_simp [hr.ne', hsqrt2.ne']

theorem gap6 (a b k m ρ₀ r : ℝ)
    (hb : 0 < b) (hba : b ≤ r) (hra : r ≤ a) :
    verticalForceDensity k m ρ₀ r =
      k * Real.pi * m * ρ₀ / r := by
  rfl

theorem gap7 (a b k m ρ₀ : ℝ) (hb : 0 < b) (hba : b ≤ a) :
    forceZ a b k m ρ₀ =
      ∫ r in b..a, k * Real.pi * m * ρ₀ / r := by
  rfl

theorem gap8 (a b k m ρ₀ : ℝ) (hb : 0 < b) (hba : b ≤ a) :
    (∫ r in b..a, k * Real.pi * m * ρ₀ / r) =
      k * Real.pi * m * ρ₀ * Real.log (a / b) := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have hpos : ∀ x ∈ Set.uIcc b a, 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le hba] at hx
    exact lt_of_lt_of_le hb hx.1
  have hderiv : ∀ x ∈ Set.uIcc b a,
      HasDerivAt Real.log x⁻¹ x := by
    intro x hx
    exact Real.hasDerivAt_log (ne_of_gt (hpos x hx))
  have hcont : ContinuousOn (fun x : ℝ => x⁻¹) (Set.uIcc b a) := by
    intro x hx
    exact (continuousAt_id.inv₀ (ne_of_gt (hpos x hx))).continuousWithinAt
  have hinv :
      (∫ r in b..a, r⁻¹) = Real.log a - Real.log b := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      hderiv hcont.intervalIntegrable
  calc
    (∫ r in b..a, k * Real.pi * m * ρ₀ / r) =
        ∫ r in b..a, (k * Real.pi * m * ρ₀) * r⁻¹ := by
      apply intervalIntegral.integral_congr
      intro r _
      rw [div_eq_mul_inv]
    _ = (k * Real.pi * m * ρ₀) * (∫ r in b..a, r⁻¹) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (k * Real.pi * m * ρ₀) *
        (Real.log a - Real.log b) := by
      exact congrArg (fun x : ℝ => (k * Real.pi * m * ρ₀) * x) hinv
    _ = k * Real.pi * m * ρ₀ * Real.log (a / b) := by
      rw [Real.log_div ha.ne' hb.ne']

theorem gap9 (a b k m ρ₀ : ℝ) (hb : 0 < b) (hba : b ≤ a) :
    forceZ a b k m ρ₀ =
      k * Real.pi * m * ρ₀ * Real.log (a / b) := by
  calc
    forceZ a b k m ρ₀ =
        ∫ r in b..a, k * Real.pi * m * ρ₀ / r :=
      gap7 a b k m ρ₀ hb hba
    _ = k * Real.pi * m * ρ₀ * Real.log (a / b) :=
      gap8 a b k m ρ₀ hb hba

theorem gap10 (a b k m ρ₀ : ℝ) (hb : 0 < b) (hba : b ≤ a) :
    forceVector a b k m ρ₀ =
      (0, 0, k * Real.pi * m * ρ₀ * Real.log (a / b)) := by
  unfold forceVector
  rw [gap3, gap4, gap9 a b k m ρ₀ hb hba]

end

end ProofGap.Exercise4357
