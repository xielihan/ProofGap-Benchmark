import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4049

noncomputable section

open MeasureTheory
open scoped Interval

def xCoord (a b phi psi : ℝ) : ℝ :=
  (b + a * Real.cos psi) * Real.cos phi

def yCoord (a b phi psi : ℝ) : ℝ :=
  (b + a * Real.cos psi) * Real.sin phi

def zCoord (a psi : ℝ) : ℝ :=
  a * Real.sin psi

def E (a b phi psi : ℝ) : ℝ :=
  deriv (fun t => xCoord a b t psi) phi ^ 2 +
    deriv (fun t => yCoord a b t psi) phi ^ 2 +
    deriv (fun _ => zCoord a psi) phi ^ 2

def G (a b phi psi : ℝ) : ℝ :=
  deriv (fun t => xCoord a b phi t) psi ^ 2 +
    deriv (fun t => yCoord a b phi t) psi ^ 2 +
    deriv (zCoord a) psi ^ 2

def F (a b phi psi : ℝ) : ℝ :=
  deriv (fun t => xCoord a b t psi) phi *
      deriv (fun t => xCoord a b phi t) psi +
    deriv (fun t => yCoord a b t psi) phi *
      deriv (fun t => yCoord a b phi t) psi +
    deriv (fun _ => zCoord a psi) phi * deriv (zCoord a) psi

def patchArea (a b phi₁ phi₂ psi₁ psi₂ : ℝ) : ℝ :=
  ∫ phi in phi₁..phi₂,
    ∫ psi in psi₁..psi₂,
      Real.sqrt (E a b phi psi * G a b phi psi - F a b phi psi ^ 2)

def totalArea (a b : ℝ) : ℝ :=
  patchArea a b 0 (2 * Real.pi) (-Real.pi) Real.pi

private theorem integral_torus_density
    (a b phi₁ phi₂ psi₁ psi₂ : ℝ) :
    (∫ phi in phi₁..phi₂,
        ∫ psi in psi₁..psi₂, a * (b + a * Real.cos psi)) =
      a * (phi₂ - phi₁) *
        (b * (psi₂ - psi₁) +
          a * (Real.sin psi₂ - Real.sin psi₁)) := by
  have hinner :
      (∫ psi in psi₁..psi₂, a * (b + a * Real.cos psi)) =
        a * b * (psi₂ - psi₁) +
          a ^ 2 * (Real.sin psi₂ - Real.sin psi₁) := by
    have hderiv : ∀ psi ∈ Set.uIcc psi₁ psi₂,
        HasDerivAt
          (fun t : ℝ => a * b * t + a ^ 2 * Real.sin t)
          (a * (b + a * Real.cos psi)) psi := by
      intro psi _
      convert
        (((hasDerivAt_id psi).const_mul (a * b)).add
          ((Real.hasDerivAt_sin psi).const_mul (a ^ 2))) using 1 <;> ring
    have hint : IntervalIntegrable
        (fun psi : ℝ => a * (b + a * Real.cos psi)) volume psi₁ psi₂ := by
      apply Continuous.intervalIntegrable
      fun_prop
    calc
      (∫ psi in psi₁..psi₂, a * (b + a * Real.cos psi)) =
          (a * b * psi₂ + a ^ 2 * Real.sin psi₂) -
            (a * b * psi₁ + a ^ 2 * Real.sin psi₁) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
      _ = a * b * (psi₂ - psi₁) +
            a ^ 2 * (Real.sin psi₂ - Real.sin psi₁) := by ring
  rw [hinner, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem gap1 (a b phi psi : ℝ) :
    E a b phi psi =
      deriv (fun t => xCoord a b t psi) phi ^ 2 +
        deriv (fun t => yCoord a b t psi) phi ^ 2 +
        deriv (fun _ => zCoord a psi) phi ^ 2 := by
  rfl

theorem gap2 (a b phi psi : ℝ) :
    deriv (fun t => xCoord a b t psi) phi ^ 2 +
        deriv (fun t => yCoord a b t psi) phi ^ 2 +
        deriv (fun _ => zCoord a psi) phi ^ 2 =
      (b + a * Real.cos psi) ^ 2 := by
  have hx : HasDerivAt (fun t : ℝ => xCoord a b t psi)
      ((b + a * Real.cos psi) * (-Real.sin phi)) phi := by
    simpa [xCoord] using
      (Real.hasDerivAt_cos phi).const_mul (b + a * Real.cos psi)
  have hy : HasDerivAt (fun t : ℝ => yCoord a b t psi)
      ((b + a * Real.cos psi) * Real.cos phi) phi := by
    simpa [yCoord] using
      (Real.hasDerivAt_sin phi).const_mul (b + a * Real.cos psi)
  have hz : HasDerivAt (fun _ : ℝ => zCoord a psi) 0 phi :=
    hasDerivAt_const phi (zCoord a psi)
  rw [hx.deriv, hy.deriv, hz.deriv]
  calc
    ((b + a * Real.cos psi) * (-Real.sin phi)) ^ 2 +
          ((b + a * Real.cos psi) * Real.cos phi) ^ 2 + 0 ^ 2 =
        (b + a * Real.cos psi) ^ 2 *
          (Real.sin phi ^ 2 + Real.cos phi ^ 2) := by ring
    _ = (b + a * Real.cos psi) ^ 2 := by
      rw [Real.sin_sq_add_cos_sq]
      ring

theorem gap3 (a b phi psi : ℝ) :
    E a b phi psi = (b + a * Real.cos psi) ^ 2 := by
  rw [gap1, gap2]

theorem gap4 (a b phi psi : ℝ) :
    G a b phi psi =
      deriv (fun t => xCoord a b phi t) psi ^ 2 +
        deriv (fun t => yCoord a b phi t) psi ^ 2 +
        deriv (zCoord a) psi ^ 2 := by
  rfl

theorem gap5 (a b phi psi : ℝ) :
    deriv (fun t => xCoord a b phi t) psi ^ 2 +
        deriv (fun t => yCoord a b phi t) psi ^ 2 +
        deriv (zCoord a) psi ^ 2 =
      a ^ 2 := by
  have hx : HasDerivAt (fun t : ℝ => xCoord a b phi t)
      ((a * (-Real.sin psi)) * Real.cos phi) psi := by
    simpa [xCoord] using
      (((hasDerivAt_const psi b).add
        ((Real.hasDerivAt_cos psi).const_mul a)).mul_const (Real.cos phi))
  have hy : HasDerivAt (fun t : ℝ => yCoord a b phi t)
      ((a * (-Real.sin psi)) * Real.sin phi) psi := by
    simpa [yCoord] using
      (((hasDerivAt_const psi b).add
        ((Real.hasDerivAt_cos psi).const_mul a)).mul_const (Real.sin phi))
  have hz : HasDerivAt (zCoord a) (a * Real.cos psi) psi := by
    simpa [zCoord] using (Real.hasDerivAt_sin psi).const_mul a
  rw [hx.deriv, hy.deriv, hz.deriv]
  calc
    ((a * (-Real.sin psi)) * Real.cos phi) ^ 2 +
          ((a * (-Real.sin psi)) * Real.sin phi) ^ 2 +
          (a * Real.cos psi) ^ 2 =
        a ^ 2 * ((Real.sin phi ^ 2 + Real.cos phi ^ 2) *
          Real.sin psi ^ 2 + Real.cos psi ^ 2) := by ring
    _ = a ^ 2 * (Real.sin psi ^ 2 + Real.cos psi ^ 2) := by
      rw [Real.sin_sq_add_cos_sq phi]
      ring
    _ = a ^ 2 := by
      rw [Real.sin_sq_add_cos_sq psi]
      ring

theorem gap6 (a b phi psi : ℝ) :
    G a b phi psi = a ^ 2 := by
  rw [gap4, gap5]

theorem gap7 (a b phi psi : ℝ) :
    F a b phi psi =
      deriv (fun t => xCoord a b t psi) phi *
          deriv (fun t => xCoord a b phi t) psi +
        deriv (fun t => yCoord a b t psi) phi *
          deriv (fun t => yCoord a b phi t) psi +
        deriv (fun _ => zCoord a psi) phi * deriv (zCoord a) psi := by
  rfl

theorem gap8 (a b phi psi : ℝ) :
    deriv (fun t => xCoord a b t psi) phi *
          deriv (fun t => xCoord a b phi t) psi +
        deriv (fun t => yCoord a b t psi) phi *
          deriv (fun t => yCoord a b phi t) psi +
        deriv (fun _ => zCoord a psi) phi * deriv (zCoord a) psi =
      0 := by
  have hxphi : HasDerivAt (fun t : ℝ => xCoord a b t psi)
      ((b + a * Real.cos psi) * (-Real.sin phi)) phi := by
    simpa [xCoord] using
      (Real.hasDerivAt_cos phi).const_mul (b + a * Real.cos psi)
  have hxpsi : HasDerivAt (fun t : ℝ => xCoord a b phi t)
      ((a * (-Real.sin psi)) * Real.cos phi) psi := by
    simpa [xCoord] using
      (((hasDerivAt_const psi b).add
        ((Real.hasDerivAt_cos psi).const_mul a)).mul_const (Real.cos phi))
  have hyphi : HasDerivAt (fun t : ℝ => yCoord a b t psi)
      ((b + a * Real.cos psi) * Real.cos phi) phi := by
    simpa [yCoord] using
      (Real.hasDerivAt_sin phi).const_mul (b + a * Real.cos psi)
  have hypsi : HasDerivAt (fun t : ℝ => yCoord a b phi t)
      ((a * (-Real.sin psi)) * Real.sin phi) psi := by
    simpa [yCoord] using
      (((hasDerivAt_const psi b).add
        ((Real.hasDerivAt_cos psi).const_mul a)).mul_const (Real.sin phi))
  have hzphi : HasDerivAt (fun _ : ℝ => zCoord a psi) 0 phi :=
    hasDerivAt_const phi (zCoord a psi)
  have hzpsi : HasDerivAt (zCoord a) (a * Real.cos psi) psi := by
    simpa [zCoord] using (Real.hasDerivAt_sin psi).const_mul a
  rw [hxphi.deriv, hxpsi.deriv, hyphi.deriv, hypsi.deriv,
    hzphi.deriv, hzpsi.deriv]
  ring

theorem gap9 (a b phi psi : ℝ) :
    F a b phi psi = 0 := by
  rw [gap7, gap8]

theorem gap10 (a b phi psi : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.sqrt
        (E a b phi psi * G a b phi psi - F a b phi psi ^ 2) =
      a * (b + a * Real.cos psi) := by
  rw [gap3, gap6, gap9]
  have hmul := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos psi) ha
  have hc : 0 ≤ b + a * Real.cos psi := by
    nlinarith
  have hp : 0 ≤ a * (b + a * Real.cos psi) := mul_nonneg ha hc
  calc
    Real.sqrt
          ((b + a * Real.cos psi) ^ 2 * a ^ 2 - 0 ^ 2) =
        Real.sqrt ((a * (b + a * Real.cos psi)) ^ 2) := by
          congr 1
          ring
    _ = |a * (b + a * Real.cos psi)| :=
      Real.sqrt_sq_eq_abs (a * (b + a * Real.cos psi))
    _ = a * (b + a * Real.cos psi) := abs_of_nonneg hp

theorem gap11 (a b phi₁ phi₂ psi₁ psi₂ : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    patchArea a b phi₁ phi₂ psi₁ psi₂ =
      ∫ phi in phi₁..phi₂,
        ∫ psi in psi₁..psi₂, a * (b + a * Real.cos psi) := by
  unfold patchArea
  simp_rw [gap10 a b _ _ ha hab]

theorem gap12 (a b phi₁ phi₂ psi₁ psi₂ : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    patchArea a b phi₁ phi₂ psi₁ psi₂ =
      a * (phi₂ - phi₁) *
        (b * (psi₂ - psi₁) +
          a * (Real.sin psi₂ - Real.sin psi₁)) := by
  calc
    patchArea a b phi₁ phi₂ psi₁ psi₂ =
        ∫ phi in phi₁..phi₂,
          ∫ psi in psi₁..psi₂, a * (b + a * Real.cos psi) :=
      gap11 a b phi₁ phi₂ psi₁ psi₂ ha hab
    _ = a * (phi₂ - phi₁) *
          (b * (psi₂ - psi₁) +
            a * (Real.sin psi₂ - Real.sin psi₁)) :=
      integral_torus_density a b phi₁ phi₂ psi₁ psi₂

theorem gap13 (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    totalArea a b =
      ∫ phi in (0 : ℝ)..2 * Real.pi,
        ∫ psi in -Real.pi..Real.pi,
          a * (b + a * Real.cos psi) := by
  unfold totalArea
  exact gap11 a b 0 (2 * Real.pi) (-Real.pi) Real.pi ha hab

theorem gap14 (a b : ℝ) :
    (∫ phi in (0 : ℝ)..2 * Real.pi,
        ∫ psi in -Real.pi..Real.pi,
          a * (b + a * Real.cos psi)) =
      4 * Real.pi ^ 2 * a * b := by
  rw [integral_torus_density]
  simp [Real.sin_pi]
  ring

theorem gap15 (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    totalArea a b = 4 * Real.pi ^ 2 * a * b := by
  calc
    totalArea a b =
        ∫ phi in (0 : ℝ)..2 * Real.pi,
          ∫ psi in -Real.pi..Real.pi,
            a * (b + a * Real.cos psi) := gap13 a b ha hab
    _ = 4 * Real.pi ^ 2 * a * b := gap14 a b

end

end ProofGap.Exercise4049
