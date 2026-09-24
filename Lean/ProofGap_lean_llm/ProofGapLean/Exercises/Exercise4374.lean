import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4374

noncomputable section

open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def dot (p q : Vec3) : ℝ :=
  p.1 * q.1 + p.2.1 * q.2.1 + p.2.2 * q.2.2

def cross (p q : Vec3) : Vec3 :=
  (p.2.1 * q.2.2 - p.2.2 * q.2.1,
    p.2.2 * q.1 - p.1 * q.2.2,
    p.1 * q.2.1 - p.2.1 * q.1)

def derivative (γ : ℝ → Vec3) (t : ℝ) : Vec3 :=
  (deriv (fun s => (γ s).1) t,
    deriv (fun s => (γ s).2.1) t,
    deriv (fun s => (γ s).2.2) t)

def curveParam (a t : ℝ) : Vec3 :=
  (a * Real.cos t, a * Real.cos (2 * t), a * Real.cos (3 * t))

def surfaceParam (u t : ℝ) : Vec3 :=
  (u * Real.cos t, u * Real.cos (2 * t), u * Real.cos (3 * t))

def vectorField (p : Vec3) : Vec3 :=
  (p.2.1 ^ 2 * p.2.2 ^ 2,
    p.1 ^ 2 * p.2.2 ^ 2,
    p.1 ^ 2 * p.2.1 ^ 2)

def stokesIntegrandField (p : Vec3) : Vec3 :=
  (p.1 ^ 2 * (p.2.1 - p.2.2),
    p.2.1 ^ 2 * (p.2.2 - p.1),
    p.2.2 ^ 2 * (p.1 - p.2.1))

def surfaceAreaVector (u t : ℝ) : Vec3 :=
  cross (derivative (fun r => surfaceParam r t) u)
    (derivative (surfaceParam u) t)

def auxiliaryIntegrand (t : ℝ) : ℝ :=
  Real.cos t ^ 2 * (Real.cos (2 * t) - Real.cos (3 * t)) *
      (2 * Real.sin (2 * t) * Real.cos (3 * t) -
        3 * Real.cos (2 * t) * Real.sin (3 * t)) +
    Real.cos (2 * t) ^ 2 * (Real.cos (3 * t) - Real.cos t) *
      (3 * Real.sin (3 * t) * Real.cos t -
        Real.sin t * Real.cos (3 * t)) +
    Real.cos (3 * t) ^ 2 * (Real.cos t - Real.cos (2 * t)) *
      (Real.sin t * Real.cos (2 * t) -
        2 * Real.sin (2 * t) * Real.cos t)

def stokesSurfaceIntegral (a : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..a,
    ∫ t in -Real.pi..Real.pi,
      dot (stokesIntegrandField (surfaceParam u t))
        (surfaceAreaVector u t)

def lineIntegral (a : ℝ) : ℝ :=
  ∫ t in -Real.pi..Real.pi,
    dot (vectorField (curveParam a t))
      (derivative (curveParam a) t)

private theorem symmetricIntegral_eq_zero (f : ℝ → ℝ) (b : ℝ)
    (hodd : ∀ x, f (-x) = -f x) :
    (∫ x in -b..b, f x) = 0 := by
  have hchange :
      (∫ x in -b..b, f (-x)) = ∫ x in -b..b, f x := by
    simpa using (intervalIntegral.integral_comp_neg f (-b) b)
  have hoddint :
      (∫ x in -b..b, f (-x)) = -(∫ x in -b..b, f x) := by
    simp only [hodd, intervalIntegral.integral_neg]
  linarith

private theorem derivative_curveParam_eq (a t : ℝ) :
    derivative (curveParam a) t =
      (-a * Real.sin t,
        -2 * a * Real.sin (2 * t),
        -3 * a * Real.sin (3 * t)) := by
  apply Prod.ext
  · change deriv (fun s : ℝ => a * Real.cos s) t = -a * Real.sin t
    convert ((Real.hasDerivAt_cos t).const_mul a).deriv using 1 <;> ring
  · apply Prod.ext
    · change deriv (fun s : ℝ => a * Real.cos (2 * s)) t =
        -2 * a * Real.sin (2 * t)
      have hlin : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
        simpa using (hasDerivAt_id t).const_mul 2
      have h := ((Real.hasDerivAt_cos (2 * t)).comp t hlin).const_mul a
      convert h.deriv using 1 <;> ring
    · change deriv (fun s : ℝ => a * Real.cos (3 * s)) t =
        -3 * a * Real.sin (3 * t)
      have hlin : HasDerivAt (fun s : ℝ => 3 * s) 3 t := by
        simpa using (hasDerivAt_id t).const_mul 3
      have h := ((Real.hasDerivAt_cos (3 * t)).comp t hlin).const_mul a
      convert h.deriv using 1 <;> ring

private theorem derivative_surface_radial_eq (u t : ℝ) :
    derivative (fun r => surfaceParam r t) u =
      (Real.cos t, Real.cos (2 * t), Real.cos (3 * t)) := by
  apply Prod.ext
  · change deriv (fun r : ℝ => r * Real.cos t) u = Real.cos t
    have h := (hasDerivAt_id u).mul_const (Real.cos t)
    convert h.deriv using 1 <;> ring
  · apply Prod.ext
    · change deriv (fun r : ℝ => r * Real.cos (2 * t)) u = Real.cos (2 * t)
      have h := (hasDerivAt_id u).mul_const (Real.cos (2 * t))
      convert h.deriv using 1 <;> ring
    · change deriv (fun r : ℝ => r * Real.cos (3 * t)) u = Real.cos (3 * t)
      have h := (hasDerivAt_id u).mul_const (Real.cos (3 * t))
      convert h.deriv using 1 <;> ring

private theorem derivative_surface_angular_eq (u t : ℝ) :
    derivative (surfaceParam u) t =
      (-u * Real.sin t,
        -2 * u * Real.sin (2 * t),
        -3 * u * Real.sin (3 * t)) := by
  change derivative (curveParam u) t = _
  exact derivative_curveParam_eq u t

private theorem lineIntegrand_odd (a t : ℝ) :
    dot (vectorField (curveParam a (-t)))
        (derivative (curveParam a) (-t)) =
      -dot (vectorField (curveParam a t))
        (derivative (curveParam a) t) := by
  rw [derivative_curveParam_eq a (-t), derivative_curveParam_eq a t]
  simp [dot, vectorField, curveParam, Real.cos_neg, Real.sin_neg] <;> ring

private theorem lineIntegral_eq_zero (a : ℝ) : lineIntegral a = 0 := by
  unfold lineIntegral
  apply symmetricIntegral_eq_zero
  intro t
  exact lineIntegrand_odd a t

private theorem surfaceIntegrand_odd (u t : ℝ) :
    dot (stokesIntegrandField (surfaceParam u (-t)))
        (surfaceAreaVector u (-t)) =
      -dot (stokesIntegrandField (surfaceParam u t))
        (surfaceAreaVector u t) := by
  unfold surfaceAreaVector
  rw [derivative_surface_radial_eq u (-t),
    derivative_surface_angular_eq u (-t),
    derivative_surface_radial_eq u t,
    derivative_surface_angular_eq u t]
  simp [dot, cross, stokesIntegrandField, surfaceParam,
    Real.cos_neg, Real.sin_neg] <;> ring

private theorem stokesSurfaceIntegral_eq_zero (a : ℝ) :
    stokesSurfaceIntegral a = 0 := by
  unfold stokesSurfaceIntegral
  have hz : ∀ u : ℝ,
      (∫ t in -Real.pi..Real.pi,
        dot (stokesIntegrandField (surfaceParam u t))
          (surfaceAreaVector u t)) = 0 := by
    intro u
    apply symmetricIntegral_eq_zero
    intro t
    exact surfaceIntegrand_odd u t
  simp [hz]

private theorem auxiliaryIntegrand_odd (t : ℝ) :
    auxiliaryIntegrand (-t) = -auxiliaryIntegrand t := by
  simp [auxiliaryIntegrand, Real.cos_neg, Real.sin_neg] <;> ring

private theorem auxiliaryIntegral_eq_zero :
    (∫ t in -Real.pi..Real.pi, auxiliaryIntegrand t) = 0 := by
  apply symmetricIntegral_eq_zero
  intro t
  exact auxiliaryIntegrand_odd t

theorem gap1 (a : ℝ) (ha : 0 < a) :
    lineIntegral a = 2 * stokesSurfaceIntegral a := by
  rw [lineIntegral_eq_zero a, stokesSurfaceIntegral_eq_zero a]
  ring

theorem gap2 (a : ℝ) (ha : 0 < a) :
    lineIntegral a =
      2 / 5 * a ^ 5 *
        ∫ t in -Real.pi..Real.pi, auxiliaryIntegrand t := by
  rw [lineIntegral_eq_zero a, auxiliaryIntegral_eq_zero]
  ring

theorem gap3 (t : ℝ) :
    auxiliaryIntegrand t =
      Real.cos t ^ 2 * (Real.cos (2 * t) - Real.cos (3 * t)) *
          (2 * Real.sin (2 * t) * Real.cos (3 * t) -
            3 * Real.cos (2 * t) * Real.sin (3 * t)) +
        Real.cos (2 * t) ^ 2 * (Real.cos (3 * t) - Real.cos t) *
          (3 * Real.sin (3 * t) * Real.cos t -
            Real.sin t * Real.cos (3 * t)) +
        Real.cos (3 * t) ^ 2 * (Real.cos t - Real.cos (2 * t)) *
          (Real.sin t * Real.cos (2 * t) -
            2 * Real.sin (2 * t) * Real.cos t) := by
  rfl

theorem gap4 :
    (∫ t in -Real.pi..Real.pi, auxiliaryIntegrand t) = 0 := by
  exact auxiliaryIntegral_eq_zero

theorem gap5 (a : ℝ) (ha : 0 < a) :
    lineIntegral a = 0 := by
  exact lineIntegral_eq_zero a

end

end ProofGap.Exercise4374
