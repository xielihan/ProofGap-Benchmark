import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise3534

noncomputable section

abbrev Point3 := ℝ × (ℝ × ℝ)

def curve (a b t : ℝ) : Point3 :=
  (a * Real.cos t, (a * Real.sin t, b * t))

def tangent (a b t : ℝ) : Point3 :=
  (deriv (fun s => (curve a b s).1) t,
    (deriv (fun s => (curve a b s).2.1) t,
      deriv (fun s => (curve a b s).2.2) t))

def norm3 (V : Point3) : ℝ :=
  Real.sqrt (V.1 ^ 2 + V.2.1 ^ 2 + V.2.2 ^ 2)

def axisAngleCos (a b t : ℝ) : ℝ :=
  (tangent a b t).2.2 / norm3 (tangent a b t)

def IsRegularHelix (a b : ℝ) : Prop := 0 < a ^ 2 + b ^ 2

theorem gap1 (a b : ℝ) :
    ∀ t, deriv (fun s => (curve a b s).1) t = -a * Real.sin t := by
  intro t
  simpa [curve] using ((Real.hasDerivAt_cos t).const_mul a).deriv

theorem gap2 (a b : ℝ) :
    ∀ t, deriv (fun s => (curve a b s).2.1) t = a * Real.cos t := by
  intro t
  simpa [curve] using ((Real.hasDerivAt_sin t).const_mul a).deriv

theorem gap3 (a b : ℝ) :
    ∀ t, deriv (fun s => (curve a b s).2.2) t = b := by
  intro t
  simpa [curve] using ((hasDerivAt_id t).const_mul b).deriv

theorem gap4 (a b t : ℝ) (hRegular : IsRegularHelix a b) :
    axisAngleCos a b t =
      deriv (fun s => (curve a b s).2.2) t /
        Real.sqrt
          ((deriv (fun s => (curve a b s).1) t) ^ 2 +
            (deriv (fun s => (curve a b s).2.1) t) ^ 2 +
            (deriv (fun s => (curve a b s).2.2) t) ^ 2) := by
  rfl

theorem gap5 (a b t : ℝ) (hRegular : IsRegularHelix a b) :
    deriv (fun s => (curve a b s).2.2) t /
        Real.sqrt
          ((deriv (fun s => (curve a b s).1) t) ^ 2 +
            (deriv (fun s => (curve a b s).2.1) t) ^ 2 +
            (deriv (fun s => (curve a b s).2.2) t) ^ 2) =
      b / Real.sqrt (a ^ 2 + b ^ 2) := by
  rw [gap1 a b t, gap2 a b t, gap3 a b t]
  have h :
      (-a * Real.sin t) ^ 2 + (a * Real.cos t) ^ 2 + b ^ 2 =
        a ^ 2 + b ^ 2 := by
    calc
      (-a * Real.sin t) ^ 2 + (a * Real.cos t) ^ 2 + b ^ 2 =
          a ^ 2 * (Real.sin t ^ 2 + Real.cos t ^ 2) + b ^ 2 := by ring
      _ = a ^ 2 + b ^ 2 := by rw [Real.sin_sq_add_cos_sq]; ring
  rw [h]

theorem gap6 (a b : ℝ) (hRegular : IsRegularHelix a b) :
    ∀ t, axisAngleCos a b t = b / Real.sqrt (a ^ 2 + b ^ 2) := by
  intro t
  exact (gap4 a b t hRegular).trans (gap5 a b t hRegular)

theorem gap7 (a b t : ℝ) (hRegular : IsRegularHelix a b) :
    axisAngleCos a b t = b / Real.sqrt (a ^ 2 + b ^ 2) := by
  exact gap6 a b hRegular t

end

end ProofGap.Exercise3534
