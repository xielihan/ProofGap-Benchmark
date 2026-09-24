import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise3528

noncomputable section

abbrev Point3 := ℝ × (ℝ × ℝ)

def curve (a α t : ℝ) : Point3 :=
  (a * Real.cos α * Real.cos t, (a * Real.sin α * Real.cos t, a * Real.sin t))

def tangent (a α t : ℝ) : Point3 :=
  (deriv (fun s => (curve a α s).1) t,
    (deriv (fun s => (curve a α s).2.1) t,
      deriv (fun s => (curve a α s).2.2) t))

def reducedDirection (α t : ℝ) : Point3 :=
  (-Real.cos α * Real.sin t,
    (-Real.sin α * Real.sin t, Real.cos t))

def linePoint (P V : Point3) (s : ℝ) : Point3 :=
  (P.1 + s * V.1, (P.2.1 + s * V.2.1, P.2.2 + s * V.2.2))

def OnTangentLine (P V Q : Point3) : Prop :=
  ∃ s : ℝ, Q = linePoint P V s

def OnNormalPlane (P V Q : Point3) : Prop :=
  V.1 * (Q.1 - P.1) + V.2.1 * (Q.2.1 - P.2.1) +
    V.2.2 * (Q.2.2 - P.2.2) = 0

theorem gap1 (a α t0 : ℝ) :
    curve a α t0 =
      (a * Real.cos α * Real.cos t0,
        (a * Real.sin α * Real.cos t0, a * Real.sin t0)) := by
  rfl

theorem gap2 (a α t0 : ℝ) :
    tangent a α t0 =
      (-a * Real.cos α * Real.sin t0,
        (-a * Real.sin α * Real.sin t0, a * Real.cos t0)) := by
  have hx :
      deriv (fun s : ℝ => a * Real.cos α * Real.cos s) t0 =
        -a * Real.cos α * Real.sin t0 := by
    convert ((Real.hasDerivAt_cos t0).const_mul (a * Real.cos α)).deriv using 1 <;> ring
  have hy :
      deriv (fun s : ℝ => a * Real.sin α * Real.cos s) t0 =
        -a * Real.sin α * Real.sin t0 := by
    convert ((Real.hasDerivAt_cos t0).const_mul (a * Real.sin α)).deriv using 1 <;> ring
  have hz :
      deriv (fun s : ℝ => a * Real.sin s) t0 = a * Real.cos t0 := by
    convert ((Real.hasDerivAt_sin t0).const_mul a).deriv using 1 <;> ring
  change
    (deriv (fun s : ℝ => a * Real.cos α * Real.cos s) t0,
      (deriv (fun s : ℝ => a * Real.sin α * Real.cos s) t0,
        deriv (fun s : ℝ => a * Real.sin s) t0)) = _
  rw [hx, hy, hz]

theorem gap3 (a α t0 : ℝ) (Q : Point3)
    (hLine : OnTangentLine (curve a α t0) (tangent a α t0) Q) :
    (Q.1 - (curve a α t0).1) * (tangent a α t0).2.1 =
      (Q.2.1 - (curve a α t0).2.1) * (tangent a α t0).1 := by
  rcases hLine with ⟨s, rfl⟩
  simp only [linePoint, Prod.fst, Prod.snd]
  ring

theorem gap4 (a α t0 : ℝ) (Q : Point3)
    (hLine : OnTangentLine (curve a α t0) (tangent a α t0) Q) :
    (Q.2.1 - (curve a α t0).2.1) * (tangent a α t0).2.2 =
      (Q.2.2 - (curve a α t0).2.2) * (tangent a α t0).2.1 := by
  rcases hLine with ⟨s, rfl⟩
  simp only [linePoint, Prod.fst, Prod.snd]
  ring

theorem gap5 (a α t0 : ℝ) (Q : Point3)
    (hLine : OnTangentLine (curve a α t0) (tangent a α t0) Q) :
    (Q.1 - (curve a α t0).1) * (tangent a α t0).2.2 =
      (Q.2.2 - (curve a α t0).2.2) * (tangent a α t0).1 := by
  rcases hLine with ⟨s, rfl⟩
  simp only [linePoint, Prod.fst, Prod.snd]
  ring

theorem gap6 (a α t0 : ℝ) (Q : Point3)
    (ha : a ≠ 0)
    (hLine : OnTangentLine (curve a α t0) (tangent a α t0) Q) :
    (Q.1 - (curve a α t0).1) * (reducedDirection α t0).2.1 =
      (Q.2.1 - (curve a α t0).2.1) * (reducedDirection α t0).1 := by
  rcases hLine with ⟨s, rfl⟩
  simp only [linePoint, gap2, reducedDirection, Prod.fst, Prod.snd]
  ring

theorem gap7 (a α t0 : ℝ) (Q : Point3)
    (ha : a ≠ 0)
    (hLine : OnTangentLine (curve a α t0) (tangent a α t0) Q) :
    (Q.2.1 - (curve a α t0).2.1) * (reducedDirection α t0).2.2 =
      (Q.2.2 - (curve a α t0).2.2) * (reducedDirection α t0).2.1 := by
  rcases hLine with ⟨s, rfl⟩
  simp only [linePoint, gap2, reducedDirection, Prod.fst, Prod.snd]
  ring

theorem gap8 (a α t0 : ℝ) (Q : Point3)
    (ha : a ≠ 0)
    (hLine : OnTangentLine (curve a α t0) (tangent a α t0) Q) :
    (Q.1 - (curve a α t0).1) * (reducedDirection α t0).2.2 =
      (Q.2.2 - (curve a α t0).2.2) * (reducedDirection α t0).1 := by
  rcases hLine with ⟨s, rfl⟩
  simp only [linePoint, gap2, reducedDirection, Prod.fst, Prod.snd]
  ring

theorem gap9 (a α t0 : ℝ) (Q : Point3)
    (hPlane : OnNormalPlane (curve a α t0) (tangent a α t0) Q) :
    (tangent a α t0).1 * (Q.1 - (curve a α t0).1) +
        (tangent a α t0).2.1 * (Q.2.1 - (curve a α t0).2.1) +
        (tangent a α t0).2.2 * (Q.2.2 - (curve a α t0).2.2) = 0 := by
  simpa only [OnNormalPlane] using hPlane

theorem gap10 (a α t0 : ℝ) (Q : Point3)
    (ha : a ≠ 0)
    (hPlane : OnNormalPlane (curve a α t0) (tangent a α t0) Q) :
    Q.1 * Real.cos α * Real.sin t0 +
        Q.2.1 * Real.sin α * Real.sin t0 -
        Q.2.2 * Real.cos t0 = 0 := by
  have hp :
      (-a * Real.cos α * Real.sin t0) *
          (Q.1 - a * Real.cos α * Real.cos t0) +
        (-a * Real.sin α * Real.sin t0) *
          (Q.2.1 - a * Real.sin α * Real.cos t0) +
        (a * Real.cos t0) * (Q.2.2 - a * Real.sin t0) = 0 := by
    simpa only [OnNormalPlane, gap2, curve, Prod.fst, Prod.snd] using hPlane
  have hid :
      (-a * Real.cos α * Real.sin t0) *
          (Q.1 - a * Real.cos α * Real.cos t0) +
        (-a * Real.sin α * Real.sin t0) *
          (Q.2.1 - a * Real.sin α * Real.cos t0) +
        (a * Real.cos t0) * (Q.2.2 - a * Real.sin t0) =
      -a *
        (Q.1 * Real.cos α * Real.sin t0 +
          Q.2.1 * Real.sin α * Real.sin t0 -
          Q.2.2 * Real.cos t0) := by
    calc
      _ = -a *
            (Q.1 * Real.cos α * Real.sin t0 +
              Q.2.1 * Real.sin α * Real.sin t0 -
              Q.2.2 * Real.cos t0) +
          a ^ 2 * Real.sin t0 * Real.cos t0 *
            (Real.sin α ^ 2 + Real.cos α ^ 2 - 1) := by ring
      _ = -a *
            (Q.1 * Real.cos α * Real.sin t0 +
              Q.2.1 * Real.sin α * Real.sin t0 -
              Q.2.2 * Real.cos t0) := by
        rw [Real.sin_sq_add_cos_sq]
        ring
  have hmul :
      -a *
        (Q.1 * Real.cos α * Real.sin t0 +
          Q.2.1 * Real.sin α * Real.sin t0 -
          Q.2.2 * Real.cos t0) = 0 := by
    rw [← hid]
    exact hp
  exact (mul_eq_zero.mp hmul).resolve_left (neg_ne_zero.mpr ha)

end

end ProofGap.Exercise3528
