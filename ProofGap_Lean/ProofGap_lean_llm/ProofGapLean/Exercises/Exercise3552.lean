import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3552

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ

def surface (a : ℝ) : Set Point3 :=
  {p | p.x * p.y * p.z = a ^ 3}

def positiveSurfacePoint (a : ℝ) (p : Point3) : Prop :=
  0 < p.x ∧ 0 < p.y ∧ 0 < p.z ∧ p ∈ surface a

def tangentPlaneAt (p : Point3) : Set Point3 :=
  {q | p.y * p.z * (q.x - p.x) +
      p.x * p.z * (q.y - p.y) +
      p.x * p.y * (q.z - p.z) = 0}

def xIntercept (p : Point3) : Point3 := ⟨3 * p.x, 0, 0⟩

def yIntercept (p : Point3) : Point3 := ⟨0, 3 * p.y, 0⟩

def zIntercept (p : Point3) : Point3 := ⟨0, 0, 3 * p.z⟩

def OA (p : Point3) : ℝ := 3 * p.x

def OB (p : Point3) : ℝ := 3 * p.y

def OC (p : Point3) : ℝ := 3 * p.z

def tangentTetrahedronVolume (p : Point3) : ℝ :=
  (1 / 3 : ℝ) * OC p * (1 / 2 : ℝ) * OA p * OB p

theorem gap1 (a : ℝ) (ha : 0 < a) :
    ∀ p : Point3, p ∈ surface a →
      tangentPlaneAt p =
        {q | p.y * p.z * (q.x - p.x) +
            p.x * p.z * (q.y - p.y) +
            p.x * p.y * (q.z - p.z) = 0} := by
  intro p hp
  rfl

theorem gap2 (a : ℝ) (p : Point3)
    (ha : 0 < a) (hp : p ∈ surface a) :
    xIntercept p = ⟨3 * p.x, 0, 0⟩ := by
  rfl

theorem gap3 (a : ℝ) (p : Point3)
    (ha : 0 < a) (hp : p ∈ surface a) :
    yIntercept p = ⟨0, 3 * p.y, 0⟩ := by
  rfl

theorem gap4 (a : ℝ) (p : Point3)
    (ha : 0 < a) (hp : p ∈ surface a) :
    zIntercept p = ⟨0, 0, 3 * p.z⟩ := by
  rfl

theorem gap5 (a : ℝ) (p : Point3)
    (ha : 0 < a) (hp : positiveSurfacePoint a p) :
    tangentTetrahedronVolume p =
      (1 / 3 : ℝ) * OC p * (1 / 2 : ℝ) * OA p * OB p := by
  rfl

theorem gap6 (a : ℝ) (p : Point3)
    (ha : 0 < a) (hp : positiveSurfacePoint a p) :
    (1 / 3 : ℝ) * OC p * (1 / 2 : ℝ) * OA p * OB p =
      (1 / 6 : ℝ) * (3 * p.z) * (3 * p.x) * (3 * p.y) := by
  unfold OA OB OC
  ring

theorem gap7 (a : ℝ) (p : Point3)
    (ha : 0 < a) (hp : positiveSurfacePoint a p) :
    (1 / 6 : ℝ) * (3 * p.z) * (3 * p.x) * (3 * p.y) =
      (9 / 2 : ℝ) * p.x * p.y * p.z := by
  ring

theorem gap8 (a : ℝ) (p : Point3)
    (ha : 0 < a) (hp : positiveSurfacePoint a p) :
    (9 / 2 : ℝ) * p.x * p.y * p.z =
      (9 / 2 : ℝ) * a ^ 3 := by
  rcases hp with ⟨hx, hy, hz, hs⟩
  change p.x * p.y * p.z = a ^ 3 at hs
  calc
    (9 / 2 : ℝ) * p.x * p.y * p.z =
        (9 / 2 : ℝ) * (p.x * p.y * p.z) := by ring
    _ = (9 / 2 : ℝ) * a ^ 3 := by rw [hs]

theorem gap9 (a : ℝ) (p : Point3)
    (ha : 0 < a) (hp : positiveSurfacePoint a p) :
    tangentTetrahedronVolume p = (9 / 2 : ℝ) * a ^ 3 := by
  calc
    tangentTetrahedronVolume p =
        (1 / 3 : ℝ) * OC p * (1 / 2 : ℝ) * OA p * OB p := gap5 a p ha hp
    _ = (1 / 6 : ℝ) * (3 * p.z) * (3 * p.x) * (3 * p.y) := gap6 a p ha hp
    _ = (9 / 2 : ℝ) * p.x * p.y * p.z := gap7 a p ha hp
    _ = (9 / 2 : ℝ) * a ^ 3 := gap8 a p ha hp

theorem gap10 (a : ℝ) (ha : 0 < a) :
    ∀ p : Point3, positiveSurfacePoint a p →
      tangentTetrahedronVolume p = (9 / 2 : ℝ) * a ^ 3 := by
  intro p hp
  exact gap9 a p ha hp

end

end ProofGap.Exercise3552
