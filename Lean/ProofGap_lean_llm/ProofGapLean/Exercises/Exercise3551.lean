import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3551

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ

def levelFunction (p : Point3) : ℝ :=
  p.x ^ 2 + 2 * p.y ^ 2 + 3 * p.z ^ 2

def surface : Set Point3 :=
  {p | levelFunction p = 21}

def referencePlane : Set Point3 :=
  {p | p.x + 4 * p.y + 6 * p.z = 0}

def normalVector (p : Point3) : Point3 :=
  ⟨deriv (fun t => levelFunction ⟨t, p.y, p.z⟩) p.x,
    deriv (fun t => levelFunction ⟨p.x, t, p.z⟩) p.y,
    deriv (fun t => levelFunction ⟨p.x, p.y, t⟩) p.z⟩

def reducedNormal (p : Point3) : Point3 :=
  ⟨p.x, 2 * p.y, 3 * p.z⟩

def parallelNormalCondition (p : Point3) (lam : ℝ) : Prop :=
  reducedNormal p = ⟨lam, 4 * lam, 6 * lam⟩

def tangencyPoints : Set Point3 :=
  {p | p = ⟨1, 2, 2⟩ ∨ p = ⟨-1, -2, -2⟩}

def tangentPlaneAt (p : Point3) : Set Point3 :=
  {q | q.x - p.x + 4 * (q.y - p.y) + 6 * (q.z - p.z) = 0}

def rawPositivePlane : Set Point3 :=
  {q | q.x - 1 + 4 * (q.y - 2) + 6 * (q.z - 2) = 0}

def rawNegativePlane : Set Point3 :=
  {q | q.x + 1 + 4 * (q.y + 2) + 6 * (q.z + 2) = 0}

def rawTangentPlanes : Set (Set Point3) :=
  {plane | plane = rawPositivePlane ∨ plane = rawNegativePlane}

def positivePlane : Set Point3 :=
  {q | q.x + 4 * q.y + 6 * q.z = 21}

def negativePlane : Set Point3 :=
  {q | q.x + 4 * q.y + 6 * q.z = -21}

def tangentPlanes : Set (Set Point3) :=
  {plane | plane = positivePlane ∨ plane = negativePlane}

private theorem Point3.ext {p q : Point3}
    (hx : p.x = q.x) (hy : p.y = q.y) (hz : p.z = q.z) : p = q := by
  cases p with
  | mk px py pz =>
    cases q with
    | mk qx qy qz =>
      dsimp at hx hy hz
      cases hx
      cases hy
      cases hz
      rfl

theorem gap1 :
    ∀ p : Point3,
      normalVector p = ⟨2 * p.x, 2 * (2 * p.y), 2 * (3 * p.z)⟩ := by
  intro p
  refine Point3.ext ?_ ?_ ?_
  · change
      deriv (fun t : ℝ => t ^ 2 + 2 * p.y ^ 2 + 3 * p.z ^ 2) p.x =
        2 * p.x
    have hsq :
        HasDerivAt (fun t : ℝ => t ^ 2) (2 * p.x) p.x := by
      simpa [pow_two, two_mul] using
        ((hasDerivAt_id p.x).mul (hasDerivAt_id p.x))
    simpa using hsq.deriv
  · change
      deriv (fun t : ℝ => p.x ^ 2 + 2 * t ^ 2 + 3 * p.z ^ 2) p.y =
        2 * (2 * p.y)
    have hsq :
        HasDerivAt (fun t : ℝ => t ^ 2) (2 * p.y) p.y := by
      simpa [pow_two, two_mul] using
        ((hasDerivAt_id p.y).mul (hasDerivAt_id p.y))
    simpa using hsq.deriv
  · change
      deriv (fun t : ℝ => p.x ^ 2 + 2 * p.y ^ 2 + 3 * t ^ 2) p.z =
        2 * (3 * p.z)
    have hsq :
        HasDerivAt (fun t : ℝ => t ^ 2) (2 * p.z) p.z := by
      simpa [pow_two, two_mul] using
        ((hasDerivAt_id p.z).mul (hasDerivAt_id p.z))
    calc
      deriv (fun t : ℝ => p.x ^ 2 + 2 * p.y ^ 2 + 3 * t ^ 2) p.z =
          3 * (2 * p.z) := by
        simpa using hsq.deriv
      _ = 2 * (3 * p.z) := by ring

theorem gap2 (p : Point3) (lam : ℝ)
    (hParallel : parallelNormalCondition p lam) :
    p.x = lam := by
  simpa [parallelNormalCondition, reducedNormal] using
    (congrArg Point3.x hParallel)

theorem gap3 (p : Point3) (lam : ℝ)
    (hParallel : parallelNormalCondition p lam) :
    2 * p.y = 4 * lam := by
  simpa [parallelNormalCondition, reducedNormal] using
    (congrArg Point3.y hParallel)

theorem gap4 (p : Point3) (lam : ℝ)
    (hParallel : parallelNormalCondition p lam) :
    3 * p.z = 6 * lam := by
  simpa [parallelNormalCondition, reducedNormal] using
    (congrArg Point3.z hParallel)

theorem gap5 (p : Point3) (lam : ℝ)
    (hParallel : parallelNormalCondition p lam) :
    p.x = lam := by
  exact gap2 p lam hParallel

theorem gap6 (p : Point3) (lam : ℝ)
    (hY : 2 * p.y = 4 * lam) :
    p.y = 2 * lam := by
  linarith

theorem gap7 (p : Point3) (lam : ℝ)
    (hZ : 3 * p.z = 6 * lam) :
    p.z = 2 * lam := by
  linarith

theorem gap8 (p : Point3) (lam : ℝ)
    (hSurface : p ∈ surface)
    (hx : p.x = lam)
    (hy : p.y = 2 * lam)
    (hz : p.z = 2 * lam) :
    lam = 1 ∨ lam = -1 := by
  have hEq :
      lam ^ 2 + 2 * (2 * lam) ^ 2 + 3 * (2 * lam) ^ 2 = 21 := by
    simpa [surface, levelFunction, hx, hy, hz] using hSurface
  have hProd : (lam - 1) * (lam + 1) = 0 := by
    nlinarith [hEq]
  rcases mul_eq_zero.mp hProd with h | h
  · left
    linarith
  · right
    linarith

theorem gap9 (p : Point3) (lam : ℝ)
    (hx : p.x = lam)
    (hy : p.y = 2 * lam)
    (hz : p.z = 2 * lam)
    (hLam : lam = 1 ∨ lam = -1) :
    p ∈ tangencyPoints := by
  change p = ⟨1, 2, 2⟩ ∨ p = ⟨-1, -2, -2⟩
  rcases hLam with hLam | hLam
  · left
    apply Point3.ext <;> dsimp <;> linarith
  · right
    apply Point3.ext <;> dsimp <;> linarith

theorem gap10 (p : Point3)
    (hPoint : p ∈ tangencyPoints) :
    tangentPlaneAt p ∈ rawTangentPlanes := by
  change p = ⟨1, 2, 2⟩ ∨ p = ⟨-1, -2, -2⟩ at hPoint
  change
    tangentPlaneAt p = rawPositivePlane ∨
      tangentPlaneAt p = rawNegativePlane
  rcases hPoint with rfl | rfl
  · left
    rfl
  · right
    apply Set.ext
    intro q
    simpa [tangentPlaneAt, rawNegativePlane]

theorem gap11 (plane : Set Point3)
    (hPlane : plane ∈ rawTangentPlanes) :
    plane ∈ tangentPlanes := by
  change plane = rawPositivePlane ∨ plane = rawNegativePlane at hPlane
  change plane = positivePlane ∨ plane = negativePlane
  rcases hPlane with rfl | rfl
  · left
    apply Set.ext
    intro q
    change
      (q.x - 1 + 4 * (q.y - 2) + 6 * (q.z - 2) = 0) ↔
        (q.x + 4 * q.y + 6 * q.z = 21)
    constructor <;> intro h <;> linarith
  · right
    apply Set.ext
    intro q
    change
      (q.x + 1 + 4 * (q.y + 2) + 6 * (q.z + 2) = 0) ↔
        (q.x + 4 * q.y + 6 * q.z = -21)
    constructor <;> intro h <;> linarith

end

end ProofGap.Exercise3551
