import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise3531

noncomputable section

abbrev Point3 := ℝ × (ℝ × ℝ)

def normal1 : Point3 := (2, (0, 6))

def normal2 : Point3 := (0, (2, 6))

def basePoint : Point3 := (1, (1, 3))

def direction : Point3 := (-3, (-3, 1))

def oppositeDirection : Point3 := (3, (3, -1))

def linePoint (P V : Point3) (s : ℝ) : Point3 :=
  (P.1 + s * V.1, (P.2.1 + s * V.2.1, P.2.2 + s * V.2.2))

def OnTangentLine (P V Q : Point3) : Prop :=
  ∃ s : ℝ, Q = linePoint P V s

def OnNormalPlane (P V Q : Point3) : Prop :=
  V.1 * (Q.1 - P.1) + V.2.1 * (Q.2.1 - P.2.1) +
    V.2.2 * (Q.2.2 - P.2.2) = 0

theorem gap1 :
    normal1 = (2, (0, 6)) := by
  rfl

theorem gap2 :
    normal2 = (0, (2, 6)) := by
  rfl

theorem gap3 :
    direction = (-3, (-3, 1)) := by
  rfl

theorem gap4 (Q : Point3)
    (hLine : OnTangentLine basePoint direction Q) :
    (Q.1 - 1) * direction.2.1 = (Q.2.1 - 1) * direction.1 := by
  rcases hLine with ⟨s, rfl⟩
  simp [linePoint, basePoint, direction] <;> ring

theorem gap5 (Q : Point3)
    (hLine : OnTangentLine basePoint direction Q) :
    (Q.2.1 - 1) * direction.2.2 = (Q.2.2 - 3) * direction.2.1 := by
  rcases hLine with ⟨s, rfl⟩
  simp [linePoint, basePoint, direction] <;> ring

theorem gap6 (Q : Point3)
    (hLine : OnTangentLine basePoint direction Q) :
    (Q.1 - 1) * direction.2.2 = (Q.2.2 - 3) * direction.1 := by
  rcases hLine with ⟨s, rfl⟩
  simp [linePoint, basePoint, direction] <;> ring

theorem gap7 (Q : Point3)
    (hLine : OnTangentLine basePoint oppositeDirection Q) :
    (Q.1 - 1) * oppositeDirection.2.1 =
      (Q.2.1 - 1) * oppositeDirection.1 := by
  rcases hLine with ⟨s, rfl⟩
  simp [linePoint, basePoint, oppositeDirection] <;> ring

theorem gap8 (Q : Point3)
    (hLine : OnTangentLine basePoint oppositeDirection Q) :
    (Q.2.1 - 1) * oppositeDirection.2.2 =
      (Q.2.2 - 3) * oppositeDirection.2.1 := by
  rcases hLine with ⟨s, rfl⟩
  simp [linePoint, basePoint, oppositeDirection] <;> ring

theorem gap9 (Q : Point3)
    (hLine : OnTangentLine basePoint oppositeDirection Q) :
    (Q.1 - 1) * oppositeDirection.2.2 =
      (Q.2.2 - 3) * oppositeDirection.1 := by
  rcases hLine with ⟨s, rfl⟩
  simp [linePoint, basePoint, oppositeDirection] <;> ring

theorem gap10 (Q : Point3)
    (hPlane : OnNormalPlane basePoint direction Q) :
    -3 * (Q.1 - 1) - 3 * (Q.2.1 - 1) + (Q.2.2 - 3) = 0 := by
  simpa [OnNormalPlane, basePoint, direction] using hPlane

theorem gap11 (Q : Point3)
    (hPlane : OnNormalPlane basePoint direction Q) :
    3 * Q.1 + 3 * Q.2.1 - Q.2.2 = 3 := by
  have h := gap10 Q hPlane
  linarith

end

end ProofGap.Exercise3531
