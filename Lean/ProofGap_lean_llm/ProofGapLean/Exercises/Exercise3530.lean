import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace ProofGap.Exercise3530

noncomputable section

abbrev Point3 := ℝ × (ℝ × ℝ)

def curve (t : ℝ) : Point3 := (t, (t, t ^ 2))

def tangent (t : ℝ) : Point3 :=
  (deriv (fun s => (curve s).1) t,
    (deriv (fun s => (curve s).2.1) t, deriv (fun s => (curve s).2.2) t))

def basePoint : Point3 := (1, (1, 1))

def direction : Point3 := (1, (1, 2))

def linePoint (P V : Point3) (s : ℝ) : Point3 :=
  (P.1 + s * V.1, (P.2.1 + s * V.2.1, P.2.2 + s * V.2.2))

def OnTangentLine (P V Q : Point3) : Prop :=
  ∃ s : ℝ, Q = linePoint P V s

def OnNormalPlane (P V Q : Point3) : Prop :=
  V.1 * (Q.1 - P.1) + V.2.1 * (Q.2.1 - P.2.1) +
    V.2.2 * (Q.2.2 - P.2.2) = 0

theorem gap1 :
    ∀ t, (curve t).2.1 = t := by
  intro t
  rfl

theorem gap2 :
    ∀ t, (curve t).2.2 = t ^ 2 := by
  intro t
  rfl

theorem gap3 :
    tangent 1 = direction := by
  have h_id : deriv (fun s : ℝ => s) 1 = 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).deriv
  have h_sq : deriv (fun s : ℝ => s ^ 2) 1 = 2 := by
    have hfun : (fun s : ℝ => s ^ 2) = (fun s : ℝ => s * s) := by
      funext s
      exact pow_two s
    calc
      deriv (fun s : ℝ => s ^ 2) 1 =
          deriv (fun s : ℝ => s * s) 1 :=
        congrArg (fun f : ℝ → ℝ => deriv f 1) hfun
      _ = 1 * 1 + 1 * 1 :=
        ((hasDerivAt_id (1 : ℝ)).mul (hasDerivAt_id (1 : ℝ))).deriv
      _ = 2 := by ring
  change
    (deriv (fun s : ℝ => s) 1,
      (deriv (fun s : ℝ => s) 1, deriv (fun s : ℝ => s ^ 2) 1)) =
      (1, (1, 2))
  rw [h_id, h_sq]

theorem gap4 (Q : Point3)
    (hLine : OnTangentLine basePoint direction Q) :
    (Q.1 - 1) * direction.2.1 = (Q.2.1 - 1) * direction.1 := by
  rcases hLine with ⟨s, rfl⟩
  unfold linePoint basePoint direction
  ring

theorem gap5 (Q : Point3)
    (hLine : OnTangentLine basePoint direction Q) :
    (Q.2.1 - 1) * direction.2.2 = (Q.2.2 - 1) * direction.2.1 := by
  rcases hLine with ⟨s, rfl⟩
  unfold linePoint basePoint direction
  ring

theorem gap6 (Q : Point3)
    (hLine : OnTangentLine basePoint direction Q) :
    (Q.1 - 1) * direction.2.2 = (Q.2.2 - 1) * direction.1 := by
  rcases hLine with ⟨s, rfl⟩
  unfold linePoint basePoint direction
  ring

theorem gap7 (Q : Point3)
    (hPlane : OnNormalPlane basePoint direction Q) :
    (Q.1 - 1) + (Q.2.1 - 1) + 2 * (Q.2.2 - 1) = 0 := by
  simpa [OnNormalPlane, basePoint, direction] using hPlane

theorem gap8 (Q : Point3)
    (hPlane : OnNormalPlane basePoint direction Q) :
    Q.1 + Q.2.1 + 2 * Q.2.2 = 4 := by
  have h := gap7 Q hPlane
  linarith

end

end ProofGap.Exercise3530
